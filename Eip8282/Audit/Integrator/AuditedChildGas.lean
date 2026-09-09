import Eip8282.Audit.Integrator.CallDispatchGas
import Eip8282.Audit.Integrator.AppendGasPath

/-!
# Audited child append charges in actual CALL dispatch

A literal child Context binds the actual Theta inputs selected by CALL. Its
successful audited append supplies the child gas bound; the parent debit then
follows through actual Z and StepOk. No child-gas inequality or supported-path
witness is supplied. This is one actual CALL edge, not aggregate tree accounting.
-/
namespace Eip8282.Audit.Integrator.AuditedChildGas

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Correspondence (runtimeCode)
open CallGasAccounting CallDispatchGas
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- Immediate source actually passed by CALL to Theta. -/
def source (pre : EVM.State) : AccountAddress :=
  AccountAddress.ofUInt256 (UInt256.ofNat pre.executionEnv.codeOwner)

/-- The exact CALL allowance before opcode-cost subtraction. -/
def allowance (pre : EVM.State) (requested target value : UInt256) : Nat :=
  Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
    value requested pre.accountMap pre.toMachineState pre.substate

/-- Literal message-call inputs selected by the existing CALL helper. -/
def context (fuel : Nat) (code : ByteArray) (pre : EVM.State)
    (requested target value inOff inLen : UInt256) : MessageCall.Context :=
  { fuel := fuel-1, created := pre.createdAccounts, genesis := pre.genesisBlockHeader,
    blocks := pre.blocks, world := pre.accountMap, originalWorld := pre.σ₀,
    substate := (pre.addAccessedAccount (AccountAddress.ofUInt256 target)).substate,
    caller := source pre, origin := pre.executionEnv.sender,
    target := AccountAddress.ofUInt256 target, code := code,
    gas := UInt256.ofNat (allowance pre requested target value),
    gasPrice := UInt256.ofNat pre.executionEnv.gasPrice, value := value, apparentValue := value,
    calldata := pre.memory.readWithPadding inOff.toNat inLen.toNat,
    depth := pre.executionEnv.depth+1, header := pre.executionEnv.header,
    permission := pre.executionEnv.perm, blobHashes := pre.executionEnv.blobVersionedHashes }

/-- Any completed literal child invocation has positive Theta fuel. -/
theorem child_positive (fuel : Nat) (pre : EVM.State)
    (requested target value inOff inLen : UInt256)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : child fuel pre.executionEnv.blobVersionedHashes requested
      (UInt256.ofNat pre.executionEnv.codeOwner) target target value value inOff inLen
      pre.executionEnv.perm (entered pre) = .ok (created,world,gas,substate,success,out)) : 0 < fuel := by
  cases fuel with
  | zero => change Except.error ExecutionException.OutOfFuel = Except.ok _ at h; cases h
  | succ fuel => omega

/-- Exact context binding includes actual toExecute code selection and fuel.
The instruction-count update changes none of the Theta inputs. -/
theorem context_result (fuel : Nat) (code : ByteArray) (pre : EVM.State)
    (requested target value inOff inLen : UInt256) (hf : 0 < fuel)
    (hcode : toExecute .EVM pre.accountMap (AccountAddress.ofUInt256 target) = .Code code) :
    (context fuel code pre requested target value inOff inLen).result =
      child fuel pre.executionEnv.blobVersionedHashes requested
        (UInt256.ofNat pre.executionEnv.codeOwner) target target value value inOff inLen
        pre.executionEnv.perm (entered pre) := by
  unfold context MessageCall.Context.result child entered allowance source
  rw [show fuel-1+1 = fuel by omega, hcode]

def inputSize : Kind → Nat | .deposit => 184 | .exit => 48

def appendCharge : Kind → Nat | .deposit => 1847 | .exit => 919

/-- Actual successful audited child execution supplies its own gas-debit bound. -/
theorem child_append_debit (kind : Kind) (fuel : Nat) (pre : EVM.State)
    (requested target value inOff inLen : UInt256)
    (hcode : toExecute .EVM pre.accountMap (AccountAddress.ofUInt256 target) = .Code (runtimeCode kind))
    (huser : source pre ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hsize : (pre.memory.readWithPadding inOff.toNat inLen.toNat).size = inputSize kind)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : child fuel pre.executionEnv.blobVersionedHashes requested
      (UInt256.ofNat pre.executionEnv.codeOwner) target target value value inOff inLen
      pre.executionEnv.perm (entered pre) = .ok (created,world,gas,substate,true,out)) :
    gas.toNat + appendCharge kind ≤ (UInt256.ofNat (allowance pre requested target value)).toNat := by
  have hf := child_positive fuel pre requested target value inOff inLen h
  have hc : (context fuel (runtimeCode kind) pre requested target value inOff inLen).result =
      .ok (created,world,gas,substate,true,out) :=
    (context_result fuel _ pre requested target value inOff inLen hf hcode).trans h
  cases kind with
  | deposit => exact AppendGasPath.deposit_theta_debit _ rfl huser hsize hc
  | exit => exact AppendGasPath.exit_theta_debit _ rfl huser hsize hc

/-- Join the observed successful child result to the child extracted from the
actual CALL step. The child charge is counted once, with stipend-adjusted overhead.
A later ancestor rollback does not affect this already executed step's gas fact. -/
theorem parent_append_debit (kind : Kind) (fuel : Nat)
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat}
    {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (stk : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::stk)
    (hz : Z vj .CALL pre = .ok (mid,cost))
    (hgate : value ≤ (mid.accountMap.get? mid.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      mid.executionEnv.depth < 1024)
    (hstep : StepOk (fuel+2) cost (.CALL,arg) mid post)
    (hcode : toExecute .EVM mid.accountMap (AccountAddress.ofUInt256 target) = .Code (runtimeCode kind))
    (huser : source mid ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hsize : (mid.memory.readWithPadding inOff.toNat inLen.toNat).size = inputSize kind)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hchild : child fuel mid.executionEnv.blobVersionedHashes requested
      (UInt256.ofNat mid.executionEnv.codeOwner) target target value value inOff inLen
      mid.executionEnv.perm (entered mid) = .ok (created,world,gas,substate,true,out)) :
    post.gasAvailable.toNat + appendCharge kind +
      (Cextra (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        value mid.accountMap mid.substate - stipend value) + memoryExpansionCost pre .CALL ≤
      pre.gasAvailable.toNat := by
  have hcharge := child_append_debit kind fuel mid requested target value inOff inLen hcode huser hsize hchild
  have hfit := (accepted_call_forwarded_fit hstack hz).2
  unfold allowance at hcharge
  rw [hfit] at hcharge
  obtain ⟨ic,iw,ig,ia,iz,io,he,hd⟩ :=
    accepted_step_call_debit fuel requested target value inOff inLen outOff outLen stk hstack hz hgate hstep
  have hgas : ig = gas :=
    congrArg (fun p => p.2.2.1) (Except.ok.inj (he.symm.trans hchild))
  have hreturn : ig.toNat ≤ Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
      value requested mid.accountMap mid.toMachineState mid.substate := by
    rw [hgas]
    omega
  have hdebit := hd hreturn
  rw [hgas] at hdebit
  omega

#print axioms context_result
#print axioms child_append_debit
#print axioms parent_append_debit

end Eip8282.Audit.Integrator.AuditedChildGas
