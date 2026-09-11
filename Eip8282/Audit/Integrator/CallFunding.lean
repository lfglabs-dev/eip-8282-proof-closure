import Eip8282.Audit.Integrator.TransferFunding
import Eip8282.Audit.Integrator.AuditedChildGas
import Eip8282.Audit.Integrator.CallFamilyGas

/-!
# Funding at actual CALL-family entry

The dispatcher funds gate yields the natural sender-balance premise for the
literal child Context's actual credit-then-debit transfer. CALL and CALLCODE
bind source to codeOwner; DELEGATECALL and STATICCALL transfer zero actual
value. No claim is made for an arbitrary-source raw call helper or for total
funds after child execution, transaction settlement, or protocol issuance.
-/
namespace Eip8282.Audit.Integrator.CallFunding

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec
open MessageCall TransferFunding
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- The word-order test reads zero for a missing account, just like worldBalance. -/
theorem gate_to_nat (world : AccountMap .EVM) (sender : AccountAddress) (value : UInt256)
    (h : value ≤ (world.get? sender |>.option ⟨0⟩ (·.balance))) :
    value.toNat ≤ worldBalance world sender := by
  unfold worldBalance
  cases he : world.get? sender with
  | none => rw [he] at h; exact h
  | some account => rw [he] at h; exact h

/-- The source passed by the real CALL dispatcher is the account it checks. -/
theorem call_source (pre : EVM.State) :
    AuditedChildGas.source pre = pre.executionEnv.codeOwner :=
  CallFamilyGas.address_word _

/-- The admitted CALL gate supplies sufficient funds before any child code runs. -/
theorem call_funded (fuel : Nat) (code : ByteArray) (pre : EVM.State)
    (requested target value inOff inLen : UInt256)
    (hgate : value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance))) :
    (AuditedChildGas.context fuel code pre requested target value inOff inLen).value.toNat ≤
      worldBalance (AuditedChildGas.context fuel code pre requested target value inOff inLen).world
        (AuditedChildGas.context fuel code pre requested target value inOff inLen).caller := by
  change value.toNat ≤ worldBalance pre.accountMap (AuditedChildGas.source pre)
  rw [call_source]
  exact gate_to_nat _ _ _ hgate

theorem call_entry_funds_le (fuel : Nat) (code : ByteArray) (pre : EVM.State)
    (requested target value inOff inLen : UInt256)
    (hgate : value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance))) :
    worldFunds (AuditedChildGas.context fuel code pre requested target value inOff inLen).entryWorld ≤
      worldFunds pre.accountMap :=
  entry_funds_le _ (call_funded fuel code pre requested target value inOff inLen hgate)

theorem call_entry_budget (fuel : Nat) (code : ByteArray) (pre : EVM.State)
    (requested target value inOff inLen : UInt256) (budget : Nat)
    (hgate : value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)))
    (hbudget : worldFunds pre.accountMap ≤ budget) :
    worldFunds (AuditedChildGas.context fuel code pre requested target value inOff inLen).entryWorld ≤ budget :=
  (call_entry_funds_le fuel code pre requested target value inOff inLen hgate).trans hbudget

/-- Literal variant Context; the storage recipient can differ from the code target. -/
def familyContext (kind : CallFamilyGas.Variant) (fuel : Nat) (code : ByteArray) (pre : EVM.State)
    (requested target value inOff inLen : UInt256) : Context :=
  { fuel := fuel-1, created := pre.createdAccounts, genesis := pre.genesisBlockHeader,
    blocks := pre.blocks, world := pre.accountMap, originalWorld := pre.σ₀,
    substate := (pre.addAccessedAccount (AccountAddress.ofUInt256 target)).substate,
    caller := AccountAddress.ofUInt256 (CallFamilyGas.source kind pre),
    origin := pre.executionEnv.sender,
    target := AccountAddress.ofUInt256 (CallFamilyGas.recipient kind pre target), code := code,
    gas := UInt256.ofNat (CallFamilyGas.allowance kind pre requested target value),
    gasPrice := UInt256.ofNat pre.executionEnv.gasPrice,
    value := CallFamilyGas.transfer kind value, apparentValue := CallFamilyGas.apparent kind pre value,
    calldata := pre.memory.readWithPadding inOff.toNat inLen.toNat,
    depth := pre.executionEnv.depth+1, header := pre.executionEnv.header,
    permission := CallFamilyGas.permission kind pre, blobHashes := pre.executionEnv.blobVersionedHashes }

/-- Exact actual Theta binding, including code selection and positive child fuel. -/
theorem family_context_result (kind : CallFamilyGas.Variant) (fuel : Nat) (code : ByteArray)
    (pre : EVM.State) (requested target value inOff inLen : UInt256) (hf : 0 < fuel)
    (hcode : toExecute .EVM pre.accountMap (AccountAddress.ofUInt256 target) = .Code code) :
    (familyContext kind fuel code pre requested target value inOff inLen).result =
      CallFamilyGas.childResult kind fuel pre requested target value inOff inLen := by
  unfold familyContext Context.result CallFamilyGas.childResult CallGasAccounting.child
    CallDispatchGas.entered CallFamilyGas.allowance
  rw [show fuel-1+1 = fuel by omega, hcode]

/-- Only CALLCODE needs a nonzero transfer gate. Apparent DELEGATECALL value
never becomes an actual transfer for this premise. -/
theorem family_funded (kind : CallFamilyGas.Variant) (fuel : Nat) (code : ByteArray)
    (pre : EVM.State) (requested target value inOff inLen : UInt256)
    (hgate : CallFamilyGas.transfer kind value ≤
      (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance))) :
    (familyContext kind fuel code pre requested target value inOff inLen).value.toNat ≤
      worldBalance (familyContext kind fuel code pre requested target value inOff inLen).world
        (familyContext kind fuel code pre requested target value inOff inLen).caller := by
  cases kind with
  | callcode =>
    change value.toNat ≤ worldBalance pre.accountMap
      (AccountAddress.ofUInt256 (UInt256.ofNat pre.executionEnv.codeOwner))
    rw [CallFamilyGas.address_word]
    exact gate_to_nat _ _ _ hgate
  | delegatecall => exact Nat.zero_le _
  | staticcall => exact Nat.zero_le _

theorem family_entry_funds_le (kind : CallFamilyGas.Variant) (fuel : Nat) (code : ByteArray)
    (pre : EVM.State) (requested target value inOff inLen : UInt256)
    (hgate : CallFamilyGas.transfer kind value ≤
      (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance))) :
    worldFunds (familyContext kind fuel code pre requested target value inOff inLen).entryWorld ≤
      worldFunds pre.accountMap :=
  entry_funds_le _ (family_funded kind fuel code pre requested target value inOff inLen hgate)

theorem family_entry_budget (kind : CallFamilyGas.Variant) (fuel : Nat) (code : ByteArray)
    (pre : EVM.State) (requested target value inOff inLen : UInt256) (budget : Nat)
    (hgate : CallFamilyGas.transfer kind value ≤
      (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)))
    (hbudget : worldFunds pre.accountMap ≤ budget) :
    worldFunds (familyContext kind fuel code pre requested target value inOff inLen).entryWorld ≤ budget :=
  (family_entry_funds_le kind fuel code pre requested target value inOff inLen hgate).trans hbudget

/-- Recover an actual CALL child from the dispatcher, retaining its real result
and the proved entry-transfer bound. No predicted child result is supplied. -/
theorem call_step_entry (fuel cost : Nat) (code : ByteArray) {pre post : EVM.State}
    {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::rest)
    (hgate : value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      pre.executionEnv.depth < 1024)
    (hcode : toExecute .EVM pre.accountMap (AccountAddress.ofUInt256 target) = .Code code)
    (h : StepOk (fuel+2) cost (.CALL,arg) pre post) :
    ∃ created world gas substate success out,
      (AuditedChildGas.context fuel code pre requested target value inOff inLen).result =
        .ok (created,world,gas,substate,success,out) ∧
      worldFunds (AuditedChildGas.context fuel code pre requested target value inOff inLen).entryWorld ≤
        worldFunds pre.accountMap := by
  obtain ⟨created,world,gas,substate,success,out,hchild,_⟩ :=
    CallDispatchGas.step_call_child_gas fuel cost requested target value inOff inLen outOff outLen rest hstack hgate h
  have hf := AuditedChildGas.child_positive fuel pre requested target value inOff inLen hchild
  exact ⟨created,world,gas,substate,success,out,
    (AuditedChildGas.context_result fuel code pre requested target value inOff inLen hf hcode).trans hchild,
    call_entry_funds_le fuel code pre requested target value inOff inLen hgate.1⟩

/-- The same actual-child extraction for CALLCODE, DELEGATECALL and STATICCALL.
The explicit admission gate excludes the helper's no-child denied branch. -/
theorem family_step_entry (kind : CallFamilyGas.Variant) (fuel cost : Nat) (code : ByteArray)
    {pre post : EVM.State} {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = CallFamilyGas.stack kind requested target value inOff inLen outOff outLen rest)
    (hgate : CallFamilyGas.gate kind pre value)
    (hcode : toExecute .EVM pre.accountMap (AccountAddress.ofUInt256 target) = .Code code)
    (h : StepOk (fuel+2) cost (CallFamilyGas.opcode kind,arg) pre post) :
    ∃ created world gas substate success out,
      (familyContext kind fuel code pre requested target value inOff inLen).result =
        .ok (created,world,gas,substate,success,out) ∧
      worldFunds (familyContext kind fuel code pre requested target value inOff inLen).entryWorld ≤
        worldFunds pre.accountMap := by
  obtain ⟨created,world,gas,substate,success,out,hchild,_⟩ :=
    CallFamilyGas.step_child_gas kind fuel cost requested target value inOff inLen outOff outLen rest hstack hgate h
  have hf : 0 < fuel := by
    cases fuel with
    | zero => change Except.error ExecutionException.OutOfFuel = Except.ok _ at hchild; cases hchild
    | succ fuel => omega
  exact ⟨created,world,gas,substate,success,out,
    (family_context_result kind fuel code pre requested target value inOff inLen hf hcode).trans hchild,
    family_entry_funds_le kind fuel code pre requested target value inOff inLen hgate.1⟩

#print axioms gate_to_nat
#print axioms call_funded
#print axioms call_entry_funds_le
#print axioms call_entry_budget
#print axioms family_context_result
#print axioms family_funded
#print axioms family_entry_funds_le
#print axioms family_entry_budget
#print axioms call_step_entry
#print axioms family_step_entry

end Eip8282.Audit.Integrator.CallFunding
