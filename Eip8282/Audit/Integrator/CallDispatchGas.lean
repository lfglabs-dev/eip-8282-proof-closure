import Eip8282.Audit.Integrator.CallGasAccounting

/-!
# Gas accounting through actual CALL opcode dispatch

The opcode's seven stack operands, instruction-count update and helper fuel
are bound to the actual EVM.step result. Child gas settlement is then obtained
from the actual helper invocation. Child remaining-gas monotonicity is an
explicit local boundary; no aggregate call-tree bound is assumed.
-/
namespace Eip8282.Audit.Integrator.CallDispatchGas

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open CallGasAccounting ActualAppendGas
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
set_option autoImplicit false

/-- The exact instruction-count update made before CALL dispatch. -/
def entered (pre : EVM.State) : EVM.State := { pre with execLength := pre.execLength+1 }

/-- The CALL opcode's literal helper invocation, with actual value also used
as apparent value and the code owner used as source. -/
def helper (fuel cost : Nat) (pre : EVM.State)
    (requested target value inOff inLen outOff outLen : UInt256) :=
  EvmYul.EVM.call (fuel+1) cost pre.executionEnv.blobVersionedHashes requested
    (UInt256.ofNat pre.executionEnv.codeOwner) target target value value inOff inLen outOff outLen
    pre.executionEnv.perm (entered pre)

/-- Recover the actual helper call and final stack/PC replacement from StepOk.
EVM.step (fuel+2) dispatches call (fuel+1), which may invoke Theta fuel. -/
theorem step_call_helper (fuel cost : Nat) {pre post : EVM.State}
    {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (stk : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::stk)
    (h : StepOk (fuel+2) cost (.CALL,arg) pre post) :
    ∃ x middle,
      helper fuel cost pre requested target value inOff inLen outOff outLen = .ok (x,middle) ∧
      post = middle.replaceStackAndIncrPC (x::stk) := by
  have hs : pre.stack.pop7 = some (stk,requested,target,value,inOff,inLen,outOff,outLen) := by
    rw [hstack]
    rfl
  simp only [StepOk, Step, EvmYul.EVM.step, Bind.bind, Except.bind, pure, Except.pure] at h
  rw [hs] at h
  change (do
    let (x,middle) ← helper fuel cost pre requested target value inOff inLen outOff outLen
    pure (middle.replaceStackAndIncrPC (x::stk))) = .ok post at h
  cases hh : helper fuel cost pre requested target value inOff inLen outOff outLen with
  | error err => simp only [hh, Bind.bind, Except.bind] at h; cases h
  | ok result =>
      obtain ⟨x,middle⟩ := result
      simp only [hh, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨x,middle,rfl,h.symm⟩

/-- CALL's final stack/PC update preserves the helper's returned gas. -/
theorem step_call_child_gas (fuel cost : Nat) {pre post : EVM.State}
    {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (stk : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::stk)
    (hgate : value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      pre.executionEnv.depth < 1024)
    (h : StepOk (fuel+2) cost (.CALL,arg) pre post) :
    ∃ created world returnedGas substate success out,
      child fuel pre.executionEnv.blobVersionedHashes requested
        (UInt256.ofNat pre.executionEnv.codeOwner) target target value value inOff inLen
        pre.executionEnv.perm (entered pre) = .ok (created,world,returnedGas,substate,success,out) ∧
      post.gasAvailable = pre.gasAvailable - UInt256.ofNat cost + returnedGas := by
  obtain ⟨x,middle,hh,hpost⟩ := step_call_helper fuel cost requested target value inOff inLen outOff outLen stk hstack h
  obtain ⟨created,world,returnedGas,substate,success,out,hchild,hgas⟩ :=
    call_child_result_gas fuel cost pre.executionEnv.blobVersionedHashes requested
      (UInt256.ofNat pre.executionEnv.codeOwner) target target value value inOff inLen outOff outLen
      pre.executionEnv.perm (entered pre) middle x hgate hh
  refine ⟨created,world,returnedGas,substate,success,out,hchild,?_⟩
  rw [hpost]
  exact hgas

/-- Actual accepted CALL dispatch preserves the helper's natural gas equation,
including the pre-op memory debit. Child returned-gas monotonicity remains local. -/
theorem accepted_step_call_debit (fuel : Nat)
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat}
    {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (stk : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::stk)
    (hz : Z vj .CALL pre = .ok (mid,cost))
    (hgate : value ≤ (mid.accountMap.get? mid.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      mid.executionEnv.depth < 1024)
    (h : StepOk (fuel+2) cost (.CALL,arg) mid post) :
    ∃ created world returnedGas substate success out,
      child fuel mid.executionEnv.blobVersionedHashes requested
        (UInt256.ofNat mid.executionEnv.codeOwner) target target value value inOff inLen
        mid.executionEnv.perm (entered mid) = .ok (created,world,returnedGas,substate,success,out) ∧
      (returnedGas.toNat ≤ Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        value requested mid.accountMap mid.toMachineState mid.substate →
        post.gasAvailable.toNat +
          (Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
            value requested mid.accountMap mid.toMachineState mid.substate - returnedGas.toNat) +
          (Cextra (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
            value mid.accountMap mid.substate - stipend value) + memoryExpansionCost pre .CALL =
          pre.gasAvailable.toNat) := by
  obtain ⟨created,world,returnedGas,substate,success,out,hchild,hgas⟩ :=
    step_call_child_gas fuel cost requested target value inOff inLen outOff outLen stk
      ((Z_ok_stack hz).trans hstack) hgate h
  refine ⟨created,world,returnedGas,substate,success,out,hchild,?_⟩
  intro hreturn
  obtain ⟨hm,hmid,hcost,_⟩ := accepted_gas hz
  have hd := (settlement_nat (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
    value requested mid post.gasAvailable returnedGas cost
    (accepted_call_cost hstack hz) hcost hreturn hgas).2
  omega

/-- Actual denied CALL dispatch pushes zero and credits back exactly callgas. -/
theorem step_call_denied_gas (fuel cost : Nat) {pre post : EVM.State}
    {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (stk : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::stk)
    (hgate : ¬ (value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      pre.executionEnv.depth < 1024))
    (h : StepOk (fuel+2) cost (.CALL,arg) pre post) :
    post.stack = ⟨0⟩::stk ∧ post.gasAvailable = pre.gasAvailable - UInt256.ofNat cost +
      UInt256.ofNat (Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        value requested pre.accountMap pre.toMachineState pre.substate) := by
  obtain ⟨x,middle,hh,hpost⟩ := step_call_helper fuel cost requested target value inOff inLen outOff outLen stk hstack h
  obtain ⟨hx,hgas⟩ := call_denied_gas fuel cost pre.executionEnv.blobVersionedHashes requested
    (UInt256.ofNat pre.executionEnv.codeOwner) target target value value inOff inLen outOff outLen
    pre.executionEnv.perm (entered pre) middle x hgate hh
  rw [hpost, hx]
  exact ⟨rfl,hgas⟩

/-- A denied CALL consumes only memory plus overhead minus stipend; no child
execution is inserted into the accounting. Every fit follows from actual Z. -/
theorem accepted_step_call_denied_debit (fuel : Nat)
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat}
    {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (stk : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::stk)
    (hz : Z vj .CALL pre = .ok (mid,cost))
    (hgate : ¬ (value ≤ (mid.accountMap.get? mid.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      mid.executionEnv.depth < 1024))
    (h : StepOk (fuel+2) cost (.CALL,arg) mid post) :
    post.stack = ⟨0⟩::stk ∧ post.gasAvailable.toNat +
      (Cextra (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        value mid.accountMap mid.substate - stipend value) + memoryExpansionCost pre .CALL =
        pre.gasAvailable.toNat := by
  obtain ⟨hstack',hgas⟩ := step_call_denied_gas fuel cost requested target value inOff inLen outOff outLen stk
    ((Z_ok_stack hz).trans hstack) hgate h
  refine ⟨hstack',?_⟩
  obtain ⟨hm,hmid,hcost,_⟩ := accepted_gas hz
  have hfit := (accepted_call_forwarded_fit hstack hz).2
  have hd := (settlement_nat (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
    value requested mid post.gasAvailable _ cost
    (accepted_call_cost hstack hz) hcost (by rw [hfit]) hgas).2
  rw [hfit, Nat.sub_self, Nat.add_zero] at hd
  omega

#print axioms step_call_helper
#print axioms step_call_child_gas
#print axioms accepted_step_call_debit
#print axioms step_call_denied_gas
#print axioms accepted_step_call_denied_debit

end Eip8282.Audit.Integrator.CallDispatchGas
