import Eip8282.Audit.Integrator.CallDispatchGas

/-!
# Actual CALLCODE, DELEGATECALL and STATICCALL gas settlement

Variant selects only the literal argument layout of the pinned EVM dispatcher.
It is not an execution model. Each helper and child is the actual EVM.call/Θ
invocation. Storage recipient and code target remain distinct; stipend depends
on transferred value, never apparent CALLVALUE. Child remaining-gas monotonicity
remains an explicit local boundary for recursive induction.
-/
namespace Eip8282.Audit.Integrator.CallFamilyGas

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open CallGasAccounting ActualAppendGas
open CallDispatchGas (entered)
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
set_option autoImplicit false

inductive Variant where
  | callcode | delegatecall | staticcall
  deriving DecidableEq

def opcode : Variant → Operation .EVM
  | .callcode => .CALLCODE | .delegatecall => .DELEGATECALL | .staticcall => .STATICCALL

/-- CALLCODE has a value operand; the other variants have exactly six operands.
The extra value parameter is ignored by those variants in every definition. -/
def stack (kind : Variant) (requested target value inOff inLen outOff outLen : UInt256)
    (rest : Stack UInt256) : Stack UInt256 :=
  match kind with
  | .callcode => requested::target::value::inOff::inLen::outOff::outLen::rest
  | .delegatecall | .staticcall => requested::target::inOff::inLen::outOff::outLen::rest

def source (kind : Variant) (pre : EVM.State) : UInt256 :=
  match kind with
  | .delegatecall => UInt256.ofNat pre.executionEnv.source
  | .callcode | .staticcall => UInt256.ofNat pre.executionEnv.codeOwner

def recipient (kind : Variant) (pre : EVM.State) (target : UInt256) : UInt256 :=
  match kind with
  | .callcode | .delegatecall => UInt256.ofNat pre.executionEnv.codeOwner
  | .staticcall => target

def transfer (kind : Variant) (value : UInt256) : UInt256 :=
  match kind with
  | .callcode => value | .delegatecall | .staticcall => ⟨0⟩

def apparent (kind : Variant) (pre : EVM.State) (value : UInt256) : UInt256 :=
  match kind with
  | .callcode => value | .delegatecall => pre.executionEnv.weiValue | .staticcall => ⟨0⟩

def permission (kind : Variant) (pre : EVM.State) : Bool :=
  match kind with
  | .callcode | .delegatecall => pre.executionEnv.perm | .staticcall => false

/-- Literal helper called by EVM.step after its instruction-count update. -/
def helper (kind : Variant) (fuel cost : Nat) (pre : EVM.State)
    (requested target value inOff inLen outOff outLen : UInt256) :=
  EVM.call (fuel+1) cost pre.executionEnv.blobVersionedHashes requested
    (source kind pre) (recipient kind pre target) target (transfer kind value)
    (apparent kind pre value) inOff inLen outOff outLen (permission kind pre) (entered pre)

/-- Literal child Θ, preserving source, recipient, code selection and both values. -/
def childResult (kind : Variant) (fuel : Nat) (pre : EVM.State)
    (requested target value inOff inLen : UInt256) :=
  child fuel pre.executionEnv.blobVersionedHashes requested
    (source kind pre) (recipient kind pre target) target (transfer kind value)
    (apparent kind pre value) inOff inLen (permission kind pre) (entered pre)

def allowance (kind : Variant) (pre : EVM.State) (requested target value : UInt256) : Nat :=
  Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 (recipient kind pre target))
    (transfer kind value) requested pre.accountMap pre.toMachineState pre.substate

def overhead (kind : Variant) (pre : EVM.State) (target value : UInt256) : Nat :=
  Cextra (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 (recipient kind pre target))
    (transfer kind value) pre.accountMap pre.substate - stipend (transfer kind value)

def gate (kind : Variant) (pre : EVM.State) (value : UInt256) : Prop :=
  transfer kind value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
    pre.executionEnv.depth < 1024

/-- Actual dispatch identifies the helper result and exact final stack update. -/
theorem step_helper (kind : Variant) (fuel cost : Nat) {pre post : EVM.State}
    {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = stack kind requested target value inOff inLen outOff outLen rest)
    (h : StepOk (fuel+2) cost (opcode kind,arg) pre post) :
    ∃ x middle, helper kind fuel cost pre requested target value inOff inLen outOff outLen = .ok (x,middle) ∧
      post = middle.replaceStackAndIncrPC (x::rest) := by
  have hexec :
      (do let (x,middle) ← helper kind fuel cost pre requested target value inOff inLen outOff outLen
          pure (middle.replaceStackAndIncrPC (x::rest))) = Except.ok post := by
    cases kind with
    | callcode =>
      have hs : pre.stack.pop7 = some (rest,requested,target,value,inOff,inLen,outOff,outLen) := by
        rw [hstack]; rfl
      simp only [StepOk, Step, opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at h
      rw [hs] at h
      exact h
    | delegatecall =>
      have hs : pre.stack.pop6 = some (rest,requested,target,inOff,inLen,outOff,outLen) := by
        rw [hstack]; rfl
      simp only [StepOk, Step, opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at h
      rw [hs] at h
      exact h
    | staticcall =>
      have hs : pre.stack.pop6 = some (rest,requested,target,inOff,inLen,outOff,outLen) := by
        rw [hstack]; rfl
      simp only [StepOk, Step, opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at h
      rw [hs] at h
      exact h
  cases hh : helper kind fuel cost pre requested target value inOff inLen outOff outLen with
  | error err => simp only [hh, Bind.bind, Except.bind] at hexec; cases hexec
  | ok result =>
    obtain ⟨x,middle⟩ := result
    simp only [hh, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hexec
    exact ⟨x,middle,rfl,hexec.symm⟩

/-- A 160-bit address round-trips through its dispatcher word. -/
theorem address_word (addr : AccountAddress) :
    AccountAddress.ofUInt256 (UInt256.ofNat addr.val) = addr := by
  apply Fin.ext
  change ((addr.val % UInt256.size) % AccountAddress.size) % AccountAddress.size = addr.val
  have hw : addr.val < UInt256.size := addr.isLt.trans_le (by decide)
  rw [Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt addr.isLt, Nat.mod_eq_of_lt addr.isLt]

/-- C' charges the same target, recipient and actual value as literal dispatch. -/
theorem accepted_cost (kind : Variant) {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    {requested target value inOff inLen outOff outLen : UInt256} {rest : Stack UInt256}
    (hstack : pre.stack = stack kind requested target value inOff inLen outOff outLen rest)
    (hz : Z vj (opcode kind) pre = .ok (mid,cost)) :
    cost = Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 (recipient kind mid target))
      (transfer kind value) requested mid.accountMap mid.toMachineState mid.substate := by
  have hs := (Z_ok_stack hz).trans hstack
  rw [(accepted_gas hz).2.2.2]
  cases kind <;> simp only [opcode, C', stack, hs, recipient, transfer,
    List.getElem!_cons_succ, List.getElem!_cons_zero, address_word]

/-- Before child execution, actual Z proves the stipend-inclusive allowance fits. -/
theorem accepted_forwarded_fit (kind : Variant)
    {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    {requested target value inOff inLen outOff outLen : UInt256} {rest : Stack UInt256}
    (hstack : pre.stack = stack kind requested target value inOff inLen outOff outLen rest)
    (hz : Z vj (opcode kind) pre = .ok (mid,cost)) :
    allowance kind mid requested target value < UInt256.size ∧
      (UInt256.ofNat (allowance kind mid requested target value)).toNat =
        allowance kind mid requested target value := by
  have hc := accepted_cost kind hstack hz
  have hb := callgas_le_call (AccountAddress.ofUInt256 target)
    (AccountAddress.ofUInt256 (recipient kind mid target)) (transfer kind value)
    requested mid.accountMap mid.toMachineState mid.substate
  rw [← hc] at hb
  have hf := (hb.trans (accepted_gas hz).2.2.1).trans_lt mid.gasAvailable.val.isLt
  exact ⟨hf, toNat_ofNat_lit _ hf⟩

/-- Actual permitted dispatch recovers one literal child result, with exact gas
settlement independent of that child's true/false returned status. -/
theorem step_child_gas (kind : Variant) (fuel cost : Nat) {pre post : EVM.State}
    {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = stack kind requested target value inOff inLen outOff outLen rest)
    (hgate : gate kind pre value)
    (h : StepOk (fuel+2) cost (opcode kind,arg) pre post) :
    ∃ created world returnedGas substate success out,
      childResult kind fuel pre requested target value inOff inLen =
        .ok (created,world,returnedGas,substate,success,out) ∧
      post.gasAvailable = pre.gasAvailable - UInt256.ofNat cost + returnedGas := by
  obtain ⟨x,middle,hh,hpost⟩ := step_helper kind fuel cost requested target value inOff inLen outOff outLen rest hstack h
  obtain ⟨created,world,returnedGas,substate,success,out,hchild,hgas⟩ :=
    call_child_result_gas fuel cost pre.executionEnv.blobVersionedHashes requested
      (source kind pre) (recipient kind pre target) target (transfer kind value)
      (apparent kind pre value) inOff inLen outOff outLen (permission kind pre)
      (entered pre) middle x hgate hh
  refine ⟨created,world,returnedGas,substate,success,out,hchild,?_⟩
  rw [hpost]
  exact hgas

/-- Natural parent/child debit for the actual accepted variant. A local returned
bound is explicit; overhead subtracts stipend to avoid charging it twice. -/
theorem accepted_step_debit (kind : Variant) (fuel : Nat)
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat}
    {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = stack kind requested target value inOff inLen outOff outLen rest)
    (hz : Z vj (opcode kind) pre = .ok (mid,cost))
    (hgate : gate kind mid value)
    (h : StepOk (fuel+2) cost (opcode kind,arg) mid post) :
    ∃ created world returnedGas substate success out,
      childResult kind fuel mid requested target value inOff inLen =
        .ok (created,world,returnedGas,substate,success,out) ∧
      (returnedGas.toNat ≤ allowance kind mid requested target value →
        post.gasAvailable.toNat + (allowance kind mid requested target value - returnedGas.toNat) +
          overhead kind mid target value + memoryExpansionCost pre (opcode kind) = pre.gasAvailable.toNat) := by
  obtain ⟨created,world,returnedGas,substate,success,out,hchild,hgas⟩ :=
    step_child_gas kind fuel cost requested target value inOff inLen outOff outLen rest
      ((Z_ok_stack hz).trans hstack) hgate h
  refine ⟨created,world,returnedGas,substate,success,out,hchild,?_⟩
  intro hreturn
  obtain ⟨hm,hmid,hcost,_⟩ := accepted_gas hz
  have hd := (settlement_nat (AccountAddress.ofUInt256 target)
    (AccountAddress.ofUInt256 (recipient kind mid target)) (transfer kind value) requested
    mid post.gasAvailable returnedGas cost (accepted_cost kind hstack hz) hcost hreturn hgas).2
  change post.gasAvailable.toNat + (allowance kind mid requested target value - returnedGas.toNat) +
    overhead kind mid target value = mid.gasAvailable.toNat at hd
  omega

/-- Denied funds/depth dispatch invokes no child, pushes zero, and returns its
actual forwarded allowance. For zero-value variants only depth can deny it. -/
theorem step_denied_gas (kind : Variant) (fuel cost : Nat) {pre post : EVM.State}
    {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = stack kind requested target value inOff inLen outOff outLen rest)
    (hgate : ¬ gate kind pre value)
    (h : StepOk (fuel+2) cost (opcode kind,arg) pre post) :
    post.stack = ⟨0⟩::rest ∧ post.gasAvailable = pre.gasAvailable - UInt256.ofNat cost +
      UInt256.ofNat (allowance kind pre requested target value) := by
  obtain ⟨x,middle,hh,hpost⟩ := step_helper kind fuel cost requested target value inOff inLen outOff outLen rest hstack h
  obtain ⟨hx,hgas⟩ := call_denied_gas fuel cost pre.executionEnv.blobVersionedHashes requested
    (source kind pre) (recipient kind pre target) target (transfer kind value)
    (apparent kind pre value) inOff inLen outOff outLen (permission kind pre)
    (entered pre) middle x hgate hh
  rw [hpost, hx]
  exact ⟨rfl,hgas⟩

/-- Denied dispatch consumes actual memory and net overhead, with no child
result or child gas bound premise. Every fit is obtained from actual Z. -/
theorem accepted_denied_debit (kind : Variant) (fuel : Nat)
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat}
    {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = stack kind requested target value inOff inLen outOff outLen rest)
    (hz : Z vj (opcode kind) pre = .ok (mid,cost))
    (hgate : ¬ gate kind mid value)
    (h : StepOk (fuel+2) cost (opcode kind,arg) mid post) :
    post.stack = ⟨0⟩::rest ∧ post.gasAvailable.toNat + overhead kind mid target value +
      memoryExpansionCost pre (opcode kind) = pre.gasAvailable.toNat := by
  obtain ⟨hstack',hgas⟩ := step_denied_gas kind fuel cost requested target value inOff inLen outOff outLen rest
    ((Z_ok_stack hz).trans hstack) hgate h
  refine ⟨hstack',?_⟩
  obtain ⟨hm,hmid,hcost,_⟩ := accepted_gas hz
  have hfit := (accepted_forwarded_fit kind hstack hz).2
  have hd := (settlement_nat (AccountAddress.ofUInt256 target)
    (AccountAddress.ofUInt256 (recipient kind mid target)) (transfer kind value) requested
    mid post.gasAvailable _ cost (accepted_cost kind hstack hz) hcost
    (by rw [hfit]; exact Nat.le_refl _) hgas).2
  change post.gasAvailable.toNat +
    (allowance kind mid requested target value - (UInt256.ofNat (allowance kind mid requested target value)).toNat) +
    overhead kind mid target value = mid.gasAvailable.toNat at hd
  rw [hfit, Nat.sub_self, Nat.add_zero] at hd
  omega

#print axioms step_helper
#print axioms address_word
#print axioms accepted_cost
#print axioms accepted_forwarded_fit
#print axioms step_child_gas
#print axioms accepted_step_debit
#print axioms step_denied_gas
#print axioms accepted_denied_debit
end Eip8282.Audit.Integrator.CallFamilyGas
