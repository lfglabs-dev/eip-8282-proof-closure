import Eip8282.Audit.Integrator.CallFamilyGas

/-!
# All outcomes of literal CALL-family dispatch

These equations retain actual helper and child errors, including OutOfFuel.
They do not assume a completed step, returned-gas bound or event inequality.
Fuel zero and the dispatcher/helper boundary at fuel one remain explicit.
The allowance bounds use actual Z acceptance independently of any step result.
-/
namespace Eip8282.Audit.Integrator.CallOutcome
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open CallGasAccounting
open CallDispatchGas (entered)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- The real helper gate checks codeOwner, even when source is a different
parameter. Funding the actual source is a separate dispatcher property. -/
def Gate (pre : EVM.State) (value : UInt256) : Prop :=
  value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
    pre.executionEnv.depth < 1024

/-- The exact final stack/PC operation adds no exceptional branch. -/
def finish (rest : Stack UInt256) (r : Except ExecutionException (UInt256 × EVM.State)) :
    Except ExecutionException EVM.State := do
  let (x,middle) ← r
  pure (middle.replaceStackAndIncrPC (x::rest))

theorem finish_error_iff (rest : Stack UInt256)
    (r : Except ExecutionException (UInt256 × EVM.State)) (err : ExecutionException) :
    finish rest r = .error err ↔ r = .error err := by
  cases r with
  | error e => simp only [finish, Bind.bind, Except.bind, Except.error.injEq]
  | ok result => obtain ⟨x,middle⟩ := result; constructor <;> intro h <;> cases h

/-- Equality of full outcomes, not just extraction from StepOk. -/
theorem step_call_equation (fuel cost : Nat) (pre : EVM.State)
    (arg : Option (UInt256 × Nat))
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::rest) :
    EVM.step (fuel+2) cost (some (.CALL,arg)) pre =
      finish rest (CallDispatchGas.helper fuel cost pre requested target value inOff inLen outOff outLen) := by
  have hs : pre.stack.pop7 = some (rest,requested,target,value,inOff,inLen,outOff,outLen) := by
    rw [hstack]; rfl
  simp only [EVM.step, Bind.bind, Except.bind, pure, Except.pure]
  rw [hs]
  rfl

theorem step_family_equation (kind : CallFamilyGas.Variant) (fuel cost : Nat) (pre : EVM.State)
    (arg : Option (UInt256 × Nat))
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = CallFamilyGas.stack kind requested target value inOff inLen outOff outLen rest) :
    EVM.step (fuel+2) cost (some (CallFamilyGas.opcode kind,arg)) pre =
      finish rest (CallFamilyGas.helper kind fuel cost pre requested target value inOff inLen outOff outLen) := by
  cases kind with
  | callcode =>
      have hs : pre.stack.pop7 = some (rest,requested,target,value,inOff,inLen,outOff,outLen) := by
        rw [hstack]; rfl
      simp only [CallFamilyGas.opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure]
      rw [hs]
      rfl
  | delegatecall =>
      have hs : pre.stack.pop6 = some (rest,requested,target,inOff,inLen,outOff,outLen) := by
        rw [hstack]; rfl
      simp only [CallFamilyGas.opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure]
      rw [hs]
      rfl
  | staticcall =>
      have hs : pre.stack.pop6 = some (rest,requested,target,inOff,inLen,outOff,outLen) := by
        rw [hstack]; rfl
      simp only [CallFamilyGas.opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure]
      rw [hs]
      rfl

/-- On the admitted branch, errors are precisely the SAME literal child Theta
errors; output memory and final state construction cannot introduce one. -/
theorem call_error_iff (fuel cost : Nat) (hashes : List ByteArray)
    (requested source recipient target value apparent inOff inLen outOff outLen : UInt256)
    (permission : Bool) (pre : EVM.State) (err : ExecutionException)
    (hgate : Gate pre value) :
    EVM.call (fuel+1) cost hashes requested source recipient target value apparent
      inOff inLen outOff outLen permission pre = .error err ↔
    child fuel hashes requested source recipient target value apparent inOff inLen permission pre = .error err := by
  unfold Gate at hgate
  cases he : child fuel hashes requested source recipient target value apparent inOff inLen permission pre with
  | error e =>
      unfold child at he
      simp only [EVM.call, hgate, true_and, ↓reduceIte, he, Bind.bind, Except.bind]
      simp only [Except.error.injEq]
  | ok result =>
      obtain ⟨created,world,gas,substate,success,out⟩ := result
      unfold child at he
      simp only [EVM.call, hgate, true_and, ↓reduceIte, he, Bind.bind, Except.bind,
        pure, Except.pure]
      constructor <;> intro h <;> cases h

/-- A denied positive-fuel helper has a literal completed no-child branch,
irrespective of what an uncalled Theta expression would have returned. -/
theorem call_denied (fuel cost : Nat) (hashes : List ByteArray)
    (requested source recipient target value apparent inOff inLen outOff outLen : UInt256)
    (permission : Bool) (pre : EVM.State) (hgate : ¬ Gate pre value) :
    ∃ post, EVM.call (fuel+1) cost hashes requested source recipient target value apparent
      inOff inLen outOff outLen permission pre = .ok (⟨0⟩,post) ∧
      post.accountMap = pre.accountMap := by
  unfold Gate at hgate
  simp only [EVM.call, hgate, ↓reduceIte, Bind.bind, Except.bind,
    Bool.not_false, Bool.true_or]
  exact ⟨_,rfl,rfl⟩

/-- Both implications retain the actual gate and error identity. -/
theorem call_error_iff_gate (fuel cost : Nat) (hashes : List ByteArray)
    (requested source recipient target value apparent inOff inLen outOff outLen : UInt256)
    (permission : Bool) (pre : EVM.State) (err : ExecutionException) :
    EVM.call (fuel+1) cost hashes requested source recipient target value apparent
      inOff inLen outOff outLen permission pre = .error err ↔
    Gate pre value ∧
      child fuel hashes requested source recipient target value apparent inOff inLen permission pre = .error err := by
  by_cases hg : Gate pre value
  · rw [call_error_iff fuel cost hashes requested source recipient target value apparent
      inOff inLen outOff outLen permission pre err hg]
    exact (and_iff_right hg).symm
  · obtain ⟨post,hp,_⟩ := call_denied fuel cost hashes requested source recipient target value apparent
      inOff inLen outOff outLen permission pre hg
    rw [hp]
    simp only [hg, false_and]
    constructor <;> intro h <;> cases h

theorem step_call_error_iff (fuel cost : Nat) (pre : EVM.State)
    (arg : Option (UInt256 × Nat))
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::rest)
    (err : ExecutionException) :
    EVM.step (fuel+2) cost (some (.CALL,arg)) pre = .error err ↔
    Gate pre value ∧ child fuel pre.executionEnv.blobVersionedHashes requested
      (UInt256.ofNat pre.executionEnv.codeOwner) target target value value inOff inLen
      pre.executionEnv.perm (entered pre) = .error err := by
  rw [step_call_equation fuel cost pre arg requested target value inOff inLen outOff outLen rest hstack,
    finish_error_iff]
  exact call_error_iff_gate fuel cost pre.executionEnv.blobVersionedHashes requested
    (UInt256.ofNat pre.executionEnv.codeOwner) target target value value inOff inLen outOff outLen
    pre.executionEnv.perm (entered pre) err

theorem step_family_error_iff (kind : CallFamilyGas.Variant) (fuel cost : Nat) (pre : EVM.State)
    (arg : Option (UInt256 × Nat))
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = CallFamilyGas.stack kind requested target value inOff inLen outOff outLen rest)
    (err : ExecutionException) :
    EVM.step (fuel+2) cost (some (CallFamilyGas.opcode kind,arg)) pre = .error err ↔
    CallFamilyGas.gate kind pre value ∧
      CallFamilyGas.childResult kind fuel pre requested target value inOff inLen = .error err := by
  rw [step_family_equation kind fuel cost pre arg requested target value inOff inLen outOff outLen rest hstack,
    finish_error_iff]
  exact call_error_iff_gate fuel cost pre.executionEnv.blobVersionedHashes requested
    (CallFamilyGas.source kind pre) (CallFamilyGas.recipient kind pre target) target
    (CallFamilyGas.transfer kind value) (CallFamilyGas.apparent kind pre value)
    inOff inLen outOff outLen (CallFamilyGas.permission kind pre) (entered pre) err

/-- The denied dispatcher result is constructed without a child premise. -/
theorem step_call_denied (fuel cost : Nat) (pre : EVM.State)
    (arg : Option (UInt256 × Nat))
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::rest)
    (hgate : ¬ Gate pre value) :
    ∃ post, EVM.step (fuel+2) cost (some (.CALL,arg)) pre = .ok post ∧
      post.stack = ⟨0⟩::rest ∧ post.accountMap = pre.accountMap := by
  obtain ⟨middle,he,hw⟩ := call_denied fuel cost pre.executionEnv.blobVersionedHashes requested
    (UInt256.ofNat pre.executionEnv.codeOwner) target target value value inOff inLen outOff outLen
    pre.executionEnv.perm (entered pre) hgate
  refine ⟨middle.replaceStackAndIncrPC (⟨0⟩::rest), ?_,rfl,hw⟩
  rw [step_call_equation fuel cost pre arg requested target value inOff inLen outOff outLen rest hstack]
  change finish rest (EVM.call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = _
  rw [he]
  rfl

theorem step_family_denied (kind : CallFamilyGas.Variant) (fuel cost : Nat) (pre : EVM.State)
    (arg : Option (UInt256 × Nat))
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = CallFamilyGas.stack kind requested target value inOff inLen outOff outLen rest)
    (hgate : ¬ CallFamilyGas.gate kind pre value) :
    ∃ post, EVM.step (fuel+2) cost (some (CallFamilyGas.opcode kind,arg)) pre = .ok post ∧
      post.stack = ⟨0⟩::rest ∧ post.accountMap = pre.accountMap := by
  obtain ⟨middle,he,hw⟩ := call_denied fuel cost pre.executionEnv.blobVersionedHashes requested
    (CallFamilyGas.source kind pre) (CallFamilyGas.recipient kind pre target) target
    (CallFamilyGas.transfer kind value) (CallFamilyGas.apparent kind pre value)
    inOff inLen outOff outLen (CallFamilyGas.permission kind pre) (entered pre) hgate
  refine ⟨middle.replaceStackAndIncrPC (⟨0⟩::rest), ?_,rfl,hw⟩
  rw [step_family_equation kind fuel cost pre arg requested target value inOff inLen outOff outLen rest hstack]
  change finish rest (EVM.call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = _
  rw [he]
  rfl

/-- No instruction, helper or child is executed at dispatcher fuel zero. -/
theorem step_zero (cost : Nat) (instr : Option (Operation .EVM × Option (UInt256 × Nat)))
    (pre : EVM.State) : EVM.step 0 cost instr pre = .error .OutOfFuel := rfl

theorem call_zero (cost : Nat) (hashes : List ByteArray)
    (requested source recipient target value apparent inOff inLen outOff outLen : UInt256)
    (permission : Bool) (pre : EVM.State) :
    EVM.call 0 cost hashes requested source recipient target value apparent
      inOff inLen outOff outLen permission pre = .error .OutOfFuel := rfl

/-- Dispatcher fuel one reaches helper fuel zero after a successful stack pop;
it cannot be confused with a denied positive-fuel no-child result. -/
theorem step_call_one (cost : Nat) (pre : EVM.State) (arg : Option (UInt256 × Nat))
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::rest) :
    EVM.step 1 cost (some (.CALL,arg)) pre = .error .OutOfFuel := by
  have hs : pre.stack.pop7 = some (rest,requested,target,value,inOff,inLen,outOff,outLen) := by
    rw [hstack]; rfl
  simp only [EVM.step, Bind.bind, Except.bind, pure, Except.pure]
  rw [hs]
  rfl

theorem step_family_one (kind : CallFamilyGas.Variant) (cost : Nat) (pre : EVM.State)
    (arg : Option (UInt256 × Nat))
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = CallFamilyGas.stack kind requested target value inOff inLen outOff outLen rest) :
    EVM.step 1 cost (some (CallFamilyGas.opcode kind,arg)) pre = .error .OutOfFuel := by
  cases kind with
  | callcode =>
      have hs : pre.stack.pop7 = some (rest,requested,target,value,inOff,inLen,outOff,outLen) := by
        rw [hstack]; rfl
      simp only [CallFamilyGas.opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure]
      rw [hs]
      rfl
  | delegatecall =>
      have hs : pre.stack.pop6 = some (rest,requested,target,inOff,inLen,outOff,outLen) := by
        rw [hstack]; rfl
      simp only [CallFamilyGas.opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure]
      rw [hs]
      rfl
  | staticcall =>
      have hs : pre.stack.pop6 = some (rest,requested,target,inOff,inLen,outOff,outLen) := by
        rw [hstack]; rfl
      simp only [CallFamilyGas.opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure]
      rw [hs]
      rfl

/-- Actual Z alone bounds the stipend-inclusive allowance. No StepOk, gate,
child outcome or returned-gas bound is required. -/
theorem accepted_call_allowance_le {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    {requested target value inOff inLen outOff outLen : UInt256} {rest : Stack UInt256}
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::rest)
    (hz : Z vj .CALL pre = .ok (mid,cost)) :
    let allowance := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
      value requested mid.accountMap mid.toMachineState mid.substate
    allowance ≤ cost ∧ allowance ≤ mid.gasAvailable.toNat ∧ allowance ≤ pre.gasAvailable.toNat := by
  have hc := accepted_call_cost hstack hz
  have hb := callgas_le_call (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
    value requested mid.accountMap mid.toMachineState mid.substate
  rw [← hc] at hb
  have hg := ActualAppendGas.accepted_gas hz
  exact ⟨hb,hb.trans hg.2.2.1,by omega⟩

theorem accepted_family_allowance_le (kind : CallFamilyGas.Variant)
    {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    {requested target value inOff inLen outOff outLen : UInt256} {rest : Stack UInt256}
    (hstack : pre.stack = CallFamilyGas.stack kind requested target value inOff inLen outOff outLen rest)
    (hz : Z vj (CallFamilyGas.opcode kind) pre = .ok (mid,cost)) :
    CallFamilyGas.allowance kind mid requested target value ≤ cost ∧
      CallFamilyGas.allowance kind mid requested target value ≤ mid.gasAvailable.toNat ∧
      CallFamilyGas.allowance kind mid requested target value ≤ pre.gasAvailable.toNat := by
  have hc := CallFamilyGas.accepted_cost kind hstack hz
  have hb := callgas_le_call (AccountAddress.ofUInt256 target)
    (AccountAddress.ofUInt256 (CallFamilyGas.recipient kind mid target))
    (CallFamilyGas.transfer kind value) requested mid.accountMap mid.toMachineState mid.substate
  rw [← hc] at hb
  have hg := ActualAppendGas.accepted_gas hz
  exact ⟨hb,hb.trans hg.2.2.1,by
    change Ccallgas _ _ _ _ _ _ _ ≤ _
    omega⟩

#print axioms step_call_equation
#print axioms step_family_equation
#print axioms call_error_iff
#print axioms call_denied
#print axioms call_error_iff_gate
#print axioms step_call_error_iff
#print axioms step_family_error_iff
#print axioms step_call_denied
#print axioms step_family_denied
#print axioms step_zero
#print axioms call_zero
#print axioms step_call_one
#print axioms step_family_one
#print axioms accepted_call_allowance_le
#print axioms accepted_family_allowance_le
end Eip8282.Audit.Integrator.CallOutcome
