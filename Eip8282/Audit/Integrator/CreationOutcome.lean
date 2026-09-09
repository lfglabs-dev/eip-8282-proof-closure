import Eip8282.Audit.Integrator.CreationGas

/-!
# All-outcome CREATE/CREATE2 child and settlement equations

The complete dispatcher is related to its literal child invocation, including
caught child errors and rejection by the post-child WORD gas guard. These
identities make attempted children visible even when the parent step errors.
They add no gas-bound, child-success or event-count premise.
-/
namespace Eip8282.Audit.Integrator.CreationOutcome
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open CreationGas
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

abbrev ChildResult := Except ExecutionException
  (AccountAddress × Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray)

abbrev Selected := AccountAddress × EVM.State × UInt256 × Bool × ByteArray

/-- The actual child result selection, including CREATE's catch of every error. -/
def select (cost : Nat) (pre : EVM.State) : ChildResult → Selected
  | .ok (address,created,world,gas,substate,success,out) =>
      (address, {(stepPre cost pre) with
        accountMap := world
        substate := substate
        createdAccounts := created}, gas, success, out)
  | .error _ => (0, {stepPre cost pre with accountMap := ∅}, ⟨0⟩, false, .empty)

/-- Literal post-child settlement; the addition in the guard is a WORD addition,
while the final gas expression uses natural subtraction and addition. -/
def finish (cost : Nat) (pre : EVM.State) (value off len : UInt256) (rest : Stack UInt256)
    (chosen : Selected) : Except ExecutionException EVM.State := do
  let charged := stepPre cost pre
  let (address,childState,gas,success,out) := chosen
  let balance := charged.accountMap.get? charged.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)
  let resultWord : UInt256 :=
    if success = false ∨ charged.executionEnv.depth = 1024 ∨ value > balance ∨
        (init charged off len).size > 49152 then ⟨0⟩ else .ofNat address
  let returnData := if success then ByteArray.empty else out
  if (charged.gasAvailable + gas).toNat < L charged.gasAvailable.toNat then
    .error .OutOfGass
  let post := {childState with
    activeWords := .ofNat (MachineState.M charged.activeWords.toNat off.toNat len.toNat),
    returnData := returnData,
    gasAvailable := .ofNat (charged.gasAvailable.toNat - L charged.gasAvailable.toNat + gas.toNat)}
  pure (post.replaceStackAndIncrPC (resultWord::rest))

def settle (cost : Nat) (pre : EVM.State) (value off len : UInt256) (rest : Stack UInt256)
    (result : ChildResult) : Except ExecutionException EVM.State :=
  finish cost pre value off len rest (select cost pre result)

/-- Exact creation equation for every actual child outcome and every final
step outcome. In particular, no successful final guard is assumed. -/
theorem admitted_equation (kind : Variant) (fuel cost : Nat) (pre : EVM.State)
    (arg : Option (UInt256 × Nat)) (value off len salt : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = stack kind value off len salt rest)
    (hnonce : nonceAllowed pre) (hgate : gate pre value off len) :
    EVM.step (fuel+1) cost (some (opcode kind,arg)) pre =
      settle cost pre value off len rest (child kind fuel cost pre value off len salt) := by
  have hn : ¬ (pre.accountMap.get? pre.executionEnv.codeOwner |>.getD default).nonce.toNat ≥ 2^64-1 :=
    Nat.not_le.mpr hnonce
  have hg : value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding off.toNat len.toNat).size ≤ 49152 := hgate
  cases kind with
  | create =>
      have hs : pre.stack.pop3 = some (rest,value,off,len) := by rw [hstack]; rfl
      simp only [opcode,EVM.step,Bind.bind,Except.bind,pure,Except.pure]
      rw [hs]
      simp only [hn,hg,true_and,↓reduceIte]
      rcases he : child .create fuel cost pre value off len salt with err | ⟨a,cr,w,g,ss,z,out⟩
      all_goals
        unfold child at he
        dsimp only [stepPre,init,saltBytes] at he
        rw [he]
        rfl
  | create2 =>
      have hs : pre.stack.pop4 = some (rest,value,off,len,salt) := by rw [hstack]; rfl
      simp only [opcode,EVM.step,Bind.bind,Except.bind,pure,Except.pure]
      rw [hs]
      simp only [hn,hg,true_and,↓reduceIte]
      rcases he : child .create2 fuel cost pre value off len salt with err | ⟨a,cr,w,g,ss,z,out⟩
      all_goals
        unfold child at he
        dsimp only [stepPre,init,saltBytes] at he
        rw [he]
        rfl

/-- No child is evaluated when either independent gate denies creation. The
same literal final guard is retained, so this is not a liveness assertion. -/
theorem denied_equation (kind : Variant) (fuel cost : Nat) (pre : EVM.State)
    (arg : Option (UInt256 × Nat)) (value off len salt : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = stack kind value off len salt rest)
    (hdenied : ¬ nonceAllowed pre ∨ ¬ gate pre value off len) :
    EVM.step (fuel+1) cost (some (opcode kind,arg)) pre =
      finish cost pre value off len rest
        (0,stepPre cost pre,UInt256.ofNat (allowance cost pre),false,.empty) := by
  have hg : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner |>.getD default).nonce.toNat < 2^64-1) ∨
      ¬ (value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding off.toNat len.toNat).size ≤ 49152) := hdenied
  cases kind with
  | create =>
      have hs : pre.stack.pop3 = some (rest,value,off,len) := by rw [hstack]; rfl
      simp only [opcode,EVM.step,Bind.bind,Except.bind,pure,Except.pure]
      rw [hs]
      rcases hg with hn | hg
      · simp only [Nat.not_lt.mp hn,↓reduceIte]; rfl
      · by_cases hn : (pre.accountMap.get? pre.executionEnv.codeOwner |>.getD default).nonce.toNat ≥ 2^64-1
        · simp only [hn,↓reduceIte]; rfl
        · simp only [hn,hg,↓reduceIte]; rfl
  | create2 =>
      have hs : pre.stack.pop4 = some (rest,value,off,len,salt) := by rw [hstack]; rfl
      simp only [opcode,EVM.step,Bind.bind,Except.bind,pure,Except.pure]
      rw [hs]
      rcases hg with hn | hg
      · simp only [Nat.not_lt.mp hn,↓reduceIte]; rfl
      · by_cases hn : (pre.accountMap.get? pre.executionEnv.codeOwner |>.getD default).nonce.toNat ≥ 2^64-1
        · simp only [hn,↓reduceIte]; rfl
        · simp only [hn,hg,↓reduceIte]; rfl

/-- The only settlement error is the literal post-child guard rejection. A
caught child's error is represented in `chosen`; it is not propagated here. -/
theorem finish_error_iff (cost : Nat) (pre : EVM.State) (value off len : UInt256)
    (rest : Stack UInt256) (chosen : Selected) (err : ExecutionException) :
    finish cost pre value off len rest chosen = .error err ↔
      ((stepPre cost pre).gasAvailable + chosen.2.2.1).toNat < allowance cost pre ∧ err = .OutOfGass := by
  obtain ⟨address,childState,gas,success,out⟩ := chosen
  unfold finish
  dsimp only
  split <;> simp_all [allowance, Bind.bind, Except.bind, pure, Except.pure, Except.error.injEq, eq_comm]

/-- Z bounds the child's real forwarding allowance even if the child or final
parent step errors. No returned-gas or desired aggregate bound is assumed. -/
theorem accepted_allowance_le (kind : Variant) {vj : Array UInt256}
    {pre mid : EVM.State} {cost : Nat}
    (hz : Z vj (opcode kind) pre = .ok (mid,cost)) :
    allowance cost mid ≤ pre.gasAvailable.toNat := by
  obtain ⟨_,hmid,hcost,_⟩ := ActualAppendGas.accepted_gas hz
  have hl : L (stepPre cost mid).gasAvailable.toNat ≤ (stepPre cost mid).gasAvailable.toNat := by
    unfold L
    exact Nat.sub_le _ _
  have hs : (stepPre cost mid).gasAvailable.toNat = mid.gasAvailable.toNat-cost :=
    toNat_sub_ofNat hcost
  unfold allowance
  omega

#print axioms admitted_equation
#print axioms denied_equation
#print axioms finish_error_iff
#print axioms accepted_allowance_le
end Eip8282.Audit.Integrator.CreationOutcome
