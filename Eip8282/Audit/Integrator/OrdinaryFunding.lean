import Eip8282.Audit.Integrator.SelfdestructFunding
import Eip8282.Audit.Integrator.OrdinaryGas

/-!
# Actual ordinary instructions do not create account funds

The quantity is the finite sum of actual account balances. Storage updates keep
it unchanged; SELFDESTRUCT can decrease it. Recursive instructions are handled
separately. No supply bound, owner existence or post-state invariant is assumed.
-/
namespace Eip8282.Audit.Integrator.OrdinaryFunding

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open TransferFunding SuccessInversion

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private theorem dup_funds (n : Nat) {pre post : EVM.State}
    (h : EvmYul.dup n pre = .ok post) : worldFunds post.accountMap ≤ worldFunds pre.accountMap := by
  unfold EvmYul.dup at h
  dsimp only at h
  split at h
  · cases h; exact Nat.le_refl _
  · cases h

private theorem swap_funds (n : Nat) {pre post : EVM.State}
    (h : EvmYul.swap n pre = .ok post) : worldFunds post.accountMap ≤ worldFunds pre.accountMap := by
  unfold EvmYul.swap at h
  dsimp only at h
  split at h
  · cases h; exact Nat.le_refl _
  · cases h

private theorem sstore_funds {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (h : EvmYul.step (τ := .EVM) .SSTORE arg pre = .ok post) :
    worldFunds post.accountMap ≤ worldFunds pre.accountMap := by
  obtain ⟨sh, pc, stk, ex⟩ := pre
  rcases stk with _ | ⟨a, _ | ⟨b, tail⟩⟩
  · cases h
  · cases h
  · cases h
    exact (StorageFunding.sstore_preserves sh.toState a b).le

private theorem tstore_funds {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (h : EvmYul.step (τ := .EVM) .TSTORE arg pre = .ok post) :
    worldFunds post.accountMap ≤ worldFunds pre.accountMap := by
  obtain ⟨sh, pc, stk, ex⟩ := pre
  rcases stk with _ | ⟨a, _ | ⟨b, tail⟩⟩
  · cases h
  · cases h
  · cases h
    exact (StorageFunding.tstore_preserves sh.toState a b).le

private theorem extcodehash_funds {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (h : EvmYul.step (τ := .EVM) .EXTCODEHASH arg pre = .ok post) :
    worldFunds post.accountMap ≤ worldFunds pre.accountMap := by
  obtain ⟨sh, pc, stk, ex⟩ := pre
  cases stk with
  | nil => cases h
  | cons a stk =>
    have hm (st : EvmYul.State .EVM) (v : UInt256) :
        (st.extCodeHash v).1.accountMap = st.accountMap := by
      unfold EvmYul.State.extCodeHash
      dsimp only
      split <;> rfl
    cases h
    change worldFunds (sh.toState.extCodeHash a).1.accountMap ≤ worldFunds sh.accountMap
    rw [hm]

/-- Every actual nonrecursive valid raw instruction respects the balance sum. -/
theorem raw_nonincrease {op : Operation .EVM} (hop : OrdinaryGas.Ordinary op)
    (hvalid : op ≠ .INVALID) {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (h : EvmYul.step op arg pre = .ok post) :
    worldFunds post.accountMap ≤ worldFunds pre.accountMap := by
  cases op <;> rename_i op <;> cases op
  all_goals first
    | exact False.elim (hvalid rfl)
    | (simp only [OrdinaryGas.Ordinary, Operation.isCall, Operation.isCreate,
        Bool.true_eq_false, false_and, and_false] at hop; done)
    | exact SelfdestructFunding.raw_nonincrease h
    | exact extcodehash_funds h
    | exact sstore_funds h
    | exact tstore_funds h
    | exact dup_funds _ h
    | exact swap_funds _ h
    | skip
  all_goals
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases arg with _ | ⟨v,n⟩
    all_goals rcases stk with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, tail⟩⟩⟩⟩⟩⟩
    all_goals first
      | (cases h <;> exact Nat.le_refl _)

/-- Exact dispatch consumes gas and updates counters without creating funds. -/
theorem step_nonincrease {op : Operation .EVM} (hop : OrdinaryGas.Ordinary op)
    (hv : op ≠ .INVALID) {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    {fuel cost : Nat} (h : StepOk fuel cost (op,arg) pre post) :
    worldFunds post.accountMap ≤ worldFunds pre.accountMap := by
  cases fuel with
  | zero => change Except.error ExecutionException.OutOfFuel = Except.ok post at h; cases h
  | succ fuel =>
    change EVM.step (fuel+1) cost (some (op,arg)) pre = .ok post at h
    rw [OrdinaryGas.dispatch hop] at h
    exact raw_nonincrease (pre := stepPre cost pre) hop hv h

/-- Z acceptance discharges validity; memory charging preserves the world. -/
theorem accepted_step_nonincrease {vj : Array UInt256} {op : Operation .EVM}
    (hop : OrdinaryGas.Ordinary op) {arg : Option (UInt256 × Nat)}
    {pre mid post : EVM.State} {fuel cost : Nat}
    (hz : Z vj op pre = .ok (mid,cost)) (hs : StepOk fuel cost (op,arg) mid post) :
    worldFunds post.accountMap ≤ worldFunds pre.accountMap := by
  have h := step_nonincrease hop (OrdinaryGas.accepted_valid hz) hs
  rw [Z_ok_state hz] at h
  exact h

#print axioms raw_nonincrease
#print axioms accepted_step_nonincrease
end Eip8282.Audit.Integrator.OrdinaryFunding
