import Eip8282.Audit.Integrator.Topics.ReferenceCall

/-! Uniform per-outcome pool accounting for a settled nested CALL frame.

Extends `ReferenceCallChildBoundary.completes` — which currently states pool
accounting only for the failing outcomes — by exposing the same equation for
the successful case and unifying the three cases into a single theorem. The
resulting statement makes it easy to reason about `pools` at the CALL
boundary regardless of outcome, without pattern matching on the outcome at
every consumer.

Definition tree that the accounting relies on:

* `finish hasValue deadRecipient outcome s child` unfolds to
  `(incorporate s.parent (settle outcome child) (failed outcome)).map (refill hasValue deadRecipient outcome)`.
* On success the refill is the identity and incorporate uses `repay`, which
  preserves `pools`, so `pools post = pools s.parent + pools child`.
* On failure the refill adds `stateCost hasValue deadRecipient` when the
  new-account charge condition applies (and adds `0` otherwise, which
  coincides with `stateCost` when the condition fails), so
  `pools post = pools s.parent + pools (settle outcome child) + stateCost hasValue deadRecipient`.

Nothing here asserts canonical outer-frame semantics; the input is still an
actual paid child meter `paid : runFull events (start s) = some child`,
already accepted by `ReferenceCallChildBoundary.completes`. The uniform
statement is a *derived* corollary, not a new premise. Interpreter/journal
coupling on nested rollback is covered upstream via `Coupled` and
`ReferenceCallChildBoundary.failed_logs`; this module contributes the exact
missing pool-accounting equation for the success case and packages the
combined identity.

Uniform accounting theorem: `finish_pools`.
Success-only accounting: `finish_pools_success`.
Deterministic finish result: `finish_deterministic` (Option.some.injective). -/
namespace Eip8282.Audit.Integrator.ReferenceNestedCallSettlement

open EvmYul EvmYul.EVM
open ReferenceMeterRollback ReferenceMeterBoundary ReferenceMeterPath
open ReferenceChildMeter ReferenceCallGrant ReferenceCallChildBoundary
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

/-- On a successful nested CALL the finished parent meter's `pools` equal
the pre-CALL parent's `pools` plus the paid child's residual `pools`. This
is the complementary case of `ReferenceCallChildBoundary.completes`, which
handles reverted and exceptional outcomes only. -/
theorem finish_pools_success {s : Split} {events : List Event} {child : Meter}
    (paid : runFull events (start s) = some child)
    (hasValue deadRecipient : Bool) :
    ∃ post, finish hasValue deadRecipient .success s child = some post ∧
      pools post = pools s.parent + pools child := by
  have committed : child.committedSpill = 0 := by
    have hm := (accounting paid s.childState).2.2.2
    exact hm
  -- Compute the finish value explicitly.
  have hi : incorporate s.parent child false = some (repay (absorb s.parent child)) := by
    unfold incorporate
    rw [if_pos]
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · exact ⟨committed, fun h => absurd h Bool.false_ne_true⟩
  have href : refill hasValue deadRecipient .success (repay (absorb s.parent child)) =
      repay (absorb s.parent child) := by
    simp only [refill, failed, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  have hf : finish hasValue deadRecipient .success s child =
      some (repay (absorb s.parent child)) := by
    show (incorporate s.parent (settle .success child) (failed .success)).map
        (refill hasValue deadRecipient .success) =
      some (repay (absorb s.parent child))
    show (incorporate s.parent child false).map
        (refill hasValue deadRecipient .success) =
      some (repay (absorb s.parent child))
    rw [hi, Option.map_some, href]
  refine ⟨_, hf, ?_⟩
  have hrepay := (repay_accounting (absorb s.parent child) 0).1
  rw [hrepay]
  simp only [absorb, pools]
  omega

/-- Uniform pool accounting for a settled nested CALL, covering all three
outcomes. Success adds no state-cost refill; reverted and exceptional
outcomes add `stateCost hasValue deadRecipient` (which is `0` unless both
`hasValue` and `deadRecipient` are `true`). -/
theorem finish_pools {s : Split} {events : List Event} {child : Meter}
    (paid : runFull events (start s) = some child)
    (hasValue deadRecipient : Bool) (outcome : Outcome) :
    ∃ post, finish hasValue deadRecipient outcome s child = some post ∧
      pools post = pools s.parent + pools (settle outcome child) +
        (if outcome = .success then (0 : Int) else stateCost hasValue deadRecipient) := by
  cases outcome with
  | success =>
    obtain ⟨post, hp, hb⟩ := finish_pools_success paid hasValue deadRecipient
    refine ⟨post, hp, ?_⟩
    show pools post = pools s.parent + pools child + 0
    rw [hb]
    ring
  | reverted =>
    obtain ⟨post, hp, hb⟩ := completes paid hasValue deadRecipient .reverted
    refine ⟨post, hp, ?_⟩
    simp only [if_neg (by decide : Outcome.reverted ≠ .success)]
    exact hb (by decide)
  | exceptional =>
    obtain ⟨post, hp, hb⟩ := completes paid hasValue deadRecipient .exceptional
    refine ⟨post, hp, ?_⟩
    simp only [if_neg (by decide : Outcome.exceptional ≠ .success)]
    exact hb (by decide)

/-- The finish function is a plain option-valued Lean function; when two
successful evaluations produce results on the same inputs, they coincide.
This is Option injectivity in a form callers can quote directly when
reasoning about identity of nested-call outcomes on top of
`NestedEvents.ThetaAt.identity`. -/
theorem finish_deterministic {hasValue deadRecipient : Bool} {outcome : Outcome}
    {s : Split} {child post₁ post₂ : Meter}
    (h₁ : finish hasValue deadRecipient outcome s child = some post₁)
    (h₂ : finish hasValue deadRecipient outcome s child = some post₂) :
    post₁ = post₂ :=
  Option.some.inj (h₁.symm.trans h₂)

#print axioms finish_pools_success
#print axioms finish_pools
#print axioms finish_deterministic
end Eip8282.Audit.Integrator.ReferenceNestedCallSettlement
