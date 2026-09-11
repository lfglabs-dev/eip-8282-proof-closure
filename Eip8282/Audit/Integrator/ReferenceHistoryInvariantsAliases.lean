import Eip8282.Audit.Integrator.ReleaseCandidate

/-! Named single-fact aliases of `ReleaseCandidate.invariants`.

`ReleaseCandidate.invariants h` returns a four-way conjunction:
`deposit.success = true`, `exit.success = true`,
`ActualJournalHistory.work h.receipts < 2^128`, and the family
`∀ kind, JournalInvariant.Invariant kind (work h.receipts) before`.
Downstream consumers frequently need only one of the four facts and
end up destructuring the conjunction at every call site. This module
exposes each fact under its own name so a consumer can quote a single
named lemma. No new premise; no new axiom; each alias is a direct
projection. -/
namespace Eip8282.Audit.Integrator.ReferenceHistoryInvariantsAliases

open EvmYul EvmYul.EVM
open TransactionAppendBudget (Receipt)
open ReleaseCandidate (History)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- The deposit receipt of any funded History records a successful call. -/
theorem deposit_success {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) : deposit.success = true :=
  (ReleaseCandidate.invariants h).1

/-- The exit receipt of any funded History records a successful call. -/
theorem exit_success {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) : exit.success = true :=
  (ReleaseCandidate.invariants h).2.1

/-- The accumulated actual work count of any funded History stays strictly
below `2^128`. This is the resource envelope bound. -/
theorem work_lt {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) :
    ActualJournalHistory.work h.receipts < 2^128 :=
  (ReleaseCandidate.invariants h).2.2.1

/-- The protected `JournalInvariant.Invariant` holds at the `before` world of
any funded History, at the accumulated work count and for every kind. -/
theorem invariant_at {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) (kind : ReachableCalls.Contract) :
    JournalInvariant.Invariant kind (ActualJournalHistory.work h.receipts) before :=
  (ReleaseCandidate.invariants h).2.2.2 kind

#print axioms deposit_success
#print axioms exit_success
#print axioms work_lt
#print axioms invariant_at

end Eip8282.Audit.Integrator.ReferenceHistoryInvariantsAliases
