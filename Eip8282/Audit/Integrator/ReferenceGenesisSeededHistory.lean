import Eip8282.Audit.Integrator.ReferenceFundedHistoryLifecycle

/-! Genesis-seeded canonical History existence.

The two public consumers `ReferenceFullFeeBlockTotal.verified` and
`ReferenceCheckedSystemBlock.verified` both take
`history : ReleaseCandidate.History deposit exit ...` as a bare premise. The
`ReferenceFundedHistoryLifecycle.initial` constructor already assembles such a
`History` from four non-trivial witnesses (factory-guarantees inputs for both
deposits, a `FundingHistory.Trace` from genesis, a `ProtocolCreditEnvelope`
ledger and its counts). This module packages the special canonical case
`deposit.call.world = GenesisFundingWorld.world`: the genesis trace is
literally `Trace.initial`, so a caller who supplies only the factory inputs,
the exit-world identity, the credit ledger and its counts obtains a witness
of the `history` premise by construction. Consumers that already control a
factory pair, a genesis ledger and a `Counts` structure can now discharge
the `history` premise without also assembling `FundingHistory.Trace` by hand.

This is a step-(a) piece of the canonical `History` producer: it removes the
`FundingHistory.Trace` construction from the caller's obligation list in the
genesis-seed case. The remaining ingredients (`depositInputs`, `exitInputs`,
`ledger`, `counts`) are still hypotheses; the associated producers remain
distinct obligations recorded in DIRECT-CLOSURE.md.
-/
namespace Eip8282.Audit.Integrator.ReferenceGenesisSeededHistory

open EvmYul EvmYul.EVM
open TransactionAppendBudget (Receipt)
open ReleaseCandidate (History)

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Existence of a canonical genesis-seeded `History`.
    Given a deposit whose call world is literally `GenesisFundingWorld.world`,
    the two factory-guarantees inputs, the exit-world identity, a genesis
    credit ledger and its counts, the composed `History deposit exit exit.world`
    is produced by `ReferenceFundedHistoryLifecycle.initial` with
    `prior := FundingHistory.Trace.initial`.

    The witness is packaged as `Nonempty` (Prop) so downstream lemmas can
    destruct it without depending on the specific structural fields. Callers
    who need the exact structural witness use
    `ReferenceFundedHistoryLifecycle.initial` directly with the same arguments
    and `FundingHistory.Trace.initial` for the `prior` field. -/
theorem exists_seed {deposit exit : Receipt}
    (depositInputs : FactoryHistoryGuarantees.Inputs .deposit deposit.call)
    (exitInputs : FactoryHistoryGuarantees.Inputs .exit exit.call)
    (linked : exit.call.world = deposit.world)
    {pow withdrawals migrations : Nat}
    (genesisSeed : deposit.call.world = GenesisFundingWorld.world)
    (ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world
      pow withdrawals migrations 0 exit.world)
    (counts : ProtocolCreditEnvelope.Counts pow withdrawals migrations) :
    Nonempty (History deposit exit exit.world) := by
  refine ⟨ReferenceFundedHistoryLifecycle.initial depositInputs exitInputs linked
    (baseCredits := 0) ?_ ledger counts⟩
  rw [genesisSeed]
  exact FundingHistory.Trace.initial

#print axioms exists_seed

end Eip8282.Audit.Integrator.ReferenceGenesisSeededHistory
