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

/-- `ProtocolCreditEnvelope.Counts 0 0 0` is directly satisfied:
    `pow_count = 0 ≤ 2^64`, `withdrawal_count = 0 ≤ 16*2^64`, and
    `migration_conserving = (0 = 0)` are all trivial. This closes the
    `counts` ingredient of the `History` producer whenever the caller
    can commit to zero pow batches, zero withdrawals and zero
    migrations — the canonical "no external credits" seed case. -/
theorem counts_zero : ProtocolCreditEnvelope.Counts 0 0 0 where
  pow_count := by decide
  withdrawal_count := by decide
  migration_conserving := rfl

#print axioms counts_zero

/-- Genesis-seed History existence in the canonical zero-count case.
    Given `depositInputs`, `exitInputs`, `linked`, the seed identity, and
    a zero-count credit ledger, produce `Nonempty (History deposit exit
    exit.world)` without requiring the caller to also assemble
    `ProtocolCreditEnvelope.Counts` — it is now discharged as `counts_zero`.
    Reduces the caller's `History`-construction obligation to four
    ingredients in this canonical case (down from six). -/
theorem exists_seed_zero_counts {deposit exit : Receipt}
    (depositInputs : FactoryHistoryGuarantees.Inputs .deposit deposit.call)
    (exitInputs : FactoryHistoryGuarantees.Inputs .exit exit.call)
    (linked : exit.call.world = deposit.world)
    (genesisSeed : deposit.call.world = GenesisFundingWorld.world)
    (ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world 0 0 0 0 exit.world) :
    Nonempty (History deposit exit exit.world) :=
  exists_seed depositInputs exitInputs linked
    (pow := 0) (withdrawals := 0) (migrations := 0)
    genesisSeed ledger counts_zero

#print axioms exists_seed_zero_counts

/-- `ProtocolCreditEnvelope.Ledger initial 0 0 0 0 initial` is directly
    inhabited by `Ledger.initial`: the trivial ledger has zero pow
    batches, zero withdrawals, zero migrations, zero credits, and
    identical initial/final worlds. Applied at
    `GenesisFundingWorld.world`, this discharges the `ledger` ingredient
    of the `History` producer in the canonical "no protocol events"
    seed case. -/
theorem ledger_genesis_trivial :
    ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world 0 0 0 0
      GenesisFundingWorld.world :=
  ProtocolCreditEnvelope.Ledger.initial

#print axioms ledger_genesis_trivial

/-- Genesis-seed History existence in the fully-trivial seed case:
    additionally require `exit.world = GenesisFundingWorld.world`, so
    `ledger` becomes `ledger_genesis_trivial`. Reduces the caller's
    `History`-construction obligation from six ingredients to three
    (`depositInputs`, `exitInputs`, `linked`). This is the canonical
    "no protocol events since genesis" seed configuration. -/
theorem exists_seed_trivial {deposit exit : Receipt}
    (depositInputs : FactoryHistoryGuarantees.Inputs .deposit deposit.call)
    (exitInputs : FactoryHistoryGuarantees.Inputs .exit exit.call)
    (linked : exit.call.world = deposit.world)
    (genesisSeed : deposit.call.world = GenesisFundingWorld.world)
    (exitSeed : exit.world = GenesisFundingWorld.world) :
    Nonempty (History deposit exit exit.world) := by
  have ledger :
      ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world 0 0 0 0 exit.world := by
    rw [exitSeed]
    exact ledger_genesis_trivial
  exact exists_seed_zero_counts depositInputs exitInputs linked genesisSeed ledger

#print axioms exists_seed_trivial

end Eip8282.Audit.Integrator.ReferenceGenesisSeededHistory
