import Eip8282.Audit.Integrator.ReleaseCandidate

/-! Bridge: a funded `ReleaseCandidate.History` at world `before` yields
the world-funds budget bound `worldFunds before < FundedDomain.fundingCeiling`.

`ProtocolCreditEnvelope.funding_budget` already gives this bound
conditional on a genesis-funds premise. `GenesisFundingWorld.initial_funds_le`
supplies exactly that premise for `initial = GenesisFundingWorld.world`,
which is the fixed initial world of every History via its `prior` and
`ledger` fields.

The bridge specializes those two facts to the concrete `History`
structure so consumers can quote a single named theorem
`worldFunds_lt_ceiling h` rather than re-threading the ledger, counts
and genesis premise at every call site. It also exposes a companion
`funding_trace_from_genesis` giving the accumulated
`FundingHistory.Trace GenesisFundingWorld.world (baseCredits + credits) before`
that `funding_budget` yields, keyed to the History's fields.

The bridge does not adopt any protocol policy or admit a new premise:
it packages the same fact that `funding_budget` and
`GenesisFundingWorld.initial_funds_le` already prove independently. -/
namespace Eip8282.Audit.Integrator.ReferenceHistoryFundsBridge

open EvmYul EvmYul.EVM
open TransactionAppendBudget (Receipt)
open ReleaseCandidate (History)
open ProtocolCreditEnvelope (funding_budget)
open GenesisFundingWorld (initial_funds_le)
open FundedDomain (fundingCeiling)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Named funding-history trace from genesis to the History's before-world,
accumulating `baseCredits + credits` credits along the way. -/
theorem funding_trace_from_genesis {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) :
    FundingHistory.Trace GenesisFundingWorld.world (h.baseCredits + h.credits) before :=
  (funding_budget h.ledger initial_funds_le h.counts).1

/-- Bridge theorem: the `before`-world of any funded History has
world-funds strictly below the audited funding ceiling. This is the
consumer-facing single-lemma form of
`GenesisFundingWorld.initial_funds_le` combined with
`ProtocolCreditEnvelope.funding_budget h.ledger _ h.counts`. -/
theorem worldFunds_lt_ceiling {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) :
    TransferFunding.worldFunds before < FundedDomain.fundingCeiling := by
  have hb := (funding_budget h.ledger initial_funds_le h.counts).2
  -- hb : worldFunds initial + (baseCredits + credits) < fundingCeiling
  -- since worldFunds before ≤ worldFunds initial + (baseCredits + credits), this gives:
  have hs := FundingHistory.trace_funds (funding_trace_from_genesis h)
  exact lt_of_le_of_lt hs hb

/-- Companion: any individual account's balance in `before` is bounded
by the funding ceiling. Consumers can quote this alongside
`worldFunds_lt_ceiling`. -/
theorem worldBalance_lt_ceiling {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) (address : AccountAddress) :
    TransferFunding.worldBalance before address < FundedDomain.fundingCeiling :=
  (TransferFunding.balance_le_funds before address).trans_lt (worldFunds_lt_ceiling h)

#print axioms funding_trace_from_genesis
#print axioms worldFunds_lt_ceiling
#print axioms worldBalance_lt_ceiling

end Eip8282.Audit.Integrator.ReferenceHistoryFundsBridge
