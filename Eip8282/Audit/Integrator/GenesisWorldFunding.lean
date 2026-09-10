import Eip8282.Audit.Integrator.GenesisFundingWorld
import Eip8282.Audit.Integrator.ProtocolCreditEnvelope

/-! Discharge the credit envelope's initial-funds premise with the complete
allocation loader already proved in GenesisFundingWorld. This does not adopt
mainnet or prove JSON/parser/reference-loader correspondence. Source metadata:
audit/receipts/direct-genesis-funding-input-20260910.json. Ledger classification
and Counts remain the explicit protocol extraction obligations. -/
namespace Eip8282.Audit.Integrator.GenesisWorldFunding
open EvmYul EvmYul.EVM
open ProtocolCreditEnvelope TransferFunding
set_option autoImplicit false

theorem funding_budget {world : AccountMap .EVM} {pow withdrawals migrations credits : Nat}
    (ledger : Ledger GenesisFundingWorld.world pow withdrawals migrations credits world)
    (counts : Counts pow withdrawals migrations) :
    FundingHistory.Trace GenesisFundingWorld.world credits world ∧
      worldFunds GenesisFundingWorld.world + credits < FundedDomain.fundingCeiling :=
  ProtocolCreditEnvelope.funding_budget ledger GenesisFundingWorld.initial_funds_le counts

theorem final_funds {world : AccountMap .EVM} {pow withdrawals migrations credits : Nat}
    (ledger : Ledger GenesisFundingWorld.world pow withdrawals migrations credits world)
    (counts : Counts pow withdrawals migrations) :
    FundingHistory.Trace GenesisFundingWorld.world credits world ∧
      worldFunds world < FundedDomain.fundingCeiling := by
  obtain ⟨trace,bound⟩ := funding_budget ledger counts
  exact ⟨trace,(FundingHistory.trace_funds trace).trans_lt bound⟩

#print axioms funding_budget
#print axioms final_funds
end Eip8282.Audit.Integrator.GenesisWorldFunding
