import Eip8282.Audit.Integrator.GenesisWorldFunding
import Eip8282.Audit.Integrator.Topics.Protocol

/-! Checked external-credit addition is derived at every literal ledger edge.
The bound comes from the complete constructed genesis and the credit/count
envelope, not from a no-wrap premise on recipients. This supplies arithmetic
guards for a reference adapter; it does not prove its state representation,
canonical ledger classification or checked-U256 implementation correspondence. -/
namespace Eip8282.Audit.Integrator.LedgerCreditSafety
open EvmYul EvmYul.EVM
open ProtocolCreditEnvelope TransferFunding
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- A literal external-credit location carries its pre-world, recipient and
amount as data indices. It ranges over all valid histories with these endpoints;
no claim about identity of Prop-valued trace proofs is needed. -/
inductive CreditAt (initial : AccountMap .EVM) : Nat → AccountMap .EVM →
    AccountMap .EVM → AccountAddress → UInt256 → Prop where
  | here {credits : Nat} {before : AccountMap .EVM}
      (prior : FundingHistory.Trace initial credits before) (recipient : AccountAddress) (amount : UInt256) :
      CreditAt initial (credits+amount.toNat) (before.increaseBalance .EVM recipient amount) before recipient amount
  | next {credits delta : Nat} {before after source : AccountMap .EVM}
      {recipient : AccountAddress} {amount : UInt256}
      (located : CreditAt initial credits before source recipient amount)
      (step : FundingHistory.Step before delta after) :
      CreditAt initial (credits+delta) after source recipient amount

/-- Every located credit yields its actual funded prefix and a derived
prefix-plus-credit index bound, even across arbitrary later operations. -/
theorem CreditAt.prefix {initial final before : AccountMap .EVM} {total : Nat}
    {recipient : AccountAddress} {amount : UInt256}
    (located : CreditAt initial total final before recipient amount) :
    ∃ credits, FundingHistory.Trace initial credits before ∧ credits+amount.toNat ≤ total := by
  induction located with
  | here prior recipient amount => exact ⟨_,prior,Nat.le_refl _⟩
  | next located step ih =>
    obtain ⟨credits,prior,bound⟩ := ih
    exact ⟨credits,prior,by omega⟩

theorem credit_at_fits {initial final before : AccountMap .EVM} {total : Nat}
    {recipient : AccountAddress} {amount : UInt256}
    (located : CreditAt initial total final before recipient amount)
    (budget : worldFunds initial+total < UInt256.size) :
    worldBalance before recipient+amount.toNat < UInt256.size := by
  obtain ⟨credits,prior,bound⟩ := located.prefix
  have balance := FundingHistory.balance_budget prior recipient
  omega

inductive BatchChecked : {before after : AccountMap .EVM} → {total : Nat} →
    CreditBatch before total after → Prop where
  | nil (world : AccountMap .EVM) : BatchChecked (.nil world)
  | cons {before after : AccountMap .EVM} {total : Nat}
      (recipient : AccountAddress) (amount : UInt256)
      (tail : CreditBatch (before.increaseBalance .EVM recipient amount) total after)
      (fits : worldBalance before recipient + amount.toNat < UInt256.size)
      (rest : BatchChecked tail) : BatchChecked (.cons recipient amount tail)

theorem batch_checked {initial before after : AccountMap .EVM} {credits total : Nat}
    (prior : FundingHistory.Trace initial credits before) (batch : CreditBatch before total after)
    (budget : worldFunds initial + (credits+total) < UInt256.size) : BatchChecked batch := by
  induction batch generalizing credits with
  | nil world => exact .nil world
  | @cons before after total recipient amount tail ih =>
    have balance := FundingHistory.balance_budget prior recipient
    refine .cons recipient amount tail (by omega) ?_
    exact ih (FundingHistory.Trace.next prior (.credit before recipient amount)) (by omega)

inductive LedgerChecked {initial : AccountMap .EVM} :
    {p w s c : Nat} → {world : AccountMap .EVM} → Ledger initial p w s c world → Prop where
  | initial : LedgerChecked (.initial : Ledger initial 0 0 0 0 initial)
  | conserving {p w s c : Nat} {before after : AccountMap .EVM}
      (prior : Ledger initial p w s c before) (step : FundingHistory.Step before 0 after)
      (safe : LedgerChecked prior) : LedgerChecked (.conserving prior step)
  | pow {p w s c amount : Nat} {before after : AccountMap .EVM}
      (prior : Ledger initial p w s c before) (batch : CreditBatch before amount after)
      (bounded : amount ≤ powMaximum) (safe : LedgerChecked prior) (checked : BatchChecked batch) :
      LedgerChecked (.pow prior batch bounded)
  | withdrawal {p w s c : Nat} {before : AccountMap .EVM}
      (prior : Ledger initial p w s c before) (recipient : AccountAddress) (amount : UInt256)
      (bounded : amount.toNat ≤ withdrawalMaximum) (safe : LedgerChecked prior)
      (fits : worldBalance before recipient + amount.toNat < UInt256.size) :
      LedgerChecked (.withdrawal prior recipient amount bounded)
  | migration {p w s c amount : Nat} {before after : AccountMap .EVM}
      (prior : Ledger initial p w s c before) (batch : CreditBatch before amount after)
      (safe : LedgerChecked prior) (checked : BatchChecked batch) : LedgerChecked (.migration prior batch)

/-- Every external-credit edge is checked in the original ledger induction.
Conserving transaction/SYSTEM/transfer internals require their own reference
adapters; this predicate does not assert those by treating them as credits. -/
theorem ledger_checked {initial world : AccountMap .EVM} {p w s c : Nat}
    (ledger : Ledger initial p w s c world)
    (budget : worldFunds initial+c < UInt256.size) : LedgerChecked ledger := by
  induction ledger with
  | initial => exact .initial
  | conserving prior step ih => exact .conserving prior step (ih budget)
  | pow prior batch bounded ih =>
    exact .pow prior batch bounded (ih (by omega)) (batch_checked (ledger_bound prior).1 batch budget)
  | withdrawal prior recipient amount bounded ih =>
    have balance := FundingHistory.balance_budget (ledger_bound prior).1 recipient
    exact .withdrawal prior recipient amount bounded (ih (by omega)) (by omega)
  | migration prior batch ih =>
    exact .migration prior batch (ih (by omega)) (batch_checked (ledger_bound prior).1 batch budget)

theorem genesis_budget {world : AccountMap .EVM} {p w s c : Nat}
    (ledger : Ledger GenesisFundingWorld.world p w s c world) (counts : Counts p w s) :
    worldFunds GenesisFundingWorld.world+c < UInt256.size := by
  have hg := GenesisFundingWorld.initial_funds_le
  have hc := (ledger_bound ledger).2
  have he := numeric_envelope counts
  have hn : 2^163 < UInt256.size := by decide +kernel
  unfold envelope at he
  omega

/-- No recipient wrap premise: the actual ledger and source-derived counts
supply all external-credit checked-addition guards. -/
theorem from_genesis {world : AccountMap .EVM} {p w s c : Nat}
    (ledger : Ledger GenesisFundingWorld.world p w s c world) (counts : Counts p w s) :
    LedgerChecked ledger := ledger_checked ledger (genesis_budget ledger counts)

/-- Universal checked-addition guard at each data-indexed external-credit
location in the same endpoint/credit envelope. This is the reference adapter's
local consumer, stronger than merely exhibiting an annotated ledger proof. -/
theorem genesis_credit_at {world before : AccountMap .EVM} {p w s c : Nat}
    (ledger : Ledger GenesisFundingWorld.world p w s c world) (counts : Counts p w s)
    {recipient : AccountAddress} {amount : UInt256}
    (located : CreditAt GenesisFundingWorld.world c world before recipient amount) :
    worldBalance before recipient+amount.toNat < UInt256.size :=
  credit_at_fits located (genesis_budget ledger counts)

/-- Conserving migration transfers read the recipient after debit, so sender
aliases also fit. The pre-world sum is supplied by the same ledger. -/
theorem migration_add_fits {world : AccountMap .EVM} {p w s c : Nat}
    (ledger : Ledger GenesisFundingWorld.world p w s c world) (counts : Counts p w s)
    (source recipient : AccountAddress) (amount : UInt256)
    (funded : amount.toNat ≤ worldBalance world source) :
    (ProtocolMigrationLedger.currentBalance (ProtocolTransfer.debit world source amount) recipient).toNat +
      amount.toNat < UInt256.size := by
  have hf := FundingHistory.trace_funds (ledger_bound ledger).1
  exact ProtocolMigrationLedger.checked_add_fits world source recipient amount funded
    (hf.trans_lt (genesis_budget ledger counts))

#print axioms CreditAt.prefix
#print axioms credit_at_fits
#print axioms genesis_credit_at
#print axioms batch_checked
#print axioms ledger_checked
#print axioms genesis_budget
#print axioms from_genesis
#print axioms migration_add_fits
end Eip8282.Audit.Integrator.LedgerCreditSafety
