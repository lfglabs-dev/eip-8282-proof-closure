import Eip8282.Audit.Integrator.FundingHistory
import Eip8282.Audit.Integrator.GenesisFundingInput

/-! Conditional arithmetic over actual explicit credit operations.
Reference EL 0cc100eb190b64b23baba72dac0165652eaec252, CL
ad0058fd0d34c5dcf504fa51ea2f4f11077b9996; source hashes and exact lines:
audit/receipts/direct-protocol-credit-envelope-audit-20260910.md. No reference is adopted here.
Frontier fork.py:581-589 gives the miner/ommer batch bound (max two, age>=1).
Amsterdam blocks.py:62 and fork.py:1118 give uint64 Gwei withdrawal amounts.
Capella beacon-chain.md:138 gives cap16; phase0:473,1788 give uint64 slots.
OPEN producers: actual canonical PoW batch extraction, all-fork coverage,
withdrawal payload/cardinality/slot linkage, migration conservation, genesis
world correspondence. EL number is Uint: the PoW count bound is NOT its width.
-/
namespace Eip8282.Audit.Integrator.ProtocolCreditEnvelope
open EvmYul EvmYul.EVM
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def powMaximum : Nat := 14062500000000000000

def withdrawalMaximum : Nat := (2^64-1)*10^9

def envelope (pow withdrawals migrations : Nat) : Nat :=
  GenesisFundingInput.totalCredit + powMaximum*pow + withdrawalMaximum*withdrawals + migrations

/-- A batch retains every literal credited world, recipient and amount. -/
inductive CreditBatch : (AccountMap .EVM) → Nat → (AccountMap .EVM) → Prop where
  | nil (world : (AccountMap .EVM)) : CreditBatch world 0 world
  | cons {before after : (AccountMap .EVM)} {total : Nat}
      (recipient : AccountAddress) (amount : UInt256)
      (tail : CreditBatch (before.increaseBalance .EVM recipient amount) total after)
      :
      CreditBatch before (amount.toNat+total) after

private theorem batch_extend {initial before after : (AccountMap .EVM)} {credits total : Nat}
    (prior : FundingHistory.Trace initial credits before) (batch : CreditBatch before total after) :
    FundingHistory.Trace initial (credits+total) after := by
  induction batch generalizing credits with
  | nil => simpa using prior
  | cons recipient amount tail ih =>
    have h := ih (FundingHistory.Trace.next prior (.credit _ recipient amount))
    simpa only [Nat.add_assoc] using h

/-- Classifications and numeric bounds are inputs to be extracted from protocol
operations, never bounds on the resulting world's wealth. -/
inductive Ledger (initial : (AccountMap .EVM)) : Nat → Nat → Nat → Nat → (AccountMap .EVM) → Prop where
  | initial : Ledger initial 0 0 0 0 initial
  | conserving {p w s c : Nat} {before after : (AccountMap .EVM)}
      (prior : Ledger initial p w s c before) (step : FundingHistory.Step before 0 after) :
      Ledger initial p w s c after
  | pow {p w s c amount : Nat} {before after : (AccountMap .EVM)}
      (prior : Ledger initial p w s c before) (batch : CreditBatch before amount after)
      (bounded : amount ≤ powMaximum) : Ledger initial (p+1) w s (c+amount) after
  | withdrawal {p w s c : Nat} {before : (AccountMap .EVM)}
      (prior : Ledger initial p w s c before) (recipient : AccountAddress) (amount : UInt256)
      (bounded : amount.toNat ≤ withdrawalMaximum) :
      Ledger initial p (w+1) s (c+amount.toNat) (before.increaseBalance .EVM recipient amount)
  | migration {p w s c amount : Nat} {before after : (AccountMap .EVM)}
      (prior : Ledger initial p w s c before) (batch : CreditBatch before amount after) :
      Ledger initial p w (s+amount) (c+amount) after

theorem ledger_bound {initial world : (AccountMap .EVM)} {p w s c : Nat}
    (h : Ledger initial p w s c world) :
    FundingHistory.Trace initial c world ∧ c ≤ powMaximum*p + withdrawalMaximum*w + s := by
  induction h with
  | initial => exact ⟨.initial,by omega⟩
  | conserving prior step ih => exact ⟨by simpa using FundingHistory.Trace.next ih.1 step,ih.2⟩
  | pow prior batch bounded ih =>
    exact ⟨batch_extend ih.1 batch,by simp only [Nat.mul_add,Nat.mul_one]; omega⟩
  | withdrawal prior recipient amount bounded ih =>
    exact ⟨FundingHistory.Trace.next ih.1 (.credit _ recipient amount),by
      simp only [Nat.mul_add,Nat.mul_one]; omega⟩
  | migration prior batch ih => exact ⟨batch_extend ih.1 batch,by omega⟩

/-- Explicit count and migration obligations, not asserted protocol facts. -/
structure Counts (pow withdrawals migrations : Nat) : Prop where
  pow_count : pow ≤ 2^64
  withdrawal_count : withdrawals ≤ 16*2^64
  migration_conserving : migrations = 0

theorem numeric_envelope {p w s : Nat} (h : Counts p w s) : envelope p w s < 2^163 := by
  have hp := Nat.mul_le_mul_left powMaximum h.pow_count
  have hw := Nat.mul_le_mul_left withdrawalMaximum h.withdrawal_count
  have hn : GenesisFundingInput.totalCredit + powMaximum*2^64 + withdrawalMaximum*(16*2^64) < 2^163 := by
    rw [GenesisFundingInput.total_credit_exact]
    decide +kernel
  unfold envelope
  rw [GenesisFundingInput.total_credit_exact] at hn ⊢
  rw [h.migration_conserving, Nat.add_zero]
  exact lt_of_le_of_lt (Nat.add_le_add (Nat.add_le_add_left hp _) hw) hn

theorem below_ceiling : 2^163 < FundedDomain.fundingCeiling := by decide +kernel

theorem funding_budget {initial world : (AccountMap .EVM)} {p w s c : Nat}
    (ledger : Ledger initial p w s c world)
    (genesis : TransferFunding.worldFunds initial ≤ GenesisFundingInput.totalCredit)
    (counts : Counts p w s) :
    FundingHistory.Trace initial c world ∧
      TransferFunding.worldFunds initial+c < FundedDomain.fundingCeiling := by
  obtain ⟨trace,bound⟩ := ledger_bound ledger
  have hn := numeric_envelope counts
  have hb := below_ceiling
  unfold envelope at hn
  exact ⟨trace,by omega⟩

#print axioms ledger_bound
#print axioms numeric_envelope
#print axioms below_ceiling
#print axioms funding_budget
end Eip8282.Audit.Integrator.ProtocolCreditEnvelope
