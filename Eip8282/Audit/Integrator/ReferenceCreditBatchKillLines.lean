import Eip8282.Audit.Integrator.ProtocolCreditEnvelope

/-! Kill-line mutations exercising the aggregate accounting inside
`ProtocolCreditEnvelope.CreditBatch`, `envelope`, `powMaximum` and
`withdrawalMaximum`.

Each theorem below is a small concrete equality or bound the constructor
must satisfy; a mutation that swaps operand order, replaces `+` with `*`,
or drops a factor would flip the statement. The theorems do not require
instantiating a `Ledger` or a `History` — they exercise the arithmetic in
isolation, so downstream `native_decide` fixtures are unnecessary.

No new premise; no new axiom. -/
namespace Eip8282.Audit.Integrator.ReferenceCreditBatchKillLines

open EvmYul EvmYul.EVM
open ProtocolCreditEnvelope
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- `powMaximum` is exactly the reference-EL Frontier miner batch bound. A
mutation dropping a digit or reordering the literal breaks this equality. -/
theorem powMaximum_value : powMaximum = 14062500000000000000 := rfl

/-- `withdrawalMaximum` is exactly `(2^64 - 1) * 10^9`. A mutation replacing
`*` with `+` or `10^9` with `10^8` breaks this equality. -/
theorem withdrawalMaximum_value : withdrawalMaximum = (2^64 - 1) * 10^9 := rfl

/-- `envelope` is exactly the sum of the three protocol credit sources plus
the genesis constant. Mutations swapping the factor order or dropping a
term break this equality. -/
theorem envelope_expansion (pow withdrawals migrations : Nat) :
    envelope pow withdrawals migrations =
      GenesisFundingInput.totalCredit + powMaximum * pow + withdrawalMaximum * withdrawals + migrations := rfl

/-- Zero pow/withdrawal/migration inputs give the genesis total exactly. -/
theorem envelope_zero : envelope 0 0 0 = GenesisFundingInput.totalCredit := by
  simp [envelope]

/-- One PoW batch contributes `powMaximum` on top of the base. -/
theorem envelope_one_pow :
    envelope 1 0 0 = GenesisFundingInput.totalCredit + powMaximum := by
  simp [envelope]

/-- One withdrawal contributes `withdrawalMaximum` on top of the base. -/
theorem envelope_one_withdrawal :
    envelope 0 1 0 = GenesisFundingInput.totalCredit + withdrawalMaximum := by
  simp [envelope]

/-- `nil` batch: source world unchanged, aggregate credit zero. This is
the identity kill-line — dropping the `world = world` requirement would
allow a mutated `nil` to pretend to teleport between worlds. -/
theorem nil_credit_zero (world : AccountMap .EVM) :
    CreditBatch world 0 world := CreditBatch.nil world

/-- A one-element batch aggregates a single `amount`. Mutations replacing
the amount with a fixed constant would fail this general form. -/
theorem cons_singleton (world : AccountMap .EVM)
    (recipient : AccountAddress) (amount : UInt256) :
    CreditBatch world (amount.toNat + 0)
      (world.increaseBalance .EVM recipient amount) :=
  CreditBatch.cons recipient amount (CreditBatch.nil _)

/-- Concrete numeric kill-line: a two-step batch aggregates exactly the sum
of its two amounts (specialised at `⟨0⟩` and `⟨0⟩`). Two zero-value
credits still walk through the batch even if `increaseBalance` yields
the same world. -/
theorem cons_two_zero_amounts (world : AccountMap .EVM)
    (r1 r2 : AccountAddress) :
    CreditBatch world ((⟨0⟩ : UInt256).toNat + ((⟨0⟩ : UInt256).toNat + 0))
      (((world.increaseBalance .EVM r1 ⟨0⟩).increaseBalance .EVM r2 ⟨0⟩)) :=
  CreditBatch.cons r1 ⟨0⟩
    (CreditBatch.cons r2 ⟨0⟩ (CreditBatch.nil _))

#print axioms powMaximum_value
#print axioms withdrawalMaximum_value
#print axioms envelope_expansion
#print axioms envelope_zero
#print axioms envelope_one_pow
#print axioms envelope_one_withdrawal
#print axioms nil_credit_zero
#print axioms cons_singleton
#print axioms cons_two_zero_amounts

end Eip8282.Audit.Integrator.ReferenceCreditBatchKillLines
