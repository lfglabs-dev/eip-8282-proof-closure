import Eip8282.Audit.Integrator.ReleaseCandidate

/-! Canonical funded History lifecycle.

Produces two independent constructors on the existing `ReleaseCandidate.History`
structure:

* `initial` packages an actual factory deployment pair, a prior funding trace
  from genesis to the deposit call world, an existing genesis-to-exit credit
  ledger and count admission into the initial funded History (empty receipts
  and empty block list).
* `next` extends any funded History by one further actual Υ receipt whose
  call world matches the current pre-world. The new receipt occupies a fresh
  one-transaction block with an independently admitted slot and gas capacity.

Neither constructor asserts canonical Ethereum production of the ingredient
records: factory deployment, funding-trace justification, credit-ledger
provenance, sequencer slot admission and per-block gas admission remain
distinct obligations already declared elsewhere in the audit. Synthetic
replay gas is never source gas; local frame effects are not ancestor
commitment.

The next-transaction lemma `receipts_extend` records that the extension is
literally `h.receipts ++ [r]`; downstream consumers can compose successive
`next` calls without pattern matching on the History structure. -/
namespace Eip8282.Audit.Integrator.ReferenceFundedHistoryLifecycle

open EvmYul EvmYul.EVM
open TransactionAppendBudget (Receipt BlockReceipt)
open ReleaseCandidate (History)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Initial funded History from an actual factory deployment pair, a prior
funding trace from `GenesisFundingWorld.world` to `deposit.call.world`, an
existing credit ledger to `exit.world` accumulating exactly `baseCredits`,
and independent count admission. Receipts and blocks are empty at
construction time; the ledger is reused as-is with the internal `0` extra
credits. -/
def initial {deposit exit : Receipt}
    (depositInputs : FactoryHistoryGuarantees.Inputs .deposit deposit.call)
    (exitInputs : FactoryHistoryGuarantees.Inputs .exit exit.call)
    (linked : exit.call.world = deposit.world)
    {baseCredits pow withdrawals migrations : Nat}
    (prior : FundingHistory.Trace GenesisFundingWorld.world baseCredits deposit.call.world)
    (ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world pow withdrawals migrations baseCredits exit.world)
    (counts : ProtocolCreditEnvelope.Counts pow withdrawals migrations) :
    History deposit exit exit.world :=
  { depositInputs
    exitInputs
    linked
    baseCredits
    credits := 0
    pow
    withdrawals
    migrations
    receipts := []
    prior
    actual := ActualJournalHistory.Trace.initial
    ledger := by simpa only [Nat.add_zero] using ledger
    counts
    blocks := []
    listed := by simp
    slots := by simp }

/-- Next-transaction funded History extension. Given a current funded History
`h : History deposit exit before`, an actual Υ receipt `r` whose call world
is `before`, an independently admitted top-level admission/data-size fit and
evaluator-fuel envelope, and a fresh block slot/gas admission, produce
`History deposit exit r.world`. The extension appends one one-transaction
block; existing slots stay unchanged, and slot uniqueness is enforced by the
`freshSlot` premise. -/
def next {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before)
    (r : Receipt) (linked : r.call.world = before)
    (account : EvmYul.Account .EVM)
    (admission : TransactionFunding.Admission r.call account)
    (fit : r.call.transaction.base.data.size < UInt256.size)
    (resources : 5*(r.call.entryGas.toNat+1) ≤ r.call.fuel)
    (slot gas : ResourceBounds.U64)
    (freshSlot : slot ∉ h.blocks.map (fun b => b.slot))
    (admittedGas : r.used.toNat ≤ gas.val) :
    History deposit exit r.world :=
  let step : FundingHistory.Step before 0 r.world := by
    have base := FundingHistory.Step.transaction r.call account admission r.executed
    exact linked ▸ base
  let newBlock : BlockReceipt :=
    { slot := slot
      gas := gas
      receipts := [r]
      admittedGas := by
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        exact admittedGas }
  { depositInputs := h.depositInputs
    exitInputs := h.exitInputs
    linked := h.linked
    baseCredits := h.baseCredits
    credits := h.credits
    pow := h.pow
    withdrawals := h.withdrawals
    migrations := h.migrations
    receipts := h.receipts ++ [r]
    prior := h.prior
    actual := ActualJournalHistory.Trace.transaction h.actual r linked account admission fit resources
    ledger := ProtocolCreditEnvelope.Ledger.conserving h.ledger step
    counts := h.counts
    blocks := h.blocks ++ [newBlock]
    listed := by
      have hl := h.listed
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        newBlock, hl] at *
    slots := by
      have hs := h.slots
      rw [List.map_append, List.map_cons, List.map_nil]
      refine List.Nodup.append hs (List.nodup_singleton _) ?_
      intro a ha
      simp only [List.mem_singleton]
      rintro rfl
      exact freshSlot ha }

/-- The extended receipt list is literally `h.receipts ++ [r]`. -/
theorem receipts_extend {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) {r : Receipt} {linked : r.call.world = before}
    {account : EvmYul.Account .EVM} {admission : TransactionFunding.Admission r.call account}
    {fit : r.call.transaction.base.data.size < UInt256.size}
    {resources : 5*(r.call.entryGas.toNat+1) ≤ r.call.fuel}
    {slot gas : ResourceBounds.U64}
    {freshSlot : slot ∉ h.blocks.map (fun b => b.slot)}
    {admittedGas : r.used.toNat ≤ gas.val} :
    (next h r linked account admission fit resources slot gas freshSlot admittedGas).receipts =
      h.receipts ++ [r] := rfl

/-- The extended block list appends exactly one one-transaction block. -/
theorem blocks_extend {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) {r : Receipt} {linked : r.call.world = before}
    {account : EvmYul.Account .EVM} {admission : TransactionFunding.Admission r.call account}
    {fit : r.call.transaction.base.data.size < UInt256.size}
    {resources : 5*(r.call.entryGas.toNat+1) ≤ r.call.fuel}
    {slot gas : ResourceBounds.U64}
    {freshSlot : slot ∉ h.blocks.map (fun b => b.slot)}
    {admittedGas : r.used.toNat ≤ gas.val} :
    ((next h r linked account admission fit resources slot gas freshSlot admittedGas).blocks).length =
      h.blocks.length + 1 := by
  simp [next]

/-- Preservation of the baseCredits/exit-linking/deployment inputs across `next`. -/
theorem depositInputs_stable {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) {r : Receipt} {linked : r.call.world = before}
    {account : EvmYul.Account .EVM} {admission : TransactionFunding.Admission r.call account}
    {fit : r.call.transaction.base.data.size < UInt256.size}
    {resources : 5*(r.call.entryGas.toNat+1) ≤ r.call.fuel}
    {slot gas : ResourceBounds.U64}
    {freshSlot : slot ∉ h.blocks.map (fun b => b.slot)}
    {admittedGas : r.used.toNat ≤ gas.val} :
    (next h r linked account admission fit resources slot gas freshSlot admittedGas).depositInputs =
      h.depositInputs := rfl

theorem exitInputs_stable {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) {r : Receipt} {linked : r.call.world = before}
    {account : EvmYul.Account .EVM} {admission : TransactionFunding.Admission r.call account}
    {fit : r.call.transaction.base.data.size < UInt256.size}
    {resources : 5*(r.call.entryGas.toNat+1) ≤ r.call.fuel}
    {slot gas : ResourceBounds.U64}
    {freshSlot : slot ∉ h.blocks.map (fun b => b.slot)}
    {admittedGas : r.used.toNat ≤ gas.val} :
    (next h r linked account admission fit resources slot gas freshSlot admittedGas).exitInputs =
      h.exitInputs := rfl

/-- The initial-History receipts and blocks are empty. -/
theorem initial_receipts_empty {deposit exit : Receipt}
    {depositInputs : FactoryHistoryGuarantees.Inputs .deposit deposit.call}
    {exitInputs : FactoryHistoryGuarantees.Inputs .exit exit.call}
    {linked : exit.call.world = deposit.world}
    {baseCredits pow withdrawals migrations : Nat}
    {prior : FundingHistory.Trace GenesisFundingWorld.world baseCredits deposit.call.world}
    {ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world pow withdrawals migrations baseCredits exit.world}
    {counts : ProtocolCreditEnvelope.Counts pow withdrawals migrations} :
    (initial depositInputs exitInputs linked prior ledger counts).receipts = [] := rfl

theorem initial_blocks_empty {deposit exit : Receipt}
    {depositInputs : FactoryHistoryGuarantees.Inputs .deposit deposit.call}
    {exitInputs : FactoryHistoryGuarantees.Inputs .exit exit.call}
    {linked : exit.call.world = deposit.world}
    {baseCredits pow withdrawals migrations : Nat}
    {prior : FundingHistory.Trace GenesisFundingWorld.world baseCredits deposit.call.world}
    {ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world pow withdrawals migrations baseCredits exit.world}
    {counts : ProtocolCreditEnvelope.Counts pow withdrawals migrations} :
    (initial depositInputs exitInputs linked prior ledger counts).blocks = [] := rfl

#print axioms initial
#print axioms next
#print axioms receipts_extend
#print axioms blocks_extend
#print axioms depositInputs_stable
#print axioms exitInputs_stable
#print axioms initial_receipts_empty
#print axioms initial_blocks_empty
end Eip8282.Audit.Integrator.ReferenceFundedHistoryLifecycle
