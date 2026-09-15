import Eip8282.Audit.Integrator.FinalizationWorldFrame
import Eip8282.Audit.Integrator.JournalInvariant
import Eip8282.Audit.Integrator.Topics.Nested
import Eip8282.Audit.Integrator.ResourceBounds
import Eip8282.Audit.Integrator.Topics.Transaction3
import Eip8282.Audit.Integrator.TransactionFunding

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## TransactionAppendBudget -/

/-!
# Actual transaction append counts feed the finite-slot resource bound

Append counts are extracted from full actual transaction executions, with
failed final status and reverted descendants retained. The only block resource
inputs are typed slot/gas values and admission of the natural sum of reported
transaction gas. Reference Ethereum admission, scheduling and dual-pool gas
adequacy must still produce these inputs; they are not asserted here.
-/
namespace Eip8282.Audit.Integrator.TransactionAppendBudget
open EvmYul EvmYul.EVM
open NestedEvents NestedAppendCount
set_option autoImplicit false

/-- A receipt of literal pinned Υ, retaining actual status and charged gas. -/
structure Receipt where
  call : RefundAccounting.Context
  world : AccountMap .EVM
  substate : Substate
  success : Bool
  used : UInt256
  executed : call.result = .ok (world,substate,success,used)

noncomputable def tree (r : Receipt) : EventTree :=
  Classical.choose (transaction_appends r.call r.executed)

theorem tree_cert (r : Receipt) :
    Cert (TransactionEventBounds.request r.call)
      (TransactionEventBounds.request r.call).eval (tree r) :=
  (Classical.choose_spec (transaction_appends r.call r.executed)).1

noncomputable def appends (r : Receipt) : Nat :=
  count (TransactionEventBounds.request r.call)
    (TransactionEventBounds.request r.call).eval (tree r)

theorem appends_le_used (r : Receipt) : appends r ≤ r.used.toNat :=
  (Classical.choose_spec (transaction_appends r.call r.executed)).2.1

/-- Aggregate charge is derived from the actual receipts, not supplied as an
append≤gas field in the input. The distinct transaction invocations remain
separate list positions even when their call inputs happen to be equal. -/
theorem sum_appends_le_used (receipts : List Receipt) :
    (receipts.map appends).sum ≤ (receipts.map (fun r => r.used.toNat)).sum := by
  induction receipts with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (appends_le_used r) ih

/-- Resource admission remains a named protocol obligation. This structure
cannot stand in for a proof that the pinned evaluator implements Amsterdam. -/
structure BlockReceipt where
  slot : ResourceBounds.U64
  gas : ResourceBounds.U64
  receipts : List Receipt
  admittedGas : (receipts.map (fun r => r.used.toNat)).sum ≤ gas.val

noncomputable def usage (b : BlockReceipt) : ResourceBounds.BlockUsage :=
  { slot := b.slot, gas := b.gas, appends := (b.receipts.map appends).sum,
    charged := (sum_appends_le_used b.receipts).trans b.admittedGas }

/-- No artificial per-transaction or fee-iteration cap occurs in this bound.
The 2^128 result follows from distinct typed block slots and admitted gas;
canonical history and protocol provenance of those two inputs remain visible. -/
theorem history_lt (blocks : List BlockReceipt)
    (slots : (blocks.map (fun b => b.slot)).Nodup) :
    (blocks.map (fun b => (b.receipts.map appends).sum)).sum < 2^128 := by
  have hs : ((blocks.map usage).map (fun b => b.slot)).Nodup := by
    simpa only [List.map_map, Function.comp_def, usage] using slots
  have h := ResourceBounds.total_lt (blocks.map usage) hs
  simpa only [ResourceBounds.totalAppends, List.map_map, Function.comp_def, usage] using h

#print axioms tree_cert
#print axioms appends_le_used
#print axioms sum_appends_le_used
#print axioms history_lt
end Eip8282.Audit.Integrator.TransactionAppendBudget

end

section

/-! ## TransactionJournalEdges -/

/-! Literal transaction checkpoint, provisional evaluator, and finalization
edges. A returned false status is retained. These projections do not assume
per-call invariants or extract protocol admission. -/
namespace Eip8282.Audit.Integrator.TransactionJournalEdges
open EvmYul EvmYul.EVM
open RefundAccounting NestedEvents CodeStorageFrame
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem checkpoint_frame (c : Context) {account : Account .EVM}
    (ha : TransactionFunding.Admission c account) (protectedAddr : AccountAddress) :
    Frame c.world c.checkpoint protectedAddr := by
  rw [TransactionFunding.checkpoint_eq c ha]
  have hl : (c.world.insert c.sender (TransactionFunding.debited c account)).get? protectedAddr =
      if c.sender = protectedAddr then some (TransactionFunding.debited c account)
      else c.world.get? protectedAddr := by
    exact (Std.TreeMap.getElem?_insert (t := c.world) (k := c.sender)
      (a := protectedAddr) (v := TransactionFunding.debited c account)).trans
      (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)
  by_cases he : c.sender = protectedAddr
  · have hold : c.world.get? protectedAddr = some account := he ▸ ha.sender
    constructor
    · intro old ho
      have ho : account = old := Option.some.inj (hold.symm.trans ho)
      subst old
      exact ⟨TransactionFunding.debited c account,by rw [hl,if_pos he],rfl⟩
    · intro slot
      simp only [SystemSpec.worldSlot,hl,if_pos he,hold,Option.map_some,Option.getD_some]
      rfl
  · constructor
    · intro old ho
      exact ⟨old,by rw [hl,if_neg he]; exact ho,rfl⟩
    · intro slot
      simp only [SystemSpec.worldSlot,hl,if_neg he]

theorem settled_frame (c : Context) (world : AccountMap .EVM) (remaining : UInt256)
    (ss : Substate) (protectedAddr : AccountAddress) {old : Account .EVM}
    (ho : world.get? protectedAddr = some old) (hc : old.code ≠ ByteArray.empty)
    (hn : protectedAddr ∉ ss.selfDestructSet) :
    Frame world (TransactionFunding.settledWorld c world remaining ss) protectedAddr := by
  let refundAmount := returnedGas c.transaction.base.gasLimit remaining ss.refundBalance * c.effectivePrice
  let refunded := world.increaseBalance .EVM c.sender refundAmount
  let fee := netGas c.transaction.base.gasLimit remaining ss.refundBalance * c.priorityFee
  let paid := if fee != ⟨0⟩ then refunded.increaseBalance .EVM c.header.beneficiary fee else refunded
  have hr : Frame world refunded protectedAddr := FinalizationWorldFrame.credit_frame _ _ _ _
  have hp : Frame refunded paid protectedAddr := by
    unfold paid
    split
    · exact FinalizationWorldFrame.credit_frame _ _ _ _
    · exact CodeStorageFrame.refl _ _
  have hf := CodeStorageFrame.trans hr hp
  obtain ⟨current,hcur,hcode⟩ := hf.existing old ho
  have hnonempty : current.code ≠ ByteArray.empty := fun he => hc (hcode.symm.trans he)
  exact CodeStorageFrame.trans hf
    (FinalizationWorldFrame.cleanup_frame paid ss protectedAddr hcur hnonempty hn)

theorem settled_codeAt_frame {kind : ReachableCalls.Contract}
    (c : Context) (world : AccountMap .EVM) (remaining : UInt256) (ss : Substate)
    (hc : JournalInvariant.CodeAt kind world)
    (hn : ReachableCalls.address kind ∉ ss.selfDestructSet) :
    Frame world (TransactionFunding.settledWorld c world remaining ss) (ReachableCalls.address kind) := by
  obtain ⟨old,ho,hcode⟩ := hc
  apply settled_frame c world remaining ss _ ho _ hn
  rw [hcode]
  cases kind <;> decide +kernel

/-- Both real provisional branches preserve all four projected result fields.
The extra values are precisely the fields erased by Context.provisional. -/
theorem provisional_cases (c : Context) {world : AccountMap .EVM} {gas : UInt256}
    {ss : Substate} {status : Bool} (hp : c.provisional = .ok (world,gas,ss,status)) :
    (c.transaction.base.recipient = none ∧ ∃ target created out,
      (Request.lambda c.fuel (TransactionEventBounds.creation c)).eval =
        .ok (target,created,world,gas,ss,status,out)) ∨
    (∃ recipient, c.transaction.base.recipient = some recipient ∧ ∃ created out,
      (Request.theta c.fuel (TransactionEventBounds.message c recipient)).eval =
        .ok (created,world,gas,ss,status,out)) := by
  unfold Context.provisional at hp
  split at hp
  · rename_i hr
    left
    refine ⟨hr,?_⟩
    split at hp
    · rename_i target created actualWorld actualGas actualSubstate actualStatus out he
      cases hp
      exact ⟨target,created,out,he⟩
    · cases hp
  · rename_i recipient hr
    right
    refine ⟨recipient,hr,?_⟩
    split at hp
    · rename_i created actualWorld actualGas actualSubstate actualStatus out he
      cases hp
      exact ⟨created,out,he⟩
    · cases hp

#print axioms checkpoint_frame
#print axioms settled_frame
#print axioms settled_codeAt_frame
#print axioms provisional_cases
end Eip8282.Audit.Integrator.TransactionJournalEdges

end
