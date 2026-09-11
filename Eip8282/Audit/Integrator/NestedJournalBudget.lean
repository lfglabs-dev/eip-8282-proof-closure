import Eip8282.Audit.Integrator.NestedCallOccurrence
import Eip8282.Audit.Integrator.TransactionAppendBudget

/-!
# Chronological executed-event budgets at actual nested call checkpoints

The step's selected child runs before its returned local effect, then the X
continuation runs. `before` follows that order and retains work even when an
ancestor later restores its journal. It counts executed marked LOG0 operations,
not persistent records. Actual ThetaAt certificates supply the call positions;
there is no caller-selected subset of invocations or supplied prefix bound.

The typed block resource inputs remain protocol producer obligations. The
lemmas here do not yet extract the storage invariant at these checkpoints.
-/
namespace Eip8282.Audit.Integrator.NestedJournalBudget
open EvmYul EvmYul.EVM
open NestedEvents
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- Work completed before descending to a structural call position. For a
child edge the parent's local effect has not occurred; for NEXT both the child
and the parent's effect have occurred. Transparent wrappers add no work. -/
def before : EventTree → EventTree.Address → Nat
  | _, [] => 0
  | .done, _::_ => 0
  | .step _ child _, false::path => before child path
  | .step marked child next, true::path =>
      child.count + (if marked then 1 else 0) + before next path

/-- Every actual located call has a certified subtree and an entry/return
interval inside the complete execution's event budget. All outcome cases,
including failed steps and reverting ancestors, use the same induction. -/
theorem call_interval {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {fuel : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt q result tree path fuel a r) :
    ∃ inner, Cert (.theta fuel a) r inner ∧
      before tree path + inner.count ≤ tree.count := by
  induction loc with
  | here body => exact ⟨_,body,by simp only [before, Nat.zero_add, Nat.le_refl]⟩
  | xStepError _ _ _ ih =>
    obtain ⟨inner,hc,hb⟩ := ih
    exact ⟨inner,hc,by simpa only [before, EventTree.count, Bool.false_eq_true,
      ↓reduceIte, Nat.zero_add, Nat.add_zero] using hb⟩
  | xNextChild _ _ _ _ _ ih =>
    obtain ⟨inner,hc,hb⟩ := ih
    refine ⟨inner,hc,?_⟩
    simp only [before, EventTree.count]
    omega
  | xNextTail _ _ _ _ _ ih =>
    obtain ⟨inner,hc,hb⟩ := ih
    refine ⟨inner,hc,?_⟩
    simp only [before, EventTree.count]
    omega
  | xHalt _ _ _ _ _ ih =>
    obtain ⟨inner,hc,hb⟩ := ih
    refine ⟨inner,hc,?_⟩
    simp only [before, EventTree.count]
    omega
  | xRevert _ _ _ _ _ ih =>
    obtain ⟨inner,hc,hb⟩ := ih
    refine ⟨inner,hc,?_⟩
    simp only [before, EventTree.count]
    omega
  | xi _ _ ih => exact ih
  | thetaCode _ _ _ _ ih => exact ih
  | lambdaInit _ _ _ _ ih => exact ih
  | stepChild _ _ _ ih => exact ih

/-- The already extracted receipt tree has the original complete event gas
bound. Determinism identifies it with the event producer's tree. -/
theorem events_le_used (r : TransactionAppendBudget.Receipt) :
    (TransactionAppendBudget.tree r).count ≤ r.used.toNat := by
  obtain ⟨tree,hc,_,hb,_⟩ := TransactionEventBounds.transaction_events r.call r.executed
  have he := NestedEvents.deterministic (TransactionAppendBudget.tree_cert r) hc
  rw [he]
  exact hb

theorem transaction_call_interval (receipt : TransactionAppendBudget.Receipt)
    {path : EventTree.Address} {fuel : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt (TransactionEventBounds.request receipt.call)
      (TransactionEventBounds.request receipt.call).eval
      (TransactionAppendBudget.tree receipt) path fuel a r) :
    ∃ inner, Cert (.theta fuel a) r inner ∧
      before (TransactionAppendBudget.tree receipt) path + inner.count ≤ receipt.used.toNat := by
  obtain ⟨inner,hc,hb⟩ := call_interval loc
  exact ⟨inner,hc,hb.trans (events_le_used receipt)⟩

noncomputable def events (receipt : TransactionAppendBudget.Receipt) : Nat :=
  (TransactionAppendBudget.tree receipt).count

theorem sum_events_le_used (receipts : List TransactionAppendBudget.Receipt) :
    (receipts.map events).sum ≤ (receipts.map (fun r => r.used.toNat)).sum := by
  induction receipts with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (events_le_used r) ih

noncomputable def usage (b : TransactionAppendBudget.BlockReceipt) : ResourceBounds.BlockUsage :=
  { slot := b.slot, gas := b.gas, appends := (b.receipts.map events).sum,
    charged := (sum_events_le_used b.receipts).trans b.admittedGas }

/-- The same protocol resource envelope bounds all marked executed work, so
it also accommodates work later rolled back. No fee-iteration cap is used. -/
theorem history_lt (blocks : List TransactionAppendBudget.BlockReceipt)
    (slots : (blocks.map (fun b => b.slot)).Nodup) :
    (blocks.map (fun b => (b.receipts.map events).sum)).sum < 2^128 := by
  have hs : ((blocks.map usage).map (fun b => b.slot)).Nodup := by
    simpa only [List.map_map, Function.comp_def, usage] using slots
  have h := ResourceBounds.total_lt (blocks.map usage) hs
  simpa only [ResourceBounds.totalAppends, List.map_map, Function.comp_def, usage] using h

/-- A linked preceding-work budget and the actual located call's complete
transaction interval yield its entry and return bounds. `prior` denotes work
already executed in preceding transactions, whose linkage is a separate input. -/
theorem bounded_call_interval (receipt : TransactionAppendBudget.Receipt) (prior : Nat)
    (hb : prior + events receipt < 2^128)
    {path : EventTree.Address} {fuel : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt (TransactionEventBounds.request receipt.call)
      (TransactionEventBounds.request receipt.call).eval
      (TransactionAppendBudget.tree receipt) path fuel a r) :
    ∃ inner, Cert (.theta fuel a) r inner ∧
      prior + before (TransactionAppendBudget.tree receipt) path + inner.count < 2^128 := by
  obtain ⟨inner,hc,hi⟩ := call_interval loc
  exact ⟨inner,hc,by unfold events at hb; omega⟩

#print axioms call_interval
#print axioms events_le_used
#print axioms transaction_call_interval
#print axioms history_lt
#print axioms bounded_call_interval
end Eip8282.Audit.Integrator.NestedJournalBudget
