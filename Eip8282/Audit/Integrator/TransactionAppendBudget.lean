import Eip8282.Audit.Integrator.NestedAppendCount
import Eip8282.Audit.Integrator.ResourceBounds

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
