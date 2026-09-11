import Eip8282.Audit.Integrator.NestedEventExtract
import Eip8282.Audit.Integrator.NestedEventDebit

/-!
# Complete extraction with derived aggregate gas

No supplied call tree, execution-success hypothesis or recursive gas hypothesis
is required. The result applies to the actual outcome at every finite evaluator
fuel. Event count is executed marked LOG0 occurrences, including those whose
journals are later rolled back; it is not a persistent-record count.
-/
namespace Eip8282.Audit.Integrator.NestedEvents
set_option autoImplicit false

/-- Unique actual tree and its aggregate budget, with structural occurrence
uniqueness. Step requests additionally pay their own local instruction marker. -/
theorem extracted_bound (q : Request) :
    ∃ tree, Cert q q.eval tree ∧ tree.occurrences.Nodup ∧
      q.residual q.eval + extra q q.eval + 919*tree.count ≤ q.gas ∧
      ∀ other, Cert q q.eval other → other = tree := by
  obtain ⟨tree,h⟩ := extract q
  exact ⟨tree,h,EventTree.occurrences_nodup tree,gas_bound h,
    fun _ ho => deterministic ho h⟩

/-- Input gas minus the accounting residual bounds every marked occurrence.
For an Except error the residual is zero: this gives an input-budget bound,
not a claim about actual transaction gas charged. Completed wrapper outcomes
can be connected separately to the transaction's pre-refund gas debit. No
committed-effect conclusion follows from this executed-occurrence metric. -/
theorem extracted_gross_bound (q : Request) :
    ∃ tree, Cert q q.eval tree ∧
      919*tree.occurrences.length ≤ q.gas - q.residual q.eval := by
  obtain ⟨tree,h,_,hb,_⟩ := extracted_bound q
  refine ⟨tree,h,?_⟩
  rw [EventTree.occurrences_length]
  omega

#print axioms extracted_bound
#print axioms extracted_gross_bound
end Eip8282.Audit.Integrator.NestedEvents
