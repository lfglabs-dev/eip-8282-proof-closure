import Eip8282.Audit.Integrator.EventTree
import Eip8282.Audit.Integrator.NestedEventDebit
import Eip8282.Audit.Integrator.NestedEventExtract
import Mathlib.Data.List.DropRight
import Mathlib.Tactic

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## NestedEventBounds -/

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

end

section

/-! ## NestedFrameOwnership -/

/-!
# Separation of frame-owned occurrence addresses

An execution frame starts either at the root or immediately after a child edge
(`false`). Its local instruction positions extend that path only with
continuation edges (`true`). Removing trailing continuation edges recovers the
unique owning frame. This is the structural separation needed by the nested
append injection; extraction must still establish this grammar for actual Ξ
invocations. These lemmas do not assume or establish protocol reachability.
-/
namespace Eip8282.Audit.Integrator.NestedFrameOwnership
set_option autoImplicit false

abbrev Address := EventTree.Address

def FrameRoot (path : Address) : Prop :=
  path = [] ∨ ∃ parent, path = parent ++ [false]

def owned (path : Address) (instruction : Nat) : Address :=
  path ++ List.replicate instruction true

def owner (event : Address) : Address := List.rdropWhile id event

theorem root_frame : FrameRoot [] := Or.inl rfl

theorem child_frame (path : Address) (instruction : Nat) :
    FrameRoot (owned path instruction ++ [false]) :=
  Or.inr ⟨owned path instruction, rfl⟩

theorem owner_continuations (path : Address) (instruction : Nat) :
    owner (owned path instruction) = owner path := by
  induction instruction with
  | zero => simp [owned]
  | succ n ih =>
      change List.rdropWhile id (path ++ List.replicate (n+1) true) = _
      rw [List.replicate_succ', ← List.append_assoc]
      rw [List.rdropWhile_concat]
      exact ih

theorem owner_root (path : Address) (h : FrameRoot path) : owner path = path := by
  rcases h with rfl | ⟨parent, rfl⟩
  · simp [owner]
  · simp [owner]

theorem owner_owned (path : Address) (instruction : Nat) (h : FrameRoot path) :
    owner (owned path instruction) = path :=
  (owner_continuations path instruction).trans (owner_root path h)

/-- Different frame roots cannot own the same event, even when one frame is
an ancestor of the other. Ordinary fixed-prefix injectivity is insufficient
for this conclusion; both root grammars are consumed here. -/
theorem owned_eq_roots {p q : Address} {i j : Nat}
    (hp : FrameRoot p) (hq : FrameRoot q) (he : owned p i = owned q j) : p = q := by
  have h := congrArg owner he
  simpa only [owner_owned p i hp, owner_owned q j hq] using h

theorem owned_distinct {p q : Address} {i j : Nat}
    (hp : FrameRoot p) (hq : FrameRoot q) (different : p ≠ q) :
    owned p i ≠ owned q j := fun h => different (owned_eq_roots hp hq h)

theorem owned_injective {p q : Address} {i j : Nat}
    (hp : FrameRoot p) (hq : FrameRoot q) (he : owned p i = owned q j) :
    p = q ∧ i = j := by
  have hpq := owned_eq_roots hp hq he
  subst q
  have hlen := congrArg List.length he
  simp only [owned, List.length_append, List.length_replicate] at hlen
  exact ⟨rfl, Nat.add_left_cancel hlen⟩

#print axioms root_frame
#print axioms child_frame
#print axioms owner_continuations
#print axioms owner_owned
#print axioms owned_eq_roots
#print axioms owned_distinct
#print axioms owned_injective
end Eip8282.Audit.Integrator.NestedFrameOwnership

end
