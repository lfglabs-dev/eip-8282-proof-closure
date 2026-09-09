import Eip8282.Audit.Integrator.EventTree
import Mathlib.Data.List.DropRight
import Mathlib.Tactic

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
