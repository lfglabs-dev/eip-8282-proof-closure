import Mathlib.Data.List.Nodup

/-!
# Structural addresses for local, child and continuation events

This tree carries no evaluator state, execution certificate or gas claim.
Occurrences are generated structurally: the local event has address [], child
addresses start with false, and continuation addresses start with true.
Actual execution extraction and aggregate charging remain separate obligations.
-/
namespace Eip8282.Audit.Integrator

inductive EventTree where
  | done
  | step (marked : Bool) (child next : EventTree)
  deriving DecidableEq

namespace EventTree
set_option autoImplicit false

abbrev Address := List Bool

def count : EventTree → Nat
  | .done => 0
  | .step marked child next => (if marked then 1 else 0) + count child + count next

def extend (side : Bool) (address : Address) : Address := side :: address

def root (marked : Bool) : List Address := if marked then [[]] else []

def occurrences : EventTree → List Address
  | .done => []
  | .step marked child next => root marked ++
      (occurrences child).map (extend false) ++ (occurrences next).map (extend true)

theorem prefix_injective (side : Bool) : Function.Injective (extend side) := by
  intro a b h
  exact (List.cons.inj h).2

/-- A fixed frame path also preserves distinct local occurrence addresses. -/
theorem path_prefix_injective (path : Address) : Function.Injective (fun a : Address => path ++ a) := by
  intro a b h
  exact List.append_cancel_left h

theorem prefix_ne_root (side : Bool) (address : Address) : extend side address ≠ [] := by
  intro h
  cases h

theorem child_ne_next (a b : Address) : extend false a ≠ extend true b := by
  intro h
  cases h

/-- Child and continuation occurrences are disjoint without any hypothesis
on the addresses inside either subtree. -/
theorem prefix_disjoint (children continuations : List Address) :
    List.Disjoint (children.map (extend false)) (continuations.map (extend true)) := by
  apply List.disjoint_left.mpr
  intro address hc hn
  obtain ⟨a,_,ha⟩ := List.mem_map.mp hc
  obtain ⟨b,_,hb⟩ := List.mem_map.mp hn
  exact child_ne_next a b (ha.trans hb.symm)

theorem root_prefix_disjoint (marked side : Bool) (addresses : List Address) :
    List.Disjoint (root marked) (addresses.map (extend side)) := by
  apply List.disjoint_left.mpr
  intro address hr hp
  obtain ⟨a,_,ha⟩ := List.mem_map.mp hp
  have he : address = [] := by
    cases marked <;> simp_all [root]
  exact prefix_ne_root side a (ha.trans he)

/-- Membership identifies exactly one of local root, child or continuation. -/
theorem mem_step_iff (marked : Bool) (child next : EventTree) (address : Address) :
    address ∈ occurrences (.step marked child next) ↔
      (marked = true ∧ address = []) ∨
      (∃ a ∈ occurrences child, extend false a = address) ∨
      (∃ a ∈ occurrences next, extend true a = address) := by
  cases marked <;> simp [occurrences, root, List.mem_map]

theorem root_mem_iff (marked : Bool) (child next : EventTree) :
    [] ∈ occurrences (.step marked child next) ↔ marked = true := by
  rw [mem_step_iff]
  simp [extend]

theorem child_mem_iff (marked : Bool) (child next : EventTree) (address : Address) :
    extend false address ∈ occurrences (.step marked child next) ↔ address ∈ occurrences child := by
  rw [mem_step_iff]
  simp [extend]

theorem next_mem_iff (marked : Bool) (child next : EventTree) (address : Address) :
    extend true address ∈ occurrences (.step marked child next) ↔ address ∈ occurrences next := by
  rw [mem_step_iff]
  simp [extend]

theorem occurrences_length (tree : EventTree) : tree.occurrences.length = tree.count := by
  induction tree with
  | done => rfl
  | step marked child next hc hn =>
      cases marked <;> simp [occurrences, root, count, hc, hn, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- IDs are derived from tree position, so repeated subtrees or equal event
payloads cannot duplicate an occurrence address. -/
theorem occurrences_nodup (tree : EventTree) : tree.occurrences.Nodup := by
  induction tree with
  | done => exact List.nodup_nil
  | step marked child next hc hn =>
      have hchildren := List.Nodup.map (prefix_injective false) hc
      have hnext := List.Nodup.map (prefix_injective true) hn
      have ht := hchildren.append hnext (prefix_disjoint _ _)
      cases marked with
      | false => simpa only [occurrences, root, Bool.false_eq_true, ↓reduceIte, List.nil_append] using ht
      | true =>
          change ([] :: (child.occurrences.map (extend false) ++ next.occurrences.map (extend true))).Nodup
          apply List.nodup_cons.mpr
          exact ⟨by simp [extend], ht⟩

#print axioms prefix_injective
#print axioms path_prefix_injective
#print axioms prefix_disjoint
#print axioms root_prefix_disjoint
#print axioms mem_step_iff
#print axioms root_mem_iff
#print axioms child_mem_iff
#print axioms next_mem_iff
#print axioms occurrences_length
#print axioms occurrences_nodup
end EventTree
end Eip8282.Audit.Integrator
