import Eip8282.Audit.Integrator.ReferenceSourceReplayTrace

/-! Parent storage overlays may contain earlier writes from the same block.
Flattening their visible reads is observationally exact for protected actions
and their prices; the original-value reading is retained, not replaced by the
current transaction value. This algebra does not identify an actual block
state with a world: the source state producer must establish that relation. -/
namespace Eip8282.Audit.Integrator.ReferenceParentEquivalence
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings
open ReferenceRuntimeReadings ReferenceMeterPath
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Equality of all visible parent reads, including pending block writes. -/
def Equivalent (p q : Parent) : Prop := ∀ a k, parentRead p a k = parentRead q a k

def flatten (p : Parent) : Parent := {writes := fun _ _ => none, pre := parentRead p}

theorem flatten_equivalent (p : Parent) : Equivalent p (flatten p) := by
  intro a k
  rfl

theorem current_eq {p q : Parent} (same : Equivalent p q) (tx : Tx) (a : AccountAddress) (k : ByteArray) :
    current p tx a k = current q tx a k := by
  simp only [current,same a k]

theorem original_eq {p q : Parent} (same : Equivalent p q) (tx : Tx) (a : AccountAddress) (k : ByteArray) :
    original p tx a k = original q tx a k := by
  classical
  simp only [original,same a k]

theorem reading_eq {p q : Parent} (same : Equivalent p q) (v : View) (warm : Warm) :
    sourceReading p v warm = sourceReading q v warm := by
  classical
  simp only [sourceReading,current_eq same,original_eq same]

theorem action {p q : Parent} (same : Equivalent p q) {kind : Kind}
    {instr : Instruction} {v next : View}
    (actual : ReferenceRuntimeAction.Action kind p instr v next) :
    ReferenceRuntimeAction.Action kind q instr v next := by
  cases actual with
  | base h =>
    apply ReferenceRuntimeAction.Action.base
    cases h with
    | pure h => exact .pure h
    | @load v key rest shape =>
      have load : loadAction p v key rest = loadAction q v key rest := by
        simp only [loadAction,current_eq same]
      rw [load]
      exact .load shape
    | store permission shape => exact .store permission shape
    | word shape => exact .word shape
    | byte shape => exact .byte shape
  | copy shape => exact .copy shape
  | log permission shape => exact .log permission shape

theorem price {p q : Parent} (same : Equivalent p q) {v next : View} {warm : Warm}
    {op : Operation .EVM} {event : Event} (actual : Price p v warm next op event) :
    Price q v warm next op event := by
  simpa only [Price,reading_eq same] using actual

/-- The same finite source-shaped run, with precisely the same actions, views,
access sets and paid event list, survives parent-overlay normalization. -/
theorem run {p q : Parent} (same : Equivalent p q) {kind : Kind}
    {v finish : View} {warm finalWarm : Warm} {events : List Event}
    (actual : ReferenceSourceReplayTrace.Run kind p v warm finish finalWarm events) :
    ReferenceSourceReplayTrace.Run kind q v warm finish finalWarm events := by
  induction actual with
  | refl => exact .refl _ _
  | cons effect priced bounded tail ih =>
    exact .cons (action same effect) (price same priced) bounded ih

/-- Committing the same transaction preserves read equivalence, even when it
writes zero. This uses the source overlay precedence, not arithmetic addition. -/
theorem commit_equivalent {p q : Parent} (same : Equivalent p q) (tx : Tx) :
    Equivalent (commit p tx) (commit q tx) := by
  intro a k
  rw [commit_read,commit_read,current_eq same]

#print axioms flatten_equivalent
#print axioms current_eq
#print axioms original_eq
#print axioms reading_eq
#print axioms action
#print axioms price
#print axioms run
#print axioms commit_equivalent
end Eip8282.Audit.Integrator.ReferenceParentEquivalence
