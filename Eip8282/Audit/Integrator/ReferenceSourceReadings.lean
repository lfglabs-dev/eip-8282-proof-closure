import Eip8282.Audit.Integrator.Topics.ReferenceRuntime3
import Eip8282.Audit.Integrator.SystemMeterResources

/-! Constructive source storage readings for the local SYSTEM adapter.
EL 0cc100eb: instructions/storage.py 37-170, state_tracker.py 244-302.
The source warm set is distinct from the rollback-persistent BAL read set.
Original values use source parent/created metadata, never an assumed equality
with pinned sigma0. Initial access-set binding and its actual-step preservation
remain separate consumers; no source execution or gas equality is asserted. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceReadings
open EvmYul EvmYul.EVM
open ReferenceRuntimeView
open Eip8282.Audit.SymExec
open Eip8282.Audit.EntryReach
set_option autoImplicit false
set_option maxHeartbeats 1000000

abbrev Warm := Set (AccountAddress × ByteArray)

def WarmRelated (w : Warm) (pre : EVM.State) : Prop :=
  ∀ (a : AccountAddress) (k : UInt256),
    ((a,k.toByteArray) ∈ w ↔ pre.substate.accessedStorageKeys.contains (a,k) = true)

noncomputable def sourceReading (parent : ReferenceStorageView.Parent)
    (v : View) (w : Warm) : SystemMeterResources.Reading := by
  classical
  exact {
    warm := decide ((v.env.codeOwner,v.stack[0]!.toByteArray) ∈ w)
    original := ReferenceStorageView.original parent v.storage v.env.codeOwner v.stack[0]!.toByteArray
    current := ReferenceStorageView.current parent v.storage v.env.codeOwner v.stack[0]!.toByteArray
    new := v.stack[1]! }

/-- A closed Inputs function. The fixed created set belongs to the source
transaction; it is not the pinned evaluator's createdAccounts field. -/
noncomputable def inputs (parent : ReferenceStorageView.Parent)
    (created : Set AccountAddress) : SystemMeterResources.Inputs := by
  classical
  exact fun pre => {
    warm := pre.substate.accessedStorageKeys.contains (pre.executionEnv.codeOwner,pre.stack[0]!)
    original := if pre.executionEnv.codeOwner ∈ created then ⟨0⟩ else
      ReferenceStorageView.parentRead parent pre.executionEnv.codeOwner pre.stack[0]!.toByteArray
    current := slotW pre.toState pre.stack[0]!
    new := pre.stack[1]! }

/-- Warm insertion happens on successful SLOAD/SSTORE, independently of BAL
read tracking. The actual access-set preservation theorem is a separate step. -/
def warmAfter (op : Operation .EVM) (v : View) (w : Warm) : Warm :=
  match op with
  | .SLOAD | .SSTORE => insert (v.env.codeOwner,v.stack[0]!.toByteArray) w
  | _ => w

private theorem warm_bool {w : Warm} {pre : EVM.State} (h : WarmRelated w pre)
    (a : AccountAddress) (k : UInt256) :
    pre.substate.accessedStorageKeys.contains (a,k) =
      @decide ((a,k.toByteArray) ∈ w) (Classical.propDecidable _) := by
  have hh := h a k
  cases hc : pre.substate.accessedStorageKeys.contains (a,k) <;> simp_all

/-- Every reading is derived from the input relation. No charge, refund,
original-world equality or desired output reading is a premise. -/
theorem reading_eq {parent : ReferenceStorageView.Parent} {v : View}
    {pre : EVM.State} {w : Warm} {created : Set AccountAddress}
    (related : Related parent v pre) (warm : WarmRelated w pre)
    (created_eq : v.storage.created = created) :
    inputs parent created pre = sourceReading parent v w := by
  classical
  unfold inputs sourceReading
  rw [related.env,related.stack]
  congr 1
  · exact warm_bool warm _ _
  · simp only [ReferenceStorageView.original,created_eq]
  · exact (related.storage _).symm

theorem original_readTracked (parent : ReferenceStorageView.Parent)
    (tx : ReferenceStorageView.Tx) (a b : AccountAddress) (key query : ByteArray) :
    ReferenceStorageView.original parent (ReferenceStorageView.readTracked tx a key) b query =
      ReferenceStorageView.original parent tx b query := rfl

theorem original_write (parent : ReferenceStorageView.Parent)
    (tx : ReferenceStorageView.Tx) (a b : AccountAddress) (key query : ByteArray) (value : UInt256) :
    ReferenceStorageView.original parent (ReferenceStorageView.write tx a key value) b query =
      ReferenceStorageView.original parent tx b query := rfl

#print axioms reading_eq
#print axioms original_readTracked
#print axioms original_write
end Eip8282.Audit.Integrator.ReferenceSourceReadings
