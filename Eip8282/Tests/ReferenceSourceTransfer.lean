import Eip8282.Audit.Integrator.ReferenceSourceValueTransfer

/-! Synthetic source-journal mutations, not canonically reachable histories.
They kill unconditional self-transfer storage identity. No native_decide witnesses. -/
namespace Eip8282.Tests.ReferenceSourceTransfer
open EvmYul
open Eip8282.Audit.Integrator
open ReferenceSourceValueTransfer
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private def base : Parent Bool := ⟨fun _ => none,fun _ => none⟩
private def storageBase : ReferenceStorageView.Parent := ⟨fun _ _ => none,fun _ _ => ⟨0⟩⟩
private def emptySelf : Tx Bool :=
  {accounts := ⟨fun _ => some (some ⟨0,⟨1⟩,false⟩),∅⟩
   storage := ⟨fun _ _ => some ⟨42⟩,∅,∅⟩
   codeWrites := fun _ => none
   transient := fun _ _ => none}

theorem empty_self_clears (address : AccountAddress) (key : ByteArray) :
    ReferenceStorageView.current storageBase (enter false base emptySelf address address ⟨1⟩ true).2.storage address key = ⟨0⟩ := by
  simp [enter,move,modifyBalance,account,ReferenceAccountLookup.peek,ReferenceAccountLookup.tracked,
    writeAccount,eraseStorage,ReferenceStorageView.current,ReferenceStorageView.parentRead,emptySelf,storageBase,empty,
    UInt256.toNat,UInt256.ofNat,UInt256.size,Id.run,ReferenceAccountLookup.parentRead,base]
  split <;> simp

theorem rejects_unconditional_self_storage (address : AccountAddress) (key : ByteArray) :
    ¬ ReferenceStorageView.current storageBase (enter false base emptySelf address address ⟨1⟩ true).2.storage address key =
      ReferenceStorageView.current storageBase emptySelf.storage address key := by
  rw [empty_self_clears]
  change (⟨0⟩ : UInt256) ≠ ⟨42⟩
  decide +kernel

#print axioms empty_self_clears
#print axioms rejects_unconditional_self_storage
end Eip8282.Tests.ReferenceSourceTransfer
