import Eip8282.Audit.Integrator.ReferenceCheckedSystemBlock

/-! Local mutation witnesses for block incorporation and parent locality.
These are injected functional journals/builders, not canonical block histories.
The arbitrary-finite composition is proved in the production modules. -/
namespace Eip8282.Tests.ReferenceSystemBlock
open EvmYul EvmYul.EVM
open Eip8282.Audit.Integrator
open ReferenceStorageView ReferenceSystemBlockAccess
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private def owner : AccountAddress := ⟨1,by decide⟩
private def key : UInt256 := ⟨2⟩
private def parent : Parent := ⟨fun _ _ => none,fun _ _ => ⟨0⟩⟩
private def tx : Tx := ⟨fun _ _ => none,∅,∅⟩
private def builder : Builder := ⟨0,∅,fun _ _ => none⟩

/-- Moving merge before BAL comparison loses the actual nonzero write. -/
theorem merge_before_bal_mutant :
    ((update parent owner [(key.toByteArray,⟨7⟩)] builder).map (fun b => b.slots owner key)) =
      some (some [⟨0,⟨7⟩⟩]) ∧
    ((update (commit parent (write tx owner key.toByteArray ⟨7⟩)) owner
      [(key.toByteArray,⟨7⟩)] builder).map (fun b => b.slots owner key)) = some none := by
  classical
  constructor
  · simp [update,parentRead,parent,decode_word,add,builder,upsert]
  · have read : parentRead (commit parent (write tx owner key.toByteArray ⟨7⟩)) owner key.toByteArray = ⟨7⟩ := by
      rw [commit_read,write_read,if_pos ⟨rfl,rfl⟩]
    simp only [update,read]
    rfl

/-- The final write dictionary has one entry even after repeated accesses.
This witness must not be interpreted as one executed SSTORE or one append. -/
theorem final_dictionary_not_attempts :
    entries owner (write (write tx owner key.toByteArray ⟨7⟩) owner key.toByteArray ⟨0⟩) [key,key] =
      [(key.toByteArray,⟨0⟩)] := by
  classical
  simp [entries,write]

/-- Equal SYSTEM indices replace the first matching change and retain other
indices. Appending blindly or clearing the old change list is a mutant. -/
theorem same_index_replacement :
    upsert 0 ⟨9⟩ [⟨2,⟨3⟩⟩,⟨0,⟨4⟩⟩,⟨5,⟨6⟩⟩] =
      [⟨2,⟨3⟩⟩,⟨0,⟨9⟩⟩,⟨5,⟨6⟩⟩] := by rfl

/-- A same-address commit cannot use the foreign-parent transport theorem. -/
theorem same_owner_transport_rejected :
    ¬ ReferenceSystemBlockParent.AtOwner (commit parent (write tx owner key.toByteArray ⟨7⟩)) parent owner := by
  intro equal
  have slot := equal key.toByteArray
  rw [commit_read,write_read,if_pos ⟨rfl,rfl⟩] at slot
  have impossible : (⟨7⟩ : UInt256) ≠ ⟨0⟩ := by decide
  exact impossible slot

/-- Checked big-endian conversion rejects 2^256; a final modulo would accept
zero and is therefore not the source BAL conversion. -/
theorem key_conversion_is_checked :
    decodeKey ([1] ++ List.replicate 32 (0 : UInt8)).toByteArray = none := by
  decide +kernel

/-- Source FixedUnsigned.from_be_bytes checks length before decoding, even
when the represented integer would be zero and fit the word constructor. -/
theorem oversized_zero_rejected :
    decodeKey (List.replicate 33 (0 : UInt8)).toByteArray = none := by
  decide +kernel

#print axioms merge_before_bal_mutant
#print axioms final_dictionary_not_attempts
#print axioms same_index_replacement
#print axioms same_owner_transport_rejected
#print axioms key_conversion_is_checked
#print axioms oversized_zero_rejected
end Eip8282.Tests.ReferenceSystemBlock
