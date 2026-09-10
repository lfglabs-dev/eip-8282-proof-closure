import Eip8282.Audit.Integrator.ReferenceSourcePrepayment

/-! Injected finite source-journal fixtures, not canonical reachability.
They detect reversing nonce/fee update order and incorrectly erasing partial
nonce effects on a fee underflow before the EVM frame is built. -/
namespace Eip8282.Tests.ReferencePrepayment
open EvmYul
open Eip8282.Audit.Integrator
open ReferenceSourceValueTransfer ReferenceSourcePrepayment
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private def base : Parent Bool := ⟨fun _ => none,fun _ => none⟩
private def storageBase : ReferenceStorageView.Parent := ⟨fun _ _ => none,fun _ _ => ⟨0⟩⟩
private noncomputable def before (sender : AccountAddress) (key : ByteArray) : Tx Bool :=
  {accounts := ⟨fun a => if a = sender then some (some ⟨0,⟨1⟩,false⟩) else none,∅⟩
   storage := ⟨fun a k => if a = sender ∧ k = key then some ⟨42⟩ else none,∅,∅⟩
   codeWrites := fun _ => none
   transient := fun _ _ => none}

/-- Actual nonce-first prepayment preserves the sender's storage even at zero
remaining balance; this is the observable killed by reversing the operations. -/
theorem nonce_first_preserves (sender : AccountAddress) (key : ByteArray) :
    ReferenceStorageView.current storageBase (pay false base (before sender key) sender 1 0).2.storage sender key = ⟨42⟩ := by
  rw [(ReferenceSourcePrepayment.fields false base (before sender key) sender 1 0).1]
  simp [ReferenceStorageView.current,before]

/-- The order mutation first clears an empty nonce-zero sender at zero balance. -/
theorem reversed_order_loses_storage (sender : AccountAddress) (key : ByteArray) :
    ReferenceStorageView.current storageBase
      (increment false base (modifyBalance false base (before sender key) sender ⟨0⟩) sender).storage sender key = ⟨0⟩ := by
  rw [increment_form]
  simp [writeAccount,modifyBalance,account,ReferenceAccountLookup.peek,ReferenceAccountLookup.parentRead,
    ReferenceAccountLookup.tracked,eraseStorage,ReferenceStorageView.current,ReferenceStorageView.parentRead,
    before,base,storageBase,empty]

theorem rejects_reversed_order (sender : AccountAddress) (key : ByteArray) :
    (pay false base (before sender key) sender 1 0).2.storage ≠
      (increment false base (modifyBalance false base (before sender key) sender ⟨0⟩) sender).storage := by
  intro wrong
  have correct := nonce_first_preserves sender key
  rw [wrong,reversed_order_loses_storage] at correct
  exact (by decide : (⟨0⟩ : UInt256) ≠ ⟨42⟩) correct

/-- Fee underflow is after increment_nonce, outside the process_call fault
catch. This is not claimed reachable under the successful admission domain. -/
theorem underflow_keeps_nonce (sender : AccountAddress) (key : ByteArray) :
    (pay false base (before sender key) sender 2 0).1 = .error .executionFeeUnderflow ∧
    (account false base (pay false base (before sender key) sender 2 0).2 sender).nonce = 1 := by
  simp [pay,increment_form,writeAccount,account,ReferenceAccountLookup.peek,ReferenceAccountLookup.parentRead,
    ReferenceAccountLookup.tracked,before,base,empty,UInt256.toNat,UInt256.size]

#print axioms nonce_first_preserves
#print axioms reversed_order_loses_storage
#print axioms rejects_reversed_order
#print axioms underflow_keeps_nonce
end Eip8282.Tests.ReferencePrepayment
