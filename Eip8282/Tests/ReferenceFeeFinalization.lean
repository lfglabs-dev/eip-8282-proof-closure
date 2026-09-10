import Eip8282.Audit.Integrator.ReferenceSourceFeeDisbursement

/-! Literal source-journal edge cases. Overflow/empty-storage fixtures are
injected states, not claims about canonical histories. They kill skipping zero
credits, losing alias accumulation, and erasing completed first-credit effects.
The general composed theorem derives guards independently from history. -/
namespace Eip8282.Tests.ReferenceFeeFinalization
open EvmYul Eip8282.Audit.Integrator
open ReferenceSourceValueTransfer ReferenceSourceFeeDisbursement
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private def parent : Parent Bool := ⟨fun _ => none,fun _ => none⟩
private def storageParent : ReferenceStorageView.Parent := ⟨fun _ _ => none,fun _ _ => ⟨0⟩⟩
private def blank : Tx Bool := ⟨⟨fun _ => none,∅⟩,⟨fun _ _ => some ⟨42⟩,∅,∅⟩,fun _ => none,fun _ _ => none⟩
private noncomputable def seed (a : AccountAddress) (balance : UInt256) : Tx Bool :=
  writeAccount blank a (some ⟨0,balance,false⟩)

theorem alias_accumulates (a : AccountAddress) :
    (account false parent (run false parent (seed a ⟨5⟩) a a 4 1 ⟨3,2,0,0⟩).2 a).balance = ⟨22⟩ := by
  simp [run,ReferenceSourceFeeCredit.credit,modifyBalance,account,ReferenceAccountLookup.peek,
    ReferenceAccountLookup.tracked,writeAccount,seed,blank,parent,empty,UInt256.toNat,UInt256.ofNat,UInt256.size,Id.run,ReferenceAccountLookup.parentRead]

theorem second_overflow_retains_refund (a : AccountAddress) :
    (run false parent (seed a (UInt256.ofNat (UInt256.size-2))) a a 1 0 ⟨2,1,0,0⟩).1 = .error .tipCreditOverflow ∧
    (account false parent (run false parent (seed a (UInt256.ofNat (UInt256.size-2))) a a 1 0 ⟨2,1,0,0⟩).2 a).balance.toNat = UInt256.size-1 := by
  simp [run,ReferenceSourceFeeCredit.credit,modifyBalance,account,ReferenceAccountLookup.peek,
    ReferenceAccountLookup.tracked,writeAccount,seed,blank,parent,empty,UInt256.toNat,UInt256.ofNat,UInt256.size,Id.run,ReferenceAccountLookup.parentRead]

theorem tip_conversion_after_refund (a : AccountAddress) :
    (run false parent (seed a ⟨0⟩) a a 1 0 ⟨UInt256.size,1,0,0⟩).1 = .error .tipAmountOverflow ∧
    (account false parent (run false parent (seed a ⟨0⟩) a a 1 0 ⟨UInt256.size,1,0,0⟩).2 a).balance = ⟨1⟩ := by
  simp [run,ReferenceSourceFeeCredit.credit,modifyBalance,account,ReferenceAccountLookup.peek,
    ReferenceAccountLookup.tracked,writeAccount,seed,blank,parent,empty,UInt256.toNat,UInt256.ofNat,UInt256.size,Id.run,ReferenceAccountLookup.parentRead]
  split
  · rename_i h
    have impossible := congrArg Fin.val h
    norm_num at impossible
  · simp
    decide +kernel

theorem zero_credit_cleans_empty (a : AccountAddress) (slot : ByteArray) :
    ReferenceStorageView.current storageParent (run false parent (seed a ⟨0⟩) a a 0 0 ⟨0,0,0,0⟩).2.storage a slot = ⟨0⟩ ∧
    ReferenceStorageView.current storageParent (seed a ⟨0⟩).storage a slot = ⟨42⟩ := by
  simp [run,ReferenceSourceFeeCredit.credit,modifyBalance,account,ReferenceAccountLookup.peek,
    ReferenceAccountLookup.parentRead,ReferenceAccountLookup.tracked,writeAccount,eraseStorage,seed,blank,parent,empty,
    ReferenceStorageView.current,ReferenceStorageView.parentRead,storageParent,UInt256.toNat,UInt256.ofNat,UInt256.size,Id.run,ReferenceAccountLookup.parentRead]

#print axioms alias_accumulates
#print axioms second_overflow_retains_refund
#print axioms tip_conversion_after_refund
#print axioms zero_credit_cleans_empty
end Eip8282.Tests.ReferenceFeeFinalization
