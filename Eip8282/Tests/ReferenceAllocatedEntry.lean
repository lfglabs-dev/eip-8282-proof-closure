import Eip8282.Audit.Integrator.ReferenceAllocatedEntry

/-! Injected finite journals and represented call transactions. No signature,
canonical history or full validator certificate is claimed. Mutations separate
charged preparation continuations, duplicate access-list fees and actual dual
source pools from scalar replay gas. -/
namespace Eip8282.Tests.ReferenceAllocatedEntry
open EvmYul EvmYul.EVM Eip8282.Audit.Integrator
open ReferenceSourceValueTransfer
open ReferenceAdmissionExtraction.AdmissionExtractionTest
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private def sourceParent : Parent Bool := ⟨fun _ => none,fun _ => none⟩
private def journal : Tx Bool := ⟨⟨fun _ => none,∅⟩,⟨fun _ _ => none,∅,∅⟩,fun _ => none,fun _ _ => none⟩
private def errorCode : ReferenceCodeAccountPresence.CodeParent Bool Unit := ⟨fun _ => none,fun _ => .error ()⟩

/-- Positive-value absent recipients stop at the source state-charge branch;
this is not misreported as readiness, an opcode failure, or a free dispatch. -/
theorem missing_recipient_needs_charge :
    (ReferenceSourceDispatch.probe false sourceParent journal errorCode bob ⟨1⟩).1 = .stateChargeRequired := by
  have positive : 0 < (⟨1⟩ : UInt256).toNat := by decide +kernel
  simp [ReferenceSourceDispatch.probe,ReferenceSourceDispatch.Alive,ReferenceAccountLookup.peek,
    ReferenceAccountLookup.parentRead,sourceParent,journal,positive]

private def designation : ByteArray := ⟨#[0xef,0x01,0x00] ++ (List.replicate 20 (0 : UInt8)).toArray⟩
private def delegatedJournal : Tx Bool :=
  {journal with accounts := ⟨fun _ => some (some ⟨0,⟨0⟩,true⟩),∅⟩}
private def delegatedCode : ReferenceCodeAccountPresence.CodeParent Bool Unit := ⟨fun _ => some designation,fun _ => .error ()⟩

/-- The delegation branch is retained as a separate charged continuation. -/
theorem designation_needs_resolution :
    (ReferenceSourceDispatch.probe false sourceParent delegatedJournal delegatedCode bob ⟨0⟩).1 =
      .delegatedResolution designation := by
  have marker : ReferenceSourceDispatch.delegation designation = true := by decide +kernel
  simp [ReferenceSourceDispatch.probe,ReferenceSourceDispatch.fetchCode,ReferenceCodeAccountPresence.load,
    ReferenceCodeAccountPresence.getCode,ReferenceAccountLookup.peek,ReferenceAccountLookup.parentRead,
    ReferenceSourceDispatch.readTarget,ReferenceAccountLookup.tracked,delegatedJournal,journal,delegatedCode,marker,UInt256.toNat]

private def tx (slots : Array UInt256) (gas : UInt256) : RefundAccounting.Context :=
  context (.dynamic {
    nonce := ⟨0⟩, gasLimit := gas, recipient := some bob, value := ⟨0⟩,
    r := .empty,s := .empty,data := ⟨#[0,1]⟩,chainId := ⟨1⟩,accessList := [(bob,slots)],
    yParity := ⟨0⟩,maxFeePerGas := ⟨100⟩,maxPriorityFeePerGas := ⟨10⟩}) 0

/-- Deduplicating the charged access list would change intrinsic fees, although
initial warmth legitimately deduplicates these same storage pairs. -/
theorem duplicate_fees_retained :
    ReferenceAllocatedEntry.intrinsic (tx #[⟨1⟩,⟨1⟩] ⟨30000⟩) = 27296 ∧
    ReferenceAllocatedEntry.intrinsic (tx #[⟨1⟩] ⟨30000⟩) = 23248 := by
  decide +kernel

/-- Reservoir above the execution cap is real source state gas, not permission
to add that reservoir to executable potential or synthetic replay resources. -/
theorem distinct_pools :
    (ReferenceAllocatedEntry.meter (tx #[⟨1⟩,⟨1⟩] ⟨30000000⟩)).execution = 16749920 ∧
    (ReferenceAllocatedEntry.meter (tx #[⟨1⟩,⟨1⟩] ⟨30000000⟩)).reservoir = 13222784 ∧
    ReferenceExecutionPotential.potential (ReferenceAllocatedEntry.meter (tx #[⟨1⟩,⟨1⟩] ⟨30000000⟩)) = 16749920 := by
  decide +kernel

#print axioms missing_recipient_needs_charge
#print axioms designation_needs_resolution
#print axioms duplicate_fees_retained
#print axioms distinct_pools
end Eip8282.Tests.ReferenceAllocatedEntry
