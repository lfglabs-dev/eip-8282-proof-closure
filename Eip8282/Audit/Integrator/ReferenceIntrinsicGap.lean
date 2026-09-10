import Eip8282.Audit.Integrator.ReferenceCalldataAdmission

/-! A local arithmetic/representation witness, not an admitted signed Ethereum
transaction. The source calldata-floor gates do not imply the pinned old
intrinsic-gas gate. Signatures are deliberately empty and no world/history or
execution outcome is claimed. The full source validator remains separate. -/
namespace Eip8282.Audit.Integrator.ReferenceIntrinsicGap
open EvmYul EvmYul.EVM
open ReferenceCalldataAdmission
set_option autoImplicit false

def sample : Transaction := .legacy
  { nonce := ⟨0⟩, gasLimit := ⟨12000⟩, recipient := some ⟨1,by decide⟩,
    value := ⟨0⟩, r := ByteArray.empty, s := ByteArray.empty,
    data := ByteArray.empty, gasPrice := ⟨0⟩, w := ⟨27⟩ }

/-- Empty data, zero access tokens, and zero recipient cost model the source
empty self-transfer cost branch. This checks only the two floor comparisons. -/
theorem source_floor_gates :
    floor sample.base.data.size 0 0 = 12000 ∧ Gate sample.base.data.size 0 0 ∧
      floor sample.base.data.size 0 0 ≤ sample.base.gasLimit.toNat := by
  unfold Gate floor
  decide +kernel

theorem old_intrinsic : intrinsicGas sample = 21000 := by decide +kernel

/-- A proof adapter may use the source size bound directly; substituting an
old intrinsic admission assumption from these source floor gates is invalid. -/
theorem no_floor_implication :
    ¬ (Gate sample.base.data.size 0 0 ∧
        floor sample.base.data.size 0 0 ≤ sample.base.gasLimit.toNat →
      intrinsicGas sample ≤ sample.base.gasLimit.toNat) := by
  unfold Gate floor
  decide +kernel

#print axioms source_floor_gates
#print axioms old_intrinsic
#print axioms no_floor_implication
end Eip8282.Audit.Integrator.ReferenceIntrinsicGap
