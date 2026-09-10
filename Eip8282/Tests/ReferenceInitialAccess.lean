import Eip8282.Audit.Integrator.ReferenceInitialAccess
import Eip8282.Audit.Integrator.ReferenceAdmissionExtraction

/-! Injected finite access list and scanner fixtures, not canonical history.
Detect losing a declared warm slot, warming an undeclared slot, and treating
PUSH immediate bytes as jump destinations. -/
namespace Eip8282.Tests.ReferenceInitialAccess
open EvmYul EvmYul.EVM Eip8282.Audit.Integrator
open ReferenceAdmissionExtraction.AdmissionExtractionTest
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private def tx : RefundAccounting.Context :=
  context (dynamic ⟨100⟩ ⟨10⟩ [(bob,#[⟨1⟩,⟨1⟩,⟨2⟩])]) 0

theorem listed_warm : (bob,(⟨1⟩ : UInt256).toByteArray) ∈ ReferenceInitialAccess.warm tx := by
  rw [ReferenceInitialAccess.warm,ReferenceInitialAccess.warm_member]
  change (bob,(⟨1⟩ : UInt256)) ∈ [(bob,⟨1⟩),(bob,⟨1⟩),(bob,⟨2⟩)]
  simp

theorem unlisted_cold : (bob,(⟨3⟩ : UInt256).toByteArray) ∉ ReferenceInitialAccess.warm tx := by
  rw [ReferenceInitialAccess.warm,ReferenceInitialAccess.warm_member]
  change (bob,(⟨3⟩ : UInt256)) ∉ [(bob,⟨1⟩),(bob,⟨1⟩),(bob,⟨2⟩)]
  simp only [List.mem_cons,List.not_mem_nil,Prod.mk.injEq,true_and,UInt256.mk.injEq]
  decide +kernel

theorem rejects_empty_warm : ReferenceInitialAccess.warm tx ≠ ∅ := by
  intro h
  have member := listed_warm
  rw [h] at member
  exact member

theorem skips_push_immediate :
    ReferenceInitialAccess.destinations ⟨#[0x60,0x5b,0x5b]⟩ = [2] ∧
    1 ∉ ReferenceInitialAccess.destinations ⟨#[0x60,0x5b,0x5b]⟩ := by
  decide +kernel

#print axioms listed_warm
#print axioms unlisted_cold
#print axioms rejects_empty_warm
#print axioms skips_push_immediate
end Eip8282.Tests.ReferenceInitialAccess
