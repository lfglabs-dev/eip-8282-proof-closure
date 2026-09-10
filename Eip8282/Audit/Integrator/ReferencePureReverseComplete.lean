import Eip8282.Audit.Integrator.ReferencePureReverseBinary
import Eip8282.Audit.Integrator.ReferencePureReverseEnvironment
import Eip8282.Audit.Integrator.ReferencePureReverseControl

/-! Compose the pure inverse families without assuming a second execution.
The successful action itself supplies classification; actual decode binds its
instruction. Guarded admission and source extraction are separate consumers. -/
namespace Eip8282.Audit.Integrator.ReferencePureReverseComplete
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferencePureAction
set_option autoImplicit false

theorem family {kind : Kind} {parent : ReferenceStorageView.Parent} {v next : View}
    {pre : EVM.State} {arg : Option (UInt256 × Nat)}
    (p : Pure) (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (opcode p,arg))
    (effect : action kind (opcode p,arg) v = some next) :
    ∃ post, EvmYul.step (opcode p) arg pre = .ok post ∧ Related parent next post := by
  cases p
  all_goals first
    | exact ReferencePureReverseBinary.raw _ related site decoded effect
    | exact ReferencePureReverseEnvironment.raw _ (by trivial) related site decoded effect
    | exact ReferencePureReverseControl.raw _ (by trivial) related site decoded effect

theorem raw {kind : Kind} {parent : ReferenceStorageView.Parent} {v next : View}
    {pre : EVM.State} (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (effect : action kind (decodeAt pre) v = some next) :
    ∃ post, EvmYul.step (decodeAt pre).1 (decodeAt pre).2 pre = .ok post ∧
      Related parent next post := by
  cases classified : classify (decodeAt pre).1 with
  | none => simp [action,classified] at effect
  | some p =>
    have op := classify_sound classified
    have decoded : decodeAt pre = (opcode p,(decodeAt pre).2) := Prod.ext op.symm rfl
    obtain ⟨post,step,relatedPost⟩ := family p related site decoded (by simpa only [op] using effect)
    exact ⟨post,by simpa only [op] using step,relatedPost⟩

#print axioms family
#print axioms raw
end Eip8282.Audit.Integrator.ReferencePureReverseComplete
