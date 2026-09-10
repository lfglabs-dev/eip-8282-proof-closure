import Eip8282.Audit.Integrator.ReferenceSystemAction

/-! Source transaction metadata carried by literal input-computed actions.
Pure actions retain the entire storage view. Storage reads/writes change only
read/write overlays, so every SYSTEM action preserves the source created set.
No equality with pinned createdAccounts or warm/BAL sets is inferred. -/
namespace Eip8282.Audit.Integrator.ReferenceActionMetadata
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferencePureAction ReferenceSystemAction
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private theorem family_storage (kind : Kind) (p : Pure) (arg : Option (UInt256 × Nat))
    (v next : View) (h : familyAction kind p arg v = some next) :
    next.storage = v.storage := by
  unfold familyAction at h
  repeat' first | split at h | (cases h <;> rfl)

/-- Every successful partial pure action changes only PC and stack. -/
theorem pure_storage {kind : Kind} {instr : Instruction} {v next : View}
    (h : ReferencePureAction.action kind instr v = some next) :
    next.storage = v.storage := by
  unfold ReferencePureAction.action at h
  cases hc : classify instr.1 with
  | none => simp only [hc,Option.bind_none] at h; cases h
  | some p =>
    simp only [hc,Option.bind_some] at h
    exact family_storage kind p instr.2 v next h

/-- In particular pure instructions neither add nor discard BAL reads. -/
theorem pure_reads {kind : Kind} {instr : Instruction} {v next : View}
    (h : ReferencePureAction.action kind instr v = some next) :
    next.storage.reads = v.storage.reads := congrArg ReferenceStorageView.Tx.reads (pure_storage h)

/-- Created metadata comes from the initial source transaction and remains
unchanged along all literal SYSTEM actions, including SLOAD and SSTORE. -/
theorem created {kind : Kind} {parent : ReferenceStorageView.Parent}
    {instr : Instruction} {v next : View} (h : Action kind parent instr v next) :
    next.storage.created = v.storage.created := by
  cases h with
  | pure hp => exact congrArg ReferenceStorageView.Tx.created (pure_storage hp)
  | load => rfl
  | store => rfl
  | word => rfl
  | byte => rfl

#print axioms pure_storage
#print axioms pure_reads
#print axioms created
end Eip8282.Audit.Integrator.ReferenceActionMetadata
