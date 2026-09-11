import Eip8282.Audit.Integrator.ReferenceCheckedSystemForward

/-! Derive the post-stack bound consumed by paid SYSTEM handler acceptance
from the actual old Z delta/alpha guards and the same source action. No output
stack bound is left as a public execution assumption. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemStackBound
open EvmYul EvmYul.EVM ReferenceRuntimeView ReferenceCheckedDispatch
open Eip8282.Audit.Model (Kind)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem stack_cases (s : List UInt256) :
    s = [] ∨ (∃ a, s = [a]) ∨ (∃ a b, s = [a,b]) ∨
    (∃ a b c, s = [a,b,c]) ∨ (∃ a b c d, s = [a,b,c,d]) ∨
    (∃ a b c d e rest, s = a::b::c::d::e::rest) := by
  cases s with
  | nil => exact Or.inl rfl
  | cons a s =>
    right
    cases s with
    | nil => exact Or.inl ⟨a,rfl⟩
    | cons b s =>
      right
      cases s with
      | nil => exact Or.inl ⟨a,b,rfl⟩
      | cons c s =>
        right
        cases s with
        | nil => exact Or.inl ⟨a,b,c,rfl⟩
        | cons d s =>
          right
          cases s with
          | nil => exact Or.inl ⟨a,b,c,d,rfl⟩
          | cons e rest => exact Or.inr ⟨a,b,c,d,e,rest,rfl⟩

theorem handler {kind : Kind} {parent : ReferenceStorageView.Parent} {h : Handler}
    {arg : Option (UInt256 × Nat)} {v next : View}
    (action : ReferenceSystemAction.Action kind parent (opcode h,arg) v next)
    (lower : (δ (opcode h)).getD 0 ≤ v.stack.length)
    (bound : v.stack.length - (δ (opcode h)).getD 0 + (α (opcode h)).getD 0 ≤ 1024) :
    next.stack.length ≤ 1024 := by
  rcases stack_cases v.stack with shape | ⟨a,shape⟩ | ⟨a,b,shape⟩ | ⟨a,b,c,shape⟩ |
    ⟨a,b,c,d,shape⟩ | ⟨a,b,c,d,e,rest,shape⟩
  all_goals cases h
  all_goals try (rename_i selected; cases selected)
  all_goals simp only [opcode,ReferenceWordOps.opcode,ReferenceCheckedEnvironmentStep.opcode,
    ReferenceCheckedStackControlStep.opcode,ReferenceCheckedStackControlStep.family,ReferencePureAction.opcode,
    ReferenceCheckedMemoryStore.opcode,ReferenceCheckedCopyLogStep.opcode,ReferenceCheckedTerminalStep.opcode,
    Bool.false_eq_true,if_false,if_true,δ,α,Option.getD_some,shape,List.length_cons,List.length_nil] at lower bound action
  all_goals cases action
  all_goals try (rename_i pure; simp only [ReferencePureAction.action,ReferencePureAction.classify,
    Option.bind_some,Option.bind_none,ReferencePureAction.familyAction,ReferenceStackOps.dupDepth,
    ReferenceStackOps.swapDepth,shape] at pure)
  all_goals repeat (first | contradiction | split at pure)
  all_goals try (by_cases hj : a.toNat ∈ ReferenceDecodeSites.referenceJumps (ReferenceRuntimeSites.reference kind) <;> simp only [hj,if_pos,if_neg] at pure)
  all_goals try contradiction
  all_goals try (rcases pure with ⟨valid,pure⟩)
  all_goals try cases pure
  all_goals simp_all [ReferencePureAction.advance,stackAction,loadAction,storeAction,memoryAction,
    List.length_take,List.length_drop]
  all_goals omega

#print axioms handler
end Eip8282.Audit.Integrator.ReferenceSystemStackBound
