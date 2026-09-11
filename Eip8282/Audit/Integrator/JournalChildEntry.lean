import Eip8282.Audit.Integrator.NestedEventArgs
import Eip8282.Audit.Integrator.CodeStorageFrame

/-! Exact selected-child input journals. CALL-family input world/set are the
literal pre-Z projections. CREATE's nonce update is framed away from its owner;
no funding or child completion premise substitutes for these execution inputs. -/
namespace Eip8282.Audit.Integrator.JournalChildEntry
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open NestedEvents CodeStorageFrame
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem selected_kind {n : Nat} {a : StepArgs} {q : Request}
    (hc : StepChild n a (some q)) :
    (∃ f b, q = .theta f b) ∨ (∃ f b, q = .lambda f b) := by
  unfold StepChild selectedChild at hc
  split at hc
  · cases hc
  · split at hc
    all_goals repeat first | split at hc | contradiction
    all_goals simp only [Option.some.injEq,reduceCtorEq] at hc
    all_goals subst q
    all_goals first | exact Or.inl ⟨_,_,rfl⟩ | exact Or.inr ⟨_,_,rfl⟩

theorem selected_theta_input {n f : Nat} {a : StepArgs} {b : ThetaArgs}
    (hc : StepChild n a (some (.theta f b))) :
    b.world = a.pre.accountMap ∧
      b.substate.selfDestructSet = a.pre.substate.selfDestructSet := by
  have hw : a.mid.accountMap = a.pre.accountMap := by rw [Z_ok_state a.guard]; rfl
  have hs : a.mid.substate.selfDestructSet = a.pre.substate.selfDestructSet := by
    rw [Z_ok_state a.guard]; rfl
  unfold StepChild selectedChild at hc
  split at hc
  · cases hc
  · split at hc
    all_goals repeat first | split at hc | contradiction
    all_goals simp only [Option.some.injEq,Request.theta.injEq,reduceCtorEq] at hc
    all_goals obtain ⟨_,rfl⟩ := hc
    all_goals exact ⟨hw,hs⟩

private theorem insert_away (world : World) (owner protectedAddr : AccountAddress)
    (account : Account .EVM) (hne : owner ≠ protectedAddr) :
    Frame world (world.insert owner account) protectedAddr := by
  have hl : (world.insert owner account).get? protectedAddr = world.get? protectedAddr := by
    exact (Std.TreeMap.getElem?_insert (t := world) (k := owner) (a := protectedAddr) (v := account)).trans
      (by simp [hne])
  constructor
  · intro old hold
    exact ⟨old,hl.trans hold,rfl⟩
  · intro slot
    simp only [SystemSpec.worldSlot,hl]

private theorem creation_input (kind : CreationGas.Variant) (a : StepArgs)
    (value off len salt : UInt256) (protectedAddr : AccountAddress)
    (hne : a.pre.executionEnv.codeOwner ≠ protectedAddr) :
    Frame a.pre.accountMap (creationArgs kind a.cost a.mid value off len salt).world protectedAddr ∧
      (creationArgs kind a.cost a.mid value off len salt).substate.selfDestructSet =
        a.pre.substate.selfDestructSet := by
  have hm := Z_ok_state a.guard
  constructor
  · change Frame a.pre.accountMap
      (a.mid.accountMap.insert a.mid.executionEnv.codeOwner
        { (a.mid.accountMap.get? a.mid.executionEnv.codeOwner).getD default with
          nonce := ((a.mid.accountMap.get? a.mid.executionEnv.codeOwner).getD default).nonce + ⟨1⟩ }) protectedAddr
    rw [hm]
    exact insert_away _ _ _ _ hne
  · change a.mid.substate.selfDestructSet = a.pre.substate.selfDestructSet
    rw [hm]
    rfl

theorem selected_lambda_input {n f : Nat} {a : StepArgs} {b : LambdaArgs}
    (hc : StepChild n a (some (.lambda f b))) (protectedAddr : AccountAddress)
    (hne : a.pre.executionEnv.codeOwner ≠ protectedAddr) :
    Frame a.pre.accountMap b.world protectedAddr ∧
      b.substate.selfDestructSet = a.pre.substate.selfDestructSet := by
  unfold StepChild selectedChild at hc
  split at hc
  · cases hc
  · split at hc
    all_goals repeat first | split at hc | contradiction
    all_goals simp only [Option.some.injEq,Request.lambda.injEq,reduceCtorEq] at hc
    all_goals obtain ⟨_,rfl⟩ := hc
    all_goals exact creation_input _ a _ _ _ _ protectedAddr hne

#print axioms selected_kind
#print axioms selected_theta_input
#print axioms selected_lambda_input
end Eip8282.Audit.Integrator.JournalChildEntry
