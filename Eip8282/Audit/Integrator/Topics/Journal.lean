import Eip8282.Audit.Integrator.CodeStorageFrame
import Eip8282.Audit.Integrator.DirectGuarantees
import Eip8282.Audit.Integrator.JournalInvariant
import Eip8282.Audit.Integrator.NestedEventArgs
import Eip8282.Audit.Integrator.PrefundedInitialization

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## JournalChildEntry -/

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

end

section

/-! ## JournalGuarantees -/

/-!
# The three local guarantees consume the derived journal invariant together

The physical queue and each public domain field are obtained from one invariant
at the actual pre-world. The guarantees then observe one and the same Theta
receipt, including its output, logs and rollback. Complete protocol extraction
must still produce this invariant at every relevant call; this module does not
replace that obligation by assuming an arbitrary call history is reachable.
-/
namespace Eip8282.Audit.Integrator.JournalGuarantees
open EvmYul EvmYul.EVM
open ReachableCalls (Contract Transition address runtime)
open JournalInvariant (Invariant modelKind)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem domains {kind : Contract} {before after : AccountMap .EVM}
    (t : Transition kind before after) {budget : Nat}
    (hi : Invariant kind budget before) (hb : budget < 2^128)
    (hd : t.call.calldata.size < UInt256.size) :
    DirectGuarantees.Domain (modelKind kind) t.call budget ∧
      ∃ queue : List (QueueInvariant.Record (modelKind kind)),
        DirectDrain.Domain (modelKind kind) t.call queue budget := by
  have ho : ∃ account, t.call.world.get? t.call.target = some account := by
    obtain ⟨account,ha,_⟩ := t.pinned.installed
    exact ⟨account,ha⟩
  have hs : SystemSpec.worldSlot t.call.world t.call.target =
      SystemSpec.worldSlot before (address kind) := by rw [t.pre,t.pinned.target]
  obtain ⟨_,hi⟩ := hi
  cases kind with
  | deposit =>
    obtain ⟨bounded,safe,queue,hq⟩ := hi
    constructor
    · refine ⟨ho,t.pinned.ordinaryValue,hd,hb,?_,?_⟩
      · rw [hs]; exact bounded
      · rw [hs]; exact safe
    · refine ⟨queue,ho,t.pinned.ordinaryValue,hd,hb,?_,?_,?_,True.intro⟩
      · rw [hs]; exact bounded
      · rw [hs]; exact safe
      · rw [hs]; exact hq
  | exit =>
    obtain ⟨bounded,safe,queue,hq,hw⟩ := hi
    constructor
    · refine ⟨ho,t.pinned.ordinaryValue,hd,hb,?_,?_⟩
      · rw [hs]; exact bounded
      · rw [hs]; exact safe
    · refine ⟨queue,ho,t.pinned.ordinaryValue,hd,hb,?_,?_,?_,hw⟩
      · rw [hs]; exact bounded
      · rw [hs]; exact safe
      · rw [hs]; exact hq

/-- All three public local predicates are composed on the same actual receipt;
their internal queue, control and slot-bounds domains are derived above. -/
theorem completed {kind : Contract} {before after : AccountMap .EVM}
    (t : Transition kind before after) {budget : Nat}
    (hi : Invariant kind budget before) (hb : budget < 2^128)
    (hd : t.call.calldata.size < UInt256.size) :
    ∃ queue : List (QueueInvariant.Record (modelKind kind)),
      DirectGuarantees.SubmitObserved (modelKind kind) t.call t.created after t.substate t.success t.output ∧
      DirectDrain.Observed (modelKind kind) t.call after t.success t.output queue ∧
      DirectControl.Observed (modelKind kind) t.call t.created after t.substate t.success t.output := by
  obtain ⟨domain,queue,drain⟩ := domains t hi hb hd
  have hc : t.call.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
    cases kind <;> exact t.pinned.code
  exact ⟨queue,
    DirectGuarantees.psubmit1_direct (modelKind kind) t.call budget hc domain
      t.created after t.gas t.substate t.success t.output t.executed,
    DirectGuarantees.pdrain1_direct (modelKind kind) t.call queue budget hc drain
      t.created after t.gas t.substate t.success t.output t.executed,
    (DirectGuarantees.pcontrol1_direct (modelKind kind)).1 t.call budget hc domain
      t.created after t.gas t.substate t.success t.output t.executed⟩

/-- Actual initialization with an admissibly prefunded target supplies the
initial invariant used by the composition, with no target-absence premise. -/
theorem initializes (kind : Contract) (c : CreationSettlement.Context)
    (preimage : ByteArray) (steps : Nat)
    (hi : c.init = Initialization.initCode (modelKind kind))
    (hd : PrefundedInitialization.Domain (modelKind kind) c preimage steps)
    (hg : InitializerProgress.creationGas (modelKind kind) ≤ c.gas.toNat)
    (hc : CreationSettlement.address preimage = address kind) :
    ∃ created world gas substate,
      c.result = .ok (CreationSettlement.address preimage,created,world,gas,substate,true,ByteArray.empty) ∧
      Invariant kind 0 world := by
  obtain ⟨created,world,gas,substate,hr,ho⟩ :=
    PrefundedInitialization.initializes_success (modelKind kind) c preimage steps hi hd hg
  exact ⟨created,world,gas,substate,hr,JournalInvariant.of_initialized kind c preimage hc ho⟩

#print axioms domains
#print axioms completed
#print axioms initializes
end Eip8282.Audit.Integrator.JournalGuarantees

end
