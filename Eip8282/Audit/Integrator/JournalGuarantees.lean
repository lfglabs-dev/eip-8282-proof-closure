import Eip8282.Audit.Integrator.JournalInvariant
import Eip8282.Audit.Integrator.DirectGuarantees
import Eip8282.Audit.Integrator.PrefundedInitialization

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
