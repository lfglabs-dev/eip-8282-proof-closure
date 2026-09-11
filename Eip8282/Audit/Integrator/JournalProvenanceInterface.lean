import Eip8282.Audit.Integrator.JournalInvariant
import Eip8282.Audit.Integrator.DirectDrain
import Eip8282.Audit.Integrator.DirectAppend

/-! Chosen physical queue witnesses and actual local append/log provenance.
The same supplied prequeue determines the returned queue. Equal record bytes
do not identify submission occurrences; global ID freshness and survival past
ancestor rollback remain separate obligations of the actual journal traversal. -/
namespace Eip8282.Audit.Integrator.JournalProvenanceInterface
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Correspondence (runtimeCode)
open QueueInvariant SystemSpec MessageCall
open JournalInvariant (modelKind)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem represents_unique {kind : Kind} {read : UInt256 → UInt256}
    {first second : List (Record kind)}
    (hf : Represents kind read first) (hs : Represents kind read second) : first = second := by
  apply List.ext_getElem
  · exact hf.length_eq.trans hs.length_eq.symm
  · intro i hi hj
    funext j
    exact (hf.contents i hi j).symm.trans (hs.contents i hj j)

def after (kind : Kind) (c : Context) (success : Bool) (queue : List (Record kind)) :
    List (Record kind) :=
  if success then
    if c.caller = Eip8282.Audit.EvmRunner.sysAddr then queue.drop (min queue.length (SystemDataSpec.cap kind))
    else DirectDrain.userQueue kind c queue
  else queue

theorem completed_queue (kind : Kind) (c : Context) (hcode : c.code = runtimeCode kind)
    (queue : List (Record kind)) (budget : Nat) (hd : DirectDrain.Domain kind c queue budget)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {ss : Substate} {success : Bool} {out : ByteArray}
    (hr : c.result = .ok (created,world,gas,ss,success,out)) :
    Represents kind (worldSlot world c.target) (after kind c success queue) := by
  have h := DirectDrain.completed_call kind c hcode queue budget hd hr
  cases success with
  | false => exact h.2
  | true =>
      by_cases hc : c.caller = Eip8282.Audit.EvmRunner.sysAddr
      · simp only [DirectDrain.Observed, after, hc, ↓reduceIte] at h ⊢
        exact h.2.1
      · simp only [DirectDrain.Observed, after, hc, ↓reduceIte] at h ⊢
        exact h.2.1

/-- One actual successful user result simultaneously extends this chosen queue
and appends the authentic anonymous log to its actual input substate. -/
theorem completed_append (kind : Kind) (c : Context) (hcode : c.code = runtimeCode kind)
    (queue : List (Record kind)) (budget : Nat) (hd : DirectDrain.Domain kind c queue budget)
    (huser : c.caller ≠ Eip8282.Audit.EvmRunner.sysAddr) (hn : c.calldata.size ≠ 0)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {ss : Substate} {out : ByteArray}
    (hr : c.result = .ok (created,world,gas,ss,true,out)) :
    Represents kind (worldSlot world c.target) (queue ++ [DirectDrain.inputRecord kind c]) ∧
      ss.logSeries = c.substate.logSeries.push
        ⟨c.target,#[],AppendDataSpec.record kind c.calldata c.caller⟩ := by
  have hq := completed_queue kind c hcode queue budget hd hr
  have hs : FundedDomain.EnabledSafe (DirectAdmission.target kind) (worldSlot c.world c.target) := by
    cases kind <;> exact hd.safe
  have hl := (DirectAppend.user_append kind c hcode huser hd.ordinaryValue hd.calldataFit hn
    hd.owner budget hd.budgetFit hd.bounded hs hr).1.2.2.1
  exact ⟨by simpa only [after,huser,↓reduceIte,DirectDrain.userQueue,if_neg hn] using hq,hl⟩

/-- Returned failure restores both the chosen queue's physical world and the
complete actual input log series. This is a local checkpoint, not an assertion
that a successful child survives its ancestors. -/
theorem failed_checkpoint (c : Context) {kind : Kind} (queue : List (Record kind))
    (hq : Represents kind (worldSlot c.world c.target) queue)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {ss : Substate} {out : ByteArray}
    (hr : c.result = .ok (created,world,gas,ss,false,out)) :
    world = c.world ∧ ss.logSeries = c.substate.logSeries ∧
      Represents kind (worldSlot world c.target) queue := by
  obtain ⟨hw,hs,_⟩ := failure_restores_journal c created world gas ss out hr
  exact ⟨hw,by rw [hs],by rw [hw]; exact hq⟩

def ChosenInvariant (kind : ReachableCalls.Contract) (budget : Nat)
    (world : AccountMap .EVM) (queue : List (Record (modelKind kind))) : Prop :=
  JournalInvariant.Invariant kind budget world ∧
    Represents (modelKind kind) (worldSlot world (ReachableCalls.address kind)) queue

theorem choose_queue {kind : ReachableCalls.Contract} {budget : Nat} {world : AccountMap .EVM}
    (h : JournalInvariant.Invariant kind budget world) :
    ∃ queue, ChosenInvariant kind budget world queue := by
  cases kind with
  | deposit => obtain ⟨queue,hq⟩ := h.2.2.2; exact ⟨queue,h,hq⟩
  | exit => obtain ⟨queue,hq,_⟩ := h.2.2.2; exact ⟨queue,h,hq⟩

theorem chosen_source {kind : ReachableCalls.Contract} {budget : Nat} {world : AccountMap .EVM}
    {queue : List (Record (modelKind kind))} (h : ChosenInvariant kind budget world queue) :
    DirectDrain.sourceWidth (modelKind kind) queue := by
  cases kind with
  | deposit => exact True.intro
  | exit =>
    obtain ⟨other,hr,hw⟩ := h.1.2.2.2
    have he := represents_unique h.2 hr
    rw [he]
    exact hw

theorem chosen_frame {kind : ReachableCalls.Contract} {budget : Nat} {before afterWorld : AccountMap .EVM}
    {queue : List (Record (modelKind kind))} (h : ChosenInvariant kind budget before queue)
    (hf : CodeStorageFrame.Frame before afterWorld (ReachableCalls.address kind)) :
    ChosenInvariant kind budget afterWorld queue := by
  refine ⟨JournalInvariant.frame h.1 hf,?_⟩
  have he := funext hf.storage
  rw [he]
  exact h.2

theorem chosen_mono {kind : ReachableCalls.Contract} {before afterBudget : Nat} {world : AccountMap .EVM}
    {queue : List (Record (modelKind kind))} (h : ChosenInvariant kind before world queue)
    (hb : before ≤ afterBudget) : ChosenInvariant kind afterBudget world queue :=
  ⟨JournalInvariant.mono h.1 hb,h.2⟩

theorem transition_domain {kind : ReachableCalls.Contract} {before afterWorld : AccountMap .EVM}
    (t : ReachableCalls.Transition kind before afterWorld) {budget : Nat}
    {queue : List (Record (modelKind kind))} (h : ChosenInvariant kind budget before queue)
    (hb : budget < 2^128) (hfit : t.call.calldata.size < UInt256.size) :
    DirectDrain.Domain (modelKind kind) t.call queue budget := by
  refine ⟨?_,t.pinned.ordinaryValue,hfit,hb,?_,?_,?_,chosen_source h⟩
  · obtain ⟨account,ha,_⟩ := t.pinned.installed
    exact ⟨account,ha⟩
  · rw [t.pre,t.pinned.target]
    cases kind <;> exact h.1.2.1
  · rw [t.pre,t.pinned.target]
    cases kind <;> exact h.1.2.2.1
  · rw [t.pre,t.pinned.target]
    exact h.2

theorem transition_preserves {kind : ReachableCalls.Contract} {before afterWorld : AccountMap .EVM}
    (t : ReachableCalls.Transition kind before afterWorld) (ha : ConcreteHistory.Allowed t.call)
    {budget : Nat} {queue : List (Record (modelKind kind))}
    (h : ChosenInvariant kind budget before queue) (hb : budget < 2^128) :
    ChosenInvariant kind (budget + ConcreteHistory.weight t.call t.success) afterWorld
      (after (modelKind kind) t.call t.success queue) := by
  have hc : t.call.code = runtimeCode (modelKind kind) := by cases kind <;> exact t.pinned.code
  have hq := completed_queue (modelKind kind) t.call hc queue budget (transition_domain t h hb ha.1) t.executed
  rw [t.pinned.target] at hq
  exact ⟨JournalInvariant.protected_call t ha hb h.1,hq⟩

#print axioms represents_unique
#print axioms completed_queue
#print axioms completed_append
#print axioms failed_checkpoint
#print axioms chosen_source
#print axioms chosen_frame
#print axioms transition_preserves
end Eip8282.Audit.Integrator.JournalProvenanceInterface
