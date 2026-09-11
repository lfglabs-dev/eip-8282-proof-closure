import Eip8282.Audit.Integrator.JournalExecution
import Eip8282.Audit.Integrator.CreationCollisionScope
import Eip8282.Audit.Integrator.FuelAdequacy

/-!
# Invariants at every actual nested message-call entry

The starting journal, actual successful preceding steps and exact wrapper
entries derive the invariant at each located Theta. Work before that position
is counted chronologically even if an ancestor later reverts. Protected runtime
bodies and occupied creation bodies cannot introduce hidden nested calls.
-/
namespace Eip8282.Audit.Integrator.JournalCheckpoints
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open NestedEvents JournalExecution
open ReachableCalls (Contract address runtime)
open NestedJournalBudget (before)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2400000

private theorem protected_no_theta {kind : Contract} {n f : Nat} {a : ThetaArgs}
    {bytes : ByteArray} {tree : EventTree} {path : EventTree.Address} {b : ThetaArgs}
    {result : XiResult} {r : ThetaResult}
    (hc : a.code = .Code bytes) (coherent : CallOwnerCoherence.Coherent kind a)
    (ht : a.target = address kind)
    (loc : ThetaAt (.xi n (a.xiArgs bytes)) result tree path f b r) : False := by
  have he : bytes = runtime kind := ToExecute.Code.inj (hc.symm.trans (coherent ht).1)
  cases kind with
  | deposit => exact RuntimeThetaExclusion.xi_no_theta (image := RuntimeExecutionScope.deposit) he loc
  | exit => exact RuntimeThetaExclusion.xi_no_theta (image := RuntimeExecutionScope.exit) he loc

/-- A complete journal invariant is derived at every actual message-call
input, including calls inside ancestors that subsequently fail or revert. -/
theorem call_ready {kind : Contract} {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt q result tree path f a r) :
    ∀ (budget : Nat), budget+tree.count < 2^128 → Ready kind budget q →
      Every CallInput q result tree → Every NoOutOfFuel q result tree →
      Ready kind (budget+before tree path) (.theta f a) := by
  induction loc with
  | here body =>
    intro budget hb ready inputs safe
    simpa only [before,Nat.add_zero] using ready
  | xStepError hz hs loc ih =>
    intro budget hb ready inputs safe
    have node := RequestAt.xStepError hz hs (.here hs)
    exact ih budget (by simpa only [EventTree.count,Bool.false_eq_true,↓reduceIte,Nat.zero_add,Nat.add_zero] using hb)
      ready (inputs.descendant node) (safe.descendant node)
  | xNextChild hz hs hh ht loc ih =>
    intro budget hb ready inputs safe
    have node := RequestAt.xNextChild hz hs hh ht (.here hs)
    exact ih budget (by simp only [EventTree.count] at hb; omega)
      ready (inputs.descendant node) (safe.descendant node)
  | @xNextTail n cost f vj pre mid post result child next path a r hz hs hh ht loc ih =>
    intro budget hb ready inputs safe
    have stepNode := RequestAt.xNextChild hz hs hh ht (.here hs)
    have nextNode := RequestAt.xNextTail hz hs hh ht (.here ht)
    have hbs : budget+child.count < 2^128 := by simp only [EventTree.count] at hb; omega
    have ds := JournalExecution.preserves hs budget hbs ready
      (inputs.descendant stepNode) (safe.descendant stepNode)
    obtain ⟨hj,he⟩ := ds post rfl
    let mark := if decide (FrameEvents.Marked pre) then 1 else 0
    have heq : budget + (EventTree.step (decide (FrameEvents.Marked pre)) child next).count =
        (budget+child.count+mark)+next.count := by simp only [EventTree.count,mark]; omega
    have hbn : (budget+child.count+mark)+next.count < 2^128 := by rw [←heq]; exact hb
    have rn : Ready kind (budget+child.count+mark) (.x n vj post) :=
      ⟨Journal.mono hj (Nat.le_add_right _ _),by rw [he]; exact ready.2⟩
    have got := ih _ hbn rn (inputs.descendant nextNode) (safe.descendant nextNode)
    have hoff : budget + before (EventTree.step (decide (FrameEvents.Marked pre)) child next) (true::path) =
        (budget+child.count+mark)+before next path := by simp only [before,mark]; omega
    rw [hoff]
    exact got
  | xHalt hz hs hh hn loc ih =>
    intro budget hb ready inputs safe
    have node := RequestAt.xHalt hz hs hh hn (.here hs)
    exact ih budget (by simp only [EventTree.count] at hb; omega)
      ready (inputs.descendant node) (safe.descendant node)
  | xRevert hz hs hh hr loc ih =>
    intro budget hb ready inputs safe
    have node := RequestAt.xRevert hz hs hh hr (.here hs)
    exact ih budget (by simp only [EventTree.count] at hb; omega)
      ready (inputs.descendant node) (safe.descendant node)
  | xi body loc ih =>
    intro budget hb ready inputs safe
    have node := RequestAt.xi body (.here body)
    exact ih budget hb ready (inputs.descendant node) (safe.descendant node)
  | @thetaCode n f outer a r bytes tree path hc body loc ih =>
    intro budget hb ready inputs safe
    by_cases ht : outer.target = address kind
    · exact False.elim (protected_no_theta hc ready.2 ht loc)
    · have node := RequestAt.thetaCode bytes hc body (.here body)
      exact ih budget hb (theta_entry bytes ready ht) (inputs.descendant node) (safe.descendant node)
  | lambdaInit bytes hp body loc ih =>
    intro budget hb ready inputs safe
    by_cases ht : CreationSettlement.address bytes = address kind
    · exact False.elim (CreationCollisionScope.no_theta ready.1.1 ht loc)
    · have node := RequestAt.lambdaInit bytes hp body (.here body)
      exact ih budget hb (lambda_entry bytes ready ht) (inputs.descendant node) (safe.descendant node)
  | stepChild hc body loc ih =>
    intro budget hb ready inputs safe
    have node := RequestAt.stepChild hc body (.here body)
    exact ih budget hb (child_ready hc ready) (inputs.descendant node) (safe.descendant node)

/-- Concrete sufficient evaluator resources discharge the all-node exception
condition in both final-world preservation and every nested entry invariant. -/
theorem from_resources {kind : Contract} {q : Request} {result : q.Outcome} {tree : EventTree}
    (cert : Cert q result tree) (adequate : FuelAdequacy.Adequate q)
    (budget : Nat) (hb : budget+tree.count < 2^128) (ready : Ready kind budget q)
    (inputs : NestedProtectedJournal.Inputs q result tree) :
    Done kind (budget+tree.count) q result ∧
      ∀ (path : EventTree.Address) (f : Nat) (a : ThetaArgs) (r : ThetaResult),
        ThetaAt q result tree path f a r → Ready kind (budget+before tree path) (.theta f a) := by
  have hi := inputs_every inputs
  have safe := FuelAdequacy.every_no_out_of_fuel cert adequate
  exact ⟨JournalExecution.preserves cert budget hb ready hi safe,
    fun _ _ _ _ loc => call_ready loc budget hb ready hi safe⟩

/-- All three observations of an actual nested protected call now follow from
the outer execution's initial journal, not a separately supplied invariant at
that call. Its local post-journal and spent work refer to the same actual tree.
Ancestor rollback remains reflected by the enclosing execution's final world. -/
theorem observed {kind : Contract} {q : Request} {result : q.Outcome} {tree : EventTree}
    (cert : Cert q result tree) (adequate : FuelAdequacy.Adequate q)
    (budget : Nat) (hb : budget+tree.count < 2^128) (ready : Ready kind budget q)
    (inputs : NestedProtectedJournal.Inputs q result tree)
    {path : EventTree.Address} {fuel : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt q result tree path (fuel+1) a r) (ht : a.target = address kind)
    {created : Created} {world : World} {gas : UInt256} {substate : Substate}
    {success : Bool} {out : ByteArray}
    (hr : r = .ok (created,world,gas,substate,success,out)) :
    ∃ inner, Cert (.theta (fuel+1) a) r inner ∧
      Journal kind (budget+before tree path+inner.count) world substate ∧
      NestedProtectedJournal.Observed kind (a.context fuel (runtime kind))
        created world substate success out := by
  have readyCall := (from_resources cert adequate budget hb ready inputs).2 _ _ _ _ loc
  obtain ⟨inner,hc,hi⟩ := NestedJournalBudget.call_interval loc
  have hbCall : budget+before tree path < 2^128 := by omega
  have he := ThetaAt.sound_inner loc
  have hc' : Cert (.theta (fuel+1) a) (Request.theta (fuel+1) a).eval inner := by rw [he]; exact hc
  obtain ⟨post,hn,observed⟩ := NestedProtectedJournal.atomic_call hc' readyCall.2 ht
    (inputs path (fuel+1) a r loc) hbCall readyCall.1.1 readyCall.1.2 (he.trans hr)
  exact ⟨inner,hc,⟨post,hn⟩,observed⟩

#print axioms call_ready
#print axioms from_resources
#print axioms observed
end Eip8282.Audit.Integrator.JournalCheckpoints
