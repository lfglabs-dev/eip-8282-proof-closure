import Eip8282.Audit.Integrator.NestedCertificateAll
import Eip8282.Audit.Integrator.NestedProtectedJournal
import Eip8282.Audit.Integrator.WrapperJournalEdges
import Eip8282.Audit.Integrator.RuntimeThetaExclusion
import Eip8282.Audit.Integrator.CreationStorageFrame
import Eip8282.Audit.Integrator.FinalizationWorldFrame
import Eip8282.Audit.Integrator.RecursiveJournalEdges
import Eip8282.Audit.Integrator.JournalChildEntry
import Eip8282.Audit.Integrator.PrecompileWorldFrame

/-!
# Journal predicates at the actual recursive evaluator boundaries

The predicates below observe the same Request inputs and actual Except result.
External X/Xi frames retain another storage owner. A protected Theta is handled
atomically by the pinned-runtime proof; its body has no nested calls. This
avoids requiring a queue invariant between the protected runtime's own SSTOREs.
All-node funding/input and adequate-fuel producers remain separately visible.
-/
namespace Eip8282.Audit.Integrator.JournalExecution
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open NestedEvents
open ReachableCalls (Contract address runtime)
open JournalInvariant (modelKind)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2400000

def Journal (kind : Contract) (budget : Nat) (world : World) (substate : Substate) : Prop :=
  JournalInvariant.Invariant kind budget world ∧ address kind ∉ substate.selfDestructSet

def Ready (kind : Contract) (budget : Nat) : Request → Prop
  | .x _ _ pre => Journal kind budget pre.accountMap pre.substate ∧
      pre.executionEnv.codeOwner ≠ address kind
  | .xi _ a => Journal kind budget a.world a.substate ∧ a.env.codeOwner ≠ address kind
  | .theta _ a => Journal kind budget a.world a.substate ∧ CallOwnerCoherence.Coherent kind a
  | .lambda _ a => Journal kind budget a.world a.substate
  | .step _ a => Journal kind budget a.pre.accountMap a.pre.substate ∧
      a.pre.executionEnv.codeOwner ≠ address kind

/-- Exceptional X/Xi results have no committed world. Returned Theta/Lambda
failures do have a world, and that exact world must satisfy this predicate. -/
def Done (kind : Contract) (budget : Nat) : (q : Request) → q.Outcome → Prop
  | .x .., r => ∀ post out, r = .ok (.success post out) →
      Journal kind budget post.accountMap post.substate
  | .xi .., r => ∀ created world gas substate out,
      r = .ok (.success (created,world,gas,substate) out) → Journal kind budget world substate
  | .theta .., r => ∀ created world gas substate success out,
      r = .ok (created,world,gas,substate,success,out) → Journal kind budget world substate
  | .lambda .., r => ∀ target created world gas substate success out,
      r = .ok (target,created,world,gas,substate,success,out) → Journal kind budget world substate
  | .step _ a, r => ∀ post, r = .ok post →
      Journal kind budget post.accountMap post.substate ∧ post.executionEnv = a.pre.executionEnv

def CallInput : (q : Request) → q.Outcome → Prop
  | .theta _ a, _ => NestedProtectedJournal.Input a
  | _, _ => True

theorem inputs_every {q : Request} {result : q.Outcome} {tree : EventTree}
    (inputs : NestedProtectedJournal.Inputs q result tree) : Every CallInput q result tree := by
  intro path inner r loc
  cases inner with
  | theta fuel a => exact inputs path fuel a r (RequestAt.theta loc)
  | x | xi | lambda | step => exact True.intro

theorem Journal.mono {kind : Contract} {before after : Nat} {world : World} {substate : Substate}
    (h : Journal kind before world substate) (hb : before ≤ after) :
    Journal kind after world substate := ⟨JournalInvariant.mono h.1 hb,h.2⟩

theorem Journal.frame {kind : Contract} {budget : Nat} {before after : World}
    {s t : Substate} (h : Journal kind budget before s)
    (hf : CodeStorageFrame.Frame before after (address kind))
    (hs : t.selfDestructSet = s.selfDestructSet) : Journal kind budget after t :=
  ⟨JournalInvariant.frame h.1 hf,by rw [hs]; exact h.2⟩

theorem Ready.mono {kind : Contract} {before after : Nat} {q : Request}
    (h : Ready kind before q) (hb : before ≤ after) : Ready kind after q := by
  cases q with
  | lambda => exact Journal.mono h hb
  | x | xi | theta | step => exact ⟨Journal.mono h.1 hb,h.2⟩

/-- The actual protected Theta is the atomic case of recursive world
preservation. The same input invariant also supplies its three observations. -/
theorem protected_done {kind : Contract} {fuel : Nat} {a : ThetaArgs} {tree : EventTree}
    (cert : Cert (.theta (fuel+1) a) (Request.theta (fuel+1) a).eval tree)
    (inputs : Every CallInput (.theta (fuel+1) a) (Request.theta (fuel+1) a).eval tree)
    {budget : Nat} (hb : budget < 2^128) (ready : Ready kind budget (.theta (fuel+1) a))
    (ht : a.target = address kind) :
    Done kind (budget+tree.count) (.theta (fuel+1) a) (Request.theta (fuel+1) a).eval := by
  intro created world gas substate success out hr
  obtain ⟨hi,hn,_⟩ := NestedProtectedJournal.atomic_call cert ready.2 ht
    (inputs.root cert) hb ready.1.1 ready.1.2 hr
  exact ⟨hi,hn⟩

/-- Code execution starts after the literal value transfer. The world and
destruction-set projections are preserved even when sender and target alias. -/
theorem theta_entry {kind : Contract} {fuel : Nat} {a : ThetaArgs} (bytes : ByteArray)
    {budget : Nat} (ready : Ready kind budget (.theta fuel a))
    (ht : a.target ≠ address kind) : Ready kind budget (.xi fuel (a.xiArgs bytes)) := by
  refine ⟨?_,ht⟩
  exact Journal.frame ready.1 (CodeStorageFrame.entry (a.context 0 bytes) (address kind)) rfl

/-- Fresh creation preserves the protected projection even when the created
account was prefunded. Its init code executes at the distinct computed owner. -/
theorem lambda_entry {kind : Contract} {fuel : Nat} {a : LambdaArgs} (bytes : ByteArray)
    {budget : Nat} (ready : Ready kind budget (.lambda fuel a))
    (ht : CreationSettlement.address bytes ≠ address kind) :
    Ready kind budget (.xi fuel (a.xiArgs bytes)) := by
  refine ⟨?_,ht⟩
  exact Journal.frame ready
    (CreationStorageFrame.entry_frame (a.context 0) (CreationSettlement.address bytes) (address kind)) rfl

theorem ordinary_done {kind : Contract} {fuel : Nat} {a : StepArgs} {budget : Nat}
    (hop : OrdinaryGas.Ordinary a.op) (ready : Ready kind budget (.step fuel a)) :
    Done kind budget (.step fuel a) (Request.step fuel a).eval := by
  intro post hr
  have hf := OrdinaryWorldFrame.accepted_step_preserved hop ready.2 a.guard hr
  exact ⟨⟨JournalInvariant.frame ready.1.1 (CodeStorageFrame.of_preserved hf.1),
    SubstateSelfdestructFrame.accepted_other_owner hop ready.2 a.guard hr ready.1.2⟩,hf.2⟩

theorem denied_done {kind : Contract} {fuel : Nat} {a : StepArgs} {budget : Nat}
    (hc : StepChild fuel a none) (hop : ¬ OrdinaryGas.Ordinary a.op)
    (ready : Ready kind budget (.step fuel a)) :
    Done kind budget (.step fuel a) (Request.step fuel a).eval := by
  intro post hr
  obtain ⟨hw,hs,he⟩ := RecursiveJournalEdges.denied_recursive hc hop hr
  refine ⟨?_,he⟩
  exact ⟨by rw [hw]; exact ready.1.1,by rw [hs]; exact ready.1.2⟩

theorem step_theta_done {kind : Contract} {fuel innerFuel : Nat} {a : StepArgs} {b : ThetaArgs}
    {budget : Nat} (hc : StepChild fuel a (some (.theta innerFuel b)))
    (child : Done kind budget (.theta innerFuel b) (Request.theta innerFuel b).eval) :
    Done kind budget (.step fuel a) (Request.step fuel a).eval := by
  intro post hr
  obtain ⟨cr,w,g,ss,z,out,he,hw,hs,henv⟩ := RecursiveJournalEdges.theta_returned hc hr
  have h := child cr w g ss z out he
  exact ⟨⟨by rw [hw]; exact h.1,by rw [hs]; exact h.2⟩,henv⟩

theorem step_lambda_done {kind : Contract} {fuel innerFuel : Nat} {a : StepArgs} {b : LambdaArgs}
    {budget : Nat} (hc : StepChild fuel a (some (.lambda innerFuel b)))
    (returned : ∃ r, (Request.lambda innerFuel b).eval = .ok r)
    (child : Done kind budget (.lambda innerFuel b) (Request.lambda innerFuel b).eval) :
    Done kind budget (.step fuel a) (Request.step fuel a).eval := by
  intro post hr
  obtain ⟨⟨target,cr,w,g,ss,z,out⟩,he⟩ := returned
  obtain ⟨hw,hs,henv⟩ := RecursiveJournalEdges.lambda_returned hc he hr
  have h := child target cr w g ss z out he
  exact ⟨⟨by rw [hw]; exact h.1,by rw [hs]; exact h.2⟩,henv⟩

theorem xi_done {kind : Contract} {fuel : Nat} {a : XiArgs} {budget : Nat}
    (child : Done kind budget (.x fuel a.jumps a.entry) (Request.x fuel a.jumps a.entry).eval) :
    Done kind budget (.xi (fuel+1) a) (Request.xi (fuel+1) a).eval := by
  intro cr w g ss out hr
  obtain ⟨n,post,hf,he,_,hw,_,hs⟩ := WrapperJournalEdges.xi_success a hr
  have hn : n = fuel := by omega
  subst n
  have h := child post out he
  rw [hw,hs] at h
  exact h

theorem theta_done {kind : Contract} {fuel : Nat} {a : ThetaArgs} {budget spent : Nat}
    (bytes : ByteArray) (hc : a.code = .Code bytes)
    (ready : Ready kind budget (.theta (fuel+1) a))
    (child : Done kind (budget+spent) (.xi fuel (a.xiArgs bytes))
      (Request.xi fuel (a.xiArgs bytes)).eval) :
    Done kind (budget+spent) (.theta (fuel+1) a) (Request.theta (fuel+1) a).eval := by
  intro cr w g ss z out hr
  have he := (thetaArgs_result a fuel bytes hc).symm.trans hr
  rcases WrapperJournalEdges.theta_code_world (a.context fuel bytes) he with ⟨hw,hs⟩ | ⟨ic,iw,ig,iss,data,hx,hw,hs⟩
  · have h := Journal.mono ready.1 (Nat.le_add_right budget spent)
    exact ⟨by rw [hw]; exact h.1,by rw [hs]; exact h.2⟩
  · have h := child ic iw ig iss data hx
    exact ⟨by rw [hw]; exact h.1,by rw [hs]; exact h.2⟩

theorem lambda_done {kind : Contract} {fuel : Nat} {a : LambdaArgs} {budget spent : Nat}
    (bytes : ByteArray) (hp : a.preimage = some bytes)
    (ht : CreationSettlement.address bytes ≠ address kind)
    (ready : Ready kind budget (.lambda (fuel+1) a))
    (child : Done kind (budget+spent) (.xi fuel (a.xiArgs bytes))
      (Request.xi fuel (a.xiArgs bytes)).eval) :
    Done kind (budget+spent) (.lambda (fuel+1) a) (Request.lambda (fuel+1) a).eval := by
  intro target cr w g ss z out hr
  obtain ⟨_,hcases⟩ := WrapperJournalEdges.lambda_context_world (a.context fuel) hp hr
  rcases hcases with ⟨hw,hs⟩ | ⟨ic,iw,ig,iss,data,hx,hw,hs⟩
  · have h := Journal.mono ready (Nat.le_add_right budget spent)
    exact ⟨by rw [hw]; exact h.1,by rw [hs]; exact h.2⟩
  · have h := child ic iw ig iss data hx
    rw [hw]
    exact Journal.frame h (CreationStorageFrame.install_away_frame iw
      (CreationSettlement.address bytes) (address kind) data ht) hs

theorem runtime_nonempty (kind : Contract) : runtime kind ≠ ByteArray.empty := by
  cases kind <;> decide +kernel

/-- Occupied protected creation always restores both journal projections.
This uses the actual deposit-failure guard, without a success assumption about
the collision-selected initializer. -/
theorem occupied_lambda_done {kind : Contract} {fuel : Nat} {a : LambdaArgs}
    {budget spent : Nat} (bytes : ByteArray) (hp : a.preimage = some bytes)
    (ht : CreationSettlement.address bytes = address kind)
    (ready : Ready kind budget (.lambda (fuel+1) a)) :
    Done kind (budget+spent) (.lambda (fuel+1) a) (Request.lambda (fuel+1) a).eval := by
  intro target cr w g ss z out hr
  let c := a.context fuel
  obtain ⟨old,hold,hcode⟩ := ready.1.1
  have hold' : c.world.get? (CreationSettlement.address bytes) = some old := by rw [ht]; exact hold
  have hn : old.code ≠ ByteArray.empty := hcode ▸ runtime_nonempty kind
  have hf (gas : UInt256) (code : ByteArray) :
      c.depositFailure (CreationSettlement.address bytes) gas code = true := by
    unfold CreationSettlement.Context.depositFailure
    simp only [hold']
    simp [hn]
  have he : c.result = .ok (target,cr,w,g,ss,z,out) := hr
  rw [CreationSettlement.result_eq_settle c hp] at he
  have hj := Journal.mono ready (Nat.le_add_right budget spent)
  cases hx : c.execution (CreationSettlement.address bytes) with
  | error err =>
    simp only [CreationSettlement.Context.settle,hx] at he
    split at he
    · cases he
    · cases he; exact hj
  | ok result =>
    cases result with
    | revert remaining data =>
      simp only [CreationSettlement.Context.settle,hx] at he
      cases he; exact hj
    | success state data =>
      obtain ⟨ic,iw,ig,iss⟩ := state
      simp only [CreationSettlement.Context.settle,hx,hf,↓reduceIte] at he
      cases he; exact hj

theorem precompiled_done {kind : Contract} {fuel : Nat} {a : ThetaArgs} {budget : Nat}
    (target : AccountAddress) (hc : a.code = .Precompiled target)
    (ready : Ready kind budget (.theta fuel a)) :
    Done kind budget (.theta fuel a) (Request.theta fuel a).eval := by
  intro cr w g ss z out hr
  have hf := PrecompileWorldFrame.theta_frame hc hr (address kind)
  exact ⟨JournalInvariant.frame ready.1.1 hf,
    PrecompileWorldFrame.theta_exclusion hc hr ready.1.2⟩

theorem child_ready {kind : Contract} {fuel : Nat} {a : StepArgs} {q : Request} {budget : Nat}
    (hc : StepChild fuel a (some q)) (ready : Ready kind budget (.step fuel a)) :
    Ready kind budget q := by
  rcases JournalChildEntry.selected_kind hc with ⟨f,b,rfl⟩ | ⟨f,b,rfl⟩
  · obtain ⟨hw,hs⟩ := JournalChildEntry.selected_theta_input hc
    refine ⟨⟨?_,?_⟩,CallOwnerCoherence.selected_theta hc ready.1.1.1 ready.2⟩
    · rw [hw]; exact ready.1.1
    · rw [hs]; exact ready.1.2
  · obtain ⟨hf,hs⟩ := JournalChildEntry.selected_lambda_input hc (address kind) ready.2
    exact Journal.frame ready.1 hf hs

/-- Actual complete recursive execution preserves the installed code, queue
and controls, including returned failures and ancestor rollback. The explicit
all-node no-fuel condition is produced by FuelAdequacy from concrete resources;
it is needed because CREATE can catch evaluator exhaustion.

This theorem does not assume a contiguous protected-call history or any child
post-state invariant. Each child checkpoint is derived from its literal entry,
and each committed world is the one returned by the same certified evaluator.
-/
theorem preserves {kind : Contract} {q : Request} {result : q.Outcome} {tree : EventTree}
    (cert : Cert q result tree) :
    ∀ (budget : Nat), budget+tree.count < 2^128 → Ready kind budget q →
      Every CallInput q result tree → Every NoOutOfFuel q result tree →
      Done kind (budget+tree.count) q result := by
  induction cert with
  | xZero => intros; simp [Done]
  | xGuardError => intros; simp [Done]
  | xStepError => intros; simp [Done]
  | xRevert =>
    intro budget hb ready inputs safe post out he
    cases he
  | xiZero => intros; simp [Done]
  | thetaZero => intros; simp [Done]
  | lambdaZero => intros; simp [Done]
  | @xNext n cost vj pre mid post result child next hz hs hh ht ihs iht =>
    intro budget hb ready inputs safe
    have ls := RequestAt.xNextChild hz hs hh ht (.here hs)
    have lt := RequestAt.xNextTail hz hs hh ht (.here ht)
    have hbs : budget+child.count < 2^128 := by simp only [EventTree.count] at hb; omega
    have ds := ihs budget hbs ready (inputs.descendant ls) (safe.descendant ls)
    obtain ⟨hj,he⟩ := ds post rfl
    let mark := if decide (FrameEvents.Marked pre) then 1 else 0
    have heq : budget + (EventTree.step (decide (FrameEvents.Marked pre)) child next).count =
        (budget+child.count+mark)+next.count := by simp only [EventTree.count,mark]; omega
    have hbn : (budget+child.count+mark)+next.count < 2^128 := by rw [←heq]; exact hb
    have rn : Ready kind (budget+child.count+mark) (.x n vj post) :=
      ⟨Journal.mono hj (Nat.le_add_right _ _),by rw [he]; exact ready.2⟩
    have dn := iht _ hbn rn (inputs.descendant lt) (safe.descendant lt)
    rw [heq]
    exact dn
  | @xHalt n cost vj pre mid post out child hz hs hh hn ihs =>
    intro budget hb ready inputs safe
    have loc := RequestAt.xHalt hz hs hh hn (.here hs)
    have hbs : budget+child.count < 2^128 := by simp only [EventTree.count] at hb; omega
    have ds := ihs budget hbs ready (inputs.descendant loc) (safe.descendant loc)
    have hj := (ds post rfl).1
    intro final data he
    cases he
    exact Journal.mono hj (by simp only [EventTree.count]; omega)
  | @xi n a tree body ih =>
    intro budget hb ready inputs safe
    have loc := RequestAt.xi body (.here body)
    exact xi_done (ih budget hb ready (inputs.descendant loc) (safe.descendant loc))
  | @thetaPrecompile n a target hc =>
    intro budget hb ready inputs safe
    exact precompiled_done target hc ready
  | @thetaCode n a bytes tree hc body ih =>
    intro budget hb ready inputs safe
    by_cases ht : a.target = address kind
    · exact protected_done (.thetaCode bytes hc body) inputs (by omega) ready ht
    · have loc := RequestAt.thetaCode bytes hc body (.here body)
      have child := ih budget hb (theta_entry bytes ready ht)
        (inputs.descendant loc) (safe.descendant loc)
      exact theta_done bytes hc ready child
  | @lambdaNoPreimage n a hp =>
    intros
    obtain ⟨bytes,hb⟩ := CreationPreimageTotal.lambdaArgs_total a
    rw [hp] at hb
    cases hb
  | @lambdaInit n a bytes tree hp body ih =>
    intro budget hb ready inputs safe
    by_cases ht : CreationSettlement.address bytes = address kind
    · exact occupied_lambda_done bytes hp ht ready
    · have loc := RequestAt.lambdaInit bytes hp body (.here body)
      have child := ih budget hb (lambda_entry bytes ready ht)
        (inputs.descendant loc) (safe.descendant loc)
      exact lambda_done bytes hp ht ready child
  | @stepNone n a hc =>
    intro budget hb ready inputs safe
    by_cases ho : OrdinaryGas.Ordinary a.op
    · exact ordinary_done ho ready
    · exact denied_done hc ho ready
  | @stepChild n a q tree hc body ih =>
    intro budget hb ready inputs safe
    have loc := RequestAt.stepChild hc body (.here body)
    have child := ih budget hb (child_ready hc ready)
      (inputs.descendant loc) (safe.descendant loc)
    rcases JournalChildEntry.selected_kind hc with ⟨f,b,hq⟩ | ⟨f,b,hq⟩
    · subst q
      exact step_theta_done hc child
    · subst q
      exact step_lambda_done hc (lambda_returns safe loc) child

#print axioms protected_done
#print axioms ordinary_done
#print axioms child_ready
#print axioms occupied_lambda_done
#print axioms preserves
end Eip8282.Audit.Integrator.JournalExecution
