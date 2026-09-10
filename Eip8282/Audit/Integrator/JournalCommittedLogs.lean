import Eip8282.Audit.Integrator.JournalRetainedPaths
import Eip8282.Audit.Integrator.ProtectedCallLogSeries
import Eip8282.Audit.Integrator.RecursiveLogEdges
import Eip8282.Audit.Integrator.JournalLogInputs

/-! Final protected-emitter logs follow the independently specified surviving
call list of the same actual evaluator. Occurrence identity, not record-byte
equality, determines each contribution. Ancestor rollback discards the entire
child contribution, while the separate executed-work measure retains its gas. -/
namespace Eip8282.Audit.Integrator.JournalCommittedLogs
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open NestedEvents JournalExecution JournalWorldPaths JournalRetainedCalls JournalRetainedPaths
open ReachableCalls (Contract address runtime Transition)
open JournalInvariant (modelKind)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def contribution {kind : Contract} {root : Request} {rr : root.Outcome} {rt : EventTree}
    (o : Occurrence kind root rr rt) : List LogEntry :=
  ProtectedCallLogSeries.contribution (modelKind kind) o.transition.call o.transition.success

theorem contribution_identity {kind : Contract} {root : Request} {rr : root.Outcome} {rt : EventTree}
    (a b : Occurrence kind root rr rt) (hp : a.path = b.path) : contribution a = contribution b := by
  have ha := a.located
  rw [hp] at ha
  obtain ⟨hf,hi,hr⟩ := ha.identity b.located
  have hc : a.transition.call = b.transition.call := by rw [a.context,b.context,hf,hi]
  have hs : a.transition.success = b.transition.success := by
    exact congrArg (fun t => t.2.2.2.2.1) (Except.ok.inj hr)
  simp only [contribution,hc,hs]

noncomputable def atContribution (kind : Contract) (root : Request) (rr : root.Outcome)
    (rt : EventTree) (path : EventTree.Address) : List LogEntry := by
  classical
  exact if h : ∃ o : Occurrence kind root rr rt, o.path = path then contribution h.choose else []

theorem at_occurrence {kind : Contract} {root : Request} {rr : root.Outcome} {rt : EventTree}
    (o : Occurrence kind root rr rt) : atContribution kind root rr rt o.path = contribution o := by
  classical
  have h : ∃ other : Occurrence kind root rr rt, other.path = o.path := ⟨o,rfl⟩
  simp only [atContribution,dif_pos h]
  exact contribution_identity h.choose o h.choose_spec

noncomputable def emitted (kind : Contract) (root : Request) (rr : root.Outcome) (rt : EventTree)
    (basePath : EventTree.Address) (q : Request) (result : q.Outcome) (tree : EventTree) : List LogEntry :=
  (retainedList kind q result tree).flatMap (fun p => atContribution kind root rr rt (basePath++p))

theorem emitted_replay {kind : Contract} {root : Request} {rr : root.Outcome} {rt tree : EventTree}
    {q : Request} {result : q.Outcome} {basePath : EventTree.Address}
    (os : List (Occurrence kind root rr rt))
    (he : os.map (·.path) = (retainedList kind q result tree).map (basePath++·)) :
    emitted kind root rr rt basePath q result tree = os.flatMap contribution := by
  have hh := congrArg (List.flatMap (atContribution kind root rr rt)) he
  simpa only [List.flatMap_map,Function.comp_def,at_occurrence,emitted] using hh.symm

def DoneLogs (kind : Contract) (root : Request) (rr : root.Outcome) (rt : EventTree)
    (basePath : EventTree.Address) (q : Request) (result : q.Outcome) (tree : EventTree) : Prop :=
  let logs := emitted kind root rr rt basePath q result tree
  match q,result with
  | .x _ _ pre,r => ∀ post out, r = .ok (.success post out) →
      ProtectedLogFrame.project (address kind) post.substate = ProtectedLogFrame.project (address kind) pre.substate ++ logs
  | .xi _ a,r => ∀ cr world gas ss out, r = .ok (.success (cr,world,gas,ss) out) →
      ProtectedLogFrame.project (address kind) ss = ProtectedLogFrame.project (address kind) a.substate ++ logs
  | .theta _ a,r => ∀ cr world gas ss z out, r = .ok (cr,world,gas,ss,z,out) →
      ProtectedLogFrame.project (address kind) ss = ProtectedLogFrame.project (address kind) a.substate ++ logs
  | .lambda _ a,r => ∀ target cr world gas ss z out, r = .ok (target,cr,world,gas,ss,z,out) →
      ProtectedLogFrame.project (address kind) ss = ProtectedLogFrame.project (address kind) a.substate ++ logs
  | .step _ a,r => ∀ post, r = .ok post →
      ProtectedLogFrame.project (address kind) post.substate = ProtectedLogFrame.project (address kind) a.pre.substate ++ logs

theorem project_eq {kind : Contract} {a b : Substate} (h : a.logSeries = b.logSeries) :
    ProtectedLogFrame.project (address kind) a = ProtectedLogFrame.project (address kind) b := by
  simp only [ProtectedLogFrame.project,h]

theorem protected_logs {kind : Contract} {root : Request} {rr : root.Outcome} {rt tree : EventTree}
    {n : Nat} {a : ThetaArgs} {basePath : EventTree.Address} {budget : Nat}
    (cert : Cert (.theta (n+1) a) (Request.theta (n+1) a).eval tree)
    (ready : Ready kind budget (.theta (n+1) a)) (hb : budget < 2^128)
    (fit : a.data.size < UInt256.size) (ht : a.target = address kind)
    (loc : RequestAt root rr rt basePath (.theta (n+1) a) (Request.theta (n+1) a).eval) :
    DoneLogs kind root rr rt basePath (.theta (n+1) a) (Request.theta (n+1) a).eval tree := by
  intro cr world gas ss z out hr
  have hc := (ready.2 ht).1
  let t : Transition kind a.world world :=
    { call := a.context n (runtime kind),
      pinned := CallOwnerCoherence.pinned n ready.1.1.1 ready.2 ht,
      pre := rfl, created := cr, gas := gas, substate := ss, success := z, output := out,
      executed := (thetaArgs_result a n (runtime kind) hc).symm.trans hr }
  have located : ThetaAt root rr rt basePath (n+1) a (.ok (cr,world,gas,ss,z,out)) := by
    rw [hr] at loc
    exact RequestAt.theta loc
  let occurrence : Occurrence kind root rr rt :=
    { path := basePath, fuel := n+1, args := a, before := a.world, after := world,
      transition := t, positive := Nat.succ_pos _, context := rfl, located := located }
  have hlog := ProtectedCallLogSeries.transition t ready.1.1 hb fit
  have hc' := cert
  rw [hr] at hc'
  change _ = _ ++ emitted kind root rr rt basePath (.theta (n+1) a) (Request.theta (n+1) a).eval tree
  rw [emitted,hr,list_theta_atomic hc' ht]
  simp only [List.flatMap_cons,List.append_nil,List.flatMap_nil]
  rw [show basePath = occurrence.path from rfl,at_occurrence]
  exact hlog

theorem empty_logs {kind : Contract} {root q : Request} {rr : root.Outcome}
    {result : q.Outcome} {rt tree : EventTree} {basePath : EventTree.Address} {before after : Substate}
    (empty : retainedList kind q result tree = []) (hl : after.logSeries = before.logSeries) :
    ProtectedLogFrame.project (address kind) after = ProtectedLogFrame.project (address kind) before ++
      emitted kind root rr rt basePath q result tree := by
  simp only [emitted,empty,List.flatMap_nil,List.append_nil]
  exact project_eq hl

theorem theta_logs {kind : Contract} {root : Request} {rr : root.Outcome} {rt tree : EventTree}
    {n : Nat} {a : ThetaArgs} {basePath : EventTree.Address}
    (bytes : ByteArray) (hc : a.code = .Code bytes) (ht : a.target ≠ address kind)
    (child : DoneLogs kind root rr rt basePath (.xi n (a.xiArgs bytes))
      (Request.xi n (a.xiArgs bytes)).eval tree) :
    DoneLogs kind root rr rt basePath (.theta (n+1) a) (Request.theta (n+1) a).eval tree := by
  intro cr w g ss z out hr
  have he := (thetaArgs_result a n bytes hc).symm.trans hr
  cases hx : (Request.xi n (a.xiArgs bytes)).eval with
  | error err =>
    have empty : retainedList kind (.theta (n+1) a) (Request.theta (n+1) a).eval tree = [] := by
      apply retained_empty
      intro p h
      obtain ⟨ic,iw,ig,iss,data,hxi,hk,h⟩ := (retained_theta_foreign hc ht p).mp h
      have e := hx.symm.trans hxi
      cases e
    rcases RecursiveLogEdges.theta_code_logs (a.context n bytes) he with ⟨_,hl⟩ | ⟨ic,iw,ig,iss,data,hxi,_,_,_⟩
    · exact empty_logs empty hl
    · have hxi' : (Request.xi n (a.xiArgs bytes)).eval = .ok (.success (ic,iw,ig,iss) data) := hxi
      rw [hx] at hxi'; cases hxi'
  | ok result =>
    cases result with
    | revert ig data =>
      have empty : retainedList kind (.theta (n+1) a) (Request.theta (n+1) a).eval tree = [] := by
        apply retained_empty
        intro p h
        obtain ⟨ic,iw,ig,iss,data,hxi,hk,h⟩ := (retained_theta_foreign hc ht p).mp h
        have e := hx.symm.trans hxi
        cases e
      rcases RecursiveLogEdges.theta_code_logs (a.context n bytes) he with ⟨_,hl⟩ | ⟨ic,iw,ig,iss,data,hxi,_,_,_⟩
      · exact empty_logs empty hl
      · have hxi' : (Request.xi n (a.xiArgs bytes)).eval = .ok (.success (ic,iw,ig,iss) data) := hxi
        rw [hx] at hxi'; cases hxi'
    | success state data =>
      obtain ⟨ic,iw,ig,iss⟩ := state
      cases keep : (iw == ∅) with
      | false =>
        have hs := theta_keep (a.context n bytes) hx keep
        have eqs := Except.ok.inj (hs.symm.trans he)
        have hl := congrArg (fun t => t.2.2.2.1.logSeries) eqs.symm
        change _ = _ ++ emitted kind root rr rt basePath (.theta (n+1) a) (Request.theta (n+1) a).eval tree
        rw [emitted,list_theta_keep hc ht hx keep,project_eq hl]
        exact child ic iw ig iss data hx
      | true =>
        have hs := theta_empty_restore (a.context n bytes) hx keep
        have eqs := Except.ok.inj (hs.symm.trans he)
        have hl := congrArg (fun t => t.2.2.2.1.logSeries) eqs.symm
        apply empty_logs (before := a.substate) (hl := hl)
        apply retained_empty
        intro p h
        obtain ⟨jc,jw,jg,jss,jdata,hxi,hk,h⟩ := (retained_theta_foreign hc ht p).mp h
        have e := hx.symm.trans hxi
        cases e
        rw [keep] at hk
        cases hk

theorem lambda_logs {kind : Contract} {root : Request} {rr : root.Outcome} {rt tree : EventTree}
    {n : Nat} {a : LambdaArgs} {basePath : EventTree.Address}
    (bytes : ByteArray) (hp : a.preimage = some bytes)
    (child : DoneLogs kind root rr rt basePath (.xi n (a.xiArgs bytes))
      (Request.xi n (a.xiArgs bytes)).eval tree) :
    DoneLogs kind root rr rt basePath (.lambda (n+1) a) (Request.lambda (n+1) a).eval tree := by
  intro target cr w g ss z out hr
  cases hx : (Request.xi n (a.xiArgs bytes)).eval with
  | error err =>
    have empty : retainedList kind (.lambda (n+1) a) (Request.lambda (n+1) a).eval tree = [] := by
      apply retained_empty
      intro p h
      obtain ⟨ic,iw,ig,iss,data,hxi,hk,h⟩ := (retained_lambda hp p).mp h
      have e := hx.symm.trans hxi
      cases e
    obtain ⟨_,hcases⟩ := RecursiveLogEdges.lambda_context_logs (a.context n) hp hr
    rcases hcases with ⟨_,hl⟩ | ⟨ic,iw,ig,iss,data,hxi,_,_,_⟩
    · exact empty_logs empty hl
    · have hxi' : (Request.xi n (a.xiArgs bytes)).eval = .ok (.success (ic,iw,ig,iss) data) := hxi
      rw [hx] at hxi'; cases hxi'
  | ok result =>
    cases result with
    | revert ig data =>
      have empty : retainedList kind (.lambda (n+1) a) (Request.lambda (n+1) a).eval tree = [] := by
        apply retained_empty
        intro p h
        obtain ⟨ic,iw,ig,iss,data,hxi,hk,h⟩ := (retained_lambda hp p).mp h
        have e := hx.symm.trans hxi
        cases e
      obtain ⟨_,hcases⟩ := RecursiveLogEdges.lambda_context_logs (a.context n) hp hr
      rcases hcases with ⟨_,hl⟩ | ⟨ic,iw,ig,iss,data,hxi,_,_,_⟩
      · exact empty_logs empty hl
      · have hxi' : (Request.xi n (a.xiArgs bytes)).eval = .ok (.success (ic,iw,ig,iss) data) := hxi
        rw [hx] at hxi'; cases hxi'
    | success state data =>
      obtain ⟨ic,iw,ig,iss⟩ := state
      cases keep : (a.context n).depositFailure (CreationSettlement.address bytes) ig data with
      | false =>
        have hs := lambda_keep (a.context n) hp hx keep
        have eqs := Except.ok.inj (hs.symm.trans hr)
        have hl := congrArg (fun t => t.2.2.2.2.1.logSeries) eqs.symm
        change _ = _ ++ emitted kind root rr rt basePath (.lambda (n+1) a) (Request.lambda (n+1) a).eval tree
        rw [emitted,list_lambda_keep hp hx keep,project_eq hl]
        exact child ic iw ig iss data hx
      | true =>
        have hs := lambda_reject_restore (a.context n) hp hx keep
        have eqs := Except.ok.inj (hs.symm.trans hr)
        have hl := congrArg (fun t => t.2.2.2.2.1.logSeries) eqs.symm
        apply empty_logs (before := a.substate) (hl := hl)
        apply retained_empty
        intro p h
        obtain ⟨jc,jw,jg,jss,jdata,hxi,hk,h⟩ := (retained_lambda hp p).mp h
        have e := hx.symm.trans hxi
        cases e
        rw [keep] at hk
        cases hk


theorem xi_logs {kind : Contract} {root : Request} {rr : root.Outcome} {rt tree : EventTree}
    {n : Nat} {a : XiArgs} {basePath : EventTree.Address}
    (child : DoneLogs kind root rr rt basePath (.x n a.jumps a.entry)
      (Request.x n a.jumps a.entry).eval tree) :
    DoneLogs kind root rr rt basePath (.xi (n+1) a) (Request.xi (n+1) a).eval tree := by
  intro cr w g ss out hr
  obtain ⟨f,post,hf,hx,_,_,_,hl⟩ := RecursiveLogEdges.xi_success_logs a hr
  have hn : f=n := by omega
  subst f
  have h := child post out hx
  rw [project_eq hl] at h
  change _ = _ ++ emitted kind root rr rt basePath (.xi (n+1) a) (Request.xi (n+1) a).eval tree
  rw [emitted,list_xi_keep hx]
  exact h

theorem step_theta_logs {kind : Contract} {root : Request} {rr : root.Outcome} {rt tree : EventTree}
    {fuel innerFuel : Nat} {a : StepArgs} {b : ThetaArgs} {basePath : EventTree.Address}
    (hc : StepChild fuel a (some (.theta innerFuel b)))
    (child : DoneLogs kind root rr rt basePath (.theta innerFuel b) (Request.theta innerFuel b).eval tree) :
    DoneLogs kind root rr rt basePath (.step fuel a) (Request.step fuel a).eval tree := by
  intro post hr
  obtain ⟨cr,w,g,ss,z,out,he,_,hl,_⟩ := RecursiveLogEdges.theta_returned hc hr
  rw [emitted,retained_congr (retained_step hc hr),project_eq hl,
    ← project_eq (JournalLogInputs.selected_theta_input hc)]
  exact child cr w g ss z out he

theorem step_lambda_logs {kind : Contract} {root : Request} {rr : root.Outcome} {rt tree : EventTree}
    {fuel innerFuel : Nat} {a : StepArgs} {b : LambdaArgs} {basePath : EventTree.Address}
    (hc : StepChild fuel a (some (.lambda innerFuel b)))
    (returned : ∃ r, (Request.lambda innerFuel b).eval = .ok r)
    (child : DoneLogs kind root rr rt basePath (.lambda innerFuel b) (Request.lambda innerFuel b).eval tree) :
    DoneLogs kind root rr rt basePath (.step fuel a) (Request.step fuel a).eval tree := by
  intro post hr
  obtain ⟨⟨target,cr,w,g,ss,z,out⟩,he⟩ := returned
  have hl := (RecursiveLogEdges.lambda_returned hc he hr).2.1
  change _ = _ ++ emitted kind root rr rt basePath (.step fuel a) (Request.step fuel a).eval tree
  rw [emitted,retained_congr (retained_step hc hr),project_eq hl,
    ← project_eq (JournalLogInputs.selected_lambda_input hc)]
  exact child target cr w g ss z out he

theorem occupied_logs {kind : Contract} {root : Request} {rr : root.Outcome} {rt tree : EventTree}
    {fuel : Nat} {a : LambdaArgs} {basePath : EventTree.Address}
    (bytes : ByteArray) (hp : a.preimage = some bytes)
    (ht : CreationSettlement.address bytes = address kind)
    (hc : JournalInvariant.CodeAt kind a.world) :
    DoneLogs kind root rr rt basePath (.lambda (fuel+1) a) (Request.lambda (fuel+1) a).eval tree := by
  intro target cr w g ss z out hr
  obtain ⟨_,hcases⟩ := RecursiveLogEdges.lambda_context_logs (a.context fuel) hp hr
  rcases hcases with ⟨_,hl⟩ | ⟨ic,iw,ig,iss,data,hx,_,_,_⟩
  · apply empty_logs (before := a.substate) (hl := hl)
    apply retained_empty
    intro p h
    obtain ⟨ic,iw,ig,iss,data,hx,_⟩ := (retained_lambda hp p).mp h
    exact CreationCollisionScope.no_success hc ht hx
  · exact False.elim (CreationCollisionScope.no_success hc ht hx)

theorem extract_at {kind : Contract} {root : Request} {rootResult : root.Outcome}
    {rootTree : EventTree} {q : Request} {result : q.Outcome} {tree : EventTree}
    (cert : Cert q result tree) :
    ∀ (budget : Nat), budget+tree.count < 2^128 → Ready kind budget q →
      Every CallInput q result tree → Every NoOutOfFuel q result tree →
      ∀ path, RequestAt root rootResult rootTree path q result →
        DoneLogs kind root rootResult rootTree path q result tree := by
  induction cert with
  | xZero => intros; simp [DoneLogs]
  | xGuardError => intros; simp [DoneLogs]
  | xStepError => intros; simp [DoneLogs]
  | xRevert =>
    intro budget hb ready inputs safe path outer post out he
    cases he
  | xiZero => intros; simp [DoneLogs]
  | thetaZero => intros; simp [DoneLogs]
  | lambdaZero => intros; simp [DoneLogs]
  | @xNext n cost vj pre mid post result child next hz hs hh ht ihs iht =>
    intro budget hb ready inputs safe path outer
    have ls := RequestAt.xNextChild hz hs hh ht (.here hs)
    have lt := RequestAt.xNextTail hz hs hh ht (.here ht)
    have hbs : budget+child.count < 2^128 := by simp only [EventTree.count] at hb; omega
    have ds := ihs budget hbs ready (inputs.descendant ls) (safe.descendant ls)
      _ (RequestAt.compose outer ls)
    have js := JournalExecution.preserves hs budget hbs ready (inputs.descendant ls) (safe.descendant ls)
    obtain ⟨hj,he⟩ := js post rfl
    let mark := if decide (FrameEvents.Marked pre) then 1 else 0
    have heq : budget + (EventTree.step (decide (FrameEvents.Marked pre)) child next).count =
        (budget+child.count+mark)+next.count := by simp only [EventTree.count,mark]; omega
    have hbn : (budget+child.count+mark)+next.count < 2^128 := by rw [←heq]; exact hb
    have rn : Ready kind (budget+child.count+mark) (.x n vj post) :=
      ⟨Journal.mono hj (Nat.le_add_right _ _),by rw [he]; exact ready.2⟩
    have dn := iht _ hbn rn (inputs.descendant lt) (safe.descendant lt)
      _ (RequestAt.compose outer lt)
    intro final out hr
    subst result
    have first := ds post rfl
    have second := dn final out rfl
    change _ = _ ++ emitted kind root rootResult rootTree path _ _ _
    rw [second,first,List.append_assoc]
    congr 1
    simp [emitted,list_xNext hz hs hh ht,List.flatMap_map,EventTree.extend,List.append_assoc]
  | @xHalt n cost vj pre mid post out child hz hs hh hn ihs =>
    intro budget hb ready inputs safe path outer
    have loc := RequestAt.xHalt hz hs hh hn (.here hs)
    have hbs : budget+child.count < 2^128 := by simp only [EventTree.count] at hb; omega
    have ds := ihs budget hbs ready (inputs.descendant loc) (safe.descendant loc)
      _ (RequestAt.compose outer loc)
    intro final data he
    cases he
    have h := ds post rfl
    change _ = _ ++ emitted kind root rootResult rootTree path _ _ _
    rw [h]
    congr 1
    simp [emitted,list_xHalt hz hs hh hn,List.flatMap_map,EventTree.extend,List.append_assoc]
  | @xi n a tree body ih =>
    intro budget hb ready inputs safe path outer
    have loc := RequestAt.xi body (.here body)
    exact xi_logs (ih budget hb ready (inputs.descendant loc) (safe.descendant loc)
      _ (by simpa using RequestAt.compose outer loc))
  | @thetaPrecompile n a target hc =>
    intro budget hb ready inputs safe path outer cr world gas ss z out hr
    apply empty_logs (hl := JournalLogInputs.precompile_logs hc hr)
    have hne : a.target ≠ address kind := by
      intro ht
      have hcode := (ready.2 ht).1
      rw [hc] at hcode
      cases hcode
    apply retained_empty
    rintro p ⟨f,b,r,h⟩
    generalize he : (Request.theta (n+1) a).eval = rr at h
    cases h with
    | here hp ht => exact hne ht
    | thetaCode hf hc' => rw [hc] at hc'; cases hc'
  | @thetaCode n a bytes tree hc body ih =>
    intro budget hb ready inputs safe path outer
    by_cases ht : a.target = address kind
    · have fit := (inputs.root (.thetaCode bytes hc body)).1
      exact protected_logs (.thetaCode bytes hc body) ready (by omega) fit ht outer
    · have loc := RequestAt.thetaCode bytes hc body (.here body)
      exact theta_logs bytes hc ht (ih budget hb (JournalExecution.theta_entry bytes ready ht)
        (inputs.descendant loc) (safe.descendant loc) _ (by simpa using RequestAt.compose outer loc))
  | @lambdaNoPreimage n a hp =>
    intros
    obtain ⟨bytes,hb⟩ := CreationPreimageTotal.lambdaArgs_total a
    rw [hp] at hb
    cases hb
  | @lambdaInit n a bytes tree hp body ih =>
    intro budget hb ready inputs safe path outer
    by_cases ht : CreationSettlement.address bytes = address kind
    · exact occupied_logs bytes hp ht ready.1.1
    · have loc := RequestAt.lambdaInit bytes hp body (.here body)
      exact lambda_logs bytes hp (ih budget hb (JournalExecution.lambda_entry bytes ready ht)
        (inputs.descendant loc) (safe.descendant loc) _ (by simpa using RequestAt.compose outer loc))
  | @stepNone n a hc =>
    intro budget hb ready inputs safe path outer post hr
    simp only [emitted,retained_step_none hc,List.flatMap_nil,List.append_nil]
    by_cases ho : OrdinaryGas.Ordinary a.op
    · exact ProtectedLogFrame.accepted_other_owner ho ready.2 a.guard hr
    · exact project_eq (RecursiveLogEdges.denied_recursive hc ho hr).2.1
  | @stepChild n a q tree hc body ih =>
    intro budget hb ready inputs safe path outer
    have loc := RequestAt.stepChild hc body (.here body)
    have child := ih budget hb (JournalExecution.child_ready hc ready)
      (inputs.descendant loc) (safe.descendant loc) _ (RequestAt.compose outer loc)
    simp only [List.append_nil] at child
    rcases JournalChildEntry.selected_kind hc with ⟨f,b,hq⟩ | ⟨f,b,hq⟩
    · subst q
      exact step_theta_logs hc child
    · subst q
      exact step_lambda_logs hc (NestedEvents.lambda_returns safe loc) child

/-- Numeric root adequacy supplies all-node error exclusion. No per-child path
or intermediate invariant is assumed, and the exact retained list is explicit. -/
theorem extract {kind : Contract} {q : Request} {result : q.Outcome} {tree : EventTree}
    (cert : Cert q result tree) (budget : Nat) (hb : budget+tree.count < 2^128)
    (ready : Ready kind budget q) (inputs : Every CallInput q result tree)
    (adequate : FuelAdequacy.Adequate q) : DoneLogs kind q result tree [] q result tree :=
  extract_at cert budget hb ready inputs (FuelAdequacy.every_no_out_of_fuel cert adequate) [] (.here cert)

#print axioms contribution_identity
#print axioms emitted_replay
#print axioms protected_logs
#print axioms theta_logs
#print axioms lambda_logs
#print axioms extract_at
#print axioms extract
end Eip8282.Audit.Integrator.JournalCommittedLogs
