import Eip8282.Audit.Integrator.JournalCheckpoints
import Eip8282.Audit.Integrator.JournalChildEntry

/-! Root-scoped queue-world paths with an explicit list of retained actual
protected Theta occurrences. Frames preserve code/existence/storage only.
Existence of a path is not completeness or uniqueness of an independently
specified committed occurrence list, and is not committed-log preservation. -/
namespace Eip8282.Audit.Integrator.JournalWorldPaths
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open NestedEvents JournalExecution
open ReachableCalls (Contract address runtime Transition)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

structure Occurrence (kind : Contract) (root : Request) (result : root.Outcome) (tree : EventTree) where
  path : EventTree.Address
  fuel : Nat
  args : ThetaArgs
  before : World
  after : World
  transition : Transition kind before after
  positive : 0 < fuel
  context : transition.call = args.context (fuel-1) (runtime kind)
  located : ThetaAt root result tree path fuel args
    (.ok (transition.created,after,transition.gas,transition.substate,transition.success,transition.output))

inductive Path (kind : Contract) (root : Request) (result : root.Outcome) (tree : EventTree) :
    List (Occurrence kind root result tree) → World → World → Prop where
  | frame {before after : World}
      (h : CodeStorageFrame.Frame before after (address kind)) : Path kind root result tree [] before after
  | call (o : Occurrence kind root result tree) :
      Path kind root result tree [o] o.before o.after
  | trans {first second : List (Occurrence kind root result tree)} {before middle after : World}
      (left : Path kind root result tree first before middle)
      (right : Path kind root result tree second middle after) :
      Path kind root result tree (first ++ second) before after

theorem Path.refl (kind : Contract) (root : Request) (result : root.Outcome) (tree : EventTree) (world : World) :
    Path kind root result tree [] world world := .frame (CodeStorageFrame.refl _ _)

def Reaches (kind : Contract) (root : Request) (result : root.Outcome) (tree : EventTree)
    (before after : World) : Prop := ∃ occurrences, Path kind root result tree occurrences before after

theorem Reaches.refl (kind : Contract) (root : Request) (result : root.Outcome) (tree : EventTree) (world : World) :
    Reaches kind root result tree world world := ⟨[],Path.refl kind root result tree world⟩

theorem Reaches.frame {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    {before after : World} (h : CodeStorageFrame.Frame before after (address kind)) :
    Reaches kind root result tree before after := ⟨[],.frame h⟩

theorem Reaches.trans {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    {before middle after : World} (h₁ : Reaches kind root result tree before middle)
    (h₂ : Reaches kind root result tree middle after) : Reaches kind root result tree before after := by
  obtain ⟨first,hf⟩ := h₁
  obtain ⟨second,hs⟩ := h₂
  exact ⟨first++second,.trans hf hs⟩

def DonePath (kind : Contract) (root : Request) (rootResult : root.Outcome) (rootTree : EventTree) :
    (q : Request) → q.Outcome → Prop
  | .x _ _ pre, r => ∀ post out, r = .ok (.success post out) →
      Reaches kind root rootResult rootTree pre.accountMap post.accountMap
  | .xi _ a, r => ∀ cr world gas ss out, r = .ok (.success (cr,world,gas,ss) out) →
      Reaches kind root rootResult rootTree a.world world
  | .theta _ a, r => ∀ cr world gas ss z out, r = .ok (cr,world,gas,ss,z,out) →
      Reaches kind root rootResult rootTree a.world world
  | .lambda _ a, r => ∀ target cr world gas ss z out, r = .ok (target,cr,world,gas,ss,z,out) →
      Reaches kind root rootResult rootTree a.world world
  | .step _ a, r => ∀ post, r = .ok post →
      Reaches kind root rootResult rootTree a.pre.accountMap post.accountMap

theorem protected_path {kind : Contract} {root : Request} {rootResult : root.Outcome} {rootTree : EventTree}
    {n : Nat} {a : ThetaArgs} {path : EventTree.Address} {budget : Nat}
    (ready : Ready kind budget (.theta (n+1) a)) (ht : a.target = address kind)
    (loc : RequestAt root rootResult rootTree path (.theta (n+1) a) (Request.theta (n+1) a).eval) :
    DonePath kind root rootResult rootTree (.theta (n+1) a) (Request.theta (n+1) a).eval := by
  intro cr world gas ss z out hr
  have hc := (ready.2 ht).1
  let t : Transition kind a.world world :=
    { call := a.context n (runtime kind),
      pinned := CallOwnerCoherence.pinned n ready.1.1.1 ready.2 ht,
      pre := rfl, created := cr, gas := gas, substate := ss, success := z, output := out,
      executed := (thetaArgs_result a n (runtime kind) hc).symm.trans hr }
  have located : ThetaAt root rootResult rootTree path (n+1) a (.ok (cr,world,gas,ss,z,out)) := by
    rw [hr] at loc
    exact RequestAt.theta loc
  let occurrence : Occurrence kind root rootResult rootTree :=
    { path := path, fuel := n+1, args := a, before := a.world, after := world,
      transition := t, positive := Nat.succ_pos _, context := rfl, located := located }
  exact ⟨[occurrence],.call occurrence⟩

theorem ordinary_path {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    {fuel : Nat} {a : StepArgs} (ho : OrdinaryGas.Ordinary a.op)
    (hne : a.pre.executionEnv.codeOwner ≠ address kind) :
    DonePath kind root result tree (.step fuel a) (Request.step fuel a).eval := by
  intro post hr
  exact Reaches.frame (CodeStorageFrame.of_preserved
    (OrdinaryWorldFrame.accepted_step_preserved ho hne a.guard hr).1)

theorem denied_path {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    {fuel : Nat} {a : StepArgs} (hc : StepChild fuel a none) (ho : ¬ OrdinaryGas.Ordinary a.op) :
    DonePath kind root result tree (.step fuel a) (Request.step fuel a).eval := by
  intro post hr
  obtain ⟨hw,_,_⟩ := RecursiveJournalEdges.denied_recursive hc ho hr
  rw [hw]
  exact Reaches.refl _ _ _ _ _

theorem step_theta_path {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    {fuel innerFuel : Nat} {a : StepArgs} {b : ThetaArgs}
    (hc : StepChild fuel a (some (.theta innerFuel b)))
    (child : DonePath kind root result tree (.theta innerFuel b) (Request.theta innerFuel b).eval) :
    DonePath kind root result tree (.step fuel a) (Request.step fuel a).eval := by
  intro post hr
  obtain ⟨cr,w,g,ss,z,out,he,hw,_,_⟩ := RecursiveJournalEdges.theta_returned hc hr
  have h := child cr w g ss z out he
  rw [(JournalChildEntry.selected_theta_input hc).1] at h
  rw [hw]
  exact h

theorem step_lambda_path {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    {fuel innerFuel : Nat} {a : StepArgs} {b : LambdaArgs}
    (hc : StepChild fuel a (some (.lambda innerFuel b)))
    (hne : a.pre.executionEnv.codeOwner ≠ address kind)
    (returned : ∃ r, (Request.lambda innerFuel b).eval = .ok r)
    (child : DonePath kind root result tree (.lambda innerFuel b) (Request.lambda innerFuel b).eval) :
    DonePath kind root result tree (.step fuel a) (Request.step fuel a).eval := by
  intro post hr
  obtain ⟨⟨target,cr,w,g,ss,z,out⟩,he⟩ := returned
  obtain ⟨hw,_,_⟩ := RecursiveJournalEdges.lambda_returned hc he hr
  have h := child target cr w g ss z out he
  have hf := (JournalChildEntry.selected_lambda_input hc (address kind) hne).1
  rw [hw]
  exact (Reaches.frame hf).trans h

theorem xi_path {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    {fuel : Nat} {a : XiArgs}
    (child : DonePath kind root result tree (.x fuel a.jumps a.entry) (Request.x fuel a.jumps a.entry).eval) :
    DonePath kind root result tree (.xi (fuel+1) a) (Request.xi (fuel+1) a).eval := by
  intro cr w g ss out hr
  obtain ⟨n,post,hf,he,_,hw,_,_⟩ := WrapperJournalEdges.xi_success a hr
  have hn : n = fuel := by omega
  subst n
  have h := child post out he
  rw [hw] at h
  exact h

theorem theta_path {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    {fuel : Nat} {a : ThetaArgs} (bytes : ByteArray) (hc : a.code = .Code bytes)
    (child : DonePath kind root result tree (.xi fuel (a.xiArgs bytes)) (Request.xi fuel (a.xiArgs bytes)).eval) :
    DonePath kind root result tree (.theta (fuel+1) a) (Request.theta (fuel+1) a).eval := by
  intro cr w g ss z out hr
  have he := (thetaArgs_result a fuel bytes hc).symm.trans hr
  rcases WrapperJournalEdges.theta_code_world (a.context fuel bytes) he with
    ⟨hw,_⟩ | ⟨ic,iw,ig,iss,data,hx,hw,_⟩
  · rw [hw]
    exact Reaches.refl _ _ _ _ _
  · have h := child ic iw ig iss data hx
    rw [hw]
    exact (Reaches.frame (CodeStorageFrame.entry (a.context fuel bytes) (address kind))).trans h

theorem lambda_path {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    {fuel : Nat} {a : LambdaArgs} (bytes : ByteArray) (hp : a.preimage = some bytes)
    (ht : CreationSettlement.address bytes ≠ address kind)
    (child : DonePath kind root result tree (.xi fuel (a.xiArgs bytes)) (Request.xi fuel (a.xiArgs bytes)).eval) :
    DonePath kind root result tree (.lambda (fuel+1) a) (Request.lambda (fuel+1) a).eval := by
  intro target cr w g ss z out hr
  obtain ⟨_,hcases⟩ := WrapperJournalEdges.lambda_context_world (a.context fuel) hp hr
  rcases hcases with ⟨hw,_⟩ | ⟨ic,iw,ig,iss,data,hx,hw,_⟩
  · rw [hw]
    exact Reaches.refl _ _ _ _ _
  · have h := child ic iw ig iss data hx
    rw [hw]
    exact ((Reaches.frame (CreationStorageFrame.entry_frame (a.context fuel)
      (CreationSettlement.address bytes) (address kind))).trans h).trans
      (Reaches.frame (CreationStorageFrame.install_away_frame iw
        (CreationSettlement.address bytes) (address kind) data ht))

theorem occupied_path {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    {fuel : Nat} {a : LambdaArgs} (bytes : ByteArray) (hp : a.preimage = some bytes)
    (ht : CreationSettlement.address bytes = address kind)
    (hc : JournalInvariant.CodeAt kind a.world) :
    DonePath kind root result tree (.lambda (fuel+1) a) (Request.lambda (fuel+1) a).eval := by
  intro target cr w g ss z out hr
  obtain ⟨_,hcases⟩ := WrapperJournalEdges.lambda_context_world (a.context fuel) hp hr
  rcases hcases with ⟨hw,_⟩ | ⟨ic,iw,ig,iss,data,hx,_,_⟩
  · rw [hw]
    exact Reaches.refl _ _ _ _ _
  · exact False.elim (CreationCollisionScope.no_success hc ht hx)

/-- Recursive extraction follows actual return/restore choices. Protected
calls are atomic list entries; rejected wrapper subtrees contribute no retained
entry. The resource budget still counts those rejected subtrees elsewhere. -/
theorem extract_at {kind : Contract} {root : Request} {rootResult : root.Outcome}
    {rootTree : EventTree} {q : Request} {result : q.Outcome} {tree : EventTree}
    (cert : Cert q result tree) :
    ∀ (budget : Nat), budget+tree.count < 2^128 → Ready kind budget q →
      Every CallInput q result tree → Every NoOutOfFuel q result tree →
      ∀ path, RequestAt root rootResult rootTree path q result →
        DonePath kind root rootResult rootTree q result := by
  induction cert with
  | xZero => intros; simp [DonePath]
  | xGuardError => intros; simp [DonePath]
  | xStepError => intros; simp [DonePath]
  | xRevert =>
    intro budget hb ready inputs safe path outer post out he
    cases he
  | xiZero => intros; simp [DonePath]
  | thetaZero => intros; simp [DonePath]
  | lambdaZero => intros; simp [DonePath]
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
    exact (ds post rfl).trans (dn final out hr)
  | @xHalt n cost vj pre mid post out child hz hs hh hn ihs =>
    intro budget hb ready inputs safe path outer
    have loc := RequestAt.xHalt hz hs hh hn (.here hs)
    have hbs : budget+child.count < 2^128 := by simp only [EventTree.count] at hb; omega
    have ds := ihs budget hbs ready (inputs.descendant loc) (safe.descendant loc)
      _ (RequestAt.compose outer loc)
    intro final data he
    cases he
    exact ds post rfl
  | @xi n a tree body ih =>
    intro budget hb ready inputs safe path outer
    have loc := RequestAt.xi body (.here body)
    exact xi_path (ih budget hb ready (inputs.descendant loc) (safe.descendant loc)
      _ (RequestAt.compose outer loc))
  | @thetaPrecompile n a target hc =>
    intro budget hb ready inputs safe path outer cr world gas ss z out hr
    exact Reaches.frame (PrecompileWorldFrame.theta_frame hc hr (address kind))
  | @thetaCode n a bytes tree hc body ih =>
    intro budget hb ready inputs safe path outer
    by_cases ht : a.target = address kind
    · exact protected_path ready ht outer
    · have loc := RequestAt.thetaCode bytes hc body (.here body)
      exact theta_path bytes hc (ih budget hb (JournalExecution.theta_entry bytes ready ht)
        (inputs.descendant loc) (safe.descendant loc) _ (RequestAt.compose outer loc))
  | @lambdaNoPreimage n a hp =>
    intros
    obtain ⟨bytes,hb⟩ := CreationPreimageTotal.lambdaArgs_total a
    rw [hp] at hb
    cases hb
  | @lambdaInit n a bytes tree hp body ih =>
    intro budget hb ready inputs safe path outer
    by_cases ht : CreationSettlement.address bytes = address kind
    · exact occupied_path bytes hp ht ready.1.1
    · have loc := RequestAt.lambdaInit bytes hp body (.here body)
      exact lambda_path bytes hp ht (ih budget hb (JournalExecution.lambda_entry bytes ready ht)
        (inputs.descendant loc) (safe.descendant loc) _ (RequestAt.compose outer loc))
  | @stepNone n a hc =>
    intro budget hb ready inputs safe path outer
    by_cases ho : OrdinaryGas.Ordinary a.op
    · exact ordinary_path ho ready.2
    · exact denied_path hc ho
  | @stepChild n a q tree hc body ih =>
    intro budget hb ready inputs safe path outer
    have loc := RequestAt.stepChild hc body (.here body)
    have child := ih budget hb (JournalExecution.child_ready hc ready)
      (inputs.descendant loc) (safe.descendant loc) _ (RequestAt.compose outer loc)
    rcases JournalChildEntry.selected_kind hc with ⟨f,b,hq⟩ | ⟨f,b,hq⟩
    · subst q
      exact step_theta_path hc child
    · subst q
      exact step_lambda_path hc ready.2 (NestedEvents.lambda_returns safe loc) child

/-- At the actual root, all-node error exclusion is derived from concrete fuel.
Only the initial journal and independent input/resource policy are supplied. -/
theorem extract {kind : Contract} {q : Request} {result : q.Outcome} {tree : EventTree}
    (cert : Cert q result tree) (budget : Nat) (hb : budget+tree.count < 2^128)
    (ready : Ready kind budget q) (inputs : Every CallInput q result tree)
    (adequate : FuelAdequacy.Adequate q) : DonePath kind q result tree q result :=
  extract_at cert budget hb ready inputs (FuelAdequacy.every_no_out_of_fuel cert adequate) [] (.here cert)

#print axioms protected_path
#print axioms theta_path
#print axioms lambda_path
#print axioms occupied_path
#print axioms extract_at
#print axioms extract
end Eip8282.Audit.Integrator.JournalWorldPaths
