import Eip8282.Audit.Integrator.JournalRetainedCalls

/-! Exact world-path replay of the independent surviving-call enumeration.
The list records actual protected calls, including returned failures; it is not
a list of successful submissions or a theorem about surviving log payloads. -/
namespace Eip8282.Audit.Integrator.JournalRetainedPaths
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open NestedEvents JournalExecution JournalWorldPaths JournalRetainedCalls
open ReachableCalls (Contract address runtime Transition)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- The local canonical enumeration is transported to its actual root basePath. -/
def ExactReaches (kind : Contract) (root : Request) (rootResult : root.Outcome)
    (rootTree : EventTree) (basePath : EventTree.Address)
    (q : Request) (result : q.Outcome) (tree : EventTree) (before after : World) : Prop :=
  ∃ occurrences, Path kind root rootResult rootTree occurrences before after ∧
    occurrences.map (·.path) = (retainedList kind q result tree).map (basePath ++ ·)

def ExactDone (kind : Contract) (root : Request) (rootResult : root.Outcome)
    (rootTree : EventTree) (basePath : EventTree.Address)
    (q : Request) (result : q.Outcome) (tree : EventTree) : Prop :=
  match q, result with
  | .x _ _ pre, r => ∀ post out, r = .ok (.success post out) →
      ExactReaches kind root rootResult rootTree basePath q result tree pre.accountMap post.accountMap
  | .xi _ a, r => ∀ cr world gas ss out, r = .ok (.success (cr,world,gas,ss) out) →
      ExactReaches kind root rootResult rootTree basePath q result tree a.world world
  | .theta _ a, r => ∀ cr world gas ss z out, r = .ok (cr,world,gas,ss,z,out) →
      ExactReaches kind root rootResult rootTree basePath q result tree a.world world
  | .lambda _ a, r => ∀ target cr world gas ss z out, r = .ok (target,cr,world,gas,ss,z,out) →
      ExactReaches kind root rootResult rootTree basePath q result tree a.world world
  | .step _ a, r => ∀ post, r = .ok post →
      ExactReaches kind root rootResult rootTree basePath q result tree a.pre.accountMap post.accountMap

theorem retained_congr {kind : Contract} {q₁ q₂ : Request}
    {r₁ : q₁.Outcome} {r₂ : q₂.Outcome} {tree : EventTree}
    (h : ∀ p, Retained kind q₁ r₁ tree p ↔ Retained kind q₂ r₂ tree p) :
    retainedList kind q₁ r₁ tree = retainedList kind q₂ r₂ tree := by
  classical
  unfold retainedList
  congr 1
  funext p
  exact congrArg (fun P : Prop => decide P) (propext (h p))

theorem retained_empty {kind : Contract} {q : Request} {r : q.Outcome} {tree : EventTree}
    (h : ∀ p, ¬ Retained kind q r tree p) : retainedList kind q r tree = [] := by
  classical
  simp only [retainedList, List.filter_eq_nil_iff]
  intro p hp
  simpa using h p

theorem exact_frame {kind : Contract} {root q : Request} {rr : root.Outcome}
    {r : q.Outcome} {rt tree : EventTree} {basePath : EventTree.Address} {before after : World}
    (frame : CodeStorageFrame.Frame before after (address kind))
    (empty : retainedList kind q r tree = []) :
    ExactReaches kind root rr rt basePath q r tree before after := by
  exact ⟨[],.frame frame,by simp [empty]⟩

theorem retained_theta_atomic {kind : Contract} {n : Nat} {a : ThetaArgs}
    {tree : EventTree} {cr : Created} {world : World} {gas : UInt256}
    {ss : Substate} {z : Bool} {out : ByteArray}
    (cert : Cert (.theta (n+1) a) (.ok (cr,world,gas,ss,z,out)) tree)
    (ht : a.target = address kind) (p : EventTree.Address) :
    Retained kind (.theta (n+1) a) (.ok (cr,world,gas,ss,z,out)) tree p ↔ p=[] := by
  constructor
  · rintro ⟨f,b,r,h⟩
    generalize he : (Except.ok (cr,world,gas,ss,z,out) : ThetaResult) = rr at h
    cases h with
    | here => rfl
    | thetaCode hf => exact False.elim (hf ht)
  · intro hp
    subst p
    exact ⟨n+1,a,_,.here (Nat.succ_pos _) ht cert⟩

theorem retained_theta_foreign {kind : Contract} {n : Nat} {a : ThetaArgs}
    {bytes : ByteArray} {tree : EventTree} (hc : a.code = .Code bytes)
    (ht : a.target ≠ address kind) (p : EventTree.Address) :
    Retained kind (.theta (n+1) a) (Request.theta (n+1) a).eval tree p ↔
      ∃ cr world gas ss out,
        (Request.xi n (a.xiArgs bytes)).eval = .ok (.success (cr,world,gas,ss) out) ∧
        (world == ∅) = false ∧
        Retained kind (.xi n (a.xiArgs bytes)) (Request.xi n (a.xiArgs bytes)).eval tree p := by
  constructor
  · rintro ⟨f,b,r,h⟩
    generalize he : (Request.theta (n+1) a).eval = rr at h
    cases h with
    | here hp target => exact False.elim (ht target)
    | thetaCode hf hc' body hx keep loc =>
      rw [hc] at hc'
      cases hc'
      exact ⟨_,_,_,_,_,hx,keep,_,_,_,loc⟩
  · rintro ⟨cr,w,g,ss,out,hx,keep,f,b,r,loc⟩
    exact ⟨f,b,r,.thetaCode ht hc loc.actual.cert_top hx keep loc⟩

theorem retained_lambda {kind : Contract} {n : Nat} {a : LambdaArgs}
    {bytes : ByteArray} {tree : EventTree} (hp : a.preimage = some bytes)
    (p : EventTree.Address) :
    Retained kind (.lambda (n+1) a) (Request.lambda (n+1) a).eval tree p ↔
      ∃ cr world gas ss out,
        (Request.xi n (a.xiArgs bytes)).eval = .ok (.success (cr,world,gas,ss) out) ∧
        (a.context n).depositFailure (CreationSettlement.address bytes) gas out = false ∧
        Retained kind (.xi n (a.xiArgs bytes)) (Request.xi n (a.xiArgs bytes)).eval tree p := by
  constructor
  · rintro ⟨f,b,r,h⟩
    cases h with
    | lambdaInit hp' body hx keep loc =>
      rw [hp] at hp'
      cases hp'
      exact ⟨_,_,_,_,_,hx,keep,_,_,_,loc⟩
  · rintro ⟨cr,w,g,ss,out,hx,keep,f,b,r,loc⟩
    exact ⟨f,b,r,.lambdaInit hp loc.actual.cert_top hx keep loc⟩

theorem retained_xi {kind : Contract} {n : Nat} {a : XiArgs}
    {tree : EventTree} (p : EventTree.Address) :
    Retained kind (.xi (n+1) a) (Request.xi (n+1) a).eval tree p ↔
      ∃ post out, (Request.x n a.jumps a.entry).eval = .ok (.success post out) ∧
        Retained kind (.x n a.jumps a.entry) (Request.x n a.jumps a.entry).eval tree p := by
  constructor
  · rintro ⟨f,b,r,h⟩
    cases h with
    | xi body hx loc => exact ⟨_,_,hx,_,_,_,loc⟩
  · rintro ⟨post,out,hx,f,b,r,loc⟩
    exact ⟨f,b,r,.xi loc.actual.cert_top hx loc⟩

theorem retained_step {kind : Contract} {n : Nat} {a : StepArgs}
    {q : Request} {tree : EventTree} {post : EVM.State}
    (hc : StepChild n a (some q)) (hs : (Request.step n a).eval = .ok post)
    (p : EventTree.Address) :
    Retained kind (.step n a) (Request.step n a).eval tree p ↔
      Retained kind q q.eval tree p := by
  constructor
  · rintro ⟨f,b,r,h⟩
    cases h with
    | stepChild hc' body hs' loc =>
      have he := stepChild_unique hc hc'
      cases he
      exact ⟨_,_,_,loc⟩
  · rintro ⟨f,b,r,loc⟩
    exact ⟨f,b,r,.stepChild hc loc.actual.cert_top hs loc⟩

theorem retained_step_none {kind : Contract} {n : Nat} {a : StepArgs}
    {tree : EventTree} (hc : StepChild n a none) :
    retainedList kind (.step n a) (Request.step n a).eval tree = [] := by
  apply retained_empty
  rintro p ⟨f,b,r,h⟩
  cases h with
  | stepChild hc' => cases stepChild_unique hc hc'

theorem retained_xNext {kind : Contract} {n cost : Nat} {vj : Array UInt256}
    {pre mid post final : EVM.State} {out : ByteArray} {child next : EventTree}
    (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
    (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
    (hh : H post.toMachineState (decodeAt pre).1 = none)
    (tail : Cert (.x n vj post) (.ok (.success final out)) next)
    (p : EventTree.Address) :
    Retained kind (.x (n+1) vj pre) (.ok (.success final out))
      (.step (decide (FrameEvents.Marked pre)) child next) p ↔
      (∃ t, p=false::t ∧ Retained kind (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child t) ∨
      (∃ t, p=true::t ∧ Retained kind (.x n vj post) (.ok (.success final out)) next t) := by
  constructor
  · rintro ⟨f,b,r,h⟩
    cases h with
    | xNextChild hz' hs' hh' tail' loc =>
      have hg := hz.symm.trans hz'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl,rfl⟩ := hg
      have he := (sound hs).symm.trans (sound hs')
      cases he
      exact Or.inl ⟨_,rfl,_,_,_,loc⟩
    | xNextTail hz' hs' hh' tail' loc =>
      have hg := hz.symm.trans hz'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl,rfl⟩ := hg
      have he := (sound hs).symm.trans (sound hs')
      cases he
      exact Or.inr ⟨_,rfl,_,_,_,loc⟩
    | xHalt hz' hs' hh' hn loc =>
      have hg := hz.symm.trans hz'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl,rfl⟩ := hg
      have he := (sound hs).symm.trans (sound hs')
      cases he
      rw [hh] at hh'
      cases hh'
  · rintro (⟨t,rfl,f,b,r,loc⟩ | ⟨t,rfl,f,b,r,loc⟩)
    · exact ⟨f,b,r,.xNextChild hz hs hh tail loc⟩
    · exact ⟨f,b,r,.xNextTail hz hs hh tail loc⟩

theorem retained_fork {kind : Contract} {q left right : Request}
    {r : q.Outcome} {lr : left.Outcome} {rr : right.Outcome}
    {mark : Bool} {child next : EventTree}
    (hroot : ¬ Retained kind q r (.step mark child next) [])
    (hl : ∀ p, Retained kind q r (.step mark child next) (false::p) ↔ Retained kind left lr child p)
    (hr : ∀ p, Retained kind q r (.step mark child next) (true::p) ↔ Retained kind right rr next p) :
    retainedList kind q r (.step mark child next) =
      (retainedList kind left lr child).map (EventTree.extend false) ++
      (retainedList kind right rr next).map (EventTree.extend true) := by
  classical
  simp [retainedList,nodePaths,List.filter_map,Function.comp_def,EventTree.extend,hroot,hl,hr]

theorem list_xNext {kind : Contract} {n cost : Nat} {vj : Array UInt256}
    {pre mid post final : EVM.State} {out : ByteArray} {child next : EventTree}
    (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
    (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
    (hh : H post.toMachineState (decodeAt pre).1 = none)
    (tail : Cert (.x n vj post) (.ok (.success final out)) next) :
    retainedList kind (.x (n+1) vj pre) (.ok (.success final out))
      (.step (decide (FrameEvents.Marked pre)) child next) =
      (retainedList kind (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child).map (EventTree.extend false) ++
      (retainedList kind (.x n vj post) (.ok (.success final out)) next).map (EventTree.extend true) := by
  apply retained_fork
  · simp [retained_xNext hz hs hh tail]
  · intro p; simp [retained_xNext hz hs hh tail]
  · intro p; simp [retained_xNext hz hs hh tail]


theorem retained_xHalt {kind : Contract} {n cost : Nat} {vj : Array UInt256}
    {pre mid post : EVM.State} {out : ByteArray} {child : EventTree}
    (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
    (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
    (hh : H post.toMachineState (decodeAt pre).1 = some out) (hn : (decodeAt pre).1 ≠ .REVERT)
    (p : EventTree.Address) :
    Retained kind (.x (n+1) vj pre) (.ok (.success post out))
      (.step (decide (FrameEvents.Marked pre)) child .done) p ↔
      ∃ t, p=false::t ∧ Retained kind (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child t := by
  constructor
  · rintro ⟨f,b,r,h⟩
    cases h with
    | xNextChild hz' hs' hh' tail' loc =>
      have hg := hz.symm.trans hz'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl,rfl⟩ := hg
      have he := (sound hs).symm.trans (sound hs')
      cases he
      rw [hh] at hh'; cases hh'
    | xNextTail hz' hs' hh' tail' loc =>
      have hg := hz.symm.trans hz'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl,rfl⟩ := hg
      have he := (sound hs).symm.trans (sound hs')
      cases he
      rw [hh] at hh'; cases hh'
    | xHalt hz' hs' hh' hn' loc =>
      have hg := hz.symm.trans hz'
      simp only [Except.ok.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl,rfl⟩ := hg
      exact ⟨_,rfl,_,_,_,loc⟩
  · rintro ⟨t,rfl,f,b,r,loc⟩
    exact ⟨f,b,r,.xHalt hz hs hh hn loc⟩

theorem list_xHalt {kind : Contract} {n cost : Nat} {vj : Array UInt256}
    {pre mid post : EVM.State} {out : ByteArray} {child : EventTree}
    (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
    (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
    (hh : H post.toMachineState (decodeAt pre).1 = some out) (hn : (decodeAt pre).1 ≠ .REVERT) :
    retainedList kind (.x (n+1) vj pre) (.ok (.success post out))
      (.step (decide (FrameEvents.Marked pre)) child .done) =
      (retainedList kind (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child).map (EventTree.extend false) := by
  classical
  simp [retainedList,nodePaths,List.filter_map,Function.comp_def,EventTree.extend,retained_xHalt hz hs hh hn]

theorem list_theta_atomic {kind : Contract} {n : Nat} {a : ThetaArgs}
    {tree : EventTree} {cr : Created} {world : World} {gas : UInt256}
    {ss : Substate} {z : Bool} {out : ByteArray}
    (cert : Cert (.theta (n+1) a) (.ok (cr,world,gas,ss,z,out)) tree)
    (ht : a.target = address kind) :
    retainedList kind (.theta (n+1) a) (.ok (cr,world,gas,ss,z,out)) tree = [[]] := by
  classical
  unfold retainedList
  simp_rw [retained_theta_atomic cert ht]
  cases tree <;> simp [nodePaths,List.filter_map,Function.comp_def,EventTree.extend]

theorem list_theta_keep {kind : Contract} {n : Nat} {a : ThetaArgs} {bytes : ByteArray}
    {tree : EventTree} {cr : Created} {world : World} {gas : UInt256} {ss : Substate} {out : ByteArray}
    (hc : a.code = .Code bytes) (ht : a.target ≠ address kind)
    (hx : (Request.xi n (a.xiArgs bytes)).eval = .ok (.success (cr,world,gas,ss) out))
    (keep : (world == ∅) = false) :
    retainedList kind (.theta (n+1) a) (Request.theta (n+1) a).eval tree =
      retainedList kind (.xi n (a.xiArgs bytes)) (Request.xi n (a.xiArgs bytes)).eval tree := by
  apply retained_congr
  intro p
  rw [retained_theta_foreign hc ht]
  constructor
  · rintro ⟨ic,iw,ig,iss,data,hxi,hk,h⟩; exact h
  · intro h; exact ⟨cr,world,gas,ss,out,hx,keep,h⟩

theorem list_lambda_keep {kind : Contract} {n : Nat} {a : LambdaArgs} {bytes : ByteArray}
    {tree : EventTree} {cr : Created} {world : World} {gas : UInt256} {ss : Substate} {out : ByteArray}
    (hp : a.preimage = some bytes)
    (hx : (Request.xi n (a.xiArgs bytes)).eval = .ok (.success (cr,world,gas,ss) out))
    (keep : (a.context n).depositFailure (CreationSettlement.address bytes) gas out = false) :
    retainedList kind (.lambda (n+1) a) (Request.lambda (n+1) a).eval tree =
      retainedList kind (.xi n (a.xiArgs bytes)) (Request.xi n (a.xiArgs bytes)).eval tree := by
  apply retained_congr
  intro p
  rw [retained_lambda hp]
  constructor
  · rintro ⟨ic,iw,ig,iss,data,hxi,hk,h⟩; exact h
  · intro h; exact ⟨cr,world,gas,ss,out,hx,keep,h⟩

theorem list_xi_keep {kind : Contract} {n : Nat} {a : XiArgs} {tree : EventTree}
    {post : EVM.State} {out : ByteArray}
    (hx : (Request.x n a.jumps a.entry).eval = .ok (.success post out)) :
    retainedList kind (.xi (n+1) a) (Request.xi (n+1) a).eval tree =
      retainedList kind (.x n a.jumps a.entry) (Request.x n a.jumps a.entry).eval tree := by
  apply retained_congr
  intro p
  rw [retained_xi]
  constructor
  · rintro ⟨s,data,he,h⟩; exact h
  · intro h; exact ⟨post,out,hx,h⟩

/-- Adding actual framing edges does not alter the exact retained list. -/
theorem ExactReaches.frame_left {kind : Contract} {root q : Request} {rr : root.Outcome}
    {r : q.Outcome} {rt tree : EventTree} {basePath : EventTree.Address} {before middle after : World}
    (frame : CodeStorageFrame.Frame before middle (address kind))
    (h : ExactReaches kind root rr rt basePath q r tree middle after) :
    ExactReaches kind root rr rt basePath q r tree before after := by
  obtain ⟨os,hp,he⟩ := h
  exact ⟨os,by simpa using JournalWorldPaths.Path.trans (.frame frame) hp,he⟩

theorem ExactReaches.frame_right {kind : Contract} {root q : Request} {rr : root.Outcome}
    {r : q.Outcome} {rt tree : EventTree} {basePath : EventTree.Address} {before middle after : World}
    (h : ExactReaches kind root rr rt basePath q r tree before middle)
    (frame : CodeStorageFrame.Frame middle after (address kind)) :
    ExactReaches kind root rr rt basePath q r tree before after := by
  obtain ⟨os,hp,he⟩ := h
  exact ⟨os,by simpa using JournalWorldPaths.Path.trans hp (.frame frame),he⟩

theorem ExactReaches.congr_list {kind : Contract} {root q₁ q₂ : Request} {rr : root.Outcome}
    {r₁ : q₁.Outcome} {r₂ : q₂.Outcome} {rt t₁ t₂ : EventTree} {basePath : EventTree.Address}
    {before after : World}
    (he : retainedList kind q₁ r₁ t₁ = retainedList kind q₂ r₂ t₂)
    (h : ExactReaches kind root rr rt basePath q₂ r₂ t₂ before after) :
    ExactReaches kind root rr rt basePath q₁ r₁ t₁ before after := by
  obtain ⟨os,hp,hl⟩ := h
  exact ⟨os,hp,by rw [he]; exact hl⟩


theorem protected_exact {kind : Contract} {root : Request} {rr : root.Outcome} {rt tree : EventTree}
    {n : Nat} {a : ThetaArgs} {basePath : EventTree.Address} {budget : Nat}
    (cert : Cert (.theta (n+1) a) (Request.theta (n+1) a).eval tree)
    (ready : Ready kind budget (.theta (n+1) a)) (ht : a.target = address kind)
    (loc : RequestAt root rr rt basePath (.theta (n+1) a) (Request.theta (n+1) a).eval) :
    ExactDone kind root rr rt basePath (.theta (n+1) a) (Request.theta (n+1) a).eval tree := by
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
  refine ⟨[occurrence],.call occurrence,?_⟩
  have hc' := cert
  rw [hr] at hc'
  rw [hr,list_theta_atomic hc' ht]
  simp [occurrence]

theorem xi_exact {kind : Contract} {root : Request} {rr : root.Outcome} {rt tree : EventTree}
    {n : Nat} {a : XiArgs} {basePath : EventTree.Address}
    (child : ExactDone kind root rr rt basePath (.x n a.jumps a.entry)
      (Request.x n a.jumps a.entry).eval tree) :
    ExactDone kind root rr rt basePath (.xi (n+1) a) (Request.xi (n+1) a).eval tree := by
  intro cr w g ss out hr
  obtain ⟨f,post,hf,hx,_,hw,_,_⟩ := WrapperJournalEdges.xi_success a hr
  have hn : f=n := by omega
  subst f
  have h := child post out hx
  rw [hw] at h
  exact h.congr_list (list_xi_keep hx)

theorem theta_exact {kind : Contract} {root : Request} {rr : root.Outcome} {rt tree : EventTree}
    {n : Nat} {a : ThetaArgs} {basePath : EventTree.Address}
    (bytes : ByteArray) (hc : a.code = .Code bytes) (ht : a.target ≠ address kind)
    (child : ExactDone kind root rr rt basePath (.xi n (a.xiArgs bytes))
      (Request.xi n (a.xiArgs bytes)).eval tree) :
    ExactDone kind root rr rt basePath (.theta (n+1) a) (Request.theta (n+1) a).eval tree := by
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
    rcases WrapperJournalEdges.theta_code_world (a.context n bytes) he with ⟨hw,_⟩ | ⟨ic,iw,ig,iss,data,hxi,hw,_⟩
    · rw [hw]; exact exact_frame (CodeStorageFrame.refl _ _) empty
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
      rcases WrapperJournalEdges.theta_code_world (a.context n bytes) he with ⟨hw,_⟩ | ⟨ic,iw,ig,iss,data,hxi,hw,_⟩
      · rw [hw]; exact exact_frame (CodeStorageFrame.refl _ _) empty
      · have hxi' : (Request.xi n (a.xiArgs bytes)).eval = .ok (.success (ic,iw,ig,iss) data) := hxi
        rw [hx] at hxi'; cases hxi'
    | success state data =>
      obtain ⟨ic,iw,ig,iss⟩ := state
      cases keep : (iw == ∅) with
      | false =>
        have hs := theta_keep (a.context n bytes) hx keep
        have eqs := Except.ok.inj (hs.symm.trans he)
        have hw := (congrArg (fun t => t.2.1) eqs).symm
        dsimp only at hw
        rw [hw]
        exact (child ic iw ig iss data hx).frame_left
          (CodeStorageFrame.entry (a.context n bytes) (address kind)) |>.congr_list (list_theta_keep hc ht hx keep)
      | true =>
        have hs := theta_empty_restore (a.context n bytes) hx keep
        have eqs := Except.ok.inj (hs.symm.trans he)
        have hw := (congrArg (fun t => t.2.1) eqs).symm
        dsimp only at hw
        rw [hw]
        apply exact_frame (CodeStorageFrame.refl _ _)
        apply retained_empty
        intro p h
        obtain ⟨jc,jw,jg,jss,jdata,hxi,hk,h⟩ := (retained_theta_foreign hc ht p).mp h
        have e := hx.symm.trans hxi
        cases e
        rw [keep] at hk
        cases hk

theorem lambda_exact {kind : Contract} {root : Request} {rr : root.Outcome} {rt tree : EventTree}
    {n : Nat} {a : LambdaArgs} {basePath : EventTree.Address}
    (bytes : ByteArray) (hp : a.preimage = some bytes)
    (ht : CreationSettlement.address bytes ≠ address kind)
    (child : ExactDone kind root rr rt basePath (.xi n (a.xiArgs bytes))
      (Request.xi n (a.xiArgs bytes)).eval tree) :
    ExactDone kind root rr rt basePath (.lambda (n+1) a) (Request.lambda (n+1) a).eval tree := by
  intro target cr w g ss z out hr
  cases hx : (Request.xi n (a.xiArgs bytes)).eval with
  | error err =>
    have empty : retainedList kind (.lambda (n+1) a) (Request.lambda (n+1) a).eval tree = [] := by
      apply retained_empty
      intro p h
      obtain ⟨ic,iw,ig,iss,data,hxi,hk,h⟩ := (retained_lambda hp p).mp h
      have e := hx.symm.trans hxi
      cases e
    obtain ⟨_,hcases⟩ := WrapperJournalEdges.lambda_context_world (a.context n) hp hr
    rcases hcases with ⟨hw,_⟩ | ⟨ic,iw,ig,iss,data,hxi,hw,_⟩
    · rw [hw]; exact exact_frame (CodeStorageFrame.refl _ _) empty
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
      obtain ⟨_,hcases⟩ := WrapperJournalEdges.lambda_context_world (a.context n) hp hr
      rcases hcases with ⟨hw,_⟩ | ⟨ic,iw,ig,iss,data,hxi,hw,_⟩
      · rw [hw]; exact exact_frame (CodeStorageFrame.refl _ _) empty
      · have hxi' : (Request.xi n (a.xiArgs bytes)).eval = .ok (.success (ic,iw,ig,iss) data) := hxi
        rw [hx] at hxi'; cases hxi'
    | success state data =>
      obtain ⟨ic,iw,ig,iss⟩ := state
      cases keep : (a.context n).depositFailure (CreationSettlement.address bytes) ig data with
      | false =>
        have hs := lambda_keep (a.context n) hp hx keep
        have eqs := Except.ok.inj (hs.symm.trans hr)
        have hw := (congrArg (fun t => t.2.2.1) eqs).symm
        dsimp only at hw
        rw [hw]
        exact ((child ic iw ig iss data hx).frame_left
          (CreationStorageFrame.entry_frame (a.context n) (CreationSettlement.address bytes) (address kind))).frame_right
          (CreationStorageFrame.install_away_frame iw (CreationSettlement.address bytes) (address kind) data ht)
          |>.congr_list (list_lambda_keep hp hx keep)
      | true =>
        have hs := lambda_reject_restore (a.context n) hp hx keep
        have eqs := Except.ok.inj (hs.symm.trans hr)
        have hw := (congrArg (fun t => t.2.2.1) eqs).symm
        dsimp only at hw
        rw [hw]
        apply exact_frame (CodeStorageFrame.refl _ _)
        apply retained_empty
        intro p h
        obtain ⟨jc,jw,jg,jss,jdata,hxi,hk,h⟩ := (retained_lambda hp p).mp h
        have e := hx.symm.trans hxi
        cases e
        rw [keep] at hk
        cases hk


theorem step_theta_exact {kind : Contract} {root : Request} {rr : root.Outcome} {rt tree : EventTree}
    {fuel innerFuel : Nat} {a : StepArgs} {b : ThetaArgs} {basePath : EventTree.Address}
    (hc : StepChild fuel a (some (.theta innerFuel b)))
    (child : ExactDone kind root rr rt basePath (.theta innerFuel b) (Request.theta innerFuel b).eval tree) :
    ExactDone kind root rr rt basePath (.step fuel a) (Request.step fuel a).eval tree := by
  intro post hr
  obtain ⟨cr,w,g,ss,z,out,he,hw,_,_⟩ := RecursiveJournalEdges.theta_returned hc hr
  have h := child cr w g ss z out he
  rw [(JournalChildEntry.selected_theta_input hc).1] at h
  rw [hw]
  exact h.congr_list (retained_congr (retained_step hc hr))

theorem step_lambda_exact {kind : Contract} {root : Request} {rr : root.Outcome} {rt tree : EventTree}
    {fuel innerFuel : Nat} {a : StepArgs} {b : LambdaArgs} {basePath : EventTree.Address}
    (hc : StepChild fuel a (some (.lambda innerFuel b)))
    (hne : a.pre.executionEnv.codeOwner ≠ address kind)
    (returned : ∃ r, (Request.lambda innerFuel b).eval = .ok r)
    (child : ExactDone kind root rr rt basePath (.lambda innerFuel b) (Request.lambda innerFuel b).eval tree) :
    ExactDone kind root rr rt basePath (.step fuel a) (Request.step fuel a).eval tree := by
  intro post hr
  obtain ⟨⟨target,cr,w,g,ss,z,out⟩,he⟩ := returned
  obtain ⟨hw,_,_⟩ := RecursiveJournalEdges.lambda_returned hc he hr
  have h := child target cr w g ss z out he
  have hf := (JournalChildEntry.selected_lambda_input hc (address kind) hne).1
  rw [hw]
  exact (h.frame_left hf).congr_list (retained_congr (retained_step hc hr))

theorem occupied_exact {kind : Contract} {root : Request} {rr : root.Outcome} {rt tree : EventTree}
    {fuel : Nat} {a : LambdaArgs} {basePath : EventTree.Address}
    (bytes : ByteArray) (hp : a.preimage = some bytes)
    (ht : CreationSettlement.address bytes = address kind)
    (hc : JournalInvariant.CodeAt kind a.world) :
    ExactDone kind root rr rt basePath (.lambda (fuel+1) a) (Request.lambda (fuel+1) a).eval tree := by
  intro target cr w g ss z out hr
  obtain ⟨_,hcases⟩ := WrapperJournalEdges.lambda_context_world (a.context fuel) hp hr
  rcases hcases with ⟨hw,_⟩ | ⟨ic,iw,ig,iss,data,hx,_,_⟩
  · rw [hw]
    apply exact_frame (CodeStorageFrame.refl _ _)
    apply retained_empty
    intro p h
    obtain ⟨ic,iw,ig,iss,data,hx,_⟩ := (retained_lambda hp p).mp h
    exact CreationCollisionScope.no_success hc ht hx
  · exact False.elim (CreationCollisionScope.no_success hc ht hx)

/-- Every list equality is proved against the independent survival predicate;
actual child and continuation lists are concatenated in execution order. -/
theorem extract_at {kind : Contract} {root : Request} {rootResult : root.Outcome}
    {rootTree : EventTree} {q : Request} {result : q.Outcome} {tree : EventTree}
    (cert : Cert q result tree) :
    ∀ (budget : Nat), budget+tree.count < 2^128 → Ready kind budget q →
      Every CallInput q result tree → Every NoOutOfFuel q result tree →
      ∀ path, RequestAt root rootResult rootTree path q result →
        ExactDone kind root rootResult rootTree path q result tree := by
  induction cert with
  | xZero => intros; simp [ExactDone]
  | xGuardError => intros; simp [ExactDone]
  | xStepError => intros; simp [ExactDone]
  | xRevert =>
    intro budget hb ready inputs safe path outer post out he
    cases he
  | xiZero => intros; simp [ExactDone]
  | thetaZero => intros; simp [ExactDone]
  | lambdaZero => intros; simp [ExactDone]
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
    obtain ⟨first,hf,ef⟩ := ds post rfl
    obtain ⟨second,hs',es⟩ := dn final out rfl
    refine ⟨first++second,.trans hf hs',?_⟩
    rw [List.map_append,ef,es,list_xNext hz hs hh ht,List.map_append]
    simp [List.map_map,Function.comp_def,EventTree.extend,List.append_assoc]
  | @xHalt n cost vj pre mid post out child hz hs hh hn ihs =>
    intro budget hb ready inputs safe path outer
    have loc := RequestAt.xHalt hz hs hh hn (.here hs)
    have hbs : budget+child.count < 2^128 := by simp only [EventTree.count] at hb; omega
    have ds := ihs budget hbs ready (inputs.descendant loc) (safe.descendant loc)
      _ (RequestAt.compose outer loc)
    intro final data he
    cases he
    obtain ⟨os,hp,he⟩ := ds post rfl
    refine ⟨os,hp,?_⟩
    rw [he,list_xHalt hz hs hh hn]
    simp [List.map_map,Function.comp_def,EventTree.extend,List.append_assoc]
  | @xi n a tree body ih =>
    intro budget hb ready inputs safe path outer
    have loc := RequestAt.xi body (.here body)
    exact xi_exact (ih budget hb ready (inputs.descendant loc) (safe.descendant loc)
      _ (by simpa using RequestAt.compose outer loc))
  | @thetaPrecompile n a target hc =>
    intro budget hb ready inputs safe path outer cr world gas ss z out hr
    apply exact_frame (PrecompileWorldFrame.theta_frame hc hr (address kind))
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
    · exact protected_exact (.thetaCode bytes hc body) ready ht outer
    · have loc := RequestAt.thetaCode bytes hc body (.here body)
      exact theta_exact bytes hc ht (ih budget hb (JournalExecution.theta_entry bytes ready ht)
        (inputs.descendant loc) (safe.descendant loc) _ (by simpa using RequestAt.compose outer loc))
  | @lambdaNoPreimage n a hp =>
    intros
    obtain ⟨bytes,hb⟩ := CreationPreimageTotal.lambdaArgs_total a
    rw [hp] at hb
    cases hb
  | @lambdaInit n a bytes tree hp body ih =>
    intro budget hb ready inputs safe path outer
    by_cases ht : CreationSettlement.address bytes = address kind
    · exact occupied_exact bytes hp ht ready.1.1
    · have loc := RequestAt.lambdaInit bytes hp body (.here body)
      exact lambda_exact bytes hp ht (ih budget hb (JournalExecution.lambda_entry bytes ready ht)
        (inputs.descendant loc) (safe.descendant loc) _ (by simpa using RequestAt.compose outer loc))
  | @stepNone n a hc =>
    intro budget hb ready inputs safe path outer post hr
    apply exact_frame _ (retained_step_none hc)
    by_cases ho : OrdinaryGas.Ordinary a.op
    · exact CodeStorageFrame.of_preserved (OrdinaryWorldFrame.accepted_step_preserved ho ready.2 a.guard hr).1
    · obtain ⟨hw,_,_⟩ := RecursiveJournalEdges.denied_recursive hc ho hr
      rw [hw]
      exact CodeStorageFrame.refl _ _
  | @stepChild n a q tree hc body ih =>
    intro budget hb ready inputs safe path outer
    have loc := RequestAt.stepChild hc body (.here body)
    have child := ih budget hb (JournalExecution.child_ready hc ready)
      (inputs.descendant loc) (safe.descendant loc) _ (RequestAt.compose outer loc)
    simp only [List.append_nil] at child
    rcases JournalChildEntry.selected_kind hc with ⟨f,b,hq⟩ | ⟨f,b,hq⟩
    · subst q
      exact step_theta_exact hc child
    · subst q
      exact step_lambda_exact hc ready.2 (NestedEvents.lambda_returns safe loc) child

/-- Numeric root adequacy supplies all-node error exclusion. No per-child path
or intermediate invariant is assumed, and the exact retained list is explicit. -/
theorem extract {kind : Contract} {q : Request} {result : q.Outcome} {tree : EventTree}
    (cert : Cert q result tree) (budget : Nat) (hb : budget+tree.count < 2^128)
    (ready : Ready kind budget q) (inputs : Every CallInput q result tree)
    (adequate : FuelAdequacy.Adequate q) : ExactDone kind q result tree [] q result tree :=
  extract_at cert budget hb ready inputs (FuelAdequacy.every_no_out_of_fuel cert adequate) [] (.here cert)

#print axioms list_xNext
#print axioms list_xHalt
#print axioms theta_exact
#print axioms lambda_exact
#print axioms extract_at
#print axioms extract
end Eip8282.Audit.Integrator.JournalRetainedPaths
