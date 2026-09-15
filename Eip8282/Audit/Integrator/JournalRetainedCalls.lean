import Eip8282.Audit.Integrator.JournalWorldPaths
import Eip8282.Audit.Integrator.Topics.Nested

/-! Actual protected calls whose enclosing evaluator checkpoints retain their
world effects. The literal empty-world and code-deposit guards are explicit.
A returned failed protected call is an atomic no-op occurrence; successful
submission counting additionally requires status=true, non-SYSTEM and nonempty
input. This relation is independent of the existential queue-world Path. -/
namespace Eip8282.Audit.Integrator.JournalRetainedCalls
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open NestedEvents
open ReachableCalls (Contract address runtime)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem theta_keep (c : MessageCall.Context)
    {cr : Created} {world : World} {gas : UInt256} {ss : Substate} {out : ByteArray}
    (hx : c.execution = .ok (.success (cr,world,gas,ss) out))
    (keep : (world == ∅) = false) : c.result = .ok (cr,world,gas,ss,true,out) := by
  rw [MessageCall.result_eq_settle, hx]
  simp only [MessageCall.Context.settle,keep,Bool.false_eq_true,↓reduceIte]

theorem theta_empty_restore (c : MessageCall.Context)
    {cr : Created} {world : World} {gas : UInt256} {ss : Substate} {out : ByteArray}
    (hx : c.execution = .ok (.success (cr,world,gas,ss) out))
    (discard : (world == ∅) = true) : c.result = .ok (cr,c.world,gas,c.substate,true,out) := by
  rw [MessageCall.result_eq_settle, hx]
  simp only [MessageCall.Context.settle,discard,↓reduceIte]

theorem lambda_keep (c : CreationSettlement.Context) {bytes : ByteArray}
    (hp : c.preimage = some bytes)
    {cr : Created} {world : World} {gas : UInt256} {ss : Substate} {out : ByteArray}
    (hx : c.execution (CreationSettlement.address bytes) = .ok (.success (cr,world,gas,ss) out))
    (keep : c.depositFailure (CreationSettlement.address bytes) gas out = false) :
    c.result = .ok (CreationSettlement.address bytes,cr,
      CreationSettlement.install world (CreationSettlement.address bytes) out,
      UInt256.ofNat (gas.toNat - GasConstants.Gcodedeposit*out.size),ss,true,ByteArray.empty) := by
  rw [CreationSettlement.result_eq_settle c hp,hx]
  simp only [CreationSettlement.Context.settle,keep,Bool.false_eq_true,↓reduceIte,Bool.not_false]

theorem lambda_reject_restore (c : CreationSettlement.Context) {bytes : ByteArray}
    (hp : c.preimage = some bytes)
    {cr : Created} {world : World} {gas : UInt256} {ss : Substate} {out : ByteArray}
    (hx : c.execution (CreationSettlement.address bytes) = .ok (.success (cr,world,gas,ss) out))
    (discard : c.depositFailure (CreationSettlement.address bytes) gas out = true) :
    c.result = .ok (CreationSettlement.address bytes,cr,c.world,UInt256.ofNat 0,
      c.accessed (CreationSettlement.address bytes),false,ByteArray.empty) := by
  rw [CreationSettlement.result_eq_settle c hp,hx]
  simp only [CreationSettlement.Context.settle,discard,↓reduceIte,Bool.not_true]

/-- Canonical calls are atomic. Under actual Ready, their pinned runtime has
no nested Theta; this atomization is not a statement about arbitrary code at
that address. All traversed ancestor worlds are actually retained. -/
inductive Survives (kind : Contract) : (q : Request) → q.Outcome → EventTree →
    EventTree.Address → Nat → ThetaArgs → ThetaResult → Prop where
  | here {fuel : Nat} {a : ThetaArgs} {tree : EventTree}
      {cr : Created} {world : World} {gas : UInt256} {ss : Substate} {z : Bool} {out : ByteArray}
      (positive : 0 < fuel) (target : a.target = address kind)
      (body : Cert (.theta fuel a) (.ok (cr,world,gas,ss,z,out)) tree) :
      Survives kind (.theta fuel a) (.ok (cr,world,gas,ss,z,out)) tree [] fuel a (.ok (cr,world,gas,ss,z,out))
  | xNextChild {n cost f : Nat} {vj : Array UInt256} {pre mid post final : EVM.State}
      {out : ByteArray} {child next : EventTree} {path : EventTree.Address} {a : ThetaArgs} {r : ThetaResult}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = none)
      (tail : Cert (.x n vj post) (.ok (.success final out)) next)
      (loc : Survives kind (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child path f a r) :
      Survives kind (.x (n+1) vj pre) (.ok (.success final out))
        (.step (decide (FrameEvents.Marked pre)) child next) (false::path) f a r
  | xNextTail {n cost f : Nat} {vj : Array UInt256} {pre mid post final : EVM.State}
      {out : ByteArray} {child next : EventTree} {path : EventTree.Address} {a : ThetaArgs} {r : ThetaResult}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = none)
      (tail : Cert (.x n vj post) (.ok (.success final out)) next)
      (loc : Survives kind (.x n vj post) (.ok (.success final out)) next path f a r) :
      Survives kind (.x (n+1) vj pre) (.ok (.success final out))
        (.step (decide (FrameEvents.Marked pre)) child next) (true::path) f a r
  | xHalt {n cost f : Nat} {vj : Array UInt256} {pre mid post : EVM.State}
      {out : ByteArray} {child : EventTree} {path : EventTree.Address} {a : ThetaArgs} {r : ThetaResult}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = some out) (hn : (decodeAt pre).1 ≠ .REVERT)
      (loc : Survives kind (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child path f a r) :
      Survives kind (.x (n+1) vj pre) (.ok (.success post out))
        (.step (decide (FrameEvents.Marked pre)) child .done) (false::path) f a r
  | xi {n f : Nat} {outer : XiArgs} {post : EVM.State} {out : ByteArray}
      {tree : EventTree} {path : EventTree.Address} {a : ThetaArgs} {r : ThetaResult}
      (body : Cert (.x n outer.jumps outer.entry) (Request.x n outer.jumps outer.entry).eval tree)
      (hx : (Request.x n outer.jumps outer.entry).eval = .ok (.success post out))
      (loc : Survives kind (.x n outer.jumps outer.entry) (Request.x n outer.jumps outer.entry).eval tree path f a r) :
      Survives kind (.xi (n+1) outer) (Request.xi (n+1) outer).eval tree path f a r
  | thetaCode {n f : Nat} {outer : ThetaArgs} {bytes : ByteArray}
      {cr : Created} {world : World} {gas : UInt256} {ss : Substate} {out : ByteArray}
      {tree : EventTree} {path : EventTree.Address} {a : ThetaArgs} {r : ThetaResult}
      (foreign : outer.target ≠ address kind) (hc : outer.code = .Code bytes)
      (body : Cert (.xi n (outer.xiArgs bytes)) (Request.xi n (outer.xiArgs bytes)).eval tree)
      (hx : (Request.xi n (outer.xiArgs bytes)).eval = .ok (.success (cr,world,gas,ss) out))
      (keep : (world == ∅) = false)
      (loc : Survives kind (.xi n (outer.xiArgs bytes)) (Request.xi n (outer.xiArgs bytes)).eval tree path f a r) :
      Survives kind (.theta (n+1) outer) (Request.theta (n+1) outer).eval tree path f a r
  | lambdaInit {n f : Nat} {outer : LambdaArgs} {bytes : ByteArray}
      {cr : Created} {world : World} {gas : UInt256} {ss : Substate} {out : ByteArray}
      {tree : EventTree} {path : EventTree.Address} {a : ThetaArgs} {r : ThetaResult}
      (hp : outer.preimage = some bytes)
      (body : Cert (.xi n (outer.xiArgs bytes)) (Request.xi n (outer.xiArgs bytes)).eval tree)
      (hx : (Request.xi n (outer.xiArgs bytes)).eval = .ok (.success (cr,world,gas,ss) out))
      (keep : (outer.context n).depositFailure (CreationSettlement.address bytes) gas out = false)
      (loc : Survives kind (.xi n (outer.xiArgs bytes)) (Request.xi n (outer.xiArgs bytes)).eval tree path f a r) :
      Survives kind (.lambda (n+1) outer) (Request.lambda (n+1) outer).eval tree path f a r
  | stepChild {n f : Nat} {outer : StepArgs} {child : Request} {post : EVM.State}
      {tree : EventTree} {path : EventTree.Address} {a : ThetaArgs} {r : ThetaResult}
      (hc : StepChild n outer (some child)) (body : Cert child child.eval tree)
      (hs : (Request.step n outer).eval = .ok post)
      (loc : Survives kind child child.eval tree path f a r) :
      Survives kind (.step n outer) (Request.step n outer).eval tree path f a r

namespace Survives

theorem actual {kind : Contract} {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {fuel : Nat} {a : ThetaArgs} {r : ThetaResult}
    (h : Survives kind q result tree path fuel a r) : ThetaAt q result tree path fuel a r := by
  induction h with
  | here hp ht body => exact .here body
  | xNextChild hz hs hh tail loc ih => exact .xNextChild hz hs hh tail ih
  | xNextTail hz hs hh tail loc ih => exact .xNextTail hz hs hh tail ih
  | xHalt hz hs hh hn loc ih => exact .xHalt hz hs hh hn ih
  | xi body hx loc ih => exact .xi body ih
  | thetaCode hf hc body hx keep loc ih => exact .thetaCode _ hc body ih
  | lambdaInit hp body hx keep loc ih => exact .lambdaInit _ hp body ih
  | stepChild hc body hs loc ih => exact .stepChild hc body ih

theorem identity {kind : Contract} {q : Request} {result₁ result₂ : q.Outcome}
    {tree₁ tree₂ : EventTree} {path : EventTree.Address} {f₁ f₂ : Nat}
    {a₁ a₂ : ThetaArgs} {r₁ r₂ : ThetaResult}
    (h₁ : Survives kind q result₁ tree₁ path f₁ a₁ r₁)
    (h₂ : Survives kind q result₂ tree₂ path f₂ a₂ r₂) : f₁=f₂ ∧ a₁=a₂ ∧ r₁=r₂ :=
  ThetaAt.identity h₁.actual h₂.actual

end Survives

/-- Structural node order: a node, its selected-child subtree, then its
continuation subtree. Done includes its root so zero-event calls are visible. -/
def nodePaths : EventTree → List EventTree.Address
  | .done => [[]]
  | .step _ child next => [] ::
      (nodePaths child).map (EventTree.extend false) ++ (nodePaths next).map (EventTree.extend true)

theorem nodePaths_root (tree : EventTree) : [] ∈ nodePaths tree := by
  cases tree <;> simp [nodePaths]

theorem nodePaths_child (mark : Bool) (child next : EventTree) {path : EventTree.Address}
    (h : path ∈ nodePaths child) : false::path ∈ nodePaths (.step mark child next) := by
  simp only [nodePaths,List.mem_cons,List.mem_append]
  exact Or.inl (Or.inr (List.mem_map.mpr ⟨path,h,rfl⟩))

theorem nodePaths_next (mark : Bool) (child next : EventTree) {path : EventTree.Address}
    (h : path ∈ nodePaths next) : true::path ∈ nodePaths (.step mark child next) := by
  simp only [nodePaths,List.mem_cons,List.mem_append]
  exact Or.inr (List.mem_map.mpr ⟨path,h,rfl⟩)

theorem nodePaths_nodup (tree : EventTree) : (nodePaths tree).Nodup := by
  induction tree with
  | done => simp [nodePaths]
  | step mark child next ihc ihn =>
    have hc := List.Nodup.map (EventTree.prefix_injective false) ihc
    have hn := List.Nodup.map (EventTree.prefix_injective true) ihn
    have ht := hc.append hn (EventTree.prefix_disjoint _ _)
    apply List.nodup_cons.mpr
    exact ⟨by simp [EventTree.extend],ht⟩

theorem actual_in_nodePaths {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {fuel : Nat} {a : ThetaArgs} {r : ThetaResult}
    (h : ThetaAt q result tree path fuel a r) : path ∈ nodePaths tree := by
  induction h with
  | here body => exact nodePaths_root _
  | xStepError _ _ _ ih => exact nodePaths_child _ _ _ ih
  | xNextChild _ _ _ _ _ ih => exact nodePaths_child _ _ _ ih
  | xNextTail _ _ _ _ _ ih => exact nodePaths_next _ _ _ ih
  | xHalt _ _ _ _ _ ih => exact nodePaths_child _ _ _ ih
  | xRevert _ _ _ _ _ ih => exact nodePaths_child _ _ _ ih
  | xi _ _ ih => exact ih
  | thetaCode _ _ _ _ ih => exact ih
  | lambdaInit _ _ _ _ ih => exact ih
  | stepChild _ _ _ ih => exact ih

theorem Survives.in_nodePaths {kind : Contract} {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {fuel : Nat} {a : ThetaArgs} {r : ThetaResult}
    (h : Survives kind q result tree path fuel a r) : path ∈ nodePaths tree :=
  actual_in_nodePaths h.actual

def Retained (kind : Contract) (q : Request) (result : q.Outcome) (tree : EventTree)
    (path : EventTree.Address) : Prop := ∃ fuel a r, Survives kind q result tree path fuel a r

/-- A canonical finite enumeration of the independently specified surviving
calls. Filtering preserves structural order and does not sort Boolean paths. -/
noncomputable def retainedList (kind : Contract) (q : Request) (result : q.Outcome)
    (tree : EventTree) : List EventTree.Address := by
  classical
  exact (nodePaths tree).filter (fun path => decide (Retained kind q result tree path))

theorem retainedList_mem_iff {kind : Contract} {q : Request} {result : q.Outcome}
    {tree : EventTree} {path : EventTree.Address} :
    path ∈ retainedList kind q result tree ↔ Retained kind q result tree path := by
  classical
  simp only [retainedList,List.mem_filter,decide_eq_true_eq]
  constructor
  · exact And.right
  · intro h
    obtain ⟨fuel,a,r,hs⟩ := h
    exact ⟨hs.in_nodePaths,⟨fuel,a,r,hs⟩⟩

theorem retainedList_nodup (kind : Contract) (q : Request) (result : q.Outcome) (tree : EventTree) :
    (retainedList kind q result tree).Nodup := by
  classical
  exact (nodePaths_nodup tree).filter _

/-- Explicit structural order, rather than an unproved lexicographic sorting
convention. Every retained occurrence stays in its original node position. -/
theorem retainedList_order (kind : Contract) (q : Request) (result : q.Outcome) (tree : EventTree) :
    (retainedList kind q result tree).Sublist (nodePaths tree) := by
  classical
  exact List.filter_sublist

/-- Each listed address determines the exact fuel, actual Theta inputs and
returned tuple uniquely, even when payloads or call inputs happen to repeat. -/
theorem retainedList_unique_call {kind : Contract} {q : Request} {result : q.Outcome}
    {tree : EventTree} {path : EventTree.Address}
    (hm : path ∈ retainedList kind q result tree) :
    ∃ fuel a r, Survives kind q result tree path fuel a r ∧
      ∀ f b s, Survives kind q result tree path f b s → fuel=f ∧ a=b ∧ r=s := by
  obtain ⟨fuel,a,r,h⟩ := retainedList_mem_iff.mp hm
  exact ⟨fuel,a,r,h,fun _ _ _ other => h.identity other⟩

#print axioms theta_keep
#print axioms theta_empty_restore
#print axioms lambda_keep
#print axioms lambda_reject_restore
#print axioms Survives.actual
#print axioms Survives.identity
#print axioms retainedList_mem_iff
#print axioms retainedList_nodup
#print axioms retainedList_order
#print axioms retainedList_unique_call
end Eip8282.Audit.Integrator.JournalRetainedCalls
