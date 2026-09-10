import Eip8282.Audit.Integrator.NestedFrameOccurrence

/-!
# Actual Theta invocations inside the same nested certificate

The relation follows the same selected evaluator children and X continuations
as Cert, retaining every actual Theta input and full Except result. The root
includes precompile and zero-fuel invocations. Surrounding errors and rollback
never erase a located call. This is an execution location, not a committed
storage history.
-/
namespace Eip8282.Audit.Integrator.NestedEvents
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open NestedFrameOwnership (FrameRoot)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- Location of an actual Theta invocation, with its own exact result and fuel. -/
inductive ThetaAt : (q : Request) → q.Outcome → EventTree → EventTree.Address →
    Nat → ThetaArgs → ThetaResult → Prop where
  | here {f : Nat} {a : ThetaArgs} {r : ThetaResult} {tree : EventTree}
      (body : Cert (.theta f a) r tree) : ThetaAt (.theta f a) r tree [] f a r
  | xStepError {n cost f : Nat} {vj : Array UInt256} {pre mid : EVM.State}
      {err : ExecutionException} {child : EventTree} {path : EventTree.Address}
      {a : ThetaArgs} {r : ThetaResult}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.error err) child)
      (loc : ThetaAt (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.error err) child path f a r) :
      ThetaAt (.x (n+1) vj pre) (.error err) (.step false child .done) (false::path) f a r
  | xNextChild {n cost f : Nat} {vj : Array UInt256} {pre mid post : EVM.State}
      {result : XResult} {child next : EventTree} {path : EventTree.Address}
      {a : ThetaArgs} {r : ThetaResult}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = none)
      (tail : Cert (.x n vj post) result next)
      (loc : ThetaAt (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child path f a r) :
      ThetaAt (.x (n+1) vj pre) result (.step (decide (FrameEvents.Marked pre)) child next)
        (false::path) f a r
  | xNextTail {n cost f : Nat} {vj : Array UInt256} {pre mid post : EVM.State}
      {result : XResult} {child next : EventTree} {path : EventTree.Address}
      {a : ThetaArgs} {r : ThetaResult}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = none)
      (tail : Cert (.x n vj post) result next)
      (loc : ThetaAt (.x n vj post) result next path f a r) :
      ThetaAt (.x (n+1) vj pre) result (.step (decide (FrameEvents.Marked pre)) child next)
        (true::path) f a r
  | xHalt {n cost f : Nat} {vj : Array UInt256} {pre mid post : EVM.State}
      {out : ByteArray} {child : EventTree} {path : EventTree.Address}
      {a : ThetaArgs} {r : ThetaResult}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = some out)
      (hn : (decodeAt pre).1 ≠ .REVERT)
      (loc : ThetaAt (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child path f a r) :
      ThetaAt (.x (n+1) vj pre) (.ok (.success post out))
        (.step (decide (FrameEvents.Marked pre)) child .done) (false::path) f a r
  | xRevert {n cost f : Nat} {vj : Array UInt256} {pre mid post : EVM.State}
      {out : ByteArray} {child : EventTree} {path : EventTree.Address}
      {a : ThetaArgs} {r : ThetaResult}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = some out)
      (hr : (decodeAt pre).1 = .REVERT)
      (loc : ThetaAt (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child path f a r) :
      ThetaAt (.x (n+1) vj pre) (.ok (.revert post.gasAvailable out))
        (.step (decide (FrameEvents.Marked pre)) child .done) (false::path) f a r
  | xi {n f : Nat} {outer : XiArgs} {a : ThetaArgs} {tree : EventTree} {path : EventTree.Address} {r : ThetaResult}
      (body : Cert (.x n outer.jumps outer.entry) (Request.x n outer.jumps outer.entry).eval tree)
      (loc : ThetaAt (.x n outer.jumps outer.entry) (Request.x n outer.jumps outer.entry).eval tree path f a r) :
      ThetaAt (.xi (n+1) outer) (Request.xi (n+1) outer).eval tree path f a r
  | thetaCode {n f : Nat} {outer : ThetaArgs} {a : ThetaArgs} {r : ThetaResult}
      (bytes : ByteArray) {tree : EventTree} {path : EventTree.Address}
      (hc : outer.code = .Code bytes)
      (body : Cert (.xi n (outer.xiArgs bytes)) (Request.xi n (outer.xiArgs bytes)).eval tree)
      (loc : ThetaAt (.xi n (outer.xiArgs bytes)) (Request.xi n (outer.xiArgs bytes)).eval tree path f a r) :
      ThetaAt (.theta (n+1) outer) (Request.theta (n+1) outer).eval tree path f a r
  | lambdaInit {n f : Nat} {outer : LambdaArgs} {a : ThetaArgs} {r : ThetaResult}
      (bytes : ByteArray) {tree : EventTree} {path : EventTree.Address}
      (hp : outer.preimage = some bytes)
      (body : Cert (.xi n (outer.xiArgs bytes)) (Request.xi n (outer.xiArgs bytes)).eval tree)
      (loc : ThetaAt (.xi n (outer.xiArgs bytes)) (Request.xi n (outer.xiArgs bytes)).eval tree path f a r) :
      ThetaAt (.lambda (n+1) outer) (Request.lambda (n+1) outer).eval tree path f a r
  | stepChild {n f : Nat} {outer : StepArgs} {q : Request} {a : ThetaArgs} {r : ThetaResult}
      {tree : EventTree} {path : EventTree.Address}
      (hc : StepChild n outer (some q)) (body : Cert q q.eval tree)
      (loc : ThetaAt q q.eval tree path f a r) :
      ThetaAt (.step n outer) (Request.step n outer).eval tree path f a r

namespace ThetaAt

/-- Every location retains the complete actual surrounding certificate. -/
theorem cert_top {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (h : ThetaAt q result tree path f a r) : Cert q result tree := by
  cases h with
  | here body => exact body
  | xStepError hz hs _ => exact .xStepError hz hs
  | xNextChild hz hs hh ht _ => exact .xNext hz hs hh ht
  | xNextTail hz hs hh ht _ => exact .xNext hz hs hh ht
  | xHalt hz hs hh hn _ => exact .xHalt hz hs hh hn
  | xRevert hz hs hh hr _ => exact .xRevert hz hs hh hr
  | xi body _ => exact .xi body
  | thetaCode bytes hc body _ => exact .thetaCode bytes hc body
  | lambdaInit bytes hp body _ => exact .lambdaInit bytes hp body
  | stepChild hc body _ => exact .stepChild hc body

theorem sound_top {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (h : ThetaAt q result tree path f a r) : q.eval = result := sound (cert_top h)

theorem sound_inner {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (h : ThetaAt q result tree path f a r) : (Request.theta f a).eval = r := by
  induction h with
  | here body => exact sound body
  | xStepError _ _ _ ih => exact ih
  | xNextChild _ _ _ _ _ ih => exact ih
  | xNextTail _ _ _ _ _ ih => exact ih
  | xHalt _ _ _ _ _ ih => exact ih
  | xRevert _ _ _ _ _ ih => exact ih
  | xi _ _ ih => exact ih
  | thetaCode _ _ _ _ ih => exact ih
  | lambdaInit _ _ _ _ ih => exact ih
  | stepChild _ _ _ ih => exact ih

/-- An X instruction or continuation is never itself a new Theta frame root. -/
theorem x_nonempty {fuel : Nat} {vj : Array UInt256} {pre : EVM.State}
    {result : XResult} {tree : EventTree} {path : EventTree.Address}
    {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (h : ThetaAt (.x fuel vj pre) result tree path f a r) : path ≠ [] := by
  cases h <;> simp

private theorem false_cons_root {path : EventTree.Address} (h : FrameRoot path) :
    FrameRoot (false::path) := by
  rcases h with rfl | ⟨parent, rfl⟩
  · exact Or.inr ⟨[], rfl⟩
  · exact Or.inr ⟨false::parent, rfl⟩

private theorem true_cons_root {path : EventTree.Address} (h : FrameRoot path) (hn : path ≠ []) :
    FrameRoot (true::path) := by
  rcases h with he | ⟨parent, rfl⟩
  · exact False.elim (hn he)
  · exact Or.inr ⟨true::parent, rfl⟩

/-- Every actual Theta location obeys the owning-frame grammar. -/
theorem frame_root {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (h : ThetaAt q result tree path f a r) : FrameRoot path := by
  induction h with
  | here => exact Or.inl rfl
  | xStepError _ _ _ ih => exact false_cons_root ih
  | xNextChild _ _ _ _ _ ih => exact false_cons_root ih
  | xNextTail _ _ _ _ loc ih => exact true_cons_root ih (x_nonempty loc)
  | xHalt _ _ _ _ _ ih => exact false_cons_root ih
  | xRevert _ _ _ _ _ ih => exact false_cons_root ih
  | xi _ _ ih => exact ih
  | thetaCode _ _ _ _ ih => exact ih
  | lambdaInit _ _ _ _ ih => exact ih
  | stepChild _ _ _ ih => exact ih

private theorem child_transport {inner child : EventTree} {path : EventTree.Address}
    (h : ∀ event ∈ inner.occurrences, path ++ event ∈ child.occurrences)
    (marked : Bool) (next : EventTree) :
    ∀ event ∈ inner.occurrences, (false::path) ++ event ∈ (EventTree.step marked child next).occurrences := by
  intro event he
  exact (EventTree.child_mem_iff marked child next (path++event)).mpr (h event he)

private theorem next_transport {inner next : EventTree} {path : EventTree.Address}
    (h : ∀ event ∈ inner.occurrences, path ++ event ∈ next.occurrences)
    (marked : Bool) (child : EventTree) :
    ∀ event ∈ inner.occurrences, (true::path) ++ event ∈ (EventTree.step marked child next).occurrences := by
  intro event he
  exact (EventTree.next_mem_iff marked child next (path++event)).mpr (h event he)

/-- The located invocation has its own actual certificate, and every one of
its structural occurrences embeds in the original tree at this exact path. -/
theorem at_tree {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (h : ThetaAt q result tree path f a r) :
    ∃ innerTree, Cert (.theta f a) r innerTree ∧
      ∀ event ∈ innerTree.occurrences, path ++ event ∈ tree.occurrences := by
  induction h with
  | here body => exact ⟨_, body, fun _ he => he⟩
  | xStepError _ _ _ ih =>
      obtain ⟨inner, cert, embed⟩ := ih
      exact ⟨inner, cert, child_transport embed _ _⟩
  | xNextChild _ _ _ _ _ ih =>
      obtain ⟨inner, cert, embed⟩ := ih
      exact ⟨inner, cert, child_transport embed _ _⟩
  | xNextTail _ _ _ _ _ ih =>
      obtain ⟨inner, cert, embed⟩ := ih
      exact ⟨inner, cert, next_transport embed _ _⟩
  | xHalt _ _ _ _ _ ih =>
      obtain ⟨inner, cert, embed⟩ := ih
      exact ⟨inner, cert, child_transport embed _ _⟩
  | xRevert _ _ _ _ _ ih =>
      obtain ⟨inner, cert, embed⟩ := ih
      exact ⟨inner, cert, child_transport embed _ _⟩
  | xi _ _ ih => exact ih
  | thetaCode _ _ _ _ ih => exact ih
  | lambdaInit _ _ _ _ ih => exact ih
  | stepChild _ _ _ ih => exact ih

/-- Transport a same-path Xi location out through a located Theta call. -/
private theorem lift_xi {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {f g : Nat} {a : ThetaArgs} {r : ThetaResult}
    {b : XiArgs} {s : XiResult}
    (h : ThetaAt q result tree path f a r)
    (inner : ∀ innerTree, Cert (.theta f a) r innerTree →
      XiAt (.theta f a) r innerTree [] g b s) :
    XiAt q result tree path g b s := by
  induction h with
  | here body => exact inner _ body
  | xStepError hz hs _ ih => exact .xStepError hz hs (ih inner)
  | xNextChild hz hs hh ht _ ih => exact .xNextChild hz hs hh ht (ih inner)
  | xNextTail hz hs hh ht _ ih => exact .xNextTail hz hs hh ht (ih inner)
  | xHalt hz hs hh hn _ ih => exact .xHalt hz hs hh hn (ih inner)
  | xRevert hz hs hh hr _ ih => exact .xRevert hz hs hh hr (ih inner)
  | xi body _ ih => exact .xi body (ih inner)
  | thetaCode bytes hc body _ ih => exact .thetaCode bytes hc body (ih inner)
  | lambdaInit bytes hp body _ ih => exact .lambdaInit bytes hp body (ih inner)
  | stepChild hc body _ ih => exact .stepChild hc body (ih inner)

/-- A positive-fuel ordinary-code Theta invocation selects this exact Xi
request at the same path. The Xi may succeed, revert, or raise any exception. -/
theorem code_xi {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {n : Nat} {a : ThetaArgs} {r : ThetaResult}
    {bytes : ByteArray}
    (h : ThetaAt q result tree path (n+1) a r) (hc : a.code = .Code bytes) :
    XiAt q result tree path n (a.xiArgs bytes) (Request.xi n (a.xiArgs bytes)).eval := by
  apply lift_xi h
  intro innerTree body
  cases body with
  | thetaPrecompile target hp => rw [hc] at hp; cases hp
  | thetaCode actual hp body =>
      have he : actual = bytes := by cases hp.symm.trans hc; rfl
      subst actual
      exact .thetaCode bytes hc body (.here body)

#print axioms cert_top
#print axioms sound_top
#print axioms sound_inner
#print axioms x_nonempty
#print axioms frame_root
#print axioms at_tree
#print axioms code_xi
end ThetaAt
end Eip8282.Audit.Integrator.NestedEvents
