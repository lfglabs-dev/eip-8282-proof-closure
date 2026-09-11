import Eip8282.Audit.Integrator.NestedEventCert
import Eip8282.Audit.Integrator.NestedFrameOwnership

/-!
# Actual Xi invocations inside the same nested certificate

The relation follows selected evaluator children and X continuations. Only a
literal Xi invocation introduces a frame: transparent wrappers and continued
X instructions do not. Both surrounding branches retain their actual Certs.
This module supplies traversal, frame-root grammar and subtree occurrence
transport, not global append counts or protocol-history extraction.
-/
namespace Eip8282.Audit.Integrator.NestedEvents
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open NestedFrameOwnership (FrameRoot)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- Location of an actual Xi invocation, with its own exact result and fuel. -/
inductive XiAt : (q : Request) → q.Outcome → EventTree → EventTree.Address →
    Nat → XiArgs → XiResult → Prop where
  | here {f : Nat} {a : XiArgs} {r : XiResult} {tree : EventTree}
      (body : Cert (.xi f a) r tree) : XiAt (.xi f a) r tree [] f a r
  | xStepError {n cost f : Nat} {vj : Array UInt256} {pre mid : EVM.State}
      {err : ExecutionException} {child : EventTree} {path : EventTree.Address}
      {a : XiArgs} {r : XiResult}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.error err) child)
      (loc : XiAt (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.error err) child path f a r) :
      XiAt (.x (n+1) vj pre) (.error err) (.step false child .done) (false::path) f a r
  | xNextChild {n cost f : Nat} {vj : Array UInt256} {pre mid post : EVM.State}
      {result : XResult} {child next : EventTree} {path : EventTree.Address}
      {a : XiArgs} {r : XiResult}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = none)
      (tail : Cert (.x n vj post) result next)
      (loc : XiAt (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child path f a r) :
      XiAt (.x (n+1) vj pre) result (.step (decide (FrameEvents.Marked pre)) child next)
        (false::path) f a r
  | xNextTail {n cost f : Nat} {vj : Array UInt256} {pre mid post : EVM.State}
      {result : XResult} {child next : EventTree} {path : EventTree.Address}
      {a : XiArgs} {r : XiResult}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = none)
      (tail : Cert (.x n vj post) result next)
      (loc : XiAt (.x n vj post) result next path f a r) :
      XiAt (.x (n+1) vj pre) result (.step (decide (FrameEvents.Marked pre)) child next)
        (true::path) f a r
  | xHalt {n cost f : Nat} {vj : Array UInt256} {pre mid post : EVM.State}
      {out : ByteArray} {child : EventTree} {path : EventTree.Address}
      {a : XiArgs} {r : XiResult}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = some out)
      (hn : (decodeAt pre).1 ≠ .REVERT)
      (loc : XiAt (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child path f a r) :
      XiAt (.x (n+1) vj pre) (.ok (.success post out))
        (.step (decide (FrameEvents.Marked pre)) child .done) (false::path) f a r
  | xRevert {n cost f : Nat} {vj : Array UInt256} {pre mid post : EVM.State}
      {out : ByteArray} {child : EventTree} {path : EventTree.Address}
      {a : XiArgs} {r : XiResult}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = some out)
      (hr : (decodeAt pre).1 = .REVERT)
      (loc : XiAt (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child path f a r) :
      XiAt (.x (n+1) vj pre) (.ok (.revert post.gasAvailable out))
        (.step (decide (FrameEvents.Marked pre)) child .done) (false::path) f a r
  | xi {n f : Nat} {outer a : XiArgs} {tree : EventTree} {path : EventTree.Address} {r : XiResult}
      (body : Cert (.x n outer.jumps outer.entry) (Request.x n outer.jumps outer.entry).eval tree)
      (loc : XiAt (.x n outer.jumps outer.entry) (Request.x n outer.jumps outer.entry).eval tree path f a r) :
      XiAt (.xi (n+1) outer) (Request.xi (n+1) outer).eval tree path f a r
  | thetaCode {n f : Nat} {outer : ThetaArgs} {a : XiArgs} {r : XiResult}
      (bytes : ByteArray) {tree : EventTree} {path : EventTree.Address}
      (hc : outer.code = .Code bytes)
      (body : Cert (.xi n (outer.xiArgs bytes)) (Request.xi n (outer.xiArgs bytes)).eval tree)
      (loc : XiAt (.xi n (outer.xiArgs bytes)) (Request.xi n (outer.xiArgs bytes)).eval tree path f a r) :
      XiAt (.theta (n+1) outer) (Request.theta (n+1) outer).eval tree path f a r
  | lambdaInit {n f : Nat} {outer : LambdaArgs} {a : XiArgs} {r : XiResult}
      (bytes : ByteArray) {tree : EventTree} {path : EventTree.Address}
      (hp : outer.preimage = some bytes)
      (body : Cert (.xi n (outer.xiArgs bytes)) (Request.xi n (outer.xiArgs bytes)).eval tree)
      (loc : XiAt (.xi n (outer.xiArgs bytes)) (Request.xi n (outer.xiArgs bytes)).eval tree path f a r) :
      XiAt (.lambda (n+1) outer) (Request.lambda (n+1) outer).eval tree path f a r
  | stepChild {n f : Nat} {outer : StepArgs} {q : Request} {a : XiArgs} {r : XiResult}
      {tree : EventTree} {path : EventTree.Address}
      (hc : StepChild n outer (some q)) (body : Cert q q.eval tree)
      (loc : XiAt q q.eval tree path f a r) :
      XiAt (.step n outer) (Request.step n outer).eval tree path f a r

namespace XiAt

/-- Every location retains the complete actual surrounding certificate. -/
theorem cert_top {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {f : Nat} {a : XiArgs} {r : XiResult}
    (h : XiAt q result tree path f a r) : Cert q result tree := by
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
    {path : EventTree.Address} {f : Nat} {a : XiArgs} {r : XiResult}
    (h : XiAt q result tree path f a r) : q.eval = result := sound (cert_top h)

theorem sound_inner {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {f : Nat} {a : XiArgs} {r : XiResult}
    (h : XiAt q result tree path f a r) : (Request.xi f a).eval = r := by
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

/-- An X instruction or continuation is never itself a new Xi frame root. -/
theorem x_nonempty {fuel : Nat} {vj : Array UInt256} {pre : EVM.State}
    {result : XResult} {tree : EventTree} {path : EventTree.Address}
    {f : Nat} {a : XiArgs} {r : XiResult}
    (h : XiAt (.x fuel vj pre) result tree path f a r) : path ≠ [] := by
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

/-- Every actual Xi location obeys the owning-frame grammar. -/
theorem frame_root {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {f : Nat} {a : XiArgs} {r : XiResult}
    (h : XiAt q result tree path f a r) : FrameRoot path := by
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
    {path : EventTree.Address} {f : Nat} {a : XiArgs} {r : XiResult}
    (h : XiAt q result tree path f a r) :
    ∃ innerTree, Cert (.xi f a) r innerTree ∧
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

#print axioms cert_top
#print axioms sound_top
#print axioms sound_inner
#print axioms x_nonempty
#print axioms frame_root
#print axioms at_tree
end XiAt
end Eip8282.Audit.Integrator.NestedEvents
