import Eip8282.Audit.Integrator.NestedCallOccurrence
import Eip8282.Audit.Integrator.Topics.Creation
import Eip8282.Audit.Integrator.NestedEventExtract

/-!
# Every request retained by the actual execution certificate

This location relation annotates the existing Cert edges, including wrapper,
selected-child and continuation nodes. It introduces no interpreter and no
new counting metric. Transparent wrappers may share an event path: this
relation is for all-node predicates, not distinct invocation counting.
-/
namespace Eip8282.Audit.Integrator.NestedEvents
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

inductive RequestAt : (q : Request) → q.Outcome → EventTree → EventTree.Address →
    (inner : Request) → inner.Outcome → Prop where
  | here {q : Request} {r : q.Outcome} {tree : EventTree}
      (body : Cert q r tree) : RequestAt q r tree [] q r
  | xStepError {n cost : Nat} {vj : Array UInt256} {pre mid : EVM.State}
      {err : ExecutionException} {child : EventTree} {path : EventTree.Address}
      {inner : Request} {r : inner.Outcome}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.error err) child)
      (loc : RequestAt (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.error err) child path inner r) :
      RequestAt (.x (n+1) vj pre) (.error err) (.step false child .done) (false::path) inner r
  | xNextChild {n cost : Nat} {vj : Array UInt256} {pre mid post : EVM.State}
      {result : XResult} {child next : EventTree} {path : EventTree.Address}
      {inner : Request} {r : inner.Outcome}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = none)
      (tail : Cert (.x n vj post) result next)
      (loc : RequestAt (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child path inner r) :
      RequestAt (.x (n+1) vj pre) result (.step (decide (FrameEvents.Marked pre)) child next)
        (false::path) inner r
  | xNextTail {n cost : Nat} {vj : Array UInt256} {pre mid post : EVM.State}
      {result : XResult} {child next : EventTree} {path : EventTree.Address}
      {inner : Request} {r : inner.Outcome}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = none)
      (tail : Cert (.x n vj post) result next)
      (loc : RequestAt (.x n vj post) result next path inner r) :
      RequestAt (.x (n+1) vj pre) result (.step (decide (FrameEvents.Marked pre)) child next)
        (true::path) inner r
  | xHalt {n cost : Nat} {vj : Array UInt256} {pre mid post : EVM.State}
      {out : ByteArray} {child : EventTree} {path : EventTree.Address}
      {inner : Request} {r : inner.Outcome}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = some out)
      (hn : (decodeAt pre).1 ≠ .REVERT)
      (loc : RequestAt (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child path inner r) :
      RequestAt (.x (n+1) vj pre) (.ok (.success post out))
        (.step (decide (FrameEvents.Marked pre)) child .done) (false::path) inner r
  | xRevert {n cost : Nat} {vj : Array UInt256} {pre mid post : EVM.State}
      {out : ByteArray} {child : EventTree} {path : EventTree.Address}
      {inner : Request} {r : inner.Outcome}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = some out)
      (hr : (decodeAt pre).1 = .REVERT)
      (loc : RequestAt (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child path inner r) :
      RequestAt (.x (n+1) vj pre) (.ok (.revert post.gasAvailable out))
        (.step (decide (FrameEvents.Marked pre)) child .done) (false::path) inner r
  | xi {n : Nat} {outer : XiArgs} {inner : Request} {tree : EventTree} {path : EventTree.Address} {r : inner.Outcome}
      (body : Cert (.x n outer.jumps outer.entry) (Request.x n outer.jumps outer.entry).eval tree)
      (loc : RequestAt (.x n outer.jumps outer.entry) (Request.x n outer.jumps outer.entry).eval tree path inner r) :
      RequestAt (.xi (n+1) outer) (Request.xi (n+1) outer).eval tree path inner r
  | thetaCode {n : Nat} {outer : ThetaArgs} {inner : Request} {r : inner.Outcome}
      (bytes : ByteArray) {tree : EventTree} {path : EventTree.Address}
      (hc : outer.code = .Code bytes)
      (body : Cert (.xi n (outer.xiArgs bytes)) (Request.xi n (outer.xiArgs bytes)).eval tree)
      (loc : RequestAt (.xi n (outer.xiArgs bytes)) (Request.xi n (outer.xiArgs bytes)).eval tree path inner r) :
      RequestAt (.theta (n+1) outer) (Request.theta (n+1) outer).eval tree path inner r
  | lambdaInit {n : Nat} {outer : LambdaArgs} {inner : Request} {r : inner.Outcome}
      (bytes : ByteArray) {tree : EventTree} {path : EventTree.Address}
      (hp : outer.preimage = some bytes)
      (body : Cert (.xi n (outer.xiArgs bytes)) (Request.xi n (outer.xiArgs bytes)).eval tree)
      (loc : RequestAt (.xi n (outer.xiArgs bytes)) (Request.xi n (outer.xiArgs bytes)).eval tree path inner r) :
      RequestAt (.lambda (n+1) outer) (Request.lambda (n+1) outer).eval tree path inner r
  | stepChild {n : Nat} {outer : StepArgs} {q : Request} {inner : Request} {r : inner.Outcome}
      {tree : EventTree} {path : EventTree.Address}
      (hc : StepChild n outer (some q)) (body : Cert q q.eval tree)
      (loc : RequestAt q q.eval tree path inner r) :
      RequestAt (.step n outer) (Request.step n outer).eval tree path inner r

namespace RequestAt

theorem cert_top {q inner : Request} {result : q.Outcome} {r : inner.Outcome}
    {tree : EventTree} {path : EventTree.Address}
    (h : RequestAt q result tree path inner r) : Cert q result tree := by
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

theorem cert_inner {q inner : Request} {result : q.Outcome} {r : inner.Outcome}
    {tree : EventTree} {path : EventTree.Address}
    (h : RequestAt q result tree path inner r) : ∃ innerTree, Cert inner r innerTree := by
  induction h with
  | here body => exact ⟨_,body⟩
  | xStepError _ _ _ ih => exact ih
  | xNextChild _ _ _ _ _ ih => exact ih
  | xNextTail _ _ _ _ _ ih => exact ih
  | xHalt _ _ _ _ _ ih => exact ih
  | xRevert _ _ _ _ _ ih => exact ih
  | xi _ _ ih => exact ih
  | thetaCode _ _ _ _ ih => exact ih
  | lambdaInit _ _ _ _ ih => exact ih
  | stepChild _ _ _ ih => exact ih

theorem sound_inner {q inner : Request} {result : q.Outcome} {r : inner.Outcome}
    {tree : EventTree} {path : EventTree.Address}
    (h : RequestAt q result tree path inner r) : inner.eval = r := by
  obtain ⟨_,hc⟩ := cert_inner h
  exact sound hc

/-- Transparent request wrappers share event paths but remain different
requests; no uniqueness of requests at a path is asserted by this relation. -/
theorem compose {q inner deepest : Request} {result : q.Outcome}
    {r : inner.Outcome} {s : deepest.Outcome} {tree innerTree : EventTree}
    {path nextPath : EventTree.Address}
    (outer : RequestAt q result tree path inner r)
    (nested : RequestAt inner r innerTree nextPath deepest s) :
    RequestAt q result tree (path ++ nextPath) deepest s := by
  induction outer with
  | here body =>
    have he := NestedEvents.deterministic (cert_top nested) body
    subst innerTree
    exact nested
  | xStepError hz hs _ ih => exact .xStepError hz hs (ih nested)
  | xNextChild hz hs hh ht _ ih => exact .xNextChild hz hs hh ht (ih nested)
  | xNextTail hz hs hh ht _ ih => exact .xNextTail hz hs hh ht (ih nested)
  | xHalt hz hs hh hn _ ih => exact .xHalt hz hs hh hn (ih nested)
  | xRevert hz hs hh hr _ ih => exact .xRevert hz hs hh hr (ih nested)
  | xi body _ ih => exact .xi body (ih nested)
  | thetaCode bytes hc body _ ih => exact .thetaCode bytes hc body (ih nested)
  | lambdaInit bytes hp body _ ih => exact .lambdaInit bytes hp body (ih nested)
  | stepChild hc body _ ih => exact .stepChild hc body (ih nested)

private def ThetaProjection (q : Request) (result : q.Outcome) (tree : EventTree)
    (path : EventTree.Address) : (inner : Request) → inner.Outcome → Prop
  | .theta fuel a, r => ThetaAt q result tree path fuel a r
  | _, _ => True

private theorem theta_projection {q inner : Request} {result : q.Outcome} {r : inner.Outcome}
    {tree : EventTree} {path : EventTree.Address}
    (h : RequestAt q result tree path inner r) : ThetaProjection q result tree path inner r := by
  induction h with
  | @here q r tree body => cases q <;> first | exact True.intro | exact ThetaAt.here body
  | @xStepError n cost vj pre mid err child path inside r hz hs loc ih =>
    cases inside <;> first | exact True.intro | exact ThetaAt.xStepError hz hs ih
  | @xNextChild n cost vj pre mid post result child next path inside r hz hs hh ht loc ih =>
    cases inside <;> first | exact True.intro | exact ThetaAt.xNextChild hz hs hh ht ih
  | @xNextTail n cost vj pre mid post result child next path inside r hz hs hh ht loc ih =>
    cases inside <;> first | exact True.intro | exact ThetaAt.xNextTail hz hs hh ht ih
  | @xHalt n cost vj pre mid post out child path inside r hz hs hh hn loc ih =>
    cases inside <;> first | exact True.intro | exact ThetaAt.xHalt hz hs hh hn ih
  | @xRevert n cost vj pre mid post out child path inside r hz hs hh hr loc ih =>
    cases inside <;> first | exact True.intro | exact ThetaAt.xRevert hz hs hh hr ih
  | @xi n outer inside tree path r body loc ih => cases inside <;> first | exact True.intro | exact ThetaAt.xi body ih
  | @thetaCode n outer inside r bytes tree path hc body loc ih =>
    cases inside <;> first | exact True.intro | exact ThetaAt.thetaCode bytes hc body ih
  | @lambdaInit n outer inside r bytes tree path hp body loc ih =>
    cases inside <;> first | exact True.intro | exact ThetaAt.lambdaInit bytes hp body ih
  | @stepChild n outer q inside r tree path hc body loc ih =>
    cases inside <;> first | exact True.intro | exact ThetaAt.stepChild hc body ih

theorem theta {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {fuel : Nat} {a : ThetaArgs} {r : ThetaResult}
    (h : RequestAt q result tree path (.theta fuel a) r) :
    ThetaAt q result tree path fuel a r := theta_projection h

end RequestAt

/-- A property at every actual retained request, including those below caught
errors. The certificate's own root is included, not just its descendants. -/
def Every (P : (q : Request) → q.Outcome → Prop)
    (q : Request) (result : q.Outcome) (tree : EventTree) : Prop :=
  ∀ (path : EventTree.Address) (inner : Request) (r : inner.Outcome),
    RequestAt q result tree path inner r → P inner r

theorem Every.root {P : (q : Request) → q.Outcome → Prop}
    {q : Request} {result : q.Outcome} {tree : EventTree}
    (h : Every P q result tree) (cert : Cert q result tree) : P q result :=
  h [] q result (.here cert)

theorem Every.descendant {P : (q : Request) → q.Outcome → Prop}
    {q inner : Request} {result : q.Outcome} {r : inner.Outcome}
    {tree innerTree : EventTree} {path : EventTree.Address}
    (h : Every P q result tree) (loc : RequestAt q result tree path inner r) :
    Every P inner r innerTree := by
  intro p deepest s inside
  exact h (path++p) deepest s (RequestAt.compose loc inside)

def NoOutOfFuel : (q : Request) → q.Outcome → Prop
  | .x .., r => r ≠ .error .OutOfFuel
  | .xi .., r => r ≠ .error .OutOfFuel
  | .theta .., r => r ≠ .error .OutOfFuel
  | .lambda .., r => r ≠ .error .OutOfFuel
  | .step .., r => r ≠ .error .OutOfFuel

/-- All-node adequacy, when produced from resources, closes the caught-Lambda
error branch. Returned failure remains allowed and is not confused with success. -/
theorem lambda_returns {q : Request} {result : q.Outcome} {tree : EventTree}
    (safe : Every NoOutOfFuel q result tree)
    {path : EventTree.Address} {fuel : Nat} {a : LambdaArgs} {r : LambdaResult}
    (loc : RequestAt q result tree path (.lambda fuel a) r) :
    ∃ returned, (Request.lambda fuel a).eval = .ok returned := by
  have hr := RequestAt.sound_inner loc
  have hn := safe path (.lambda fuel a) r loc
  cases r with
  | ok returned => exact ⟨returned,hr⟩
  | error err =>
    have he := CreationErrorScope.lambda_error hr
    subst err
    exact False.elim (hn rfl)

#print axioms RequestAt.cert_top
#print axioms RequestAt.cert_inner
#print axioms RequestAt.compose
#print axioms RequestAt.theta
#print axioms Every.descendant
#print axioms lambda_returns
end Eip8282.Audit.Integrator.NestedEvents

