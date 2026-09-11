import Eip8282.Audit.Integrator.NestedEventArgs
import Eip8282.Audit.Integrator.EventTree

/-!
# Certificates of every actual nested evaluator outcome

X owns the executed local marker and continuation. A step owns exactly its
selected child. Wrapper nodes are transparent. In particular a failed step
retains a selected child's tree even when the child error is caught, propagated,
or followed by CREATE's rejecting final word-gas guard.
-/
namespace Eip8282.Audit.Integrator.NestedEvents
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open SuccessInversion
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- The explicit instruction and states before and after memory charging of literal X. -/
def StepArgs.ofGuard (vj : Array UInt256) (pre mid : EVM.State) (cost : Nat)
    (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost)) : StepArgs :=
  { vj := vj, pre := pre, mid := mid, cost := cost,
    op := (decodeAt pre).1, arg := (decodeAt pre).2, guard := hz }

/-- The full Except result is indexed; no success assumption erases children. -/
inductive Cert : (q : Request) → q.Outcome → EventTree → Prop where
  | xZero (vj : Array UInt256) (pre : EVM.State) :
      Cert (.x 0 vj pre) (.error .OutOfFuel) .done
  | xGuardError {n : Nat} {vj : Array UInt256} {pre : EVM.State} {err : ExecutionException}
      (hz : Z vj (decodeAt pre).1 pre = .error err) :
      Cert (.x (n+1) vj pre) (.error err) .done
  | xStepError {n cost : Nat} {vj : Array UInt256} {pre mid : EVM.State}
      {err : ExecutionException} {child : EventTree}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.error err) child) :
      Cert (.x (n+1) vj pre) (.error err) (.step false child .done)
  | xNext {n cost : Nat} {vj : Array UInt256} {pre mid post : EVM.State}
      {result : XResult} {child next : EventTree}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = none)
      (tail : Cert (.x n vj post) result next) :
      Cert (.x (n+1) vj pre) result (.step (decide (FrameEvents.Marked pre)) child next)
  | xHalt {n cost : Nat} {vj : Array UInt256} {pre mid post : EVM.State}
      {out : ByteArray} {child : EventTree}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = some out)
      (hn : (decodeAt pre).1 ≠ .REVERT) :
      Cert (.x (n+1) vj pre) (.ok (.success post out))
        (.step (decide (FrameEvents.Marked pre)) child .done)
  | xRevert {n cost : Nat} {vj : Array UInt256} {pre mid post : EVM.State}
      {out : ByteArray} {child : EventTree}
      (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
      (hs : Cert (.step n (StepArgs.ofGuard vj pre mid cost hz)) (.ok post) child)
      (hh : H post.toMachineState (decodeAt pre).1 = some out)
      (hr : (decodeAt pre).1 = .REVERT) :
      Cert (.x (n+1) vj pre) (.ok (.revert post.gasAvailable out))
        (.step (decide (FrameEvents.Marked pre)) child .done)
  | xiZero (a : XiArgs) : Cert (.xi 0 a) (.error .OutOfFuel) .done
  | xi {n : Nat} {a : XiArgs} {tree : EventTree}
      (body : Cert (.x n a.jumps a.entry) (Request.x n a.jumps a.entry).eval tree) :
      Cert (.xi (n+1) a) (Request.xi (n+1) a).eval tree
  | thetaZero (a : ThetaArgs) : Cert (.theta 0 a) (.error .OutOfFuel) .done
  | thetaPrecompile {n : Nat} {a : ThetaArgs} (target : AccountAddress)
      (hc : a.code = .Precompiled target) :
      Cert (.theta (n+1) a) (Request.theta (n+1) a).eval .done
  | thetaCode {n : Nat} {a : ThetaArgs} (bytes : ByteArray) {tree : EventTree}
      (hc : a.code = .Code bytes)
      (body : Cert (.xi n (a.xiArgs bytes)) (Request.xi n (a.xiArgs bytes)).eval tree) :
      Cert (.theta (n+1) a) (Request.theta (n+1) a).eval tree
  | lambdaZero (a : LambdaArgs) : Cert (.lambda 0 a) (.error .OutOfFuel) .done
  | lambdaNoPreimage {n : Nat} {a : LambdaArgs} (hp : a.preimage = none) :
      Cert (.lambda (n+1) a) (Request.lambda (n+1) a).eval .done
  | lambdaInit {n : Nat} {a : LambdaArgs} (bytes : ByteArray) {tree : EventTree}
      (hp : a.preimage = some bytes)
      (body : Cert (.xi n (a.xiArgs bytes)) (Request.xi n (a.xiArgs bytes)).eval tree) :
      Cert (.lambda (n+1) a) (Request.lambda (n+1) a).eval tree
  | stepNone {n : Nat} {a : StepArgs} (hc : StepChild n a none) :
      Cert (.step n a) (Request.step n a).eval .done
  | stepChild {n : Nat} {a : StepArgs} {q : Request} {tree : EventTree}
      (hc : StepChild n a (some q)) (body : Cert q q.eval tree) :
      Cert (.step n a) (Request.step n a).eval tree

/-- Certificates erase to the same literal evaluator, including error outcomes. -/
theorem sound {q : Request} {result : q.Outcome} {tree : EventTree}
    (h : Cert q result tree) : q.eval = result := by
  induction h with
  | xZero => rfl
  | xGuardError hz => exact X_succ_of_Z_error rfl hz
  | xStepError hz _ ih => exact X_succ_of_step_error rfl hz ih
  | xNext hz _ hh _ ihs iht => exact (X_succ_of_continue rfl hz ihs hh).trans iht
  | xHalt hz _ hh hn ih => exact X_succ_of_halt rfl hz ih hh hn
  | xRevert hz _ hh hr ih => exact X_succ_of_revert rfl hz ih hh hr
  | xiZero => rfl
  | xi => rfl
  | thetaZero => rfl
  | thetaPrecompile => rfl
  | thetaCode => rfl
  | lambdaZero => rfl
  | lambdaNoPreimage => rfl
  | lambdaInit => rfl
  | stepNone => rfl
  | stepChild => rfl

theorem outcome_deterministic {q : Request} {r₁ r₂ : q.Outcome} {t₁ t₂ : EventTree}
    (h₁ : Cert q r₁ t₁) (h₂ : Cert q r₂ t₂) : r₁ = r₂ :=
  (sound h₁).symm.trans (sound h₂)

#print axioms sound
end Eip8282.Audit.Integrator.NestedEvents
