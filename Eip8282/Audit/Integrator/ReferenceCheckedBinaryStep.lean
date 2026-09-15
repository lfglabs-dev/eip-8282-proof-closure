import Eip8282.Audit.Integrator.ReferenceSourceStackAdmission
import Eip8282.Audit.Integrator.Topics.ReferenceRuntime
import Eip8282.Audit.Integrator.Topics.ReferenceMeter

/-! Checked handlers for the ten protected binary operations. Audited EL pin
0cc100eb190b64b23baba72dac0165652eaec252, full bodies archived in
 audit/receipts/direct-reference-amsterdam-gas-sources-20260910.json:
arithmetic.py SHA2567bd39760ffa9c27334129a89974d863362579dc1d221d09983532dec4be81d9f
(add28-52,sub55-79,mul82-106,div109-136), comparison.py
45a320c05063bb8d1d281a5383f73a936961552e3b29c08f0e9ac7ccc8916700
(LT24-48,GT77-101,EQ130-154), bitwise.py
 e48944ae09c914f44e348e68de107f3af52233504772a8d6077e6d9bd1449f22
(AND24-46,SHL159-186,SHR189-216). All pop twice, charge, compute,
push, then increment PC. Shifts pop shift FIRST and value SECOND.
Gas.py80-81,180-202 supplies3 except MUL/DIV5;389-403 raises OOG
before decrement. Its SHA256 is41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c.
Failures retain completed pops and successful charges, with PC unchanged.
Outer exception forfeiture and journal rollback are separate. The handler
transcription and word formulas are audited; this is not Python extraction. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedBinaryStep
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceWordOps
open ReferenceMeterRollback ReferenceMeterBoundary
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

inductive Failure where
  | stack (reason : ReferenceSourceStackAdmission.Failure)
  | outOfGas
  deriving DecidableEq

/-- Exact fixed source execution charge; no memory expansion occurs. -/
def charge : Binary → Nat
  | .mul | .div => 5
  | _ => 3

/-- Error carries the literal partially mutated view and meter. In particular,
OOG has already popped both operands but has not changed the execution meter. -/
def run (b : Binary) (v : View) (meter : Meter) :
    Except (Failure × View × Meter) (View × Meter) :=
  match ReferenceSourceStackAdmission.pop v.stack with
  | .error e => .error (.stack e,v,meter)
  | .ok (first,x) =>
    let v1 := {v with stack := first}
    match ReferenceSourceStackAdmission.pop first with
    | .error e => .error (.stack e,v1,meter)
    | .ok (rest,y) =>
      let v2 := {v with stack := rest}
      match ReferenceStorageGas.chargeExecution (core meter) (charge b) with
      | none => .error (.outOfGas,v2,meter)
      | some charged =>
        let m := update meter charged
        let value := UInt256.ofNat (reference b x.toNat y.toNat)
        match ReferenceSourceStackAdmission.push value rest with
        | .error e => .error (.stack e,v2,m)
        | .ok nextStack => .ok ({v with stack := nextStack,pc := v.pc+1},m)

private theorem success_shape {b : Binary} {v next : View} {meter final : Meter}
    (actual : run b v meter = .ok (next,final)) :
    ∃ x y rest charged,
      v.stack = x::y::rest ∧
      ReferenceStorageGas.chargeExecution (core meter) (charge b) = some charged ∧
      next = {v with stack := UInt256.ofNat (reference b x.toNat y.toNat)::rest,pc := v.pc+1} ∧
      final = update meter charged := by
  unfold run at actual
  cases hs : v.stack with
  | nil => simp only [hs,ReferenceSourceStackAdmission.pop] at actual; contradiction
  | cons x first =>
    simp only [hs,ReferenceSourceStackAdmission.pop] at actual
    cases first with
    | nil => contradiction
    | cons y rest =>
      cases hc : ReferenceStorageGas.chargeExecution (core meter) (charge b) with
      | none => simp only [hc] at actual; contradiction
      | some charged =>
        simp only [hc] at actual
        cases hp : ReferenceSourceStackAdmission.push
            (UInt256.ofNat (reference b x.toNat y.toNat)) rest with
        | error e => simp only [hp] at actual; contradiction
        | ok nextStack =>
          simp only [hp] at actual
          cases actual
          have nextEq : nextStack = UInt256.ofNat (reference b x.toNat y.toNat)::rest := by
            unfold ReferenceSourceStackAdmission.push at hp
            split at hp
            · contradiction
            · cases hp; rfl
          subst nextStack
          exact ⟨x,y,rest,charged,rfl,rfl,rfl,rfl⟩

/-- Successful checked execution supplies the effect, literal payment, source
price and post-stack bound. No Action, old Z, gas bound or operand shape input. -/
theorem success {b : Binary} {v next : View} {meter final : Meter}
    (kind : Kind) (parent : ReferenceStorageView.Parent) (warm : ReferenceSourceReadings.Warm)
    (initial : v.stack.length ≤ 1024) (actual : run b v meter = .ok (next,final)) :
    ReferencePureAction.action kind (opcode b,none) v = some next ∧
    ReferenceRuntimeAction.Action kind parent (opcode b,none) v next ∧
    ReferenceRuntimeReadings.Price parent v warm next (opcode b) (.ordinary (charge b)) ∧
    runFull [.ordinary (charge b)] meter = some final ∧ next.stack.length ≤ 1024 := by
  obtain ⟨x,y,rest,charged,shape,hcharge,rfl,rfl⟩ := success_shape actual
  have action : ReferencePureAction.action kind (opcode b,none) v =
      some {v with stack := UInt256.ofNat (reference b x.toNat y.toNat)::rest,pc := v.pc+1} := by
    cases b <;> simp [ReferencePureAction.action,ReferencePureAction.classify,
      ReferencePureAction.familyAction,ReferencePureAction.advance,stackAction,opcode,shape]
  refine ⟨action,.base (.pure action),?_,?_,?_⟩
  · cases b <;> simp [ReferenceRuntimeReadings.Price,ReferenceCopyLogGas.ordinaryCost,
      ReferenceOrdinaryGas.ordinaryCost,opcode,charge,words]
  · simp only [runFull,ReferenceMeterPath.run,ReferenceMeterPath.pay,hcharge,Option.bind_some,Option.map_some]
  · rw [shape] at initial
    simp only [List.length_cons] at initial ⊢
    omega

/-- First-pop underflow preserves the entire input context. -/
theorem empty (b : Binary) (v : View) (meter : Meter) (stack : v.stack = []) :
    run b v meter = .error (.stack .underflow,v,meter) := by
  simp only [run,stack,ReferenceSourceStackAdmission.pop]

/-- Second-pop underflow retains the first pop but performs no gas charge. -/
theorem one (b : Binary) (v : View) (meter : Meter) (x : UInt256) (stack : v.stack = [x]) :
    run b v meter = .error (.stack .underflow,{v with stack := []},meter) := by
  simp only [run,stack,ReferenceSourceStackAdmission.pop]

/-- OOG leaves both popped operands removed and the meter unchanged. -/
theorem out_of_gas (b : Binary) (v : View) (meter : Meter) (x y : UInt256)
    (rest : List UInt256) (stack : v.stack = x::y::rest) (insufficient : meter.execution < charge b) :
    run b v meter = .error (.outOfGas,{v with stack := rest},meter) := by
  simp only [run,stack,ReferenceSourceStackAdmission.pop,ReferenceStorageGas.chargeExecution,core]
  rw [if_neg (by omega)]

/-- Literal equality1024 push guard: this injected overfull input is excluded
by normal bounded entry, but its failure must retain the already paid charge. -/
theorem overflow (b : Binary) (v : View) (meter : Meter) (x y : UInt256)
    (rest : List UInt256) (stack : v.stack = x::y::rest) (full : rest.length = 1024)
    (charged : ReferenceStorageGas.Meter)
    (paid : ReferenceStorageGas.chargeExecution (core meter) (charge b) = some charged) :
    run b v meter = .error (.stack .overflow,{v with stack := rest},update meter charged) := by
  simp only [run,stack,ReferenceSourceStackAdmission.pop,paid,ReferenceSourceStackAdmission.push,full,if_pos]

#print axioms success
#print axioms empty
#print axioms one
#print axioms out_of_gas
#print axioms overflow
end Eip8282.Audit.Integrator.ReferenceCheckedBinaryStep
