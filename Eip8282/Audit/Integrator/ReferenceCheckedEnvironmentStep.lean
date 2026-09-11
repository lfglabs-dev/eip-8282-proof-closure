import Eip8282.Audit.Integrator.ReferenceCheckedBinaryStep

/-! Audited checked EL handlers at 0cc100eb190b64b23baba72dac0165652eaec252.
Full bodies: audit/receipts/direct-reference-amsterdam-gas-sources-20260910.json.
environment.py SHA2568c57bd699b99ff8b4d8e41e6a9c89cd1a03dda8160bf1d6dffe091932ec03657,
CALLER113-133, CALLVALUE136-156, CALLDATALOAD159-182, CALLDATASIZE185-205;
comparison.py45a320c05063bb8d1d281a5383f73a936961552e3b29c08f0e9ac7ccc8916700,
ISZERO157-180; control_flow.pyb6b481918211a8e86ded3acd9ec13e940ba05860786e584913478aec13abc0c3,
JUMPDEST152-174. Unary handlers pop before charging; all pushes follow charge.
CALLDATASIZE checks U256 conversion after charge, before push (never modulo).
Errors retain partial mutations; outer forfeiture/rollback is separate.
Caller/value types, buffer semantics and handlers are audited transcriptions,
not an extraction theorem for Python or a canonical frame binding. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedEnvironmentStep
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceMeterRollback ReferenceMeterBoundary
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

inductive Handler where
  | caller | value | size | load | iszero | jumpdest
  deriving DecidableEq

inductive Failure where
  | checked (reason : ReferenceCheckedBinaryStep.Failure)
  | conversionOverflow
  deriving DecidableEq

def opcode : Handler → Operation .EVM
  | .caller => .CALLER | .value => .CALLVALUE | .size => .CALLDATASIZE
  | .load => .CALLDATALOAD | .iszero => .ISZERO | .jumpdest => .JUMPDEST

def charge : Handler → Nat
  | .load | .iszero => 3 | .jumpdest => 1 | _ => 2

/-- None is checked conversion failure; some none is the no-push JUMPDEST.
The value calculation is pure; the failure is observed only after charging. -/
def finish (v : View) (rest : List UInt256) (value : Option (Option UInt256))
    (meter : Meter) (amount : Nat) : Except (Failure × View × Meter) (View × Meter) :=
  match ReferenceStorageGas.chargeExecution (core meter) amount with
  | none => .error (.checked .outOfGas,{v with stack := rest},meter)
  | some charged =>
    let m := update meter charged
    match value with
    | none => .error (.conversionOverflow,{v with stack := rest},m)
    | some none => .ok ({v with stack := rest,pc := v.pc+1},m)
    | some (some x) =>
      match ReferenceSourceStackAdmission.push x rest with
      | .error e => .error (.checked (.stack e),{v with stack := rest},m)
      | .ok stack => .ok ({v with stack := stack,pc := v.pc+1},m)

def run (h : Handler) (v : View) (meter : Meter) :
    Except (Failure × View × Meter) (View × Meter) :=
  match h with
  | .caller => finish v v.stack (some (some (UInt256.ofNat v.env.source.val))) meter 2
  | .value => finish v v.stack (some (some v.env.weiValue)) meter 2
  | .size => finish v v.stack
      (if v.env.calldata.size < UInt256.size then some (some (UInt256.ofNat v.env.calldata.size)) else none) meter 2
  | .jumpdest => finish v v.stack (some none) meter 1
  | .load | .iszero =>
    match ReferenceSourceStackAdmission.pop v.stack with
    | .error e => .error (.checked (.stack e),v,meter)
    | .ok (rest,x) => finish v rest (some (some
        (if h = .load then ReferenceEnvironmentOps.load v.env.calldata x.toNat
         else UInt256.ofNat (ReferenceWordOps.referenceIsZero x.toNat)))) meter 3

private theorem finish_success {v next : View} {rest : List UInt256}
    {value : Option (Option UInt256)} {meter final : Meter} {amount : Nat}
    (bound : rest.length ≤ 1024) (actual : finish v rest value meter amount = .ok (next,final)) :
    ∃ output charged,
      value = some output ∧
      ReferenceStorageGas.chargeExecution (core meter) amount = some charged ∧
      next = {v with stack := match output with | none => rest | some x => x::rest,pc := v.pc+1} ∧
      final = update meter charged ∧ next.stack.length ≤ 1024 := by
  unfold finish at actual
  cases hc : ReferenceStorageGas.chargeExecution (core meter) amount with
  | none => simp only [hc] at actual; contradiction
  | some charged =>
    simp only [hc] at actual
    cases value with
    | none => contradiction
    | some output =>
      cases output with
      | none => cases actual; exact ⟨none,charged,rfl,rfl,rfl,rfl,bound⟩
      | some x =>
        cases hp : ReferenceSourceStackAdmission.push x rest with
        | error e => simp only [hp] at actual; contradiction
        | ok stack =>
          simp only [hp] at actual
          cases actual
          have hb := (ReferenceSourceStackAdmission.push_length bound hp).2
          have he : stack = x::rest := by
            unfold ReferenceSourceStackAdmission.push at hp
            split at hp
            · contradiction
            · cases hp; rfl
          subst stack
          exact ⟨some x,charged,rfl,rfl,rfl,rfl,hb⟩

/-- Successful literal checked handler supplies its action and exact payment.
No old Z, supplied operand shape, calldata fit or desired postcondition. -/
theorem success {h : Handler} {v next : View} {meter final : Meter}
    (kind : Kind) (parent : ReferenceStorageView.Parent) (warm : ReferenceSourceReadings.Warm)
    (initial : v.stack.length ≤ 1024) (actual : run h v meter = .ok (next,final)) :
    ReferencePureAction.action kind (opcode h,none) v = some next ∧
    ReferenceRuntimeAction.Action kind parent (opcode h,none) v next ∧
    ReferenceRuntimeReadings.Price parent v warm next (opcode h) (.ordinary (charge h)) ∧
    runFull [.ordinary (charge h)] meter = some final ∧ next.stack.length ≤ 1024 := by
  have bridge : ReferencePureAction.action kind (opcode h,none) v = some next ∧
      runFull [.ordinary (charge h)] meter = some final ∧ next.stack.length ≤ 1024 ∧ next.memory = v.memory := by
    cases h <;> cases shape : v.stack <;>
      simp only [run,shape,ReferenceSourceStackAdmission.pop,ite_true,
        show Handler.iszero ≠ Handler.load by decide,ite_false] at actual
    all_goals try contradiction
    all_goals try (split at actual)
    all_goals obtain ⟨output,charged,ho,hc,hn,hf,hb⟩ := finish_success (by first | exact initial | rw [shape] at initial; simp only [List.length_cons, List.length_nil] at initial ⊢; omega) actual
    all_goals try contradiction
    all_goals cases ho
    all_goals subst next; subst final
    all_goals
      refine ⟨?_,?_,hb,rfl⟩
      · simp [opcode,ReferencePureAction.action,ReferencePureAction.classify,
          ReferencePureAction.familyAction,ReferencePureAction.advance,stackAction, *]
      · simp only [charge,runFull,ReferenceMeterPath.run,ReferenceMeterPath.pay,
          hc,Option.bind_some,Option.map_some]
  obtain ⟨ha,hpaid,hbound,memory⟩ := bridge
  refine ⟨ha,.base (.pure ha),?_,hpaid,hbound⟩
  cases h <;> simp [ReferenceRuntimeReadings.Price,ReferenceCopyLogGas.ordinaryCost,
    ReferenceOrdinaryGas.ordinaryCost,opcode,charge,words,memory]

/-- Unary underflow occurs before charging. -/
theorem underflow (h : Handler) (v : View) (meter : Meter)
    (unary : h = .load ∨ h = .iszero) (empty : v.stack = []) :
    run h v meter = .error (.checked (.stack .underflow),v,meter) := by
  rcases unary with rfl | rfl <;> simp only [run,empty,ReferenceSourceStackAdmission.pop]

/-- Checked size conversion fails after payment, without a push or PC change. -/
theorem size_overflow (v : View) (meter : Meter) (charged : ReferenceStorageGas.Meter)
    (large : UInt256.size ≤ v.env.calldata.size)
    (paid : ReferenceStorageGas.chargeExecution (core meter) 2 = some charged) :
    run .size v meter = .error (.conversionOverflow,v,update meter charged) := by
  simp [run,finish,paid,show ¬ v.env.calldata.size < UInt256.size by omega]

/-- OOG retains the supplied already-popped stack and does not debit the meter. -/
theorem finish_out_of_gas (v : View) (rest : List UInt256)
    (value : Option (Option UInt256)) (meter : Meter) (amount : Nat)
    (insufficient : meter.execution < amount) :
    finish v rest value meter amount =
      .error (.checked .outOfGas,{v with stack := rest},meter) := by
  simp [finish,ReferenceStorageGas.chargeExecution,core,show ¬ amount ≤ meter.execution by omega]

/-- Stack overflow follows payment; no rollback of the earlier pop or charge. -/
theorem finish_overflow (v : View) (rest : List UInt256) (x : UInt256)
    (meter : Meter) (amount : Nat) (charged : ReferenceStorageGas.Meter)
    (full : rest.length = 1024)
    (paid : ReferenceStorageGas.chargeExecution (core meter) amount = some charged) :
    finish v rest (some (some x)) meter amount =
      .error (.checked (.stack .overflow),{v with stack := rest},update meter charged) := by
  simp only [finish,paid,ReferenceSourceStackAdmission.push,full,if_pos]

#print axioms underflow
#print axioms size_overflow
#print axioms finish_out_of_gas
#print axioms finish_overflow

#print axioms success
end Eip8282.Audit.Integrator.ReferenceCheckedEnvironmentStep
