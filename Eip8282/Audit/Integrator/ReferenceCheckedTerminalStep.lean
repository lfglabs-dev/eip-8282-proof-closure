import Eip8282.Audit.Integrator.ReferenceCheckedCopyLogStep
import Eip8282.Audit.Integrator.ReferenceTerminalReplay

/-! Literal STOP/RETURN/REVERT terminal handlers, EL0cc100eb190b64b23baba72dac0165652eaec252.
Full archived control_flow.py25-45 and system.py314-344/994-1028. STOP leaves
output unchanged, stops running and increments source PC. RETURN/REVERT pop
twice, charge memory expansion, extend then read the actual output slice;
neither advances PC. RETURN stops running; REVERT raises its distinct signal.
End records these terminal signals (REVERT is not successful commitment).
Errors retain previous output and completed pops/charge before outer rollback.
Actual source dispatch, frame output initialization and enclosing exception/
journal settlement are separate from this audited handler transcription. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedTerminalStep
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceMemoryExpansionSource
open ReferenceActionMemoryBounds (Aligned)
open ReferenceCheckedBinaryStep (Failure)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

inductive Halt where
  | stop | returned | reverted
  deriving DecidableEq

structure End where
  halt : Halt
  view : View
  meter : Meter
  output : ByteArray

abbrev Partial := Failure × View × Meter × ByteArray

def opcode : Halt → Operation .EVM
  | .stop => .STOP | .returned => .RETURN | .reverted => .REVERT

/-- The returned End.reverted is the captured Revert signal; it requires its
own enclosing journal/gas settlement, not the success path. -/
def run (h : Halt) (v : View) (meter : Meter) (previousOutput : ByteArray) : Except Partial End :=
  if h = .stop then .ok ⟨h,{v with pc := v.pc+1},meter,previousOutput⟩ else
    match ReferenceSourceStackAdmission.pop v.stack with
    | .error e => .error (.stack e,v,meter,previousOutput)
    | .ok (first,off) =>
      match ReferenceSourceStackAdmission.pop first with
      | .error e => .error (.stack e,{v with stack := first},meter,previousOutput)
      | .ok (rest,len) =>
        match ReferenceStorageGas.chargeExecution (core meter)
            (calculate v.memory.size off.toNat len.toNat).cost with
        | none => .error (.outOfGas,{v with stack := rest},meter,previousOutput)
        | some charged =>
          let next := ReferenceCheckedCopyLogStep.expanded v off len rest
          .ok ⟨h,next,update meter charged,next.memory.extract off.toNat (off.toNat+len.toNat)⟩

/-- STOP preserves the incoming output; empty output must be derived from the
actual fresh protected frame, not silently substituted into the handler. -/
theorem stop (v : View) (meter : Meter) (previousOutput : ByteArray) :
    run .stop v meter previousOutput = .ok ⟨.stop,{v with pc := v.pc+1},meter,previousOutput⟩ := by
  simp only [run,if_true]

/-- Same checked terminal computation supplies both operands, actual extended
output and exact payment. PC/storage/logs remain those of the terminal entry. -/
theorem slice {h : Halt} {v : View} {meter : Meter} {previousOutput : ByteArray} {result : End}
    (notStop : h ≠ .stop) (aligned : Aligned v)
    (actual : run h v meter previousOutput = .ok result) :
    ∃ off len rest,
      v.stack = off::len::rest ∧ result.halt = h ∧
      result.view = ReferenceCheckedCopyLogStep.expanded v off len rest ∧
      result.output = ReferenceReturnView.output v off len ∧
      runFull [.ordinary (ReferenceTerminalReplay.charge v off len)] meter = some result.meter := by
  unfold run at actual
  rw [if_neg notStop] at actual
  cases shape : v.stack with
  | nil => simp only [shape,ReferenceSourceStackAdmission.pop] at actual; contradiction
  | cons off first =>
    simp only [shape,ReferenceSourceStackAdmission.pop] at actual
    cases first with
    | nil => contradiction
    | cons len rest =>
      dsimp only [ReferenceSourceStackAdmission.pop] at actual
      split at actual
      · contradiction
      · rename_i charged paid
        cases actual
        refine ⟨off,len,rest,rfl,rfl,rfl,ReferenceCheckedCopyLogStep.expanded_slice v off len rest aligned,?_⟩
        have price := (ReferenceMemoryExpansionSource.aligned (words v) off.toNat len.toNat).2
        rw [←aligned] at price
        change (calculate v.memory.size off.toNat len.toNat).cost = ReferenceTerminalReplay.charge v off len at price
        rw [←price]
        simp only [runFull,ReferenceMeterPath.run,ReferenceMeterPath.pay,paid,Option.bind_some,Option.map_some]

/-- A failed memory charge has already popped both operands and preserves the
previous output, original memory and current meter. -/
theorem out_of_gas (h : Halt) (v : View) (meter : Meter) (previousOutput : ByteArray)
    (off len : UInt256) (rest : List UInt256) (notStop : h ≠ .stop)
    (shape : v.stack = off::len::rest)
    (insufficient : meter.execution < (calculate v.memory.size off.toNat len.toNat).cost) :
    run h v meter previousOutput = .error (.outOfGas,{v with stack := rest},meter,previousOutput) := by
  simp only [run,if_neg notStop,shape,ReferenceSourceStackAdmission.pop,ReferenceStorageGas.chargeExecution,core]
  rw [if_neg (by omega)]

#print axioms stop
#print axioms slice
#print axioms out_of_gas
end Eip8282.Audit.Integrator.ReferenceCheckedTerminalStep
