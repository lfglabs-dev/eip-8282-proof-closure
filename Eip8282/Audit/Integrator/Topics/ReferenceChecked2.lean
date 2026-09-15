import Eip8282.Audit.Integrator.ReferenceActionMemoryBounds
import Eip8282.Audit.Integrator.ReferenceCheckedBinaryStep
import Eip8282.Audit.Integrator.ReferenceCheckedCopyLogStep
import Eip8282.Audit.Integrator.ReferenceCheckedStackControlStep
import Eip8282.Audit.Integrator.Topics.ReferenceMemory2
import Eip8282.Audit.Integrator.ReferenceSourceReplayTrace
import Eip8282.Audit.Integrator.ReferenceTerminalReplay

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceCheckedDecode -/

/-! Source decoder-to-checked-handler immediate binding. The decoder is the
existing audited EL0cc100eb transcript, with pinned parseInstr as opcode-name
translation. The finite tag-width equation is kernel-checked; no old decode,
Z, Action or actual execution is assumed. Right padding is preserved even for
truncated PUSH (where old interpreter parity is known to fail).
This does not add support for Amsterdam extended instructions: their dispatch
and semantics are not represented by this legacy opcode translation. Actual
source dispatch extraction and fixed-image exclusion of those tags remain the
separate decoder/body binding established by ReferenceDecodeSites.
The replay helper instruction.getD STOP conflates decode failure and EOF;
our fallback equation describes only that helper. Actual source dispatch must
check pc<code length and classify invalid tags as faults, not STOP. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedDecode
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceDecodeSites
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem extract_eq (bytes : ByteArray) (off width : Nat) :
    bytes.extract' off (off+width) = bytes.extract off (off+width) := by
  unfold ByteArray.extract'
  split
  · rfl
  · apply ByteArray.ext
    apply Array.toList_inj.mp
    simp [ReferenceEnvironmentOps.toList_eq,ByteArray.data_extract,Array.toList_extract,List.extract]

/-- Both source representations use the same natural-index slice and padding,
including arbitrary offsets and truncated code. No host-fit premise. -/
theorem padded_eq_buffer (bytes : ByteArray) (pc width : Nat) :
    paddedImmediate bytes pc width = ReferenceMemoryView.buffer bytes (pc+1) width := by
  have pad : width-(bytes.size-(pc+1)) = width-(min (pc+1+width) bytes.size-(pc+1)) := by omega
  apply ByteArray.ext
  simp [paddedImmediate,extract_eq,ReferenceMemoryView.buffer,pad]

private theorem tag_width (tag : UInt8) :
    (parseInstr tag).map argOnNBytesOfInstr =
      (parseInstr tag).map (fun _ => pushWidth tag) := by
  have all : ∀ t : Fin 256, (parseInstr (UInt8.ofNat t.val)).map argOnNBytesOfInstr =
      (parseInstr (UInt8.ofNat t.val)).map (fun _ => pushWidth (UInt8.ofNat t.val)) := by decide +kernel
  simpa using all ⟨tag.toNat,tag.toNat_lt⟩

/-- Successful source-shaped decoding determines its entire immediate, not
just the opcode. The table check concerns this decoder's supported opcode map. -/
theorem decode_width {bytes : ByteArray} {pc : Nat} {op : Operation .EVM}
    {arg : Option (UInt256 × Nat)} (actual : referenceDecode bytes pc = some (op,arg)) :
    arg = if argOnNBytesOfInstr op = 0 then none else
      some (uInt256OfByteArray (ReferenceMemoryView.buffer bytes (pc+1) (argOnNBytesOfInstr op)),
        argOnNBytesOfInstr op) := by
  cases ht : bytes[pc]? with
  | none => simp [referenceDecode,ht] at actual
  | some tag =>
    cases hp : parseInstr tag with
    | none => simp [referenceDecode,ht,hp] at actual
    | some decoded =>
      have ha : some (decoded, if pushWidth tag = 0 then none else
          some (uInt256OfByteArray (paddedImmediate bytes pc (pushWidth tag)),pushWidth tag)) = some (op,arg) := by
        simpa [referenceDecode,ht,hp] using actual
      cases ha
      have width := tag_width tag
      simp only [hp,Option.map_some,Option.some.injEq] at width
      rw [width,padded_eq_buffer]

private theorem instruction_width (v : View) :
    (ReferenceSourceReplayTrace.instruction v).2 =
      if argOnNBytesOfInstr (ReferenceSourceReplayTrace.instruction v).1 = 0 then none else
        some (uInt256OfByteArray (ReferenceMemoryView.buffer v.env.code (v.pc+1)
          (argOnNBytesOfInstr (ReferenceSourceReplayTrace.instruction v).1)),
          argOnNBytesOfInstr (ReferenceSourceReplayTrace.instruction v).1) := by
  cases hd : referenceDecode v.env.code v.pc with
  | none => simp [ReferenceSourceReplayTrace.instruction,hd,argOnNBytesOfInstr]
  | some pair =>
    rcases pair with ⟨op,arg⟩
    simpa only [ReferenceSourceReplayTrace.instruction,hd,Option.getD_some] using decode_width hd

/-- Opcode-only dispatch into checked StackControl automatically binds the
literal source code immediate; no supplied immediate equality or old site. -/
theorem stack_control (h : ReferenceCheckedStackControlStep.Handler) (v : View)
    (decoded : (ReferenceSourceReplayTrace.instruction v).1 = ReferenceCheckedStackControlStep.opcode h) :
    ReferenceSourceReplayTrace.instruction v = ReferenceCheckedStackControlStep.instruction h v := by
  apply Prod.ext
  · exact decoded
  · rw [instruction_width,decoded]
    rfl

/-- A zero-width opcode has no immediate, including the decoder's STOP
fallback. This is an instruction binding, not a source halt classification. -/
theorem nonpush (v : View) (op : Operation .EVM)
    (decoded : (ReferenceSourceReplayTrace.instruction v).1 = op)
    (width : argOnNBytesOfInstr op = 0) :
    ReferenceSourceReplayTrace.instruction v = (op,none) := by
  apply Prod.ext
  · exact decoded
  · rw [instruction_width,decoded,width]
    rfl

#print axioms padded_eq_buffer
#print axioms decode_width
#print axioms stack_control
#print axioms nonpush
end Eip8282.Audit.Integrator.ReferenceCheckedDecode

end

section

/-! ## ReferenceCheckedMemoryStore -/

/-! Checked MSTORE/MSTORE8: two ordered pops, literal single-span memory charge,
then eager extension and slice write, then PC increment. Amsterdam EL0cc100eb,
vm/instructions/memory.py31-93, full body in the49-file source archive.
The existing audited splice implements extension followed by source memory_write.
Actual source frame/buffer extraction and outer failure restoration are separate.
Raw expansion uses source Uint/Nat operations; alignment is needed only by the
successful replay theorem and is derived along initialized handler histories. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedMemoryStore
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceCheckedBinaryStep (Failure)
open ReferenceMemoryExpansionSource
open ReferenceActionMemoryBounds (Aligned)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def length (byte : Bool) : Nat := if byte then 1 else 32

def opcode (byte : Bool) : Operation .EVM := if byte then .MSTORE8 else .MSTORE

def data (byte : Bool) (value : UInt256) : ByteArray :=
  if byte then ⟨#[UInt8.ofNat (value.toNat%256)]⟩ else value.toByteArray

def run (byte : Bool) (v : View) (meter : Meter) :
    Except (Failure × View × Meter) (View × Meter) :=
  match ReferenceSourceStackAdmission.pop v.stack with
  | .error e => .error (.stack e,v,meter)
  | .ok (first,off) =>
    match ReferenceSourceStackAdmission.pop first with
    | .error e => .error (.stack e,{v with stack := first},meter)
    | .ok (rest,value) =>
      let expansion := calculate v.memory.size off.toNat (length byte)
      match ReferenceStorageGas.chargeExecution (core meter) (3+expansion.cost) with
      | none => .error (.outOfGas,{v with stack := rest},meter)
      | some charged => .ok ({v with stack := rest,pc := v.pc+1, memory := ReferenceMemoryOperations.splice v.memory off.toNat (data byte value) (v.memory.size+expansion.bytes)},update meter charged)

private theorem shape {byte : Bool} {v next : View} {meter final : Meter}
    (actual : run byte v meter = .ok (next,final)) :
    ∃ off value rest charged,
      v.stack = off::value::rest ∧
      ReferenceStorageGas.chargeExecution (core meter)
        (3+(calculate v.memory.size off.toNat (length byte)).cost) = some charged ∧
      next = {v with stack := rest,pc := v.pc+1, memory := ReferenceMemoryOperations.splice v.memory off.toNat (data byte value) (v.memory.size+(calculate v.memory.size off.toNat (length byte)).bytes)} ∧
      final = update meter charged := by
  unfold run at actual
  cases hs : v.stack with
  | nil => simp only [hs,ReferenceSourceStackAdmission.pop] at actual; contradiction
  | cons off first =>
    simp only [hs,ReferenceSourceStackAdmission.pop] at actual
    cases first with
    | nil => contradiction
    | cons value rest =>
      dsimp only [ReferenceSourceStackAdmission.pop] at actual
      split at actual
      · contradiction
      · rename_i charged hc
        cases actual
        exact ⟨off,value,rest,charged,rfl,hc,rfl,rfl⟩

/-- Exact same raw expansion pays the price computed from its actual result.
No output memory capacity, action, desired stack or paid event is supplied. -/
theorem success {byte : Bool} {v next : View} {meter final : Meter}
    (kind : Kind) (parent : ReferenceStorageView.Parent) (warm : ReferenceSourceReadings.Warm)
    (initial : v.stack.length ≤ 1024) (aligned : Aligned v)
    (actual : run byte v meter = .ok (next,final)) :
    ReferenceRuntimeAction.Action kind parent (opcode byte,none) v next ∧
    ReferenceRuntimeReadings.Price parent v warm next (opcode byte)
      (.ordinary (3+(ReferenceMemoryCapacity.cost (words next)-ReferenceMemoryCapacity.cost (words v)))) ∧
    runFull [.ordinary (3+(ReferenceMemoryCapacity.cost (words next)-ReferenceMemoryCapacity.cost (words v)))]
      meter = some final ∧ next.stack.length ≤ 1024 := by
  obtain ⟨off,value,rest,charged,hs,hc,rfl,rfl⟩ := shape actual
  have expansionFacts := ReferenceMemoryExpansionSource.aligned (words v) off.toNat (length byte)
  rw [←aligned] at expansionFacts
  have lower := (ReferenceMemoryCapacity.expansion_bounds (words v) off.toNat (length byte)).1
  have capacity : v.memory.size+(calculate v.memory.size off.toNat (length byte)).bytes =
      32*MachineState.M (words v) off.toNat (length byte) := by
    change v.memory.size = 32*words v at aligned
    omega
  rw [capacity]
  have action : ReferenceRuntimeAction.Action kind parent (opcode byte,none) v
      {v with stack := rest,pc := v.pc+1, memory := ReferenceMemoryOperations.splice v.memory off.toNat (data byte value) (32*MachineState.M (words v) off.toNat (length byte))} := by
    cases byte with
    | false =>
      have step : ReferenceRuntimeAction.Action kind parent (.MSTORE,none) v (memoryAction v off value.toByteArray rest) := .base (.word hs)
      simpa only [opcode,length,data,Bool.false_eq_true,if_false,memoryAction,UInt256.size_toByteArray] using step
    | true =>
      have byteEq : UInt8.ofNat (value.toNat%256) = UInt8.ofNat value.toNat := UInt8.ofNat_mod_size
      have sizeByte : (⟨#[UInt8.ofNat value.toNat]⟩ : ByteArray).size = 1 := rfl
      simpa [opcode,length,data,memoryAction,byteEq,sizeByte] using (ReferenceRuntimeAction.Action.base (ReferenceSystemAction.Action.byte hs) :
        ReferenceRuntimeAction.Action kind parent (.MSTORE8,none) v (memoryAction v off ⟨#[UInt8.ofNat value.toNat]⟩ rest))
  have computed := (ReferenceActionMemoryBounds.computed action aligned).2
  have span : ReferenceActionMemoryBounds.span v (opcode byte) = (off.toNat,length byte) := by
    cases byte <;> simp [ReferenceActionMemoryBounds.span,opcode,length,hs]
  rw [span] at computed
  dsimp only at computed
  refine ⟨action,?_,?_,?_⟩
  · cases byte <;> simp [ReferenceRuntimeReadings.Price,ReferenceCopyLogGas.ordinaryCost,
      ReferenceOrdinaryGas.ordinaryCost,opcode,computed]
  · have amount : 3+(ReferenceMemoryCapacity.cost (words
        {v with stack := rest,pc := v.pc+1, memory := ReferenceMemoryOperations.splice v.memory off.toNat (data byte value) (32*MachineState.M (words v) off.toNat (length byte))})-ReferenceMemoryCapacity.cost (words v)) =
        3+(calculate v.memory.size off.toNat (length byte)).cost := by
      rw [computed,expansionFacts.2]
    rw [amount]
    simp only [runFull,ReferenceMeterPath.run,ReferenceMeterPath.pay,hc,Option.bind_some,Option.map_some]
  · change rest.length ≤ 1024
    rw [hs] at initial
    simp only [List.length_cons] at initial
    omega

#print axioms success
end Eip8282.Audit.Integrator.ReferenceCheckedMemoryStore

end

section

/-! ## ReferenceCheckedTerminalStep -/

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

end
