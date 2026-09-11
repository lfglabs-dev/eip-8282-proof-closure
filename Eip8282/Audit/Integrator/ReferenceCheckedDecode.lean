import Eip8282.Audit.Integrator.ReferenceCheckedStackControlStep
import Eip8282.Audit.Integrator.ReferenceSourceReplayTrace

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
