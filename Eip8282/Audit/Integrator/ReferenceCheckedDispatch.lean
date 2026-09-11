import Eip8282.Audit.Integrator.ReferenceCheckedRuntimeTrace
import Eip8282.Audit.Integrator.ReferenceCheckedTerminalStep
import Eip8282.Audit.Integrator.ReferenceSourceOpcodeTable

/-! Literal opcode lookup and protected-handler dispatch from current code/PC.
EL0cc100eb process_call checks pc<len before Ops(tag); invalid Ops tags raise
InvalidOpcode. A valid source opcode outside these44 handlers is represented
as unsupported, never as an EVM failure or STOP. EOF preserves view/meter/output.
All handler errors preserve their recorded partial state; outer source exception
classification, journal restoration and resource forfeiture remain separate.
This audited source dispatch transcription is not a mechanical Python proof.
The actual account-existence lookup and frame/world initialization remain inputs.
-/
namespace Eip8282.Audit.Integrator.ReferenceCheckedDispatch
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceMeterBoundary
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

inductive Handler where
  | binary (h : ReferenceWordOps.Binary)
  | environment (h : ReferenceCheckedEnvironmentStep.Handler)
  | stackControl (h : ReferenceCheckedStackControlStep.Handler)
  | memoryStore (byte : Bool)
  | copyLog (h : ReferenceCheckedCopyLogStep.Handler)
  | load | store
  | terminal (h : ReferenceCheckedTerminalStep.Halt)
  deriving DecidableEq

def opcode : Handler → Operation .EVM
  | .binary h => ReferenceWordOps.opcode h
  | .environment h => ReferenceCheckedEnvironmentStep.opcode h
  | .stackControl h => ReferenceCheckedStackControlStep.opcode h
  | .memoryStore b => ReferenceCheckedMemoryStore.opcode b
  | .copyLog h => ReferenceCheckedCopyLogStep.opcode h
  | .load => .SLOAD | .store => .SSTORE
  | .terminal h => ReferenceCheckedTerminalStep.opcode h

def select (tag : UInt8) : Option Handler :=
  match tag.toNat with
  | 0x1 => some (.binary .add)
  | 0x2 => some (.binary .mul)
  | 0x3 => some (.binary .sub)
  | 0x4 => some (.binary .div)
  | 0x10 => some (.binary .lt)
  | 0x11 => some (.binary .gt)
  | 0x14 => some (.binary .eq)
  | 0x16 => some (.binary .and)
  | 0x1b => some (.binary .shl)
  | 0x1c => some (.binary .shr)
  | 0x33 => some (.environment .caller)
  | 0x34 => some (.environment .value)
  | 0x36 => some (.environment .size)
  | 0x35 => some (.environment .load)
  | 0x15 => some (.environment .iszero)
  | 0x5b => some (.environment .jumpdest)
  | 0x50 => some (.stackControl .pop)
  | 0x5f => some (.stackControl .push0)
  | 0x60 => some (.stackControl .push1)
  | 0x61 => some (.stackControl .push2)
  | 0x63 => some (.stackControl .push4)
  | 0x67 => some (.stackControl .push8)
  | 0x73 => some (.stackControl .push20)
  | 0x7f => some (.stackControl .push32)
  | 0x80 => some (.stackControl .dup1)
  | 0x81 => some (.stackControl .dup2)
  | 0x82 => some (.stackControl .dup3)
  | 0x83 => some (.stackControl .dup4)
  | 0x84 => some (.stackControl .dup5)
  | 0x90 => some (.stackControl .swap1)
  | 0x91 => some (.stackControl .swap2)
  | 0x92 => some (.stackControl .swap3)
  | 0x93 => some (.stackControl .swap4)
  | 0x56 => some (.stackControl .jump)
  | 0x57 => some (.stackControl .jumpi)
  | 0x52 => some (.memoryStore false)
  | 0x53 => some (.memoryStore true)
  | 0x37 => some (.copyLog .copy)
  | 0xa0 => some (.copyLog .log0)
  | 0x54 => some (.load)
  | 0x55 => some (.store)
  | 0x0 => some (.terminal .stop)
  | 0xf3 => some (.terminal .returned)
  | 0xfd => some (.terminal .reverted)
  | _ => none

/-- Exhaustive byte-table binding. This finite universe check imposes no bound
on executions or fee-loop iterations. -/
theorem select_facts (tag : UInt8) {h : Handler} (selected : select tag = some h) :
    ReferenceSourceOpcodeTable.validTag tag = true ∧ parseInstr tag = some (opcode h) := by
  have table : ∀ t : Fin 256,
      ((select (UInt8.ofNat t.val)).map (fun h => decide
        (ReferenceSourceOpcodeTable.validTag (UInt8.ofNat t.val) = true ∧
          parseInstr (UInt8.ofNat t.val) = some (opcode h)))).getD true = true := by decide +kernel
  have fact := table ⟨tag.toNat,tag.toNat_lt⟩
  simpa only [UInt8.ofNat_toNat,selected,Option.map_some,Option.getD_some,decide_eq_true_eq] using fact

inductive Dispatch where
  | eof
  | invalid (tag : UInt8)
  | unsupported (tag : UInt8)
  | handler (h : Handler)
  deriving DecidableEq

def read (bytes : ByteArray) (pc : Nat) : Dispatch :=
  match bytes[pc]? with
  | none => .eof
  | some tag => if ReferenceSourceOpcodeTable.validTag tag then
      match select tag with
      | none => .unsupported tag
      | some h => .handler h
    else .invalid tag

/-- Source EOF is a failed code lookup, not execution of STOP. -/
theorem read_eof (bytes : ByteArray) (pc : Nat) (absent : bytes[pc]? = none) :
    read bytes pc = .eof := by simp only [read,absent]

/-- The selected source tag determines the actual decoded opcode. No fallback
instruction is used to classify EOF or an invalid opcode. -/
theorem read_handler {v : View} {h : Handler} (actual : read v.env.code v.pc = .handler h) :
    ∃ arg, ReferenceDecodeSites.referenceDecode v.env.code v.pc = some (opcode h,arg) := by
  unfold read at actual
  cases ht : v.env.code[v.pc]? with
  | none => simp only [ht] at actual; contradiction
  | some tag =>
    simp only [ht] at actual
    split at actual
    · cases hs : select tag with
      | none => simp only [hs] at actual; contradiction
      | some chosen =>
        simp only [hs,Dispatch.handler.injEq] at actual
        subst chosen
        have parsed := (select_facts tag hs).2
        refine ⟨if ReferenceDecodeSites.pushWidth tag = 0 then none else
          some (uInt256OfByteArray (ReferenceDecodeSites.paddedImmediate v.env.code v.pc (ReferenceDecodeSites.pushWidth tag)),ReferenceDecodeSites.pushWidth tag),?_⟩
        simp [ReferenceDecodeSites.referenceDecode,ht,parsed]
    · contradiction

theorem read_opcode {v : View} {h : Handler} (actual : read v.env.code v.pc = .handler h) :
    (ReferenceSourceReplayTrace.instruction v).1 = opcode h := by
  obtain ⟨arg,decoded⟩ := read_handler actual
  simp only [ReferenceSourceReplayTrace.instruction,decoded,Option.getD_some]

inductive Fault where
  | binary (e : ReferenceCheckedBinaryStep.Failure)
  | environment (e : ReferenceCheckedEnvironmentStep.Failure)
  | stackControl (e : ReferenceCheckedStackControlStep.Failure)
  | storage (e : ReferenceCheckedStorageStep.Failure)
  | copyLog (e : ReferenceCheckedCopyLogStep.Failure)
  | invalidOpcode (tag : UInt8)

inductive Outcome where
  | continued (v : View) (warm : Warm) (meter : Meter) (event : Event)
  | terminal (result : ReferenceCheckedTerminalStep.End)
  | eof (v : View) (warm : Warm) (meter : Meter) (output : ByteArray)
  | failed (e : Fault) (v : View) (warm : Warm) (meter : Meter) (output : ByteArray)
  | unsupported (tag : UInt8) (v : View) (warm : Warm) (meter : Meter) (output : ByteArray)

noncomputable def runHandler (h : Handler) (destinations : List Nat) (ownerExists : Bool)
    (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm) (meter : Meter)
    (output : ByteArray) : Outcome :=
  match h with
  | .binary h => match ReferenceCheckedBinaryStep.run h v meter with
    | .error (e,next,final) => .failed (.binary e) next warm final output
    | .ok (next,final) => .continued next warm final (.ordinary (ReferenceCheckedBinaryStep.charge h))
  | .environment h => match ReferenceCheckedEnvironmentStep.run h v meter with
    | .error (e,next,final) => .failed (.environment e) next warm final output
    | .ok (next,final) => .continued next warm final (.ordinary (ReferenceCheckedEnvironmentStep.charge h))
  | .stackControl h => match ReferenceCheckedStackControlStep.run h destinations v meter with
    | .error (e,next,final) => .failed (.stackControl e) next warm final output
    | .ok (next,final) => .continued next warm final (.ordinary (ReferenceCheckedStackControlStep.charge h))
  | .memoryStore b => match ReferenceCheckedMemoryStore.run b v meter with
    | .error (e,next,final) => .failed (.binary e) next warm final output
    | .ok (next,final) => .continued next warm final (.ordinary (3+(ReferenceMemoryCapacity.cost (words next)-ReferenceMemoryCapacity.cost (words v))))
  | .copyLog h => match ReferenceCheckedCopyLogStep.run h v meter with
    | .error (e,next,final) => .failed (.copyLog e) next warm final output
    | .ok (next,final) => .continued next warm final (.ordinary (ReferenceCheckedCopyLogStep.cost h v))
  | .load => match ReferenceCheckedStorageStep.load parent v warm meter with
    | .error (e,next,finalWarm,final) => .failed (.storage e) next finalWarm final output
    | .ok (next,finalWarm,final) => .continued next finalWarm final
        (.ordinary (if (sourceReading parent v warm).warm then 100 else 2100))
  | .store => match ReferenceCheckedStorageStep.store ownerExists parent v warm meter with
    | .error (e,next,finalWarm,final) => .failed (.storage e) next finalWarm final output
    | .ok (next,finalWarm,final) => .continued next finalWarm final
        (.store (sourceReading parent v warm).warm (sourceReading parent v warm).original
          (sourceReading parent v warm).current (sourceReading parent v warm).new)
  | .terminal h => match ReferenceCheckedTerminalStep.run h v meter output with
    | .error (e,next,final,previousOutput) => .failed (.binary e) next warm final previousOutput
    | .ok result => .terminal result

noncomputable def run (destinations : List Nat) (ownerExists : Bool)
    (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm) (meter : Meter)
    (output : ByteArray) : Outcome :=
  match read v.env.code v.pc with
  | .eof => .eof v warm meter output
  | .invalid tag => .failed (.invalidOpcode tag) v warm meter output
  | .unsupported tag => .unsupported tag v warm meter output
  | .handler h => runHandler h destinations ownerExists parent v warm meter output

/-- Derive one existing checked step from the handler computation; the caller
does not choose an instruction, action, event or desired next state. -/
theorem runHandler_step {kind : Kind} {parent : ReferenceStorageView.Parent}
    {h : Handler} {destinations : List Nat} {ownerExists : Bool}
    {v next : View} {warm finalWarm : Warm} {meter final : Meter} {output : ByteArray} {event : Event}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (decoded : (ReferenceSourceReplayTrace.instruction v).1 = opcode h)
    (actual : runHandler h destinations ownerExists parent v warm meter output = .continued next finalWarm final event) :
    ReferenceCheckedRuntimeTrace.Step kind parent v warm meter next finalWarm final event := by
  cases h with
  | binary h =>
    simp only [runHandler] at actual
    split at actual
    · contradiction
    · rename_i checked
      cases actual
      exact .binary h decoded checked
  | environment h =>
    simp only [runHandler] at actual
    split at actual
    · contradiction
    · rename_i checked
      cases actual
      exact .environment h decoded checked
  | stackControl h =>
    simp only [runHandler] at actual
    split at actual
    · contradiction
    · rename_i checked
      cases actual
      exact .stackControl h destinations context decoded checked
  | memoryStore b =>
    simp only [runHandler] at actual
    split at actual
    · contradiction
    · rename_i checked
      cases actual
      exact .memoryStore b decoded checked
  | copyLog h =>
    simp only [runHandler] at actual
    split at actual
    · contradiction
    · rename_i checked
      cases actual
      exact .copyLog h decoded checked
  | load =>
    simp only [runHandler] at actual
    split at actual
    · contradiction
    · rename_i checked
      cases actual
      exact .load decoded checked
  | store =>
    simp only [runHandler] at actual
    split at actual
    · contradiction
    · rename_i checked
      cases actual
      exact .store ownerExists decoded checked
  | terminal h =>
    simp only [runHandler] at actual
    split at actual <;> contradiction

theorem step {kind : Kind} {parent : ReferenceStorageView.Parent}
    {destinations : List Nat} {ownerExists : Bool}
    {v next : View} {warm finalWarm : Warm} {meter final : Meter} {output : ByteArray} {event : Event}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : run destinations ownerExists parent v warm meter output = .continued next finalWarm final event) :
    ReferenceCheckedRuntimeTrace.Step kind parent v warm meter next finalWarm final event := by
  unfold run at actual
  cases hd : read v.env.code v.pc <;> rw [hd] at actual
  · contradiction
  · contradiction
  · contradiction
  · exact runHandler_step context (read_opcode hd) actual

#print axioms select_facts
#print axioms read_eof
#print axioms read_handler
#print axioms read_opcode
#print axioms runHandler_step
#print axioms step
end Eip8282.Audit.Integrator.ReferenceCheckedDispatch
