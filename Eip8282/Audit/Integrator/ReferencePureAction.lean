import Eip8282.Audit.Integrator.ReferenceRuntimeView
import Eip8282.Audit.Integrator.ReferenceAcceptedStack
import Eip8282.Audit.Integrator.ReferenceEnvironmentOps
import Eip8282.Audit.Integrator.ReferenceDecodeShape

/-! Partial source-shaped pure actions on the protected runtime view. The
source stack has already been reversed into the view's top-first representation.
Arithmetic uses the audited reference formulas; taken jumps check the fixed
source jump table, and CALLDATASIZE retains the checked word-size gate.
No memory/storage/log/terminal operation receives a default successful action.
This is a local audited transcription, not executable Python refinement. -/
namespace Eip8282.Audit.Integrator.ReferencePureAction
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

inductive Pure where
  | binary (b : ReferenceWordOps.Binary)
  | iszero | caller | value | size | load | pop | jump | jumpi | jumpdest
  | push (p : Operation.POp)
  | dup (d : Operation.DOp)
  | swap (d : Operation.ExOp)

def opcode : Pure → Operation .EVM
  | .binary b => ReferenceWordOps.opcode b
  | .iszero => .ISZERO | .caller => .CALLER | .value => .CALLVALUE
  | .size => .CALLDATASIZE | .load => .CALLDATALOAD | .pop => .POP
  | .jump => .JUMP | .jumpi => .JUMPI | .jumpdest => .JUMPDEST
  | .push p => .Push p | .dup d => .Dup d | .swap d => .Exchange d

def classify : Operation .EVM → Option Pure
  | .ADD => some (.binary .add) | .MUL => some (.binary .mul)
  | .SUB => some (.binary .sub) | .DIV => some (.binary .div)
  | .LT => some (.binary .lt) | .GT => some (.binary .gt)
  | .EQ => some (.binary .eq) | .AND => some (.binary .and)
  | .SHL => some (.binary .shl) | .SHR => some (.binary .shr)
  | .ISZERO => some .iszero | .CALLER => some .caller | .CALLVALUE => some .value
  | .CALLDATASIZE => some .size | .CALLDATALOAD => some .load | .POP => some .pop
  | .JUMP => some .jump | .JUMPI => some .jumpi | .JUMPDEST => some .jumpdest
  | .Push p => some (.push p) | .Dup d => some (.dup d) | .Exchange d => some (.swap d)
  | _ => none

def Supported (op : Operation .EVM) : Prop := ∃ p, opcode p = op

def advance (v : View) (stack : Stack UInt256) (width : Nat := 1) : View :=
  stackAction v (v.pc+width) stack

def familyAction (kind : Kind) (p : Pure) (arg : Option (UInt256 × Nat)) (v : View) : Option View :=
  match p with
  | .binary b => match v.stack with
    | x::y::rest => some (advance v (UInt256.ofNat (ReferenceWordOps.reference b x.toNat y.toNat)::rest))
    | _ => none
  | .iszero => match v.stack with
    | x::rest => some (advance v (UInt256.ofNat (ReferenceWordOps.referenceIsZero x.toNat)::rest))
    | _ => none
  | .caller => some (advance v (UInt256.ofNat v.env.source.val::v.stack))
  | .value => some (advance v (v.env.weiValue::v.stack))
  | .size => if v.env.calldata.size < UInt256.size then
      some (advance v (UInt256.ofNat v.env.calldata.size::v.stack)) else none
  | .load => match v.stack with
    | off::rest => some (advance v (ReferenceEnvironmentOps.load v.env.calldata off.toNat::rest))
    | _ => none
  | .pop => match v.stack with | _::rest => some (advance v rest) | _ => none
  | .push op => if op = .PUSH0 then some (advance v (⟨0⟩::v.stack)) else
    match arg with
    | some (value,width) => if width = argOnNBytesOfInstr (.Push op) then
        some (advance v (value::v.stack) (width+1)) else none
    | none => none
  | .dup op => match v.stack[ReferenceStackOps.dupDepth op-1]? with
    | some value => some (advance v (value::v.stack))
    | none => none
  | .swap op => match v.stack with
    | top::tail => match tail[ReferenceStackOps.swapDepth op-1]? with
      | some value => some (advance v
          (value::(tail.take (ReferenceStackOps.swapDepth op-1) ++ [top] ++
            tail.drop (ReferenceStackOps.swapDepth op))))
      | none => none
    | [] => none
  | .jump => match v.stack with
    | dest::rest => if dest.toNat ∈ ReferenceDecodeSites.referenceJumps (ReferenceRuntimeSites.reference kind)
      then some (stackAction v dest.toNat rest) else none
    | [] => none
  | .jumpi => match v.stack with
    | dest::cond::rest => if cond = ⟨0⟩ then some (advance v rest) else
      if dest.toNat ∈ ReferenceDecodeSites.referenceJumps (ReferenceRuntimeSites.reference kind)
      then some (stackAction v dest.toNat rest) else none
    | _ => none
  | .jumpdest => some (advance v v.stack)

def action (kind : Kind) (instr : Instruction) (v : View) : Option View :=
  (classify instr.1).bind (fun p => familyAction kind p instr.2 v)

theorem classify_opcode (p : Pure) : classify (opcode p) = some p := by
  cases p <;> try rfl
  rename_i b
  cases b <;> rfl

theorem classify_sound {op : Operation .EVM} {p : Pure}
    (h : classify op = some p) : opcode p = op := by
  unfold classify at h
  split at h <;> cases h <;> rfl

theorem ordinary (p : Pure) : OrdinaryGas.Ordinary (opcode p) := by
  cases p <;> try exact ⟨rfl,rfl⟩
  rename_i b
  cases b <;> exact ⟨rfl,rfl⟩

theorem related_advance {parent : ReferenceStorageView.Parent} {v : View} {pre : EVM.State}
    (h : Related parent v pre) (stack : Stack UInt256) (width : Nat)
    (fit : pre.pc.toNat+width < UInt256.size) :
    Related parent (advance v stack width) (pre.replaceStackAndIncrPC stack width) := by
  refine ⟨h.env,?_,rfl,?_,h.storage,h.logs,h.owner⟩
  · change v.pc+width = (pre.replaceStackAndIncrPC stack width).pc.toNat
    rw [h.pc,ReferenceControlOps.next_pc pre stack width fit]
  · exact ⟨h.memory.coherent,h.memory.size,h.memory.bytes⟩

theorem related_jump {parent : ReferenceStorageView.Parent} {v : View} {pre : EVM.State}
    (h : Related parent v pre) (stack : Stack UInt256) (dest : UInt256) :
    Related parent (stackAction v dest.toNat stack) {pre with pc := dest,stack := stack} :=
  ⟨h.env,rfl,rfl,⟨h.memory.coherent,h.memory.size,h.memory.bytes⟩,h.storage,h.logs,h.owner⟩

theorem binary_raw (b : ReferenceWordOps.Binary) (arg : Option (UInt256 × Nat))
    (pre : EVM.State) (x y : UInt256) (rest : Stack UInt256) (shape : pre.stack = x::y::rest) :
    EvmYul.step (ReferenceWordOps.opcode b) arg pre =
      .ok (pre.replaceStackAndIncrPC (UInt256.ofNat (ReferenceWordOps.reference b x.toNat y.toNat)::rest)) := by
  have hp := ReferenceWordOps.step_parity b pre x y rest shape
  cases b <;> exact hp

/-- Common actual charged-dispatch boundary; no view field is gas or execLength. -/
theorem raw_dispatch {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel cost : Nat} {arg : Option (UInt256 × Nat)}
    (p : Pure) (h : Related parent v pre)
    (hz : Z (D_J pre.executionEnv.code ⟨0⟩) (opcode p) pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (opcode p,arg) mid post) :
    Related parent v (stepPre cost (zMid pre (opcode p))) ∧
    EvmYul.step (opcode p) arg (stepPre cost (zMid pre (opcode p))) = .ok post := by
  refine ⟨charged h _ _,?_⟩
  rw [Z_ok_state hz] at hs
  change EVM.step (fuel+1) cost (some (opcode p,arg)) _ = .ok post at hs
  rw [OrdinaryGas.dispatch (ordinary p)] at hs
  exact hs

/-- First complete family: literal reference arithmetic on the actual operands. -/
theorem binary {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel cost : Nat} {arg : Option (UInt256 × Nat)}
    (b : ReferenceWordOps.Binary) (h : Related parent v pre)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (ReferenceWordOps.opcode b,arg))
    (hz : Z (D_J pre.executionEnv.code ⟨0⟩) (ReferenceWordOps.opcode b) pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (ReferenceWordOps.opcode b,arg) mid post) :
    ∃ next, action kind (ReferenceWordOps.opcode b,arg) v = some next ∧ Related parent next post := by
  obtain ⟨hr,hsraw⟩ := raw_dispatch (.binary b) h hz hs
  obtain ⟨rest,x,y,shape,_⟩ := ReferenceAcceptedStack.pop2 hz (by cases b <;> decide)
  have known := binary_raw b arg (stepPre cost (zMid pre (ReferenceWordOps.opcode b))) x y rest shape
  have same := Except.ok.inj (hsraw.symm.trans known)
  subst post
  have fit := ReferenceRuntimeSites.pc_fit hat
  rw [decoded] at fit
  have width : argOnNBytesOfInstr (ReferenceWordOps.opcode b) = 0 := by cases b <;> rfl
  refine ⟨advance v (UInt256.ofNat (ReferenceWordOps.reference b x.toNat y.toNat)::rest),?_,
    related_advance hr _ 1 (by simpa [stepPre,zMid,width] using fit)⟩
  change (classify (opcode (.binary b))).bind _ = _
  rw [classify_opcode]
  simp only [Option.bind_some,familyAction,h.stack,shape]


#print axioms classify_sound
#print axioms raw_dispatch
#print axioms related_advance
#print axioms related_jump
#print axioms binary
end Eip8282.Audit.Integrator.ReferencePureAction
