import Eip8282.Audit.Integrator.ReferenceCheckedEnvironmentStep

/-! Literal checked stack/control handlers at EL0cc100eb190b64b23baba72dac0165652eaec252.
Full source archive: audit/receipts/direct-reference-amsterdam-gas-sources-20260910.json.
stack.py SHA2561065b389a6d8e4a0ed72945b0be5e67b18484836695041aae83bbc08484caace,
POP29-49, PUSH52-82, DUP85-110, SWAP113-144; control_flow.py
b6b481918211a8e86ded3acd9ec13e940ba05860786e584913478aec13abc0c3,
JUMP48-70/JUMPI73-101. DUP/SWAP charge BEFORE depth checking. POP/JUMP/JUMPI
pop before charging. PUSH checks U256(pc+1) after charge, before buffered read;
PC conversion never silently wraps. JUMPI zero bypasses destination checking.
The explicit destination table and chosen handler must be bound to the actual
source frame/dispatch separately. This is audited transcription, not Python
extraction, foreign-bytecode parity, or exception rollback. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedStackControlStep
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceMeterRollback ReferenceMeterBoundary
open ReferencePureAction (Pure)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

inductive Handler where
  | pop | push0 | push1 | push2 | push4 | push8 | push20 | push32
  | dup1 | dup2 | dup3 | dup4 | dup5
  | swap1 | swap2 | swap3 | swap4 | jump | jumpi
  deriving DecidableEq

def family : Handler → Pure
  | .pop => .pop | .jump => .jump | .jumpi => .jumpi
  | .push0 => .push .PUSH0 | .push1 => .push .PUSH1 | .push2 => .push .PUSH2
  | .push4 => .push .PUSH4 | .push8 => .push .PUSH8
  | .push20 => .push .PUSH20 | .push32 => .push .PUSH32
  | .dup1 => .dup .DUP1 | .dup2 => .dup .DUP2 | .dup3 => .dup .DUP3
  | .dup4 => .dup .DUP4 | .dup5 => .dup .DUP5
  | .swap1 => .swap .SWAP1 | .swap2 => .swap .SWAP2
  | .swap3 => .swap .SWAP3 | .swap4 => .swap .SWAP4

def opcode (h : Handler) := ReferencePureAction.opcode (family h)
def charge (h : Handler) : Nat :=
  match h with | .pop | .push0 => 2 | .jump => 8 | .jumpi => 10 | _ => 3

def width (h : Handler) : Nat := argOnNBytesOfInstr (opcode h)

def immediate (h : Handler) (v : View) : Option (UInt256 × Nat) :=
  if width h = 0 then none else
    some (uInt256OfByteArray (ReferenceMemoryView.buffer v.env.code (v.pc+1) (width h)),width h)
def instruction (h : Handler) (v : View) := (opcode h,immediate h v)

inductive Failure where
  | checked (reason : ReferenceCheckedBinaryStep.Failure)
  | conversionOverflow | invalidJump
  deriving DecidableEq

/-- Prefix pops retain their exact middle failure state. -/
def prepare (h : Handler) (v : View) : Except (Failure × View) (View × List UInt256) :=
  if h = .pop ∨ h = .jump ∨ h = .jumpi then
    match ReferenceSourceStackAdmission.pop v.stack with
    | .error e => .error (.checked (.stack e),v)
    | .ok (rest,x) =>
      let v1 := {v with stack := rest}
      if h = .jumpi then
        match ReferenceSourceStackAdmission.pop rest with
        | .error e => .error (.checked (.stack e),v1)
        | .ok (tail,y) => .ok ({v with stack := tail},[x,y])
      else .ok (v1,[x])
  else .ok (v,[])

private def push (v : View) (x : UInt256) (pc : Nat) : Except Failure View :=
  match ReferenceSourceStackAdmission.push x v.stack with
  | .error e => .error (.checked (.stack e))
  | .ok stack => .ok {v with stack := stack,pc := pc}

private theorem push_success {v next : View} {x : UInt256} {pc : Nat}
    (actual : push v x pc = .ok next) :
    next = {v with stack := x::v.stack,pc := pc} ∧ v.stack.length ≠ 1024 := by
  by_cases full : v.stack.length = 1024
  · simp [push,ReferenceSourceStackAdmission.push,full] at actual
  · simp only [push,ReferenceSourceStackAdmission.push,if_neg full] at actual
    cases actual
    exact ⟨rfl,full⟩

/-- Operations after payment, on the already popped view. -/
def operate (h : Handler) (destinations : List Nat) (v : View) (popped : List UInt256) :
    Except Failure View :=
  match family h with
  | .pop => .ok {v with pc := v.pc+1}
  | .push _ =>
    if v.pc+1 < UInt256.size then
      push v (uInt256OfByteArray (ReferenceMemoryView.buffer v.env.code (v.pc+1) (width h)))
        (v.pc+1+width h)
    else .error .conversionOverflow
  | .dup d =>
    match v.stack[ReferenceStackOps.dupDepth d-1]? with
    | none => .error (.checked (.stack .underflow))
    | some x => push v x (v.pc+1)
  | .swap d =>
    match v.stack with
    | [] => .error (.checked (.stack .underflow))
    | top::tail =>
      match tail[ReferenceStackOps.swapDepth d-1]? with
      | none => .error (.checked (.stack .underflow))
      | some x => .ok {v with pc := v.pc+1, stack := (x::(tail.take (ReferenceStackOps.swapDepth d-1) ++ [top] ++ tail.drop (ReferenceStackOps.swapDepth d)))}
  | .jump =>
    match popped with
    | dest::_ => if dest.toNat ∈ destinations then .ok {v with pc := dest.toNat}
        else .error .invalidJump
    | _ => .error (.checked (.stack .underflow))
  | .jumpi =>
    match popped with
    | dest::cond::_ => if cond = ⟨0⟩ then .ok {v with pc := v.pc+1}
        else if dest.toNat ∈ destinations then .ok {v with pc := dest.toNat}
        else .error .invalidJump
    | _ => .error (.checked (.stack .underflow))
  | _ => .error (.checked (.stack .underflow))

def run (h : Handler) (destinations : List Nat) (v : View) (meter : Meter) :
    Except (Failure × View × Meter) (View × Meter) :=
  match prepare h v with
  | .error (e,middle) => .error (e,middle,meter)
  | .ok (middle,popped) =>
    match ReferenceStorageGas.chargeExecution (core meter) (charge h) with
    | none => .error (.checked .outOfGas,middle,meter)
    | some charged =>
      let m := update meter charged
      match operate h destinations middle popped with
      | .error e => .error (e,middle,m)
      | .ok next => .ok (next,m)

/-- Context binding only; actual source jump-table extraction remains separate. -/
def DestinationContext (kind : Kind) (destinations : List Nat) : Prop :=
  destinations = ReferenceDecodeSites.referenceJumps (ReferenceRuntimeSites.reference kind)

private theorem run_success {h : Handler} {destinations : List Nat} {v next : View}
    {meter final : Meter} (actual : run h destinations v meter = .ok (next,final)) :
    ∃ middle popped charged,
      prepare h v = .ok (middle,popped) ∧
      ReferenceStorageGas.chargeExecution (core meter) (charge h) = some charged ∧
      operate h destinations middle popped = .ok next ∧ final = update meter charged := by
  unfold run at actual
  cases hp : prepare h v with
  | error e => cases e; simp only [hp] at actual; contradiction
  | ok pair =>
    rcases pair with ⟨middle,popped⟩
    simp only [hp] at actual
    cases hc : ReferenceStorageGas.chargeExecution (core meter) (charge h) with
    | none => simp only [hc] at actual; contradiction
    | some charged =>
      simp only [hc] at actual
      cases ho : operate h destinations middle popped with
      | error e => simp only [ho] at actual; contradiction
      | ok result =>
        simp only [ho] at actual
        cases actual
        exact ⟨middle,popped,charged,rfl,rfl,ho,rfl⟩

private theorem stack_cases (s : List UInt256) :
    s = [] ∨ (∃ a, s = [a]) ∨ (∃ a b, s = [a,b]) ∨
    (∃ a b c, s = [a,b,c]) ∨ (∃ a b c d, s = [a,b,c,d]) ∨
    (∃ a b c d e rest, s = a::b::c::d::e::rest) := by
  cases s with
  | nil => exact Or.inl rfl
  | cons a s =>
    right
    cases s with
    | nil => exact Or.inl ⟨a,rfl⟩
    | cons b s =>
      right
      cases s with
      | nil => exact Or.inl ⟨a,b,rfl⟩
      | cons c s =>
        right
        cases s with
        | nil => exact Or.inl ⟨a,b,c,rfl⟩
        | cons d s =>
          right
          cases s with
          | nil => exact Or.inl ⟨a,b,c,d,rfl⟩
          | cons e rest => exact Or.inr ⟨a,b,c,d,e,rest,rfl⟩

private theorem effects {h : Handler} {destinations : List Nat} {v middle next : View}
    {popped : List UInt256} (kind : Kind)
    (context : DestinationContext kind destinations) (initial : v.stack.length ≤ 1024)
    (hp : prepare h v = .ok (middle,popped))
    (ho : operate h destinations middle popped = .ok next) :
    ReferencePureAction.action kind (instruction h v) v = some next ∧
      next.stack.length ≤ 1024 ∧ next.memory = v.memory := by
  unfold DestinationContext at context
  subst destinations
  rcases stack_cases v.stack with shape | ⟨a,shape⟩ | ⟨a,b,shape⟩ | ⟨a,b,c,shape⟩ |
    ⟨a,b,c,d,shape⟩ | ⟨a,b,c,d,e,rest,shape⟩
  all_goals cases h <;>
    simp [prepare,shape,ReferenceSourceStackAdmission.pop] at hp
  all_goals rcases hp with ⟨rfl,rfl⟩
  all_goals simp only [operate,family] at ho
  all_goals try simp [shape,ReferenceStackOps.dupDepth,ReferenceStackOps.swapDepth] at ho
  all_goals repeat (first | contradiction |
    (obtain ⟨hn,hnot⟩ := push_success ho; subst next; clear ho) | split at ho)
  all_goals try (by_cases hj : a.toNat ∈ ReferenceDecodeSites.referenceJumps (ReferenceRuntimeSites.reference kind) <;> simp only [hj,if_pos] at ho)
  all_goals try contradiction
  all_goals try cases ho
  all_goals
    refine ⟨?_,?_,rfl⟩
    · simp [ReferencePureAction.action,ReferencePureAction.classify,ReferencePureAction.familyAction,
        ReferencePureAction.advance,stackAction,instruction,immediate,width,opcode,family,
        argOnNBytesOfInstr,ReferencePureAction.opcode,ReferenceStackOps.dupDepth,ReferenceStackOps.swapDepth,
        ReferenceMemoryView.buffer,uInt256OfByteArray,fromBytes', *] <;> rfl
    · simp only [shape,List.length_cons,List.length_nil] at *
      omega

/-- Successful handlers yield the same source-shaped action, literal price and
single-event meter payment. The instruction's PUSH immediate uses real code
bytes and padding; the context supplies only its actual jump-table binding. -/
theorem success {h : Handler} {destinations : List Nat} {v next : View} {meter final : Meter}
    (kind : Kind) (parent : ReferenceStorageView.Parent) (warm : ReferenceSourceReadings.Warm)
    (context : DestinationContext kind destinations) (initial : v.stack.length ≤ 1024)
    (actual : run h destinations v meter = .ok (next,final)) :
    ReferencePureAction.action kind (instruction h v) v = some next ∧
    ReferenceRuntimeAction.Action kind parent (instruction h v) v next ∧
    ReferenceRuntimeReadings.Price parent v warm next (opcode h) (.ordinary (charge h)) ∧
    runFull [.ordinary (charge h)] meter = some final ∧ next.stack.length ≤ 1024 := by
  obtain ⟨middle,popped,charged,hp,hc,ho,rfl⟩ := run_success actual
  obtain ⟨ha,hb,hm⟩ := effects kind context initial hp ho
  refine ⟨ha,.base (.pure ha),?_,?_,hb⟩
  · cases h <;> simp [ReferenceRuntimeReadings.Price,ReferenceCopyLogGas.ordinaryCost,
      ReferenceOrdinaryGas.ordinaryCost,opcode,family,ReferencePureAction.opcode,charge,words,hm]
  · simp only [runFull,ReferenceMeterPath.run,ReferenceMeterPath.pay,hc,Option.bind_some,Option.map_some]

/-- Prefix stack pops do not change the PC whose U256 conversion follows. -/
theorem prepare_pc {h : Handler} {v middle : View} {popped : List UInt256}
    (actual : prepare h v = .ok (middle,popped)) : middle.pc = v.pc := by
  unfold prepare at actual
  dsimp only at actual
  repeat' first | split at actual | cases actual
  all_goals rfl

/-- Preparing the stack cannot emit the host conversion exception. -/
theorem prepare_no_conversion {h : Handler} {v middle : View} :
    prepare h v ≠ .error (.conversionOverflow,middle) := by
  intro actual
  unfold prepare at actual
  dsimp only at actual
  repeat' first | split at actual | cases actual

/-- The actual PUSH pc+1 conversion is safe on this input bound; no modulo
is substituted. Other operations cannot emit conversionOverflow. -/
theorem operate_no_conversion {h : Handler} {destinations : List Nat} {v : View} {popped : List UInt256}
    (fit : v.pc+1 < UInt256.size) : operate h destinations v popped ≠ .error .conversionOverflow := by
  intro actual
  cases h <;> simp only [operate,family,if_pos fit,push] at actual
  all_goals repeat' first | split at actual | cases actual

/-- Bound propagated through actual prefix pops and charges to the operation. -/
theorem run_no_conversion {h : Handler} {destinations : List Nat} {v next : View} {meter final : Meter}
    (fit : v.pc+1 < UInt256.size) : run h destinations v meter ≠ .error (.conversionOverflow,next,final) := by
  intro actual
  unfold run at actual
  cases prepared : prepare h v with
  | error pair =>
    obtain ⟨error,middle⟩ := pair
    simp only [prepared] at actual
    cases actual
    exact prepare_no_conversion prepared
  | ok pair =>
    obtain ⟨middle,popped⟩ := pair
    have middleFit : middle.pc+1 < UInt256.size := by rw [prepare_pc prepared]; exact fit
    simp only [prepared] at actual
    cases charged : ReferenceStorageGas.chargeExecution (core meter) (charge h) with
    | none => simp only [charged] at actual; cases actual
    | some gas =>
      simp only [charged] at actual
      cases operated : operate h destinations middle popped with
      | ok value => simp only [operated] at actual; contradiction
      | error error =>
        simp only [operated] at actual
        cases actual
        exact operate_no_conversion middleFit operated

#print axioms prepare_pc
#print axioms prepare_no_conversion
#print axioms operate_no_conversion
#print axioms run_no_conversion

#print axioms success

end Eip8282.Audit.Integrator.ReferenceCheckedStackControlStep
