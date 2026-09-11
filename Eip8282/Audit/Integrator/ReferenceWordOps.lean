import Eip8282.Audit.EntryReach.Path

/-! Local word-operation parity with an audited transcription of execution-specs
0cc100eb190b64b23baba72dac0165652eaec252 Amsterdam arithmetic/comparison/bitwise.py.
This does not interpret Python or prove its runtime, numeric library, gas/error
control flow, or program-counter representation refines Lean. The transcription
boundary is explicit; exact pinned successful stack effects are proved below. -/
namespace Eip8282.Audit.Integrator.ReferenceWordOps
open EvmYul EvmYul.EVM
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

inductive Binary where
  | add | mul | sub | div | lt | gt | eq | and | shl | shr
  deriving DecidableEq

def opcode : Binary → Operation .EVM
  | .add => .ADD | .mul => .MUL | .sub => .SUB | .div => .DIV
  | .lt => .LT | .gt => .GT | .eq => .EQ | .and => .AND | .shl => .SHL | .shr => .SHR

/-- First pop is x; shifts pop the shift first and the value second. The SUB
expression is unsigned wrapping subtraction on inputs below 2^256. -/
def reference (op : Binary) (x y : Nat) : Nat :=
  match op with
  | .add => (x+y) % UInt256.size
  | .mul => (x*y) % UInt256.size
  | .sub => (UInt256.size-y+x) % UInt256.size
  | .div => if y=0 then 0 else x/y
  | .lt => if x<y then 1 else 0
  | .gt => if x>y then 1 else 0
  | .eq => if x=y then 1 else 0
  | .and => x &&& y
  | .shl => if x<256 then (y <<< x) &&& (2^256-1) else 0
  | .shr => if x<256 then y >>> x else 0

def pinned : Binary → UInt256 → UInt256 → UInt256
  | .add => UInt256.add | .mul => UInt256.mul | .sub => UInt256.sub | .div => UInt256.div
  | .lt => UInt256.lt | .gt => UInt256.gt | .eq => UInt256.eq | .and => UInt256.land
  | .shl => fun x y => UInt256.shiftLeft y x
  | .shr => fun x y => UInt256.shiftRight y x

private theorem eq_toNat (x y : UInt256) : x=y ↔ x.toNat=y.toNat := by
  constructor
  · intro h; rw [h]
  · intro h
    rw [← ofNat_toNat' x,← ofNat_toNat' y,h]

/-- Exact unsigned results, including modular wrap, zero divisor and large shifts. -/
theorem value_parity (op : Binary) (x y : UInt256) :
    (pinned op x y).toNat = reference op x.toNat y.toNat := by
  cases op with
  | add => rfl
  | mul => rfl
  | sub => rfl
  | div =>
    change x.toNat/y.toNat = if y.toNat=0 then 0 else x.toNat/y.toNat
    split <;> simp_all
  | lt =>
    change (Bool.toUInt256 (decide (x.toNat<y.toNat))).toNat = _
    by_cases h : x.toNat<y.toNat <;> simp [reference,Bool.toUInt256,h] <;> rfl
  | gt =>
    change (Bool.toUInt256 (decide (x.toNat>y.toNat))).toNat = _
    by_cases h : x.toNat>y.toNat <;> simp [reference,Bool.toUInt256,h] <;> rfl
  | eq =>
    simp only [pinned,UInt256.eq,UInt256.fromBool,eq_toNat]
    by_cases h : x.toNat=y.toNat <;> simp [reference,Bool.toUInt256,h] <;> rfl
  | and =>
    change (x.toNat &&& y.toNat) % UInt256.size = x.toNat &&& y.toNat
    exact Nat.mod_eq_of_lt (Nat.and_le_left.trans_lt x.val.isLt)
  | shl =>
    dsimp only [pinned,reference]
    unfold UInt256.shiftLeft
    by_cases h : x.toNat<256
    · rw [if_neg (by exact Nat.not_le.mpr h),if_pos h,Nat.and_two_pow_sub_one_eq_mod]
      rfl
    · rw [if_pos (by exact Nat.le_of_not_gt h),if_neg h]
      rfl
  | shr =>
    dsimp only [pinned,reference]
    unfold UInt256.shiftRight
    by_cases h : x.toNat<256
    · rw [if_neg (by exact Nat.not_le.mpr h),if_pos h]
      change (y.toNat >>> x.toNat) % UInt256.size = y.toNat >>> x.toNat
      exact Nat.mod_eq_of_lt ((Nat.shiftRight_le _ _).trans_lt y.val.isLt)
    · rw [if_pos (by exact Nat.le_of_not_gt h),if_neg h]
      rfl

theorem step_parity (op : Binary) (s : EVM.State) (x y : UInt256) (rest : Stack UInt256)
    (hs : s.stack = x::y::rest) :
    EvmYul.step (opcode op) none s =
      .ok (s.replaceStackAndIncrPC (UInt256.ofNat (reference op x.toNat y.toNat)::rest)) := by
  have hm : opcode op ∈ blockOps := by cases op <;> decide
  have hp : pureStep (opcode op,none) s = some (s.replaceStackAndIncrPC (pinned op x y::rest)) := by
    cases op <;> simp only [opcode,pureStep,hs,pinned]
  have hv : pinned op x y = UInt256.ofNat (reference op x.toNat y.toNat) := by
    rw [← value_parity,ofNat_toNat']
  rw [hv] at hp
  exact pureStep_sound hm hp

def referenceIsZero (x : Nat) : Nat := if x=0 then 1 else 0

theorem isZero_parity (x : UInt256) :
    (UInt256.isZero x).toNat = referenceIsZero x.toNat := by
  by_cases h : x.toNat=0
  · have he : x=(⟨0⟩ : UInt256) := (eq_toNat _ _).mpr h
    subst x
    rfl
  · have hn : x.val ≠ 0 := by intro he; exact h (congrArg Fin.val he)
    have hb : (x.val == 0) = false := beq_eq_false_iff_ne.mpr hn
    change (Bool.toUInt256 (x.val == 0)).toNat = _
    rw [hb]
    simp only [referenceIsZero,if_neg h]
    rfl

theorem isZero_step (s : EVM.State) (x : UInt256) (rest : Stack UInt256)
    (hs : s.stack = x::rest) :
    EvmYul.step (τ := .EVM) .ISZERO none s =
      .ok (s.replaceStackAndIncrPC (UInt256.ofNat (referenceIsZero x.toNat)::rest)) := by
  have hp : pureStep (.ISZERO,none) s = some (s.replaceStackAndIncrPC (UInt256.isZero x::rest)) := by
    simp only [pureStep,hs]
  have he : UInt256.isZero x = UInt256.ofNat (referenceIsZero x.toNat) := by
    rw [← isZero_parity,ofNat_toNat']
  rw [he] at hp
  exact pureStep_sound (by decide) hp

/-- Python's list end is the top; the Lean stack head is the top. -/
def fromPython (stack : List UInt256) : Stack UInt256 := stack.reverse

theorem python_binary (op : Binary) (base : List UInt256) (x y : UInt256) :
    fromPython (base ++ [y,x]) = x::y::fromPython base ∧
    fromPython (base ++ [UInt256.ofNat (reference op x.toNat y.toNat)]) =
      UInt256.ofNat (reference op x.toNat y.toNat)::fromPython base := by
  simp [fromPython,List.reverse_append]

#print axioms isZero_parity
#print axioms isZero_step
#print axioms value_parity
#print axioms step_parity
#print axioms python_binary
end Eip8282.Audit.Integrator.ReferenceWordOps
