import Eip8282.Audit.Integrator.Topics.Reference

/-! Literal checked source stack primitives at EL0cc100eb, vm/stack.py121-148,
SHA25620cdb907098ae500c47abc6a1437cb9e4cdb5809f6c40b7d8935038aedd57b2a,
full body in audit/receipts/direct-reference-amsterdam-gas-sources-20260910.json.
The list is top-first (reverse of the Python list). Source push tests equality
with1024, not greater-or-equal; boundedness therefore starts at an actual frame
entry/inherited bound. This is a source transcription, not Python refinement.
An error projects the source exception only, not rollback of earlier mutations.
Opcode extraction must supply actual primitive order and delta/alpha binding;
DUP/SWAP indexed-access admission is a separate producer. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceStackAdmission
open EvmYul EvmYul.EVM
set_option autoImplicit false

inductive Failure where
  | underflow | overflow
  deriving DecidableEq, Repr

abbrev Stack := List UInt256

def pop : Stack → Except Failure (Stack × UInt256)
  | [] => .error .underflow
  | value::rest => .ok (rest,value)

def push (value : UInt256) (stack : Stack) : Except Failure Stack :=
  if stack.length = 1024 then .error .overflow else .ok (value::stack)

inductive Op where
  | pop | push (value : UInt256)

def run : List Op → Stack → Except Failure Stack
  | [],stack => .ok stack
  | .pop::ops,stack => do
      let (rest,_) ← pop stack
      run ops rest
  | .push value::ops,stack => do
      let next ← push value stack
      run ops next

theorem pop_length {pre rest : Stack} {value : UInt256}
    (actual : pop pre = .ok (rest,value)) : rest.length+1 = pre.length := by
  cases pre with
  | nil => cases actual
  | cons head tail => cases actual; rfl

theorem push_length {pre post : Stack} {value : UInt256}
    (initial : pre.length ≤ 1024) (actual : push value pre = .ok post) :
    post.length = pre.length+1 ∧ post.length ≤ 1024 := by
  unfold push at actual
  split at actual
  · contradiction
  · cases actual
    exact ⟨rfl,by simp only [List.length_cons]; omega⟩

theorem run_bounded {ops : List Op} {pre post : Stack}
    (initial : pre.length ≤ 1024) (actual : run ops pre = .ok post) : post.length ≤ 1024 := by
  induction ops generalizing pre with
  | nil => cases actual; exact initial
  | cons op ops ih =>
    cases op with
    | pop =>
      cases pre with
      | nil => cases actual
      | cons value rest =>
        have hr : run ops rest = .ok post := actual
        exact ih (by simpa only [List.length_cons] using (Nat.le_trans (Nat.le_succ _) initial)) hr
    | push value =>
      unfold run at actual
      cases hp : push value pre with
      | error e => simp only [hp,Except.bind,Bind.bind] at actual; contradiction
      | ok middle =>
        have hm := (push_length initial hp).2
        exact ih hm (by simpa only [hp,Except.bind,Bind.bind] using actual)

/-- Pop results are discarded only in this length/admission projection. -/
def popMany : Nat → Stack → Except Failure Stack
  | 0,stack => .ok stack
  | n+1,stack => do
      let (rest,_) ← pop stack
      popMany n rest

def pushMany : List UInt256 → Stack → Except Failure Stack
  | [],stack => .ok stack
  | value::values,stack => do
      let next ← push value stack
      pushMany values next

def popsThenPushes (pops : Nat) (values : List UInt256) (pre : Stack) : Except Failure Stack := do
  let middle ← popMany pops pre
  pushMany values middle

theorem popMany_length {n : Nat} {pre post : Stack}
    (actual : popMany n pre = .ok post) : n ≤ pre.length ∧ post.length+n = pre.length := by
  induction n generalizing pre with
  | zero => cases actual; simp
  | succ n ih =>
    cases pre with
    | nil => cases actual
    | cons value rest =>
      have hr : popMany n rest = .ok post := actual
      have h := ih hr
      simp only [List.length_cons]
      omega

theorem pushMany_length {values : List UInt256} {pre post : Stack}
    (initial : pre.length ≤ 1024) (actual : pushMany values pre = .ok post) :
    post.length = pre.length+values.length ∧ post.length ≤ 1024 := by
  induction values generalizing pre with
  | nil => cases actual; exact ⟨by simp,initial⟩
  | cons value values ih =>
    unfold pushMany at actual
    cases hp : push value pre with
    | error e => simp only [hp,Except.bind,Bind.bind] at actual; contradiction
    | ok middle =>
      have hm := push_length initial hp
      have hr : pushMany values middle = .ok post := by
        simpa only [hp,Except.bind,Bind.bind] using actual
      have ht := ih hm.2 hr
      simp only [List.length_cons]
      omega

theorem admission {pops : Nat} {values : List UInt256} {pre post : Stack}
    (initial : pre.length ≤ 1024) (actual : popsThenPushes pops values pre = .ok post) :
    pops ≤ pre.length ∧ post.length = pre.length-pops+values.length ∧
      pre.length-pops+values.length ≤ 1024 := by
  unfold popsThenPushes at actual
  cases hm : popMany pops pre with
  | error e => simp only [hm,Except.bind,Bind.bind] at actual; contradiction
  | ok middle =>
    have hp := popMany_length hm
    have hi : middle.length ≤ 1024 := by omega
    have hs : pushMany values middle = .ok post := by
      simpa only [hm,Except.bind,Bind.bind] using actual
    have ht := pushMany_length hi hs
    omega

/-- Exact old Z stack inequalities, after the source opcode's primitive
sequence has been bound to delta/alpha. These bindings are not guessed. -/
theorem old_admission {op : Operation .EVM} {pops : Nat} {values : List UInt256} {pre post : Stack}
    (initial : pre.length ≤ 1024) (actual : popsThenPushes pops values pre = .ok post)
    (inputs : δ op = some pops) (outputs : α op = some values.length) :
    (δ op).getD 0 ≤ pre.length ∧ pre.length-(δ op).getD 0+(α op).getD 0 ≤ 1024 := by
  have h := admission initial actual
  simpa only [inputs,outputs,Option.getD_some] using ⟨h.1,h.2.2⟩

/-- Actual empty frame initialization discharges the sole initial bound. -/
theorem from_empty {ops : List Op} {post : Stack} (actual : run ops [] = .ok post) :
    post.length ≤ 1024 := run_bounded (by simp) actual

/-- Literal source equality guard permits an already malformed injected stack.
The from_empty theorem prevents this state in the modeled primitive history. -/
theorem injected_overfull_push (value : UInt256) :
    push value (List.replicate 1025 (UInt256.ofNat 0)) =
      .ok (value::List.replicate 1025 (UInt256.ofNat 0)) := by
  simp only [push,List.length_replicate,show ¬ (1025 : Nat) = 1024 by decide,if_false]

#print axioms pop_length
#print axioms push_length
#print axioms run_bounded
#print axioms popMany_length
#print axioms pushMany_length
#print axioms admission
#print axioms old_admission
#print axioms from_empty
#print axioms injected_overfull_push
end Eip8282.Audit.Integrator.ReferenceSourceStackAdmission
