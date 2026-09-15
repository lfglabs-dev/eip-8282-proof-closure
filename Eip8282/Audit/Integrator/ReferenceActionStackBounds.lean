import Eip8282.Audit.Integrator.Topics.ReferenceRuntime

/-! Old stack signature admission from a successful source-shaped action and
an independently source-produced bound on its resulting stack. No Z premise.
DUP/SWAP require indexed depth, not their physical number of pop operations.
Action itself omits overflow; the explicit post bound must come from successful
checked source primitives/history (ReferenceSourceStackAdmission), not a desired
old postcondition. Source opcode extraction remains a separate boundary. -/
namespace Eip8282.Audit.Integrator.ReferenceActionStackBounds
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferencePureAction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private def inputs : Pure → Nat
  | .binary _ => 2
  | .iszero | .load | .pop | .jump => 1
  | .jumpi => 2
  | .dup d => ReferenceStackOps.dupDepth d
  | .swap d => ReferenceStackOps.swapDepth d+1
  | _ => 0

private def outputs : Pure → Nat
  | .pop | .jump | .jumpi | .jumpdest => 0
  | .dup d => ReferenceStackOps.dupDepth d+1
  | .swap d => ReferenceStackOps.swapDepth d+1
  | _ => 1

private theorem arity (p : Pure) : δ (opcode p) = some (inputs p) ∧ α (opcode p) = some (outputs p) := by
  cases p with
  | binary b => cases b <;> decide
  | push p => cases p <;> decide
  | dup d => cases d <;> decide
  | swap d => cases d <;> decide
  | _ => decide

private theorem lookup_lt {s : List UInt256} {n : Nat} {x : UInt256}
    (actual : s[n]? = some x) : n < s.length := by
  by_contra hn
  have hnone : s[n]? = none := List.getElem?_eq_none (by omega)
  rw [hnone] at actual
  contradiction

private theorem family_balance {kind : Kind} {v next : View} {arg : Option (UInt256 × Nat)}
    (p : Pure) (effect : familyAction kind p arg v = some next) :
    inputs p ≤ v.stack.length ∧ next.stack.length+inputs p = v.stack.length+outputs p := by
  cases p with
  | binary b =>
    cases shape : v.stack with
    | nil => simp [familyAction,shape] at effect
    | cons x tail =>
      cases tail with
      | nil => simp [familyAction,shape] at effect
      | cons y rest =>
        simp only [familyAction,shape] at effect
        cases effect
        simp [inputs,outputs,advance,stackAction]
  | iszero | load | pop | jump =>
    cases shape : v.stack with
    | nil => simp [familyAction,shape] at effect
    | cons x rest =>
      simp only [familyAction,shape] at effect
      repeat' first | split at effect | cases effect
      all_goals simp [inputs,outputs,advance,stackAction]
  | caller | value | jumpdest =>
    cases effect
    simp [inputs,outputs,advance,stackAction]
  | size =>
    simp only [familyAction] at effect
    split at effect
    · cases effect
      simp [inputs,outputs,advance,stackAction]
    · contradiction
  | jumpi =>
    cases shape : v.stack with
    | nil => simp [familyAction,shape] at effect
    | cons x tail =>
      cases tail with
      | nil => simp [familyAction,shape] at effect
      | cons y rest =>
        simp only [familyAction,shape] at effect
        repeat' first | split at effect | cases effect
        all_goals simp [inputs,outputs,advance,stackAction]
  | push op =>
    simp only [familyAction] at effect
    split at effect
    · cases effect
      simp [inputs,outputs,advance,stackAction]
    · cases arg with
      | none => contradiction
      | some pair =>
        obtain ⟨value,width⟩ := pair
        change (if width = argOnNBytesOfInstr (.Push op) then
          some (advance v (value::v.stack) (width+1)) else none) = some next at effect
        split at effect
        · cases effect
          simp [inputs,outputs,advance,stackAction]
        · contradiction
  | dup d =>
    simp only [familyAction] at effect
    cases selected : v.stack[ReferenceStackOps.dupDepth d-1]? with
    | none => simp only [selected] at effect; contradiction
    | some value =>
      simp only [selected] at effect
      cases effect
      have hl := lookup_lt selected
      have hd := (ReferenceStackOps.dup_depth d).1
      simp only [inputs,outputs,advance,stackAction,List.length_cons]
      omega
  | swap d =>
    cases shape : v.stack with
    | nil => simp [familyAction,shape] at effect
    | cons top tail =>
      simp only [familyAction,shape] at effect
      cases selected : tail[ReferenceStackOps.swapDepth d-1]? with
      | none => simp only [selected] at effect; contradiction
      | some value =>
        simp only [selected] at effect
        cases effect
        have hl := lookup_lt selected
        have hd := (ReferenceStackOps.swap_depth d).1
        simp only [inputs,outputs,advance,stackAction,List.length_cons,List.length_append,
          List.length_take,List.length_drop,List.length_nil]
        omega

private theorem pure_balance {kind : Kind} {instr : Instruction} {v next : View}
    (effect : action kind instr v = some next) :
    (δ instr.1).getD 0 ≤ v.stack.length ∧
      next.stack.length+(δ instr.1).getD 0 = v.stack.length+(α instr.1).getD 0 := by
  unfold action at effect
  cases selected : classify instr.1 with
  | none => simp only [selected,Option.bind_none] at effect; contradiction
  | some p =>
    simp only [selected,Option.bind_some] at effect
    have h := family_balance p effect
    have hop := classify_sound selected
    rw [←hop,(arity p).1,(arity p).2]
    exact h

/-- Exact length balance, with indexed DUP/SWAP underflow derived internally. -/
theorem balance {kind : Kind} {parent : ReferenceStorageView.Parent} {instr : Instruction} {v next : View}
    (effect : ReferenceRuntimeAction.Action kind parent instr v next) :
    (δ instr.1).getD 0 ≤ v.stack.length ∧
      next.stack.length+(δ instr.1).getD 0 = v.stack.length+(α instr.1).getD 0 := by
  cases effect with
  | base base =>
    cases base with
    | pure pure => exact pure_balance pure
    | load shape => simp [δ,α,loadAction,shape]
    | store permission shape => simp [δ,α,storeAction,shape]
    | word shape => simp [δ,α,memoryAction,shape]
    | byte shape => simp [δ,α,memoryAction,shape]
  | copy shape => simp [δ,α,ReferenceCalldataCopy.copyAction,shape]
  | log permission shape => simp [δ,α,ReferenceLogView.logAction,shape]

/-- The overflow bound remains a source admission input; it is not implied by
unchecked Action. Underflow and old delta/alpha arithmetic are produced. -/
theorem admission {kind : Kind} {parent : ReferenceStorageView.Parent} {instr : Instruction} {v next : View}
    (effect : ReferenceRuntimeAction.Action kind parent instr v next)
    (postbounded : next.stack.length ≤ 1024) :
    (δ instr.1).getD 0 ≤ v.stack.length ∧
      v.stack.length-(δ instr.1).getD 0+(α instr.1).getD 0 ≤ 1024 := by
  have h := balance effect
  omega

#print axioms balance
#print axioms admission
end Eip8282.Audit.Integrator.ReferenceActionStackBounds
