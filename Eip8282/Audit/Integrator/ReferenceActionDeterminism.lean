import Eip8282.Audit.Integrator.ReferenceRuntimeAction

/-! Source-shaped protected actions are deterministic at a fixed input view.
This supports guarded effect replay: an independently constructed accepted old
step and its forward adapter must produce the same source action result. It
does not assert that Action itself contains source admission guards. -/
namespace Eip8282.Audit.Integrator.ReferenceActionDeterminism
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceStorageView ReferenceRuntimeView
set_option autoImplicit false
set_option maxHeartbeats 2000000

private theorem base_deterministic {kind : Kind} {p : Parent} {instr : Instruction} {v a b : View}
    (first : ReferenceSystemAction.Action kind p instr v a)
    (second : ReferenceSystemAction.Action kind p instr v b) : a = b := by
  cases first <;> cases second <;>
    simp_all [ReferencePureAction.action,ReferencePureAction.classify]

private theorem base_not_copy {kind : Kind} {p : Parent} {v next : View}
    (h : ReferenceSystemAction.Action kind p (.CALLDATACOPY,none) v next) : False := by
  cases h
  simp_all [ReferencePureAction.action,ReferencePureAction.classify]

private theorem base_not_log {kind : Kind} {p : Parent} {v next : View}
    (h : ReferenceSystemAction.Action kind p (.LOG0,none) v next) : False := by
  cases h
  simp_all [ReferencePureAction.action,ReferencePureAction.classify]

theorem deterministic {kind : Kind} {p : Parent} {instr : Instruction} {v a b : View}
    (first : ReferenceRuntimeAction.Action kind p instr v a)
    (second : ReferenceRuntimeAction.Action kind p instr v b) : a = b := by
  cases first with
  | base first =>
    cases second with
    | base second => exact base_deterministic first second
    | copy => exact False.elim (base_not_copy first)
    | log => exact False.elim (base_not_log first)
  | copy stack =>
    cases second with
    | base second => exact False.elim (base_not_copy second)
    | copy stack' => simp_all
  | log permission stack =>
    cases second with
    | base second => exact False.elim (base_not_log second)
    | log permission' stack' => simp_all

/-- A local injected counterexample to reversing an unchecked action as an
admitted opcode. PC0 is CALLER in both images, but the action lacks the source
stack guard: with1024 incoming elements it computes1025. Such a frame state
still needs a reachability proof and is not claimed constructor-reachable. -/
theorem unchecked_caller (kind : Kind) (v : View) (length : v.stack.length = 1024) :
    ∃ next, ReferencePureAction.action kind (.CALLER,none) v = some next ∧ next.stack.length = 1025 := by
  refine ⟨ReferencePureAction.advance v (UInt256.ofNat v.env.source.val::v.stack),rfl,?_⟩
  simp [ReferencePureAction.advance,stackAction,length]

theorem full_stack_caller_rejected {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    (length : pre.stack.length = 1024) : Z vj .CALLER pre ≠ .ok (mid,cost) := by
  intro accepted
  have h := (ReferenceAcceptedStack.bounds accepted).2
  simp only [δ,α,Option.getD_some,length] at h
  omega

#print axioms deterministic
#print axioms unchecked_caller
#print axioms full_stack_caller_rejected
end Eip8282.Audit.Integrator.ReferenceActionDeterminism
