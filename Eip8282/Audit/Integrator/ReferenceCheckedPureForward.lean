import Eip8282.Audit.Integrator.ReferenceCheckedRuntimeTrace

/-! Forward acceptance of source-shaped pure actions with the same literal
payment. Consumer: the paid SYSTEM trace-to-checked evaluator connection.
The source action is supplied by an accepted old step and its stack bound;
it is not a public guaranteed-success premise. No instruction formula or
resource allowance changes here. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedPureForward
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceMeterRollback ReferenceMeterBoundary
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- Invert the same full-meter ordinary payment, preserving baseline fields. -/
theorem ordinary_paid {amount : Nat} {meter final : Meter}
    (paid : runFull [.ordinary amount] meter = some final) :
    ∃ charged, ReferenceStorageGas.chargeExecution (core meter) amount = some charged ∧
      final = update meter charged := by
  unfold runFull ReferenceMeterPath.run ReferenceMeterPath.pay at paid
  cases hc : ReferenceStorageGas.chargeExecution (core meter) amount with
  | none => simp [hc] at paid
  | some charged =>
    simp only [hc,Option.bind_some,ReferenceMeterPath.run,Option.map_some,Option.some.injEq] at paid
    exact ⟨charged,rfl,paid.symm⟩

/-- Arithmetic action and its real payment suffice once its output stack fits. -/
theorem binary {kind : Kind} {b : ReferenceWordOps.Binary} {arg : Option (UInt256 × Nat)}
    {v next : View} {meter final : Meter}
    (action : ReferencePureAction.action kind (ReferenceWordOps.opcode b,arg) v = some next)
    (bound : next.stack.length ≤ 1024)
    (paid : runFull [.ordinary (ReferenceCheckedBinaryStep.charge b)] meter = some final) :
    ReferenceCheckedBinaryStep.run b v meter = .ok (next,final) := by
  obtain ⟨charged,hc,rfl⟩ := ordinary_paid paid
  have family : ReferencePureAction.familyAction kind (.binary b) arg v = some next := by
    change (ReferencePureAction.classify (ReferencePureAction.opcode (.binary b))).bind _ = _ at action
    simpa only [ReferencePureAction.classify_opcode,Option.bind_some] using action
  cases shape : v.stack with
  | nil => simp [ReferencePureAction.familyAction,shape] at family
  | cons x tail =>
    cases tail with
    | nil => simp [ReferencePureAction.familyAction,shape] at family
    | cons y rest =>
      simp only [ReferencePureAction.familyAction,shape,Option.some.injEq] at family
      subst next
      have notfull : rest.length ≠ 1024 := by
        simp only [ReferencePureAction.advance,stackAction,List.length_cons] at bound
        omega
      simp only [ReferenceCheckedBinaryStep.run,shape,ReferenceSourceStackAdmission.pop,hc,
        ReferenceSourceStackAdmission.push,if_neg notfull]
      rfl

private theorem push_fits (value : UInt256) (stack : List UInt256) (bound : stack.length < 1024) :
    ReferenceSourceStackAdmission.push value stack = .ok (value::stack) := by
  simp [ReferenceSourceStackAdmission.push,show stack.length ≠ 1024 by omega]

/-- The same source action already contains CALLDATASIZE's checked conversion;
output-stack admission discharges the literal equality1024 push guard. -/
theorem environment {kind : Kind} {h : ReferenceCheckedEnvironmentStep.Handler}
    {arg : Option (UInt256 × Nat)} {v next : View} {meter final : Meter}
    (action : ReferencePureAction.action kind (ReferenceCheckedEnvironmentStep.opcode h,arg) v = some next)
    (bound : next.stack.length ≤ 1024)
    (paid : runFull [.ordinary (ReferenceCheckedEnvironmentStep.charge h)] meter = some final) :
    ReferenceCheckedEnvironmentStep.run h v meter = .ok (next,final) := by
  obtain ⟨charged,hc,rfl⟩ := ordinary_paid paid
  cases h <;> cases shape : v.stack <;>
    simp only [ReferenceCheckedEnvironmentStep.opcode,ReferencePureAction.action,
      ReferencePureAction.classify,Option.bind_some,ReferencePureAction.familyAction,shape] at action
  all_goals try contradiction
  all_goals try split at action
  all_goals try contradiction
  all_goals cases action
  all_goals try dsimp only [ReferencePureAction.advance,stackAction,List.length_cons,List.length_nil] at bound
  all_goals simp only [ReferenceCheckedEnvironmentStep.charge] at hc
  all_goals
    simp (disch := simp_all only [List.length_cons,List.length_nil] <;> omega) [ReferenceCheckedEnvironmentStep.run,ReferenceCheckedEnvironmentStep.finish,
      ReferenceSourceStackAdmission.pop,push_fits,shape,hc,
      ReferencePureAction.advance,stackAction, *]
  all_goals rw [push_fits _ _ (by omega)]
  all_goals rfl


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

/-- Paid stack/control actions run through the actual guarded implementation.
The code-PC fit and scanned destination context are produced along SYSTEM's
accepted trace; PUSH bytes come from the same instruction/view. -/
theorem stack_control {kind : Kind} {h : ReferenceCheckedStackControlStep.Handler}
    {destinations : List Nat} {v next : View} {meter final : Meter}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (action : ReferencePureAction.action kind (ReferenceCheckedStackControlStep.instruction h v) v = some next)
    (bound : next.stack.length ≤ 1024) (pcfit : v.pc+1 < UInt256.size)
    (paid : runFull [.ordinary (ReferenceCheckedStackControlStep.charge h)] meter = some final) :
    ReferenceCheckedStackControlStep.run h destinations v meter = .ok (next,final) := by
  obtain ⟨charged,hc,rfl⟩ := ordinary_paid paid
  unfold ReferenceCheckedStackControlStep.DestinationContext at context
  subst destinations
  rcases stack_cases v.stack with shape | ⟨a,shape⟩ | ⟨a,b,shape⟩ | ⟨a,b,c,shape⟩ |
    ⟨a,b,c,d,shape⟩ | ⟨a,b,c,d,e,rest,shape⟩
  all_goals cases h <;>
    simp only [ReferenceCheckedStackControlStep.instruction,ReferenceCheckedStackControlStep.immediate,
      ReferenceCheckedStackControlStep.width,ReferenceCheckedStackControlStep.opcode,
      ReferenceCheckedStackControlStep.family,ReferencePureAction.opcode,
      ReferencePureAction.action,ReferencePureAction.classify,Option.bind_some,
      ReferencePureAction.familyAction,ReferenceStackOps.dupDepth,ReferenceStackOps.swapDepth,
      argOnNBytesOfInstr,shape] at action
  all_goals try simp at action
  all_goals repeat (first | contradiction | split at action)
  all_goals try (by_cases hj : a.toNat ∈ ReferenceDecodeSites.referenceJumps (ReferenceRuntimeSites.reference kind) <;> simp only [hj,if_pos,if_neg] at action)
  all_goals try contradiction
  all_goals try (rcases action with ⟨jumpValid,action⟩)
  all_goals try cases action
  all_goals try dsimp only [ReferencePureAction.advance,stackAction,List.length_cons,List.length_nil] at bound
  all_goals simp only [ReferenceCheckedStackControlStep.charge] at hc
  all_goals
    simp (disch := simp_all only [List.length_cons,List.length_nil] <;> omega) [ReferenceCheckedStackControlStep.run,ReferenceCheckedStackControlStep.prepare,
      ReferenceCheckedStackControlStep.operate,ReferenceCheckedStackControlStep.family,ReferenceCheckedStackControlStep.charge,
      ReferenceCheckedStackControlStep.push_definition,
      ReferenceCheckedStackControlStep.width,ReferenceCheckedStackControlStep.opcode,
      ReferencePureAction.opcode,argOnNBytesOfInstr,
      ReferenceSourceStackAdmission.pop,push_fits,
      ReferenceStackOps.dupDepth,ReferenceStackOps.swapDepth,
      ReferencePureAction.advance,stackAction,shape,hc,pcfit,
      ReferenceMemoryView.buffer,uInt256OfByteArray,fromBytes',Nat.add_assoc,show UInt256.ofNat 0 = ⟨0⟩ from rfl, *]
  all_goals try (rw [push_fits _ _ (by simp_all only [List.length_cons,List.length_nil]; omega)]; rfl)
  all_goals try rfl

#print axioms ordinary_paid
#print axioms binary
#print axioms environment
#print axioms stack_control
end Eip8282.Audit.Integrator.ReferenceCheckedPureForward
