import Eip8282.Audit.Integrator.CallBridge

/-!
# Necessity of successful code execution for successful message calls

Invert actual Θ success, preserving the exact empty-world settlement branch.
This lets successful-execution classification consume a complete message call
without an assumed Ξ success witness or a nonempty-world premise.
-/
namespace Eip8282.Audit.Integrator.CallSuccess

open EvmYul EvmYul.EVM
open MessageCall CallBridge
open Eip8282.Audit.Correspondence (runtimeCode)

/-- True returned status forces a successful code execution with the same
created accounts, remaining gas and return bytes. World/substate are related
by the real settlement fallback rather than assumed equal. -/
theorem execution_of_success (c : Context)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    ∃ execWorld execSubstate,
      c.execution = .ok (.success (created, execWorld, gas, execSubstate) out) ∧
      world = (if execWorld == ∅ then c.world else execWorld) ∧
      substate = (if execWorld == ∅ then c.substate else execSubstate) := by
  rw [result_eq_settle] at h
  cases he : c.execution with
  | error err =>
    simp only [Context.settle, he] at h
    split at h <;> cases h
  | ok res =>
    cases res with
    | revert g data =>
      simp only [Context.settle, he] at h
      cases h
    | success published data =>
      rcases published with ⟨cr, ew, g, es⟩
      simp only [Context.settle, he, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, hw, rfl, hs, _, rfl⟩
      exact ⟨ew, es, rfl, hw.symm, hs.symm⟩

/-- The same necessity statement for the pinned code frame at its exact fuel
index. No gas lower bound or successful-execution premise is supplied. -/
theorem codeCall_of_success (c : Context) {kind : Model.Kind}
    (hcode : c.code = runtimeCode kind) (steps : Nat) (hf : c.fuel = steps+1)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    ∃ execWorld execSubstate,
      (codeCall c hcode steps).result = .ok (.success (created, execWorld, gas, execSubstate) out) ∧
      world = (if execWorld == ∅ then c.world else execWorld) ∧
      substate = (if execWorld == ∅ then c.substate else execSubstate) := by
  obtain ⟨ew, es, he, hw, hs⟩ := execution_of_success c h
  rw [execution_eq_codeCall c hcode steps hf] at he
  exact ⟨ew, es, he, hw, hs⟩

#print axioms execution_of_success
#print axioms codeCall_of_success

end Eip8282.Audit.Integrator.CallSuccess
