import Eip8282.Audit.Integrator.ReferenceCheckedDispatch

/-! Actual checked dispatch terminal inversion. The selected terminal result
comes from the same literal handler, code and PC; its reference decoding is
some terminal, never the replay helper's STOP fallback. No old execution,
Action, desired output or source frame hypothesis is supplied.
Fixed-image coverage is a kernel check of the two existing site tables, not
an execution iteration ceiling or arbitrary-bytecode interpreter parity.
Source interpreter extraction and outer REVERT/error settlement remain separate. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedDispatchTerminal
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback
open ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem handler_terminal {h : Handler} {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {v : View} {warm : Warm} {meter : Meter}
    {output : ByteArray} {result : ReferenceCheckedTerminalStep.End}
    (actual : runHandler h destinations ownerExists parent v warm meter output = .terminal result) :
    ∃ halt, h = .terminal halt ∧ ReferenceCheckedTerminalStep.run halt v meter output = .ok result := by
  cases h
  case terminal halt =>
    simp only [runHandler] at actual
    cases ht : ReferenceCheckedTerminalStep.run halt v meter output with
    | error fault =>
      rcases fault with ⟨e,next,final,previous⟩
      simp only [ht] at actual
      contradiction
    | ok endState =>
      simp only [ht,Outcome.terminal.injEq] at actual
      subst endState
      exact ⟨halt,rfl,ht⟩
  all_goals simp only [runHandler] at actual
  all_goals split at actual <;> contradiction

/-- A dispatched terminal is the exact same successful terminal-handler result
and a successful source-shaped decode at the current code/PC. -/
theorem terminal {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {v : View} {warm : Warm} {meter : Meter}
    {output : ByteArray} {result : ReferenceCheckedTerminalStep.End}
    (actual : run destinations ownerExists parent v warm meter output = .terminal result) :
    ∃ halt,
      ReferenceCheckedTerminalStep.run halt v meter output = .ok result ∧
      ReferenceDecodeSites.referenceDecode v.env.code v.pc =
        some (ReferenceCheckedTerminalStep.opcode halt,none) := by
  unfold run at actual
  cases hd : read v.env.code v.pc <;> rw [hd] at actual
  · contradiction
  · contradiction
  · contradiction
  · obtain ⟨halt,rfl,checked⟩ := handler_terminal actual
    obtain ⟨arg,decoded⟩ := read_handler hd
    have width : argOnNBytesOfInstr (ReferenceCheckedTerminalStep.opcode halt) = 0 := by
      cases halt <;> rfl
    have immediate := ReferenceCheckedDecode.decode_width decoded
    change arg = if argOnNBytesOfInstr (ReferenceCheckedTerminalStep.opcode halt) = 0 then none else _ at immediate
    rw [width,if_pos rfl] at immediate
    subst arg
    exact ⟨halt,checked,decoded⟩

private theorem site_table (kind : Kind) :
    (ReferenceDecodeSites.sites (ReferenceRuntimeSites.reference kind)).all
      (fun pc => match read (ReferenceDecodeSites.code (ReferenceRuntimeSites.reference kind)) pc with
        | .handler _ => true | _ => false) = true := by
  cases kind <;> decide +kernel

/-- Every genuine listed site in either pinned runtime dispatches a supported
handler. This does not classify EOF as a handler or claim site reachability. -/
theorem runtime_coverage (kind : Kind) (v : View)
    (code : v.env.code = ReferenceDecodeSites.code (ReferenceRuntimeSites.reference kind))
    (site : v.pc ∈ ReferenceDecodeSites.sites (ReferenceRuntimeSites.reference kind)) :
    ∃ h, read v.env.code v.pc = .handler h := by
  have covered := List.all_eq_true.mp (site_table kind) v.pc site
  rw [←code] at covered
  cases hd : read v.env.code v.pc <;> simp only [hd] at covered
  · contradiction
  · contradiction
  · contradiction
  · exact ⟨_,rfl⟩

#print axioms terminal
#print axioms runtime_coverage
end Eip8282.Audit.Integrator.ReferenceCheckedDispatchTerminal
