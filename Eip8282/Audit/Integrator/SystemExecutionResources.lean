import Eip8282.Audit.Integrator.SystemTraceWitness
import Eip8282.Audit.Integrator.RuntimeMemoryMonotone

/-! The actual SYSTEM path, including the terminal instruction, tied to one
successful evaluator result. Intermediate access bounds come from that path's
endpoint capacity. Reference interpreter replay and dual-pool progress remain
separate consumers; these are not claims about their gas metering. -/
namespace Eip8282.Audit.Integrator.SystemExecutionResources
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall)
open RuntimeExecutionScope SystemTraceAnnotations SystemPathBudget
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

structure Completed (image : Image) (steps cap outputBytes fuel : Nat) (pre : EVM.State) where
  exitState : EVM.State
  finalState : EVM.State
  output : ByteArray
  trace : List Labelled
  rem : Nat
  run : XRuns (D_J image.code ⟨0⟩) fuel pre trace (rem+2) exitState
  halt : Halt (D_J image.code ⟨0⟩) exitState .RETURN output
  terminal : StepOk (rem+1) (C' (charged exitState .RETURN) .RETURN)
    (.RETURN,none) (charged exitState .RETURN) finalState
  returned : H finalState.toMachineState .RETURN = some output
  success : X fuel (D_J image.code ⟨0⟩) pre = .ok (.success finalState output)
  operations_bound : (operations trace ++ [Operation.RETURN]).length ≤ steps+1
  stores_bound : weight storeWeight (operations trace ++ [Operation.RETURN]) ≤ 4
  allowed : ∀ op ∈ operations trace ++ [Operation.RETURN], Allowed op
  at_exit : At image exitState
  exit_capacity : exitState.activeWords.toNat ≤ cap
  output_operands : ∃ len : UInt256, exitState.stack = [UInt256.ofNat 0,len] ∧ len.toNat ≤ outputBytes

/-- No whole-execution success or intermediate memory bound is a premise. -/
theorem complete {image : Image} {steps cap outputBytes fuel : Nat} {pre : EVM.State}
    (hat : At image pre)
    (path : SystemTraceWitness.Path (D_J image.code ⟨0⟩) steps cap outputBytes pre)
    (enough : steps+2 ≤ fuel) : Nonempty (Completed image steps cap outputBytes fuel pre) := by
  obtain ⟨finish,out,tr,rem,hr,hl,hs,ha,hm,ho,hh⟩ := SystemTraceWitness.instantiate path (by omega : steps+1 ≤ fuel)
  have hlen : tr.length ≤ steps := by simpa [operations] using hl
  have hrpos : 1 ≤ rem := by have := hr.length; omega
  have hrun : XRuns (D_J image.code ⟨0⟩) fuel pre tr (rem-1+2) finish := by
    convert hr using 1
    omega
  obtain ⟨post,hstep,hout⟩ := hh.step (rem-1)
  exact ⟨{
    exitState := finish, finalState := post, output := out, trace := tr, rem := rem-1,
    run := hrun, halt := hh, terminal := hstep, returned := hout,
    success := hrun.X_success hh.decode hh.charge hstep hout (by decide),
    operations_bound := hl, stores_bound := hs, allowed := ha,
    at_exit := (RuntimeMemoryMonotone.runs hat hrun).1,
    exit_capacity := hm, output_operands := ho }⟩

/-- Every selected actual edge of this completed run has bounded operands.
The prefix/edge/suffix are actual execution facts, not assumed span bounds. -/
theorem intermediate {image : Image} {steps cap outputBytes fuel : Nat} {start : EVM.State}
    (h : Completed image steps cap outputBytes fuel start) (hat : At image start)
    {edgeFuel cost : Nat} {pre post : EVM.State} {before after : List Labelled}
    (hp : XRuns (D_J image.code ⟨0⟩) fuel start before (edgeFuel+1) pre)
    (he : XStepAt (D_J image.code ⟨0⟩) edgeFuel cost pre post)
    (ht : XRuns (D_J image.code ⟨0⟩) edgeFuel post after (h.rem+2) h.exitState) :
    pre.activeWords.toNat ≤ cap ∧ post.activeWords.toNat ≤ cap ∧
    (0 < (RuntimeMemoryMonotone.span pre (decodeAt pre).1).2 →
      (RuntimeMemoryMonotone.span pre (decodeAt pre).1).1 +
      (RuntimeMemoryMonotone.span pre (decodeAt pre).1).2 ≤ 32*cap) :=
  RuntimeMemoryMonotone.suffix_bounds hat hp he ht h.exit_capacity

theorem deposit (c : XiCall .deposit) (system : Deposit.callerWord c = sysW)
    (permission : c.env.perm = true) (gas : 2500000 ≤ c.gas.toNat)
    (fuel : 8502 ≤ c.fuel) :
    Nonempty (Completed RuntimeExecutionScope.deposit 8500 400 11776 c.fuel c.entry) := by
  have hp := SystemTraceWitness.deposit c system permission gas
  rw [← deposit_D_J] at hp
  exact complete ⟨c.code_pinned,Or.inl RuntimeExecutionScope.deposit.entry⟩ hp fuel

theorem exit (c : XiCall .exit) (system : Exit.callerWord c = sysW)
    (permission : c.env.perm = true) (gas : 250000 ≤ c.gas.toNat)
    (fuel : 802 ≤ c.fuel) :
    Nonempty (Completed RuntimeExecutionScope.exit 800 40 1088 c.fuel c.entry) := by
  have hp := SystemTraceWitness.exit c system permission gas
  rw [← exit_D_J] at hp
  exact complete ⟨c.code_pinned,Or.inl RuntimeExecutionScope.exit.entry⟩ hp fuel

#print axioms complete
#print axioms intermediate
#print axioms deposit
#print axioms exit
end Eip8282.Audit.Integrator.SystemExecutionResources
