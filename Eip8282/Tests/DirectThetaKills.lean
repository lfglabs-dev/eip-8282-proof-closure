import Eip8282.Tests.DirectThetaSubmitCounterexample
import Eip8282.Tests.DirectThetaDrainMutations

/-!
# Mutation refutations for the three registered direct predicates

These conjunctions collect only tests. They are not conjuncts of the universal
correctness parents. Five refutations retain their historical native receipts;
the funded LOG0 refutation is kernel checked. No universal sibling survival is
claimed: the guarantees have intentional overlapping clauses.
-/
namespace Eip8282.Tests.DirectThetaKills
open Eip8282.Audit.Integrator
open EvmYul

theorem submit_kill :
    ¬ DirectGuarantees.PSubmit .deposit PSubmit1Mutant.logSizeMutatedDeposit :=
  DirectThetaSubmitCounterexample.log_refutes_psubmit

theorem drain_kills :
    (¬ DirectGuarantees.PDrain .deposit PDrain1Mutant.capMutatedDeposit) ∧
    (¬ DirectGuarantees.PDrain .deposit PDrain1Mutant.headSlotMutatedDeposit) ∧
    (¬ DirectGuarantees.PDrain .exit PDrain1Mutant.capMutatedExit) :=
  ⟨DirectThetaDrainMutations.deposit_cap_refutes_pdrain,
    DirectThetaDrainMutations.deposit_stale_refutes_pdrain,
    DirectThetaDrainMutations.exit_cap_refutes_pdrain⟩

theorem control_kills (init : ByteArray) :
    (¬ DirectGuarantees.PControl .deposit PControl1Mutant.gateMutatedDeposit init) ∧
    (¬ DirectGuarantees.PControl .deposit PControl1Mutant.targetMutatedDeposit init) :=
  ⟨DirectThetaMutations.gate_refutes_pcontrol init,
    DirectThetaMutations.target_refutes_pcontrol init⟩

#print axioms submit_kill
#print axioms drain_kills
#print axioms control_kills
end Eip8282.Tests.DirectThetaKills
