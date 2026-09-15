import Eip8282.Audit.Integrator.DirectGuarantees
import Eip8282.Tests.DirectThetaKills

/-!
# Trust report for the registered guarantees

The three correctness theorems and the funded LOG0 refutation use only Lean's
standard foundations (`propext`, `Classical.choice`, `Quot.sound`).
The drain/control refutations additionally retain five historical finite
native-evaluation receipts, disclosed as A-NATIVE-DECIDE. They are tests,
not assumptions or conjuncts of the correctness theorems.

The superseded broad report is preserved in audit/history/Trust-20260915.lean.
Candidate modules retain their own axiom reports and build in `make candidates`.
-/

#print axioms Eip8282.Audit.Integrator.DirectGuarantees.psubmit1_direct
#print axioms Eip8282.Audit.Integrator.DirectGuarantees.pdrain1_direct
#print axioms Eip8282.Audit.Integrator.DirectGuarantees.pcontrol1_direct
#print axioms Eip8282.Tests.DirectThetaKills.submit_kill
#print axioms Eip8282.Tests.DirectThetaKills.drain_kills
#print axioms Eip8282.Tests.DirectThetaKills.control_kills

-- Fail the build if a correctness theorem acquires an additional trust premise.
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for theoremName in #[
      ``Eip8282.Audit.Integrator.DirectGuarantees.psubmit1_direct,
      ``Eip8282.Audit.Integrator.DirectGuarantees.pdrain1_direct,
      ``Eip8282.Audit.Integrator.DirectGuarantees.pcontrol1_direct,
      ``Eip8282.Tests.DirectThetaKills.submit_kill] do
    let axioms ← Lean.collectAxioms theoremName
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {theoremName}"
