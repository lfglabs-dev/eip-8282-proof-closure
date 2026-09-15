import Eip8282.Audit.Integrator.ResourceAssumptions

/-! Keep the supply/work derivation free of additional axioms. -/
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for theoremName in #[
      ``Eip8282.Audit.Integrator.ResourceAssumptions.supply_units,
      ``Eip8282.Audit.Integrator.ResourceAssumptions.supply_below_fee_boundary,
      ``Eip8282.Audit.Integrator.ResourceAssumptions.supply_fits_word,
      ``Eip8282.Audit.Integrator.ResourceAssumptions.preserves,
      ``Eip8282.Audit.Integrator.ResourceAssumptions.domains,
      ``Eip8282.Audit.Integrator.ResourceAssumptions.completed_call,
      ``Eip8282.Audit.Integrator.ResourceAssumptions.guarantees,
      ``Eip8282.Audit.Integrator.ResourceAssumptions.from_deployment] do
    for axiomName in ← Lean.collectAxioms theoremName do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {theoremName}"
