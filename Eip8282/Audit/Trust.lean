import Eip8282.Audit.Guarantees.PSubmit1
import Eip8282.Audit.Guarantees.PDrain1
import Eip8282.Audit.Guarantees.PControl1

/-!
Machine-readable-in-build trust report.

## Allowed axioms

Every theorem printed below may depend only on the three Lean foundational
axioms `propext`, `Classical.choice`, and `Quot.sound`.

`Classical.choice` is an accepted dependency, disclosed in
`audit/assumptions.yaml` as `A-CLASSICAL-CHOICE`. Anything outside those
three is a proof escape and is not accepted. In particular `sorryAx`,
`Lean.ofReduceBool` (except the disclosed `native_decide` uses below),
and any project-introduced `axiom` must not appear.

The current campaign proves only the abstract model. Verity and bytecode
layers are OPEN.
-/

#print axioms Eip8282.Audit.Guarantees.PSubmit1.revert_is_atomic
#print axioms Eip8282.Audit.Guarantees.PSubmit1.success_count_and_balance
#print axioms Eip8282.Audit.Guarantees.PSubmit1.deposit_appends_calldata
#print axioms Eip8282.Audit.Guarantees.PSubmit1.exit_binds_caller
#print axioms Eip8282.Audit.Guarantees.PSubmit1.inhibited_blocks_users
#print axioms Eip8282.Audit.Guarantees.PDrain1.system_always_succeeds
#print axioms Eip8282.Audit.Guarantees.PDrain1.fifo_return
#print axioms Eip8282.Audit.Guarantees.PDrain1.empty_queue_after_full_drain
#print axioms Eip8282.Audit.Guarantees.PDrain1.encoding
#print axioms Eip8282.Audit.Guarantees.PControl1.targets
#print axioms Eip8282.Audit.Guarantees.PControl1.initial_gating
#print axioms Eip8282.Audit.Guarantees.PControl1.fee_getter_readonly
#print axioms Eip8282.Audit.Guarantees.PControl1.count_increments
#print axioms Eip8282.Audit.Guarantees.PControl1.system_resets_count
#print axioms Eip8282.Audit.Guarantees.PControl1.nonempty_sets_inhibitor
#print axioms Eip8282.Audit.Guarantees.PControl1.empty_clears_inhibitor
#print axioms Eip8282.Audit.Guarantees.PControl1.empty_updates_excess
#print axioms Eip8282.Audit.Guarantees.PControl1.inhibit_users_not_system
