import Eip8282.Audit.Guarantees.PSubmit1
import Eip8282.Audit.Guarantees.PDrain1
import Eip8282.Audit.Guarantees.PControl1
import Eip8282.Tests.PSubmit1Mutant
import Eip8282.Tests.PControl1Mutant
import Eip8282.Tests.PDrain1Mutant

/-!
Machine-readable-in-build trust report.

## Allowed axioms

Abstract-model theorems may depend only on the three Lean foundational
axioms `propext`, `Classical.choice`, and `Quot.sound`.

`Classical.choice` is an accepted dependency, disclosed in
`audit/assumptions.yaml` as `A-CLASSICAL-CHOICE`. `sorryAx` and any
project-introduced `axiom` must never appear anywhere.

## Disclosed `native_decide` escape (bytecode layer)

`Eip8282.Audit.Guarantees.PSubmit1.psubmit1_bytecode_parent`,
`Eip8282.Audit.Guarantees.PDrain1.pdrain1_bytecode_parent`,
`Eip8282.Audit.Guarantees.PControl1.pcontrol1_bytecode_parent`,
`Eip8282.Audit.Guarantees.PControl1.pcontrol1_nonempty_bytecode_parent` and the
`Eip8282.Tests.PSubmit1Mutant` / `Eip8282.Tests.PDrain1Mutant` /
`Eip8282.Tests.PControl1Mutant` kill-lines additionally depend on one
compiler-generated axiom each, of the form
`<theorem>._native.native_decide.ax_1_1`. That is Lean 4.31's
`native_decide` receipt; it is not a hand-written `axiom`. Disclosed as
`A-NATIVE-DECIDE`.

This is forced, not chosen. `EvmYul.EVM.Ξ` reaches `D_J`, whose worker
`D_J_aux` is a `partial def` (`EvmYul/EVM/Semantics.lean:99`) and is
therefore kernel-opaque: `decide` and `rfl` cannot reduce any concrete Ξ
trace. The trusted base for the bytecode layer is consequently the Lean
compiler plus the EVMYulLean interpreter, not the kernel alone. Removing it
requires a non-`partial` jumpdest scanner upstream.

The public surface is the abstract model plus pinned-bytecode traces under `Ξ`.
-/

#print axioms Eip8282.Audit.Guarantees.PSubmit1.revert_is_atomic
#print axioms Eip8282.Audit.Guarantees.PSubmit1.success_count_and_balance
#print axioms Eip8282.Audit.Guarantees.PSubmit1.deposit_appends_calldata
#print axioms Eip8282.Audit.Guarantees.PSubmit1.exit_binds_caller
#print axioms Eip8282.Audit.Guarantees.PSubmit1.inhibited_blocks_users
#print axioms Eip8282.Audit.Guarantees.PSubmit1.psubmit1_bytecode_parent
#print axioms Eip8282.Tests.PSubmit1Mutant.mutant_refutes_parent
#print axioms Eip8282.Tests.PSubmit1Mutant.pinned_satisfies_what_mutant_breaks
#print axioms Eip8282.Tests.PSubmit1Mutant.log_size_mutant_empties_the_log
#print axioms Eip8282.Tests.PSubmit1Mutant.pinned_satisfies_what_log_mutant_breaks
#print axioms Eip8282.Tests.PSubmit1Mutant.log_mutant_leaves_siblings_intact
#print axioms Eip8282.Tests.PSubmit1Mutant.underpay_mutant_accepts_the_underpay
#print axioms Eip8282.Tests.PSubmit1Mutant.pinned_satisfies_what_underpay_mutant_breaks
#print axioms Eip8282.Tests.PSubmit1Mutant.underpay_mutant_leaves_siblings_intact
#print axioms Eip8282.Audit.Guarantees.PDrain1.system_always_succeeds
#print axioms Eip8282.Audit.Guarantees.PDrain1.fifo_bounded
#print axioms Eip8282.Audit.Guarantees.PDrain1.fifo_return
#print axioms Eip8282.Audit.Guarantees.PDrain1.empty_queue_after_full_drain
#print axioms Eip8282.Audit.Guarantees.PDrain1.encoding
#print axioms Eip8282.Audit.Guarantees.PDrain1.pdrain1_bytecode_parent
#print axioms Eip8282.Tests.PDrain1Mutant.pinned_drain_bytes
#print axioms Eip8282.Tests.PDrain1Mutant.mutant_refutes_parent
#print axioms Eip8282.Tests.PDrain1Mutant.cap_mutant_halves_the_over_cap_drain
#print axioms Eip8282.Tests.PDrain1Mutant.rec_size_mutant_shrinks_the_return
#print axioms Eip8282.Tests.PDrain1Mutant.deposit_cap_mutant_halves_the_over_cap_drain
#print axioms Eip8282.Tests.PDrain1Mutant.head_slot_mutant_overwrites_a_drained_word
#print axioms Eip8282.Tests.PDrain1Mutant.head_slot_mutant_item32_overwrites_item32_first_word
#print axioms Eip8282.Tests.PDrain1Mutant.head_slot_mutant_item7_overwrites_item7_src
#print axioms Eip8282.Tests.PDrain1Mutant.pinned_satisfies_what_mutants_break
#print axioms Eip8282.Tests.PDrain1Mutant.drain_mutants_leave_siblings_intact
#print axioms Eip8282.Audit.Guarantees.PControl1.targets
#print axioms Eip8282.Audit.Guarantees.PControl1.initial_gating
#print axioms Eip8282.Audit.Guarantees.PControl1.fee_getter_readonly
#print axioms Eip8282.Audit.Guarantees.PControl1.count_increments
#print axioms Eip8282.Audit.Guarantees.PControl1.system_resets_count
#print axioms Eip8282.Audit.Guarantees.PControl1.nonempty_sets_inhibitor
#print axioms Eip8282.Audit.Guarantees.PControl1.empty_clears_inhibitor
#print axioms Eip8282.Audit.Guarantees.PControl1.empty_updates_excess
#print axioms Eip8282.Audit.Guarantees.PControl1.inhibit_users_not_system
#print axioms Eip8282.Audit.Guarantees.PControl1.pcontrol1_bytecode_parent
#print axioms Eip8282.Audit.Guarantees.PControl1.pcontrol1_nonempty_bytecode_parent
#print axioms Eip8282.Tests.PControl1Mutant.pinned_control_bytes
#print axioms Eip8282.Tests.PControl1Mutant.mutant_refutes_parent
#print axioms Eip8282.Tests.PControl1Mutant.gate_mutant_loses_the_system_subroutine
#print axioms Eip8282.Tests.PControl1Mutant.target_mutant_shifts_only_the_system_recurrence
#print axioms Eip8282.Tests.PControl1Mutant.pinned_satisfies_what_mutants_break
#print axioms Eip8282.Tests.PControl1Mutant.control_mutants_leave_psubmit1_intact
#print axioms Eip8282.Tests.PControl1Mutant.wave5_pinned_bytes
#print axioms Eip8282.Tests.PControl1Mutant.wave5_mutant_refutes_nonempty_parent
#print axioms Eip8282.Tests.PControl1Mutant.wave5_target_shifts_nonempty_excess
#print axioms Eip8282.Tests.PControl1Mutant.wave5_mutants_leave_psubmit1_intact
#print axioms Eip8282.Tests.PControl1Mutant.nonempty_is_not_empty
