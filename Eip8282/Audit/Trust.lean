import Eip8282.Audit.Guarantees.PSubmit1
import Eip8282.Audit.Guarantees.PDrain1
import Eip8282.Audit.Guarantees.PControl1
import Eip8282.Audit.Step
import Eip8282.Audit.XiTransport
import Eip8282.Audit.Reachable
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

`Eip8282.Audit.Guarantees.PSubmit1.psubmit1_forall_parent` (via the
kept `psubmit1_bytecode_parent` traces),
`Eip8282.Audit.Guarantees.PSubmit1.psubmit1_bytecode_parent`,
`Eip8282.Audit.Guarantees.PDrain1.pdrain1_forall_parent` (via the
kept `pdrain1_bytecode_parent` traces),
`Eip8282.Audit.Guarantees.PDrain1.pdrain1_bytecode_parent`,
`Eip8282.Audit.Guarantees.PControl1.pcontrol1_forall_parent` (via the
kept `pcontrol1_bytecode_parent` / `pcontrol1_nonempty_bytecode_parent`
traces),
`Eip8282.Audit.Guarantees.PControl1.pcontrol1_bytecode_parent`,
`Eip8282.Audit.Guarantees.PControl1.pcontrol1_nonempty_bytecode_parent` and the
`Eip8282.Tests.PSubmit1Mutant` / `Eip8282.Tests.PDrain1Mutant` /
`Eip8282.Tests.PControl1Mutant` kill-lines additionally depend on one
compiler-generated axiom each, of the form
`<theorem>._native.native_decide.ax_1_1`. That is Lean 4.31's
`native_decide` receipt; it is not a hand-written `axiom`. Disclosed as
`A-NATIVE-DECIDE`.

The trusted base for those trace theorems is the Lean compiler plus the
EVMYulLean interpreter, not the kernel alone.

What still forces it, as of EVMYulLean `0ff72b2`, is **not** `D_J`, and it is
**not** an irreducible definition either. It is cost.

Earlier revisions of this file blamed `EvmYul.FFI.keccak256` / `sha256` /
`BLAKE2Compress` and the `partial` RLP decoders. Neither is reachable here.
Decoding the four pinned images (`depositRuntime`, `depositInit`,
`exitRuntime`, `exitInit`) finds no `SHA3`, no `BLOCKHASH`, no call/create
opcode and therefore no precompile dispatch, so the evaluator branches that
mention those `opaque ... @[extern]` constants are never entered; merely
importing them does not put them into kernel reduction. And
`EvmRunner.run` builds a world and applies `EVM.Ξ` to it directly — no
transaction RLP is decoded on this path, so `separateListRLP` /
`deserializeRLP` (`EvmYul/Wheels.lean`) are never called.

What is actually out of reach is evaluating the trace in the kernel. Each
kept trace is a `Ξ` run of up to `FUEL = 80000` interpreter steps (`300000`
for the deposit-cap traces) over EVMYulLean's monad-transformer stack,
`AccountMap` / `Std.TreeSet` lookups and `UInt256` / `ByteArray` operations.
`decide +kernel` would have to whnf that whole unfolding; `native_decide`
compiles it instead and runs it at native speed. The gap is time and memory,
not reducibility in principle.

`make prove` still builds the FFI dynlibs before `lake build` because
`native_decide` compiles and links the interpreter as a whole, and the
compiled artifact resolves the FFI symbols regardless of which branches the
pinned images actually execute.

## Jumpdest tables: no longer `native_decide`

`D_J_aux` used to be a `partial def`, which made the jumpdest scans
kernel-opaque too. EVMYulLean `0ff72b2` replaced it with a structurally
recursive definition (fuel = `c.size`), so the four ground `D_J`
applications now reduce in the kernel and are discharged by
`decide +kernel`. They carry no `native_decide` receipt, and neither do the
`validJumps = D_J _ ⟨0⟩` bridges the registered `∀` parents rewrite with.
The `#print axioms` lines below are the check: each must report only the
three foundational axioms, never an `ax_1_1` receipt.

The public P-SUBMIT-1 surface is the CFG-level `∀` parent
`psubmit1_forall_parent` plus the kept `submitFacts` traces under `Ξ`.
The public P-CONTROL-1 surface is the CFG-level `∀` parent
`pcontrol1_forall_parent` plus the kept `controlFacts` /
`nonemptyControlFacts` traces under `Ξ`.
The public P-DRAIN-1 surface is the CFG-level `∀` parent
`pdrain1_forall_parent` plus the kept `drainFacts` traces under `Ξ`.
The `∀` conjuncts (S1–S4, C1–C4, D1–D3, kill-line opcode pins) must not
introduce `sorryAx` or a project `axiom`. `native_decide` receipts belong
only on the kept trace theorems.

## R4: the `X` → `Ξ` layer

`Eip8282.Audit.XiTransport` transports the three *existing* registered
parents (`P-SUBMIT-1`, `P-DRAIN-1`, `P-CONTROL-1`; same IDs) to the
complete `Ξ` message call. Two of its facts are unconditional and must
report only the three foundational axioms — **no `native_decide` receipt**:

* `observe_Xi_eq_observe_X` — `Ξ` and the `X` run it delegates to have the
  same observation. `Ξ` re-wraps the success payload and passes `.revert`
  through, so neither the status flag nor the return bytes move.
* `Xi_validJumps_eq` — the table `Ξ` computes for itself from the pinned
  code is `depositJumpdests` / `exitJumpdests`, via the kernel `D_J`
  bridges above.

`xiTransport` and the three per-parent Ξ statements
(`psubmit1_xi_inhibited_reverts`, `pdrain1_xi_returns_fifo_prefix`,
`pcontrol1_xi_fee_getter`) are **conditional on `XiTransport.EndpointAgrees`**,
which is the named OPEN `A-ABSTRACT-TX` and is taken as a hypothesis,
never discharged. A green build of this module is therefore not evidence
that `A-ABSTRACT-TX` holds. No closed `∀` endpoint theorem is claimed.

`psubmit1_xi_forall_parent` / `pdrain1_xi_forall_parent` /
`pcontrol1_xi_forall_parent` each carry the unchanged registered parent as
a conjunct, so they inherit that parent's `native_decide` receipts and
remain refutable by the same one-byte kill-lines. YAML `parent:` still
names the original CFG theorems; R4 does not introduce new parent IDs.

## Reachability: kernel-checked, no receipts

`Eip8282.Audit.Reachable` closes the *coverage* direction of `A-REACHABLE`:
every packed image reachable from the pinned constructor post-images by a
successful submission or a system drain satisfies the `WellFormed` guard the
three registered parents quantify over, and abstracts under `toModel` to a
`Model.Reachable` state. That module never runs `Ξ`, so none of the lines
below may report a `native_decide` receipt — each must show only the three
foundational axioms. A receipt appearing here would mean the reachability
argument had silently acquired a trace dependency.

What it does *not* close is whether `Ξ` on the pinned runtimes realises
`applyUser` / `applySystem`. That residual is `A-ABSTRACT-TX`, which stays
open at HIGH.
-/

-- Kernel-checked jumpdest tables and the `validJumps` bridges (no receipts).
#print axioms Eip8282.Audit.Jumpdests.deposit_D_J
#print axioms Eip8282.Audit.Jumpdests.exit_D_J
#print axioms Eip8282.Audit.Jumpdests.depositInit_D_J
#print axioms Eip8282.Audit.Jumpdests.exitInit_D_J
#print axioms Eip8282.Audit.Step.deposit_validJumps_eq_D_J
#print axioms Eip8282.Audit.Step.exit_validJumps_eq_D_J
#print axioms Eip8282.Audit.Step.depositInit_validJumps_eq_D_J
#print axioms Eip8282.Audit.Step.exitInit_validJumps_eq_D_J
#print axioms Eip8282.Audit.Step.validJumps_are_Xi_tables

-- Reachability closure: packed-storage layer only, no `Ξ`, no receipts.
#print axioms Eip8282.Audit.Reachable.ctorStorage_wellFormed
#print axioms Eip8282.Audit.Reachable.ctorStorage_toModel
#print axioms Eip8282.Audit.Reachable.ctorStorage_reachable
#print axioms Eip8282.Audit.Reachable.ctorStorage_reachableStorage
#print axioms Eip8282.Audit.Reachable.applyUser_wellFormed
#print axioms Eip8282.Audit.Reachable.applySystem_wellFormed
#print axioms Eip8282.Audit.Reachable.queueOf_applyUser
#print axioms Eip8282.Audit.Reachable.queueOf_applySystem
#print axioms Eip8282.Audit.Reachable.toModel_applyUser_eq_userCall
#print axioms Eip8282.Audit.Reachable.toModel_applySystem
#print axioms Eip8282.Audit.Reachable.ReachableStorage.wellFormed
#print axioms Eip8282.Audit.Reachable.ReachableStorage.model_reachable
#print axioms Eip8282.Audit.Reachable.ReachableStorage.callHyp

#print axioms Eip8282.Audit.Guarantees.PSubmit1.revert_is_atomic
#print axioms Eip8282.Audit.Guarantees.PSubmit1.success_count_and_balance
#print axioms Eip8282.Audit.Guarantees.PSubmit1.deposit_appends_calldata
#print axioms Eip8282.Audit.Guarantees.PSubmit1.exit_binds_caller
#print axioms Eip8282.Audit.Guarantees.PSubmit1.inhibited_blocks_users
#print axioms Eip8282.Audit.Guarantees.PSubmit1.psubmit1_kill_line_opcodes
#print axioms Eip8282.Audit.Guarantees.PSubmit1.Revert.deposit_underpay_reverts_before_writes
#print axioms Eip8282.Audit.Guarantees.PSubmit1.Append.deposit_handle_input_append
#print axioms Eip8282.Audit.Guarantees.PSubmit1.Fee.fee_getter_readonly
#print axioms Eip8282.Audit.Guarantees.PSubmit1.FakeExpo.s4_algebraic_forall
#print axioms Eip8282.Audit.Guarantees.PSubmit1.psubmit1_forall_parent
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
#print axioms Eip8282.Audit.Guarantees.PDrain1.pdrain1_kill_line_opcodes
#print axioms Eip8282.Audit.Guarantees.PDrain1.pdrain1_d1_footprint_forall
#print axioms Eip8282.Audit.Guarantees.PDrain1.pdrain1_d2_fifo_forall
#print axioms Eip8282.Audit.Guarantees.PDrain1.pdrain1_d3_encode_forall
#print axioms Eip8282.Audit.Guarantees.PDrain1.pdrain1_forall_parent
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
#print axioms Eip8282.Audit.Guarantees.PControl1.pcontrol1_kill_line_opcodes
#print axioms Eip8282.Audit.Guarantees.PControl1.pcontrol1_c1_gate_forall
#print axioms Eip8282.Audit.Guarantees.PControl1.pcontrol1_c2_excess_forall
#print axioms Eip8282.Audit.Guarantees.PControl1.pcontrol1_c3_count_forall
#print axioms Eip8282.Audit.Guarantees.PControl1.pcontrol1_c4_ctor_forall
#print axioms Eip8282.Audit.Guarantees.PControl1.pcontrol1_forall_parent
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

-- R4: unconditional `X` → `Ξ` layer. Three foundational axioms only.
#print axioms Eip8282.Audit.XiTransport.observe_Xi_eq_observe_X
#print axioms Eip8282.Audit.XiTransport.observe_Xi_zero
#print axioms Eip8282.Audit.XiTransport.Xi_validJumps_eq
#print axioms Eip8282.Audit.XiTransport.XiCall.observe_result
#print axioms Eip8282.Audit.XiTransport.observe_result_success
#print axioms Eip8282.Audit.XiTransport.observe_result_revert
-- R4: conditional on `EndpointAgrees` (the named OPEN `A-ABSTRACT-TX`).
#print axioms Eip8282.Audit.XiTransport.xiTransport
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_inhibited_reverts
#print axioms Eip8282.Audit.XiTransport.pdrain1_xi_returns_fifo_prefix
#print axioms Eip8282.Audit.XiTransport.pcontrol1_xi_fee_getter
-- R4: registered parents carried verbatim (inherit their trace receipts).
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_forall_parent
#print axioms Eip8282.Audit.XiTransport.pdrain1_xi_forall_parent
#print axioms Eip8282.Audit.XiTransport.pcontrol1_xi_forall_parent
#print axioms Eip8282.Audit.XiTransport.registered_parents_at_Xi
