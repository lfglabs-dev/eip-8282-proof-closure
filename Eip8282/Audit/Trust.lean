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
complete `Ξ` message call. Its unconditional facts must report only the
three foundational axioms — **no `native_decide` receipt**:

* `observe_Xi_eq_observe_X` — `Ξ` and the `X` run it delegates to have the
  same observation. `Ξ` re-wraps the success payload and passes `.revert`
  through, so neither the status flag nor the return bytes move.
* `Xi_validJumps_eq` — the table `Ξ` computes for itself from the pinned
  code is `depositJumpdests` / `exitJumpdests`, via the kernel `D_J`
  bridges above.
* `observe_result_exit` — the complete `Ξ` call observes exactly the
  halting instruction the code run exits on. No premise at all.
* `exit_op_cases` / `out_eq_H_return` / `bytes_eq_nil_of_silent` — read
  off EVMYulLean's `H`: the exit opcode is one of four, `RETURN`/`REVERT`
  publish the requested memory slice, and `STOP`/`SELFDESTRUCT` publish
  nothing.
* `exit_halting` / `exit_H` — the `H ... = some out` side condition is
  *derived from the run*, not assumed: `RunUntil.stop_of_rem_pos` says a
  block that stopped with fuel left stopped at a halting opcode, and
  `H_eq_none_iff` says `H` is `some` there. So `out` is neither
  quantified nor supplied; it is `haltData post.toMachineState op`.
* `xiExitTransport` — the facts above bundled as the `∀` conjunct each
  registered parent now carries. It has **no hypothesis beyond the run**.

**What is still assumed.** `xiTransport` and the three per-parent Ξ
statements (`psubmit1_xi_inhibited_reverts`, `pdrain1_xi_returns_fifo_prefix`,
`pcontrol1_xi_fee_getter`) remain **conditional**. Two restatements have
happened and they differ in kind:

* `EndpointAgrees` → `ExitAgrees` is at *equal strength*;
  `endpointAgrees_iff_exitAgrees` proves the equivalence.
* dropping the `H ... = some out` premise and the bound `out` *strictly
  reduces* what a caller must supply, because `exit_H` proves it.

Neither discharges anything. `ExitAgrees` is the same named OPEN
`A-ABSTRACT-TX`, taken as a hypothesis and never proved.

What did change is the *surface* that hypothesis still has to cover, and
those reductions are theorems rather than claims:

* `exitAgrees_of_silent` closes the `STOP` / `SELFDESTRUCT` branches.
* `pcontrol1_xi_exit_is_RETURN` pins P-CONTROL-1's exit opcode to `RETURN`
  (the fee quote is 32 bytes, so the silent halts are refuted and the
  success status rules out `REVERT`).
* `pdrain1_xi_exit_publishes` rules out the silent halts for P-DRAIN-1
  whenever the FIFO window is non-empty.
* `psubmit1_exitAgrees_iff` shows P-SUBMIT-1's residual is exactly the two
  EVM-side facts `op = .REVERT ∧ bytes out = []`, with no `Model` in it.
* `bytes_toByteArray` and `bytes_readWithPadding_of_step_MSTORE` close the
  *byte-content* half for a single store. Spending EVMYulLean PR #9's
  opcode-path lemmas — the private `toBytes'` is never unfolded — the bytes a
  `RETURN` publishes out of memory that a real `MSTORE` opcode wrote are proved
  to be the model's big-endian encoding of the stored word.
  `endpointAgrees_of_mstore_return_zero` states that as `EndpointAgrees` in
  *conclusion* position for the `MSTORE(0, v); RETURN(0, 32)` fragment, which is
  the first place in this campaign where `EndpointAgrees` is proved rather than
  assumed or restated. `pcontrol1_xi_fee_getter_of_mstore` carries it to
  P-CONTROL-1's complete-`Ξ` observation, replacing thirty-two assumed byte
  equations with the single scalar `v.toNat = currentFee model`.

That last item **reduces** P-CONTROL-1's share of the assumption; it does not
discharge `A-ABSTRACT-TX`. The fragment lemma is universally quantified over its
starting state, so it says nothing about whether the pinned fee getter reaches
that `MSTORE` / `RETURN` pair — its `hmstore` / `hframe` / `hval` hypotheses
assert precisely that it does. P-DRAIN-1's non-empty window is not covered at
all: that window is written by a queue-dependent loop of stores, and the #9
opcode-path API covers a single store.

A green build of this module is therefore still **not** evidence that
`A-ABSTRACT-TX` holds. No closed `∀` endpoint theorem is claimed, and no
run of the pinned bytecode is proved to reach any particular opcode.

The `step` inversion this file used to list as the next lemma owed is no
longer outstanding. `EvmYul.EVM.Proof` still ships none at the pinned
revision, so it is proved here instead: `step_REVERT_H_return` /
`step_RETURN_H_return` and `haltData_eq_memory_slice` give
`haltData post.toMachineState op = mid.memory.readWithPadding μ₀.toNat μ₁.toNat`
from the exit's own stack operands. That moved the residual off an opaque
post-state field and onto a slice of pre-step memory; it discharged
nothing.

What is owed next is the other half: nothing yet connects a `Ξ` run of a
pinned runtime *to* those operands. `psubmit1_xi_inhibited_reverts_of_zero_length`
still takes `op = .REVERT` and `μ₁.toNat = 0` as hypotheses, and the width
equalities below are likewise implications. Proving those antecedents for
the pinned images — not restating the residual again — is what would bear
on `A-ABSTRACT-TX`.

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

-- R4 exit layer: unconditional, no receipts.
#print axioms Eip8282.Audit.XiTransport.observe_result_exit
#print axioms Eip8282.Audit.XiTransport.exit_op_cases
#print axioms Eip8282.Audit.XiTransport.out_eq_H_return
#print axioms Eip8282.Audit.XiTransport.bytes_eq_nil_of_silent
#print axioms Eip8282.Audit.XiTransport.exitObservation_of_silent
-- The `H` side condition is derived from the run, not assumed.
#print axioms Eip8282.Audit.XiTransport.H_eq_haltData
#print axioms Eip8282.Audit.XiTransport.exit_halting
#print axioms Eip8282.Audit.XiTransport.exit_H
#print axioms Eip8282.Audit.XiTransport.observe_result_of_run
#print axioms Eip8282.Audit.XiTransport.exit_op_cases_of_run
#print axioms Eip8282.Audit.XiTransport.xiExitTransport
-- Inverting EVMYulLean's `step` at the publishing halts: the bytes a call
-- publishes are the memory slice the exit's own stack operands select.
#print axioms Eip8282.Audit.XiTransport.zeroes_zero
#print axioms Eip8282.Audit.XiTransport.readWithPadding_size_zero
#print axioms Eip8282.Audit.XiTransport.bytes_readWithPadding_zero
#print axioms Eip8282.Audit.XiTransport.not_stepOk_zero
#print axioms Eip8282.Audit.XiTransport.step_REVERT_delegates
#print axioms Eip8282.Audit.XiTransport.step_RETURN_delegates
#print axioms Eip8282.Audit.XiTransport.sharedStep_REVERT
#print axioms Eip8282.Audit.XiTransport.sharedStep_RETURN
#print axioms Eip8282.Audit.XiTransport.evmRevert_H_return
#print axioms Eip8282.Audit.XiTransport.evmReturn_H_return
#print axioms Eip8282.Audit.XiTransport.step_REVERT_H_return
#print axioms Eip8282.Audit.XiTransport.step_RETURN_H_return
#print axioms Eip8282.Audit.XiTransport.haltData_eq_memory_slice
#print axioms Eip8282.Audit.XiTransport.bytes_haltData_eq_nil_of_zero_length
#print axioms Eip8282.Audit.XiTransport.xiSliceTransport

-- R4 width layer: how *much* a publishing halt emits is the exit's own length
-- operand, whatever memory holds. `readWithPadding` zero-pads up to the
-- requested length, so these are theorems about the machine, not assumptions.
-- Unconditional beyond the run -- none of them may report a `native_decide`
-- receipt, and none may report a project `axiom`.
#print axioms Eip8282.Audit.XiTransport.bytes_length
#print axioms Eip8282.Audit.XiTransport.size_zeroes
#print axioms Eip8282.Audit.XiTransport.natCast_sub_bitvec
#print axioms Eip8282.Audit.XiTransport.toNat_natCast_sub
#print axioms Eip8282.Audit.XiTransport.size_readWithoutPadding_le
#print axioms Eip8282.Audit.XiTransport.size_readWithPadding_le
#print axioms Eip8282.Audit.XiTransport.size_readWithPadding
#print axioms Eip8282.Audit.XiTransport.size_readWithPadding_of_lt_two_pow_32
#print axioms Eip8282.Audit.XiTransport.length_bytes_haltData_le
#print axioms Eip8282.Audit.XiTransport.length_bytes_haltData
-- The residual read on the return-data component alone, and the length operand
-- it therefore pins. The `≤` directions are unconditional; the exact-width
-- equalities carry `μ₁.toNat < USize.size` because `readWithPadding` truncates
-- its pad count through a machine word.
#print axioms Eip8282.Audit.XiTransport.exitAgrees_returnData
#print axioms Eip8282.Audit.XiTransport.exitAgrees_length_operand_le
#print axioms Eip8282.Audit.XiTransport.exitAgrees_length_operand
#print axioms Eip8282.Audit.XiTransport.XiWidthTransport
#print axioms Eip8282.Audit.XiTransport.xiWidthTransport
-- Per parent: P-SUBMIT-1's residual becomes `op = .REVERT ∧ μ₁.toNat = 0`, with
-- no `ByteArray` left in it; P-DRAIN-1's length operand is pinned to the width
-- of the drained FIFO window; P-CONTROL-1's is sharpened from non-zero to
-- exactly 32. All three still take the residual `ExitAgrees` as a *premise* —
-- they say what the pinned runtime's exit machine must look like **if**
-- `A-ABSTRACT-TX` holds. That narrows its surface to *which* bytes are
-- published; it does not close it, and `A-ABSTRACT-TX` stays OPEN at HIGH.
#print axioms Eip8282.Audit.XiTransport.psubmit1_exitAgrees_iff_operand
#print axioms Eip8282.Audit.XiTransport.pdrain1_returnData
#print axioms Eip8282.Audit.XiTransport.pdrain1_xi_exit_length_ge
#print axioms Eip8282.Audit.XiTransport.pdrain1_xi_exit_length_eq
#print axioms Eip8282.Audit.XiTransport.pcontrol1_returnData_length
#print axioms Eip8282.Audit.XiTransport.pcontrol1_xi_exit_length_ge_32
#print axioms Eip8282.Audit.XiTransport.pcontrol1_xi_exit_length_eq_32

-- The residual is equivalent to the old premise, and its reductions.
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_iff_exitAgrees
#print axioms Eip8282.Audit.XiTransport.exitAgrees_of_silent
#print axioms Eip8282.Audit.XiTransport.exit_op_publishes_of_returnData_ne_nil
#print axioms Eip8282.Audit.XiTransport.psubmit1_exitAgrees_iff
#print axioms Eip8282.Audit.XiTransport.pdrain1_xi_exit_publishes
#print axioms Eip8282.Audit.XiTransport.pcontrol1_xi_exit_is_RETURN
#print axioms Eip8282.Audit.XiTransport.exitAgrees_iff_memory_slice
#print axioms Eip8282.Audit.XiTransport.exitAgrees_of_zero_length
#print axioms Eip8282.Audit.XiTransport.pcontrol1_xi_exit_length_ne_zero
-- P-DRAIN-1's residual in closed form, and the `REVERT` branch refuted.
-- `Model.systemCall` has no `revert` constructor, so `pdrain1_xi_exit_not_REVERT`
-- takes no hypothesis about the window, the kind or the run: one of `H`'s four
-- exit branches is *discharged* for this parent rather than assumed, and on a
-- non-empty window `pdrain1_xi_exit_is_RETURN` leaves exactly one.
#print axioms Eip8282.Audit.XiTransport.pdrain1_exitAgrees_iff
#print axioms Eip8282.Audit.XiTransport.pdrain1_xi_exit_not_REVERT
#print axioms Eip8282.Audit.XiTransport.pdrain1_xi_exit_is_RETURN
-- The residual discharged for P-SUBMIT-1: no `ExitAgrees` premise remains.
#print axioms Eip8282.Audit.XiTransport.psubmit1_exitAgrees_of_zero_length
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_inhibited_reverts_of_zero_length
-- ... and for P-DRAIN-1's empty-window branch: these *produce* `ExitAgrees`
-- instead of consuming it, so `pdrain1_xi_empty_window_returns_nothing` is a
-- complete-`Ξ` observation that does not rest on `A-ABSTRACT-TX` at all.
#print axioms Eip8282.Audit.XiTransport.pdrain1_exitAgrees_of_silent
#print axioms Eip8282.Audit.XiTransport.pdrain1_exitAgrees_of_zero_length
#print axioms Eip8282.Audit.XiTransport.pdrain1_xi_empty_window_returns_nothing
-- ... and for P-SUBMIT-1's *accepting* path. `Model.userCall` answers an
-- admissible non-empty submission with `.success _ []`, so the residual is the
-- same shape as P-DRAIN-1's empty window and is produced, not consumed:
-- `psubmit1_xi_accepted_returns_nothing` carries no `ExitAgrees` premise. Both
-- halves of P-SUBMIT-1's user call — refusal and acceptance — are now off the
-- assumption.
#print axioms Eip8282.Audit.XiTransport.psubmit1_exitAgrees_iff_accepted
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_accepted_exit_not_REVERT
#print axioms Eip8282.Audit.XiTransport.psubmit1_exitAgrees_of_silent_accepted
#print axioms Eip8282.Audit.XiTransport.psubmit1_exitAgrees_of_zero_length_accepted
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_accepted_returns_nothing
-- ... and for P-CONTROL-1. `pcontrol1_exitAgrees_iff` states the fee getter's
-- residual in closed form with no `Outcome` in it, so
-- `pcontrol1_xi_exit_not_REVERT` needs no `H` side condition. The fee getter is
-- not payable: an empty-calldata call carrying value is refused before the quote
-- is computed, and `pcontrol1_xi_paid_fee_getter_reverts_of_zero_length` observes
-- that at complete `Ξ` with no `ExitAgrees` premise.
#print axioms Eip8282.Audit.XiTransport.pcontrol1_exitAgrees_iff
#print axioms Eip8282.Audit.XiTransport.pcontrol1_xi_exit_not_REVERT
#print axioms Eip8282.Audit.XiTransport.pcontrol1_exitAgrees_iff_paid
#print axioms Eip8282.Audit.XiTransport.pcontrol1_xi_paid_exit_is_REVERT
#print axioms Eip8282.Audit.XiTransport.pcontrol1_exitAgrees_of_zero_length_paid
#print axioms Eip8282.Audit.XiTransport.pcontrol1_xi_paid_fee_getter_reverts_of_zero_length
-- R4: byte-content half, from EVMYulLean PR #9's opcode-path lemmas. These are
-- unconditional in the byte equation and must show no `native_decide` receipt;
-- `endpointAgrees_of_mstore_return_zero` is `EndpointAgrees` in *conclusion*
-- position for the `MSTORE(0, v); RETURN(0, 32)` fragment. They reduce, and do
-- not discharge, `A-ABSTRACT-TX`: reaching that fragment is still assumed.
#print axioms Eip8282.Audit.XiTransport.getElem_toLeBytes
#print axioms Eip8282.Audit.XiTransport.toBeBytes_eq_map_range
#print axioms Eip8282.Audit.XiTransport.bytes_toByteArray
#print axioms Eip8282.Audit.XiTransport.bytes_readWithPadding_of_step_MSTORE
#print axioms Eip8282.Audit.XiTransport.bytes_readWithPadding_of_step_MSTORE_zero
#print axioms Eip8282.Audit.XiTransport.memory_step_Push
#print axioms Eip8282.Audit.XiTransport.memory_Runs_Push
#print axioms Eip8282.Audit.XiTransport.bytes_readWithPadding_of_mstore_pushes_zero
#print axioms Eip8282.Audit.XiTransport.bytes_H_return_of_mstore_return_zero
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_of_mstore_return_zero
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_of_mstore_pushes_return_zero
#print axioms Eip8282.Audit.XiTransport.pcontrol1_xi_fee_getter_of_mstore
#print axioms Eip8282.Audit.XiTransport.pcontrol1_xi_fee_getter_of_mstore_zero
#print axioms Eip8282.Audit.XiTransport.pcontrol1_xi_fee_getter_of_mstore_pushes
-- R4: conditional on `EndpointAgrees` (the named OPEN `A-ABSTRACT-TX`).
#print axioms Eip8282.Audit.XiTransport.xiTransport
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_inhibited_reverts
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_inhibited_reverts_of_exit
#print axioms Eip8282.Audit.XiTransport.pdrain1_xi_returns_fifo_prefix
#print axioms Eip8282.Audit.XiTransport.pcontrol1_xi_fee_getter
-- R4: registered parents carried verbatim (inherit their trace receipts).
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_forall_parent
#print axioms Eip8282.Audit.XiTransport.pdrain1_xi_forall_parent
#print axioms Eip8282.Audit.XiTransport.pcontrol1_xi_forall_parent
#print axioms Eip8282.Audit.XiTransport.registered_parents_at_Xi
