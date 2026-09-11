import Eip8282.Audit.Guarantees.PSubmit1
import Eip8282.Audit.Guarantees.PDrain1
import Eip8282.Audit.Guarantees.PControl1
import Eip8282.Audit.Represents
import Eip8282.Audit.UserXiCorrespondence
import Eip8282.Audit.SystemXiCorrespondence
import Eip8282.Audit.Step
import Eip8282.Audit.XiTransport
import Eip8282.Audit.Reachable
import Eip8282.Audit.UniversalBoundary
import Eip8282.Audit.EntryReach
import Eip8282.Audit.EntryReach.Operands
import Eip8282.Audit.EntryReach.Endpoint
import Eip8282.Audit.Integrator
import Eip8282.Tests.DirectThetaKills
import Eip8282.Tests.PSubmit1Mutant
import Eip8282.Tests.PControl1Mutant
import Eip8282.Tests.PDrain1Mutant
import Eip8282.Tests.DirectThetaMutations
import Eip8282.Tests.DirectThetaDrainMutations

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
* `memory_mstore_append` … `exitAgrees_of_mstores_return` close that same
  byte-content half for an `MSTORE` **loop of arbitrary length**, which is the
  shape a drain window takes. #9's read-over-write frame lemmas require
  `destAddr + len ≤ dest.size`, so they cannot be chained across stores that grow
  memory; a store landing at the current end of memory instead makes
  `ByteArray.write_eq_of_grows` degenerate to a plain append, so a run of such
  stores appends `concatWords vs` with no frame and no window splitting
  (`memory_AppendStores`), and a `RETURN(0, 32·n)` off an initially empty memory
  reads it back whole (`bytes_readWithPadding_of_appendStores`). Each loop step
  is a real `StepOk (.MSTORE, none)` via `step_MSTORE`, `AppendStores.runs`
  composes the chain with the existing `Runs` plumbing, and `appendStores_two`
  exhibits a concrete two-store inhabitant so the predicate is not vacuous.
  `pdrain1_xi_returns_fifo_prefix_of_mstores` carries that to P-DRAIN-1's
  complete-`Ξ` observation, replacing the whole-memory equation `hbytes` with
  `hwords`, which mentions no EVM state.
* `memory_mstore_overwrite` … `pdrain1_xi_returns_fifo_prefix_of_exitStores`
  remove `hwords` itself for the exit layout. `AppendStores` grows memory one
  whole word at a time, so it can only describe a `32·n`-byte window, and a real
  EIP-7002 exit drain does not have that shape: its records are 68 bytes, so
  every record after the first begins mid-word. `OverlapStores` allows exactly
  the store that overwrites the previous record's 32-byte overshoot
  (`memory_mstore_overwrite` makes such a store a truncate-then-append), and
  `storedBytes_exitStores` computes the resulting bytes at the 68-byte stride to
  be the model's own `concatReturned` of those records — proved, not assumed,
  via `toBeBytes_beBytes`, which inverts the model's big-endian encoder.
  `endpointAgrees_of_exitStores_return` is `EndpointAgrees` in *conclusion*
  position for that unaligned window, and
  `pdrain1_xi_returns_fifo_prefix_of_exitStores` carries it to P-DRAIN-1's
  complete-`Ξ` observation with **no `hwords` and no `hbytes`**: what remains per
  record is `ExitRecordWords.ok`, three *scalar* equations saying what number the
  runtime put in each word, and `exists_exitRecordWords` proves those are
  satisfiable for every 20-byte source and 48-byte pubkey, so the hypothesis
  constrains the runtime rather than excluding it. `overlapStores_exitRecord`
  inhabits the predicate with three real `MSTORE` opcodes at `0`, `20`, `52`.
* `overlapStores_exitStores` … `exitAgrees_of_exitRun_return` remove `hstores`
  itself. `overlapStores_exitRecord` inhabits `OverlapStores` at *one* record on
  a fresh frame, but every statement that consumes `hstores` quantifies over a
  list, so one record left open whether the predicate is reachable at the lengths
  those statements are about. `overlapStores_exitRecord_step` runs one record at
  an arbitrary base `b` whose frame is covered to within one word, and
  `overlapStores_exitStores` iterates it: for any `rs` and any such base, the
  68-byte-stride drain runs on real `MSTORE` opcodes, consumes exactly its
  operands, and re-establishes the same coverage invariant at `b + 68 * rs.length`.
  `endpointAgrees_of_exitRun_return` then states `EndpointAgrees` with that run
  *constructed* rather than hypothesised: no `hstores`, no `hbytes`, no `hwords`,
  no `ExitAgrees` / `EndpointAgrees` premise, no `native_decide`, and at every
  record count rather than one. What is still **not** proved is that the pinned
  EIP-7002 bytecode places these operands on the stack in this order; that gap is
  the whole of what `A-ABSTRACT-TX` carries, and `EndpointAgrees` stays open in
  general. The shift is that `hstores` was a claim that such a run exists; it is
  now a claim about *which* run the runtime takes.

Those items **reduce** P-CONTROL-1's and P-DRAIN-1's share of the assumption;
they do not discharge `A-ABSTRACT-TX`. The fragment lemmas are universally
quantified over their starting state, so they say nothing about whether the
pinned runtimes reach the `MSTORE` / `RETURN` shapes they describe — their
`hmstore` / `hframe` / `hval` and `hfresh` / `hstores` / `hlen` hypotheses assert
precisely that they do. `hwords` is now gone for the deposit layout too. The
deposit record is 184 bytes, and six of the seven stores in its drain loop are
plain `MSTORE`s that `OverlapStores` could express; the seventh is not.
`encodeReturned (.deposit …)` carries the amount little-endian
(`toLeBytes amount 8`) and the runtime writes it with the `%MSTORE64_le` macro, a
byte-level 8-byte splice into the middle of an already-stored word, which a
whole-word `OverlapStores` step cannot describe. `bytes_memory_mstore8` and
`bytes_memory_step_MSTORE8` supply the read-over-`MSTORE8` reasoning that was
missing, `MixedStores` admits `MSTORE` and `MSTORE8` in one loop, and
`splicedBytes_depositRecord` computes the 184-byte stride — three words, the
eight-byte little-endian splice at `+80`, three more words — to be the model's own
`encodeReturned`. `pdrain1_xi_returns_fifo_prefix_of_depositStores` carries that
to P-DRAIN-1's complete-`Ξ` observation with **no `hwords` and no `hbytes`**; what
remains per record is `DepositRecordWords.ok`, six scalar word equations and one
little-endian byte equation, and `exists_depositRecordWords` proves those
satisfiable for any 184 genuine bytes and any amount, so the hypothesis
constrains the runtime rather than excluding it. `mixedStores_depositPrefix`
inhabits the predicate with three real `MSTORE`s at `0`, `32`, `64` and the first
real `MSTORE8` of `%MSTORE64_le` at `80`. So
`pdrain1_xi_returns_fifo_prefix_of_mstores` and its `hwords` are no longer the
only statement covering the deposit path. What is still assumed there is
reachability: nothing proves the pinned runtime performs that `MixedStores` run,
and `hfresh` / `hstores` / `hlen` / `hok` assert exactly that it does.

* `memory_execBinOp` … `pdrain1_xi_returns_fifo_prefix_of_spacedExitStores`
  remove the *adjacency* hypothesis. Everything above asks for `OverlapStores` or
  `MixedStores`, both of which require the record's stores to be consecutive, and
  no pinned EIP-7002 runtime is shaped that way: `builder_exits` writes its window
  from the `accum_loop` body (PC 247, back-jump at PC 300), so between the stores
  at PC 274, 284 and 294 sit the `SLOAD` that reads the queue slot, the `ADD` /
  `MUL` / `SHL` / `EQ` that build the operands, the `DUP` / `SWAP` / `POP`
  shuffling and the `JUMPDEST` / `JUMP` / `JUMPI` that close the loop. Adjacency
  was not presentational: it is a hypothesis the pinned bytecode provably never
  satisfies, so every `EndpointAgrees`-in-conclusion statement above was
  inapplicable to the real drain. `NeutralOp` names exactly that non-`MSTORE`
  opcode set and `memory_step_neutral` proves each of them leaves `memory` alone,
  spending the four EVMYulLean opcode-family frames `memory_execBinOp`,
  `memory_dup`, `memory_swap` and `memory_unaryStateOp` — the last because
  `EvmYul.State` has no memory field at all, memory living in `MachineState`, so
  the `SLOAD` path's wholesale `toState` replacement cannot disturb it.
  `memory_Runs_neutral` closes that transitively, and `SpacedStores` then admits
  an arbitrary run between two stores under a *syntactic* condition on the gap
  trace rather than a semantic claim about the resulting state.
  `OverlapStores.spaced` embeds the old relation with empty gaps, so no statement
  proved from adjacency is lost and none of the new ones is weaker.
  `endpointAgrees_of_spacedExitStores_return` is `EndpointAgrees` in *conclusion*
  position for a loop-written window and
  `pdrain1_xi_returns_fifo_prefix_of_spacedExitStores` carries it to P-DRAIN-1's
  complete-`Ξ` observation. The residual is unchanged in kind — nothing proves the
  pinned runtime reaches those stores — but it no longer contains a claim that is
  false of the pinned runtime.

* `SpacedMixedStores.nil_neutral` …
  `pdrain1_xi_returns_fifo_prefix_of_spacedDepositStores` do the same for the
  *deposit* layout, which the previous item left behind. `SpacedStores` only
  admits `MSTORE`, so the exit window was the only one it reached; the deposit
  record needs the `%MSTORE64_le` byte splice and therefore still went through
  `MixedStores`, which was still requiring adjacency. `builder_deposits` writes
  its 184-byte records from a loop of its own, so that half of P-DRAIN-1's
  non-empty window remained stated about a store shape the pinned runtime does
  not have. `SpacedMixedStores` drops the requirement on both constructors under
  the same syntactic gap condition — `nil_neutral`, `word_neutral` and
  `byte_neutral` derive the gap's memory equation from `memory_Runs_neutral`, so
  a caller asserts nothing about intermediate states — and `MixedStores.spaced`
  embeds the adjacency relation with empty gaps, so again nothing proved from it
  is lost. `bytes_memory_SpacedMixedStores` recomputes the byte image and
  `endpointAgrees_of_spacedDepositStores_return` /
  `exitAgrees_of_spacedDepositStores_return` put `EndpointAgrees` / `ExitAgrees`
  in *conclusion* position for a loop-written deposit window. Both drain layouts
  are now in that form, and the residual on each is reachability alone.

* Those same eight spaced-window statements also drop
  `hfresh : pre.memory.size = 0`. Both windows are written at offset `0`, so the
  first store truncates whatever memory held before it;
  `storedBytes_exitStores` and `splicedBytes_depositStores` were already stated
  for an arbitrary initial byte list, and at base `0` the `acc.take 0` they
  thread is `[]` regardless. The pinned runtimes run a dispatcher before the
  drain loop, so an untouched-memory frame was — like adjacency — a shape the
  real runtime does not have. What still constrains the pre-state is
  `SpacedStores.cons`'s own `hcov`, which asks each store to land at the memory
  frontier; that is a hypothesis of the relation rather than of these theorems,
  and is the next residual on this path.

One boundary in that stride is worth naming separately, because it is assumed
rather than read. The seven stores of `depositRecordStores` and their seven
offsets are read off `pinned/sys-asm/builder_deposits/main.eas` (lines 355-430).
The expansion of `%MSTORE64_le` into eight ascending `MSTORE8`s carrying
`toLeBytes amount 8` is not: that macro lives in `../common/mstore.eas`, which
`main.eas:543` `#include`s and which this repository does not vendor. So the
little-endian splice is a hypothesis of `depositRecordStores` and of
`DepositRecordWords.ok`, never a conclusion, and a reader checking this claim
against pinned source will find the six word stores there and the macro body
absent.

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

### The `revert:` subroutine: what this revision moved, and what it did not

Both pinned runtimes end in the same four bytes, `5b 5f 5f fd` —
`JUMPDEST; PUSH0; PUSH0; REVERT`. That is the `revert:` label of `main.eas`,
the single target every refusal path jumps to. `deposit_tail_is_revert_subroutine`
and `exit_tail_is_revert_subroutine` check this against the pinned byte arrays
with `decide +kernel`; they are facts about the images, not assumptions, and
their receipts below depend on no axioms at all.

Three things follow, and are now proved.

*One.* `EvmYul.EVM.Proof.MemoryStep` ships `step_RETURN` but no `REVERT`
counterpart at the pinned revision, so `step_REVERT` is proved here through
`binaryMachineStateOp`, together with `step_PUSH0` and the two post-state
projections.

*Two.* Because the length operand `revert:` pushes is **zero**, the published
slice is empty whatever memory holds. `endpointAgrees_of_revertEpilogue`
therefore puts `EndpointAgrees` in *conclusion* position, with the three-step
run **constructed** rather than assumed and with memory, gas, substate and the
preceding trace all universally quantified. Its inhibited and rejected instances
discharge the model half from `inhibited`/`admissible` alone. This is the first
place in the campaign where `EndpointAgrees` for a refusing branch is a
conclusion and no memory hypothesis, `NeutralOp` gap condition or `MSTORE`
accounting is needed anywhere in the argument.

*Three.* `psubmit1_xi_{inhibited,rejected}_reverts_of_zeroTop` narrow the
complete-`Ξ` residual from two premises to one. Where the `_of_zero_length`
forms took an existentially shaped `pop2` on the *internal* state `mid` plus a
numeric side condition on the popped word, these take a single syntactic fact
about the *exit* state — `exit.stack = ⟨0⟩ :: ⟨0⟩ :: rest`. `Z_ok_stack`
bridges `exit` to `mid`; `zeroTop_push0_push0` shows the subroutine's two
`PUSH0`s leave exactly that stack.

**`EndpointAgrees` is nonetheless still OPEN, and `A-ABSTRACT-TX` stays OPEN at
HIGH severity.** The gap is now a single named thing rather than a family of
operand conditions, and it is worth stating precisely so that no reader
overcounts what a green build shows:

> nothing here proves that a `Ξ` run of a pinned runtime ever *reaches* the
> `revert:` `JUMPDEST` — offset 624 in the deposit image, 454 in the exit image.

Concretely, `endpointAgrees_of_revertEpilogue` quantifies over the run `tr` and
its endpoint; it never asserts that `tr` is a run of `depositRuntime` or
`exitRuntime`, and it never appeals to `decodeAt`.

*Four.* The previous revision listed two things as owed: bridging the
byte-offset facts to `decodeAt`, and proving that each `jump revert` site is
taken exactly on the abstract refusal condition. **The first is now closed.**
`deposit_revert_decodes` / `exit_revert_decodes` put the four `revert:` bytes of
each pinned image through EVMYulLean's own `decode`, `decide +kernel`, so the
claim is no longer "these bytes sit at these offsets" but "`decode` of the
pinned image at this offset *is* this instruction". `decodeAt_of_code_pc`
transports that to any state whose code is the pinned image and whose `pc` is
that offset — `decodeAt` reads exactly those two fields and nothing else.

The payoff is `op_eq_REVERT_of_atRevertByte`, and through it the two
`_at_revertByte` forms: the premise `op = .REVERT`, which the `_of_zeroTop`
forms took on trust, is now **derived**. One of the two unproved antecedents is
gone.

*Five.* **The second half is now closed as well, and the residual moves one
label earlier.** The previous revision named precisely what was missing: the
stack conjunct "needs the run to have entered the subroutine at its `JUMPDEST`
(624 / 454) and taken three steps: a forward `Z`/`XStepAt` construction plus a
`RunUntil` composition lemma, neither of which exists here." Both now exist.

`revertSubroutine_decodes` puts *all four* `revert:` bytes of each pinned image
through `decode`, `decide +kernel` — the `JUMPDEST` and the two `PUSH0`s as well
as the `REVERT`. `Z_PUSH0` and `Z_REVERT` discharge EVMYulLean's gas and
stack-bound side condition `Z` for those opcodes, and `xStepAt_PUSH0` turns the
`PUSH0` case into an `XStepAt`. `runUntil_revertSubroutine` chains the three:

> from `AtRevertJumpdest kind st` — the state's code is the pinned image and its
> `pc` is 624 (deposit) / 454 (exit) — plus `Gjumpdest + Gbase + Gbase ≤ gas` and
> two free stack slots, it *builds* a `RunUntil` of four fuel units ending in a
> state satisfying `AtRevertByte kind exit`, with
> `exit.stack = ⟨0⟩ :: ⟨0⟩ :: st.stack`.

`runUntil_of_xRuns` composes an arbitrary `XRuns` prefix onto that halting run,
and `revert_exit_of_reaches_revertJumpdest` packages the result: it *returns*
the `RunUntil`, the `decodeAt`, the `Z`, the `StepOk` and the `pop2`.

The payoff is `psubmit1_xi_{inhibited,rejected}_reverts_of_reaches_revert`,
which conclude the same `observe c.result = some { reverted := true,
returnData := [] }` as the `_at_revertByte` forms from strictly weaker premises.
**Five named hypotheses are discharged rather than restated** — `hat`, `htop`,
`hdec`, `hZ` and `hstep` — and what replaces them is one reachability premise
plus two ordinary side conditions on the run:

> `XRuns (jumpdestsOf kind) c.fuel c.entry tr (n + 5) st` together with
> `AtRevertJumpdest kind st`; `Gjumpdest + Gbase + Gbase ≤ st.gasAvailable.toNat`;
> and `st.stack.length + 2 ≤ 1024`.

The gas and stack conditions are arithmetic facts about a run, not assumptions
about what the bytecode means. `AtRevertJumpdest` does still state the code
identity over the state's own `executionEnv.code`, for the same reason
`AtRevertByte` did: nothing in this repository or in EVMYulLean at the pinned
revision proves that `step` preserves `executionEnv` across a frame, so the
identity is assumed where the subroutine is *entered* rather than inherited from
`XiCall.code_pinned`.

So the whole residual is now the single question that was always behind it:
reachability of the `revert:` `JUMPDEST`.

*Six.* **`AtRevertJumpdest` stops being a hypothesis too; the residual moves one
instruction earlier still.** Landing on a `JUMPDEST` is not something a run does
by itself — it is something a `JUMP` or `JUMPI` does to it. Ten offsets of the
pinned images are listed in `revertJumpiSites` and kernel-checked in
`revertJumpi_sites_pinned`: at each one the image really does decode a `JUMPI`,
and the `PUSH2` three bytes earlier really does carry the `revert:` offset as its
immediate — the `PUSH2 @revert; JUMPI` idiom the two `main.eas` files emit for
`jump revert`. Nothing there is `native_decide` — the sites are `decide +kernel`
facts about the pinned bytes.

That enumeration is **sound but not proved complete**. Each listed offset is
verified to be such a branch; nothing proves that no *other* offset is one. The
derivation only reads the list forwards — `AtRevertJumpi` names a listed site —
so completeness is not needed for soundness, but the ten sites must not be read
as "all the ways into `revert:`", and no ∀-over-the-image claim is made here.

`Z_JUMPI_taken` discharges EVMYulLean's own side condition for the branch (the
destination is in the campaign's jumpdest table, which `revert_mem_table`
kernel-checks) and `step_JUMPI_taken` is the taken-branch `pc` update;
`xStepAt_JUMPI_taken` chains them into one `X` iteration. The payoff is
`atRevertJumpdest_of_atRevertJumpi`:

> from `AtRevertJumpi kind st` — the state's code is the pinned image and its
> `pc` is one of the ten kernel-checked sites — plus a nonzero branch condition,
> `Ghigh ≤ gas` and a stack bound, one `X` iteration *lands* on the `revert:`
> `JUMPDEST`, so `AtRevertJumpdest` comes out as a conclusion.

`revert_exit_of_reaches_revertJumpi` and the two `_of_reaches_revertJumpi` branch
forms reach the same `observe c.result = some { reverted := true, returnData :=
[] }` as the `_of_reaches_revert` forms, with `AtRevertJumpdest` discharged
rather than assumed.

What remains is unchanged in kind and named the same way:

> **still OPEN:** nothing proves that a `Ξ` run of a pinned runtime *reaches* one
> of the ten `PUSH2 @revert; JUMPI` sites, nor that a site's branch is taken
> exactly on the abstract refusal condition. No `XRuns` prefix landing in
> `AtRevertJumpi` is constructed for either image; the `XRuns` premise, the
> taken-branch condition, and the ordinary gas and stack side conditions are what
> is left.

That is still one hypothesis about *control flow*, now one instruction further
back in the CFG than the previous revision's. `EndpointAgrees` is still OPEN and
`A-ABSTRACT-TX` stays OPEN at HIGH severity: a green build of this module is
still not evidence that it holds, and finitely many pinned sites are not a
universal ∀ correspondence.

*Seven.* **The branch operand stops being a hypothesis; the residual moves one
instruction earlier again.** `revert_exit_of_reaches_revertJumpi` still took two
things on trust about the state it started from: that the `pc` was a listed
`JUMPI` site, and that the `revert:` offset was *already* the top of the stack.
The second was never a fact about a run — the operand is put there by the
`PUSH2` three bytes earlier, and `revertJumpi_sites_pinned` already
kernel-checks that that `PUSH2` carries the `revert:` offset as its immediate.

`Z_PUSH2` discharges EVMYulLean's gas and stack-bound side condition for the
push, `step_PUSH2` is the `pc` update — the `pc` advances by `argWidth.succ`,
which is exactly the three bytes that land the run on the `JUMPI` — and
`xStepAt_PUSH2` chains them into one `X` iteration. The payoff is
`atRevertJumpi_of_atRevertPush`:

> from `AtRevertPush kind st` — the state's code is the pinned image and its
> `pc` is three before one of the same ten kernel-checked sites — plus
> `Gverylow ≤ gas` and one free stack slot, one `X` iteration *lands* on the
> `JUMPI` site with the pinned `revert:` offset pushed. `AtRevertJumpi` and the
> destination-operand equation both come out as conclusions.

`revert_exit_of_reaches_revertPush` and the two `_of_reaches_revertPush` branch
forms reach the same observation with *one hypothesis fewer than before*: the
stack premise is now `st.stack = cond :: rest`, naming only the branch
condition, where the previous revision also had to be handed the destination
word. No gas or stack bound is strengthened beyond the one extra `Gverylow`.

The ten sites are read forwards exactly as before, so the soundness caveat on
`revertJumpiSites` is unchanged and no completeness claim is added:

> **still OPEN:** nothing proves that a `Ξ` run of a pinned runtime *reaches*
> one of the ten `PUSH2 @revert` sites, nor that the branch three bytes on is
> taken exactly on the abstract refusal condition. No `XRuns` prefix landing in
> `AtRevertPush` is constructed for either image; the `XRuns` premise, the
> taken-branch condition, and the ordinary gas and stack side conditions are
> what is left.

`EndpointAgrees` is still OPEN and `A-ABSTRACT-TX` stays OPEN at HIGH severity
for the same reason as before. What changed is only that one more premise which
was an *assumption about the pinned bytes* became a consequence of them.

*Eight.* **The branch is an `iff`, and the chain is now on the registered
parent.** Two things were wrong with the state the previous revisions left.

The first is a gap in the reasoning. Everything from *Four* through *Seven*
walks the **taken** branch: given a nonzero condition word at one of the ten
sites, the run lands on `revert:`. On its own that says nothing about what
happens when the condition is zero, so nothing ruled out the ten sites drifting
into `revert:` regardless — which is the shape of doubt the residual is
supposed to be about. `Z_JUMPI_untaken` closes that half. EVMYulLean conditions
its `BadJumpDestination` guard on the second stack word being nonzero, so the
untaken step needs **no** `validJumps` premise at all; `step_JUMPI_untaken`
advances the `pc` by one rather than jumping, and
`succ_revertJumpiSite_ne_revertPc` settles over the literals that one byte past
a site is not the label — the ten sites are all below offset 205 while `revert:`
sits at 624 and 454. The payoff is
`not_atRevertJumpdest_of_atRevertJumpi_untaken`, and
`atRevertJumpdest_iff_cond_ne_zero` states it with the taken direction:

> from a pinned `JUMPI @revert` site, the run reaches the `revert:` `JUMPDEST`
> **exactly** when the condition word is nonzero, and provably does not
> otherwise.

The second was a registration gap, and it is the more serious of the two.
`psubmit1_xi_forall_parent` was declared *before* the `revert:` sections in the
module, so it could not mention them: none of *Four* through *Seven* was a
conjunct of the registered parent. The work existed in `XiTransport` but nothing
reachable from the P-SUBMIT-1 guarantee ID asserted it. The three parents now
sit after those sections, and `psubmit1_xi_forall_parent` carries the chain as
named conjuncts — `endpointAgrees_of_revertEpilogue` and its two branch
instances, `decodeAt_of_code_pc`, `revertSubroutine_decodes`,
`revert_exit_of_reaches_revertJumpdest`, `revertJumpi_sites_pinned`,
`atRevertJumpdest_of_atRevertJumpi`, `atRevertJumpi_of_atRevertPush`, the three
`revert_exit_of_reaches_*` forms with their inhibited and rejected branch
instances, the two fall-through results, and the nonpayable-guard chain of
*Eight* (`valueGuard_pinned`, `atRevertPush_of_atValueGuard`,
`revert_exit_of_reaches_valueGuard`, `psubmit1_exitAgrees_iff_paidGetter`,
`psubmit1_xi_paidGetter_reverts_of_reaches_valueGuard`,
`endpointAgrees_of_revertEpilogue_paidGetter`), and the size-guard chain of
*Nine* (`sizeGuard_pinned`, `atRevertPush_of_atSizeGuard`,
`revert_exit_of_reaches_sizeGuard`, `succ_sizeGuardJumpi_eq_valueGuardPc`,
`atValueGuard_of_atSizeGuard`, `calldata_size_eq_zero_of_bytes_nil`,
`psubmit1_xi_paidGetter_reverts_of_reaches_sizeGuard`), and the fee-comparison
chain of *Ten* (`feeGuard_pinned`, `atRevertPush_of_atFeeGuard`,
`revert_exit_of_reaches_feeGuard`, `admissible_eq_false_of_lt_requiredWei`,
`lt_bne_zero_of_toNat_lt`,
`psubmit1_xi_rejected_reverts_of_reaches_feeGuard`), and the inhibitor chain of
*Eleven* (`inhibitGuard_pinned`, `atRevertPush_of_atInhibitGuard`,
`revert_exit_of_reaches_inhibitGuard`,
`inhibited_iff_storedExcess_eq_inhibitor`, `eq_bne_zero_of_toNat_eq`,
`eq_inhibitor_bne_zero_of_inhibited`,
`psubmit1_xi_inhibited_reverts_of_reaches_inhibitGuard`), and the excess-load
chain of *Twelve* (`excessLoad_pinned`, `sloadCost_le`, `xStepAt_SLOAD`,
`xStepAt_DUP1`, `sload_excess_of_represents`,
`atInhibitGuard_of_atExcessLoad`,
`psubmit1_xi_inhibited_reverts_of_reaches_excessLoad`). Only the ordering and
the conjunct list changed; no statement was weakened or restated, and the final
`type_of%` conjunct is still `psubmit1_forall_parent` itself.

## Eight: one branch condition, tied to `Iᵥ`

Through *Seven* the condition word at the ten sites is opaque. The bytecode
refuses when it is nonzero, the model refuses under its own conditions, and
nothing said they were the same number — that was half of the residual.

At deposit `pc = 148` and exit `pc = 147` the instruction feeding the
`PUSH2 @revert; JUMPI` pair is `CALLVALUE`, so at *that* site the word is not
opaque: it is `Iᵥ`, read from the execution environment.  `valueGuard_pinned`
settles both facts over the literals with `decide +kernel` — the opcode is
`CALLVALUE`, and `pc + 4` is one of the sites already pinned by
`revertJumpi_sites_pinned` — so this conjunct carries no `native_decide`
receipt.  `Z_CALLVALUE` / `step_CALLVALUE` / `xStepAt_CALLVALUE` supply the
step, and `stack_callvaluePost` is the equation that matters: the word pushed
*is* `Iᵥ`.  `atRevertPush_of_atValueGuard` walks the guard into *Seven*'s
`AtRevertPush`, and `revert_exit_of_reaches_valueGuard` carries it to the
`REVERT` exit with empty return data.

On the abstract side, `Model.userCall` on empty calldata reverts exactly when
`value ≠ 0`; `psubmit1_exitAgrees_iff_paidGetter` turns `ExitAgrees` into
precisely "the exit op is `REVERT` and its data is empty" for that clause.
`psubmit1_xi_paidGetter_reverts_of_reaches_valueGuard` composes the two through
`xiTransport`:

> a run reaching the nonpayable guard with nonzero `Iᵥ` produces the observation
> the model produces for `.user caller [] value`, where `value` **is** `Iᵥ.toNat`
> — not an assumption relating two unknowns, but the definition of one in terms
> of the other.

`endpointAgrees_of_revertEpilogue_paidGetter` states the same clause with
`EndpointAgrees` in conclusion position.

What *Eight* does not do is construct the run that reaches the guard: through
*Eight*, `AtValueGuard` is a hypothesis, and no `XRuns` prefix reaching any of
the ten sites exists anywhere in the module.

## Nine: the dispatch size guard, `|I_d|`, and the first constructed prefix

*Nine* attacks that residual one instruction earlier. At deposit `pc = 143` and
exit `pc = 142` the images run a second guard whose `PUSH2 @revert; JUMPI` pair
at `pc = 147` / `pc = 146` is two more of the ten already-pinned sites, and
whose instruction is `CALLDATASIZE`. `sizeGuard_pinned` settles all three facts
over the literals — the opcode, the site membership, and
`sizeGuardPc + 5 = valueGuardPc` — with `decide +kernel` and `decide`, so it
carries no `native_decide` receipt. `Z_CALLDATASIZE` / `step_CALLDATASIZE` /
`xStepAt_CALLDATASIZE` supply the step and `stack_calldatasizePost` is the
equation that matters: the word pushed *is* `|I_d|`. That is the **second** of
the ten sites whose condition word is no longer opaque.

`revert_exit_of_reaches_sizeGuard` is the taken branch — nonempty calldata at
the size guard halts at `REVERT` with empty data, the same shape as
`revert_exit_of_reaches_valueGuard` one guard earlier.

`atValueGuard_of_atSizeGuard` is the fall-through, and it is what changes the
residual:

> with `|I_d| = 0` the branch is not taken, and three `X` iterations —
> `CALLDATASIZE`, `PUSH2 @revert`, untaken `JUMPI` — are **constructed** into an
> `XRuns` landing exactly on the nonpayable guard, with the stack, the code and
> `Iᵥ` carried through unchanged and the gas fully accounted. `AtValueGuard`
> stops being a hypothesis of *Eight* and becomes a conclusion.

That run passes through `AtRevertPush` and `AtRevertJumpi` on the way, so the
"no `XRuns` prefix landing in `AtRevertPush` / `AtRevertJumpi` is constructed
for either image" clauses recorded under *Six* and *Seven* above are superseded
as of *Nine*: such a prefix now exists, starting at the size guard. What has not
been constructed is a prefix from `c.entry`.

`psubmit1_xi_paidGetter_reverts_of_reaches_sizeGuard` composes the two guards
through `xiTransport`: a run reaching the **size** guard with `bytes I_d = []`
and nonzero `Iᵥ` produces the observation the model produces for
`.user caller [] value`. Both branch conditions are now read from the execution
environment rather than assumed — `bytes I_d` *is* the model's calldata argument
(`calldata_size_eq_zero_of_bytes_nil` is the length-preservation step) and
`Iᵥ.toNat` *is* its `value`.

What is still open after *Nine* is one step further back:

> **still OPEN:** reaching the *size* guard is itself a hypothesis. The dispatch
> prefix from the entry `pc` to deposit `pc = 143` / exit `pc = 142` is not
> constructed for either image, so no `XRuns` from `c.entry` to a pinned site
> exists end to end. *Nine* identifies the condition word at **two** of the ten
> sites (`Iᵥ`, `|I_d|`); the other eight still branch on words nothing has
> identified. The two identified conditions cover the empty-calldata fee-getter
> clause of `userCall` only — the deposit and exit submission clauses,
> `depositWellFormed` / `exitWellFormed` and the fee comparison, are untouched.

## Ten: the fee comparison, and the rejected branch of `userCall`

*Eight* and *Nine* both walk the **fee-getter** path — the empty-calldata call
that reads the current fee. The clause `Model.userCall` calls *rejection*, where
the dispatcher accepts the calldata length but `admissible model calldata value`
is false, was the largest untouched piece of P-SUBMIT-1's bytecode side, and it
is what the last line of *Nine*'s residual names.

*Ten* closes the value half of it. At deposit `pc = 161` and exit `pc = 159` the
images run `CALLVALUE; LT; PUSH2 @revert; JUMPI`, whose `JUMPI` at deposit 166 /
exit 164 is a third pair of the ten already-pinned sites. `feeGuard_pinned`
settles the opcode at `pc`, the opcode at `pc + 1` and the membership of
`pc + 5` over the literals with `decide +kernel` and `decide`, so it carries no
`native_decide` receipt.

This is the first of the ten sites whose condition word is a **computed
comparison** rather than a word lifted straight off the execution environment.
`Z_LT` / `step_LT` / `xStepAt_LT` supply the step, and `stack_ltPost` is the
equation that matters: what `LT` leaves on the stack is `UInt256.lt Iᵥ req`.
`atRevertPush_of_atFeeGuard` constructs two `X` iterations from the guard onto
the pinned `PUSH2 @revert`, so the branch condition arrives there *computed from
the wei actually attached to the call* rather than assumed. That is the second
`XRuns` prefix in the module reaching one of the ten sites, and the first on the
rejected branch.

The abstract half is `admissible_eq_false_of_lt_requiredWei`. `requiredWei` is
literally the right-hand side of the value conjunct of `Model.admissible` —
`depositAmount calldata * gwei + currentFee` in the deposit image, `currentFee`
in the exit image — so underpayment refutes admissibility outright, in both
images, with no well-formedness premise needed.
`psubmit1_xi_rejected_reverts_of_reaches_feeGuard` composes the two halves
through `xiTransport`, and in doing so removes three assumptions at once from
`psubmit1_xi_rejected_reverts_of_reaches_revertPush`: the pinned `PUSH2 @revert`
is reached rather than assumed, the branch condition is computed rather than
assumed, and `admissible model calldata value = false` is derived from the same
underpayment rather than taken as a bare hypothesis.

Six of the ten sites now branch on an identified word. What *Ten* does **not**
do:

> **still OPEN:** `hreq`, the equation that the word the image staged as `req`
> is `requiredWei model calldata`, is a hypothesis and not a step. That word is
> the output of the `fake_exponential` loop at offsets 100–126, which this
> module does not evaluate; until it does, *Ten* says "the image reverts when
> `Iᵥ` is below the word it staged" and only `hreq` says that word is the fee
> the model charges. Arriving at the fee guard is a hypothesis as before, no
> `XRuns` from `c.entry` exists end to end, and four sites — deposit 67, 190,
> 204 and exit 66 — still branch on words nothing has identified. The
> well-formedness half of `admissible` (`depositWellFormed` /
> `exitWellFormed`, the calldata *content* rather than its length or the value
> paid) is untouched.

## Eleven: the inhibitor guard, tied to `storedExcess`

*Ten* left four sites opaque. Two of them — deposit 67 and exit 66 — are the
same guard in the two images, and it is the one guard whose model side needs no
bridging hypothesis at all.

Both images open the user subroutine with
`SLOAD; DUP1; PUSH32 INHIBITOR; EQ; PUSH2 @revert; JUMPI`, reading the excess
slot and refusing when it holds the inhibitor sentinel. `inhibitGuard_pinned`
is `decide +kernel` / `decide` over the literals at deposit `pc = 30` and exit
`pc = 29`: the `PUSH32` whose 32-byte immediate is `INHIBITOR` itself, the `EQ`
33 bytes on, and the membership of `pc + 37` in the pinned `JUMPI @revert`
sites. `atRevertPush_of_atInhibitGuard` builds the two `X` iterations from the
guard onto that `PUSH2 @revert`, using the new `Z_PUSH32` / `step_PUSH32` and
`Z_EQ` / `step_EQ` step lemmas; `stack_eqPost` is the equation identifying the
condition word at deposit 67 / exit 66 as `UInt256.eq INHIBITOR excess`.

The abstract half is where this differs from *Ten*, and why it is worth having.
`Model.inhibited` is *defined* as `decide (storedExcess = inhibitor)` and the
`PUSH32` immediate *is* that same `inhibitor`, so
`inhibited_iff_storedExcess_eq_inhibitor` and
`eq_inhibitor_bne_zero_of_inhibited` derive the taken branch from
`inhibited model = true` directly. There is no `hreq`-shaped assumption here:
the branch condition is identified with the very hypothesis
`psubmit1_exitAgrees_iff` is stated on, rather than with a second word the
module has to assume something about.
`psubmit1_xi_inhibited_reverts_of_reaches_inhibitGuard` composes the two halves
through `xiTransport`, dropping two assumptions from
`psubmit1_xi_inhibited_reverts_of_reaches_revertPush`: the pinned
`PUSH2 @revert` is reached rather than assumed, and the branch condition is
computed rather than assumed.

Eight of the ten sites now branch on an identified word, and the first clause of
`Model.userCall` — `if inhibited s then .revert s` — is matched by bytecode the
module actually steps through.

> **still OPEN:** arriving at the inhibitor guard is a hypothesis exactly as
> arriving at the fee guard is; no `XRuns` from `c.entry` reaches any guard end
> to end. `hreq` is untouched. Two sites — deposit 190 and 204 — still branch on
> words nothing has identified, and the well-formedness half of `admissible` is
> still untouched.

`EndpointAgrees` is NOT discharged and `A-ABSTRACT-TX` stays OPEN at HIGH.

## Twelve: the excess load, so the guard's word is read rather than assumed

*Eleven* named `hexc` as its next hole: the word the inhibitor guard compares
was *assumed* to be `model.storedExcess` rather than produced by running the
instruction that loads it. *Twelve* runs it.

Three bytes before the guard both images execute `PUSH0; SLOAD; DUP1` — deposit
`27 PUSH0; 28 SLOAD; 29 DUP1`, the same one byte earlier in the exit image — and
`SLOT_EXCESS` is slot `0`, exactly what `PUSH0` pushes. `excessLoad_pinned` is
`decide +kernel` over the literals for all three opcodes *and* for
`excessLoadPc kind + 3 = inhibitGuardPc kind`, so the guard is landed on rather
than reached by an asserted offset, and no `native_decide` receipt is added.

EVMYulLean ships `X`-level lemmas for neither opcode, so `Z_SLOAD` /
`step_SLOAD` / `xStepAt_SLOAD` and the `DUP1` triple are supplied here.
`SLOAD`'s charge is the access-list-dependent `Csload`, which this module says
nothing about; it is carried symbolically as `sloadCost` and bounded above by
`sloadCost_le : sloadCost s ≤ Gcoldsload`, which is what keeps every downstream
gas hypothesis a literal whether the slot is warm or cold.

`sload_excess_of_represents` is the abstract half, and it is the reason this is
worth having: `Represents` observes the pinned account's packed storage and
`toModel` reads `storedExcess` straight off slot `0`, so the word the `SLOAD`
returns *is* `model.storedExcess` by unfolding `toModel` — no arithmetic and no
correspondence assumption stands between the machine and the model. This is the
same shape as `inhibited_iff_storedExcess_eq_inhibitor` in *Eleven*.

`atInhibitGuard_of_atExcessLoad` composes the three iterations. It is the fourth
`XRuns` prefix in the module and the first that *produces* a guard's condition
operand instead of consuming one: the `DUP1` copy underneath is what the code
past the guard reads, and the guard's own copy is the `SLOAD` result.
`psubmit1_xi_inhibited_reverts_of_reaches_excessLoad` is *Eleven*'s theorem with
`hexc` deleted. What a caller supplies in its place is `Represents` at the load
site together with `codeOwner = targetAddr kind` — the pinned code running as
the account that owns it. Neither is a claim about a word on the stack, and
neither mentions the guard.

> **still OPEN:** arriving at the load site is still a hypothesis — for this
> pair it is now four instructions of straight-line code from the entry point
> rather than seven — and `Represents` is assumed *at* the load site rather than
> transported there from `c.entry`, because no frame theorem for `XRuns` exists
> in this module. Nothing here touches the other nine `JUMPI @revert` sites, the
> two opaque ones included, nothing here touches `hreq`, and nothing here
> touches `P-DRAIN-1` or `P-CONTROL-1`.

`EndpointAgrees` is NOT discharged and `A-ABSTRACT-TX` stays OPEN at HIGH.

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
`Model.Reachable` state. Its system step carries the branch-sensitive result
bound `DrainHyp.noWrap` (`nextExcessOf kind σ b < UInt256.size`):
`nextExcessOf_lt_size_iff` reads it branch by branch — automatic on the
nonempty-calldata latch and the inhibited clear, `SLOT_EXCESS + SLOT_COUNT <
2^256 + target` on the enabled empty-calldata branch — and
`nextExcessOf_lt_size_of_sum_lt` / `drainHyp_of_sum_lt` show the former
`SLOT_EXCESS + SLOT_COUNT < 2^256` bound still supplies it, so the closure only
widened. That module never runs `Ξ`, so none of the lines
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
#print axioms Eip8282.Audit.Reachable.nextExcessOf_lt_size_iff
#print axioms Eip8282.Audit.Reachable.nextExcessOf_lt_size_of_sum_lt
#print axioms Eip8282.Audit.Reachable.drainHyp_of_sum_lt
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

/-! ## Node R1 — `Represents`

The state relation carries no `native_decide` receipt: it never runs `Ξ`.
Each line below must report only the three foundational axioms. -/

#print axioms Eip8282.Audit.Represents.represents_of_lookup
#print axioms Eip8282.Audit.Represents.Represents.unique
#print axioms Eip8282.Audit.Represents.Represents.fields
#print axioms Eip8282.Audit.Represents.Represents.queue_length
#print axioms Eip8282.Audit.Represents.Represents.inhibited_iff
#print axioms Eip8282.Audit.Represents.represents_packed_deposit
#print axioms Eip8282.Audit.Represents.represents_packed_exit
#print axioms Eip8282.Audit.Represents.represents_liveStorage
#print axioms Eip8282.Audit.Represents.represents_depositQueue65
#print axioms Eip8282.Audit.Represents.represents_default_storage
#print axioms Eip8282.Audit.Represents.default_storage_not_initialExit

-- C4 code-deposit half: Ξ on the full pinned init images (Node 4).
#print axioms Eip8282.Audit.Guarantees.PControl1.CtorXi.pcontrol1_ctor_xi_parent
#print axioms Eip8282.Tests.PControl1Mutant.pinned_ctor_bytes
#print axioms Eip8282.Tests.PControl1Mutant.ctor_mutants_differ_in_one_byte
#print axioms Eip8282.Tests.PControl1Mutant.ctor_mutant_refutes_parent
#print axioms Eip8282.Tests.PControl1Mutant.ctor_mutants_are_independent
#print axioms Eip8282.Tests.PControl1Mutant.ctor_mutants_leave_runtime_guarantees_intact

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
-- R4: the same byte-content half for an `MSTORE` *loop* of arbitrary length --
-- the shape a drain window takes. A store landing at the current end of memory
-- is a plain append, so no frame lemma and no window splitting is needed and the
-- trip count is unbounded. `AppendStores` is built from real
-- `StepOk (.MSTORE, none)` steps and `appendStores_two` inhabits it, so nothing
-- below is vacuous. `endpointAgrees_of_mstores_return` /
-- `exitAgrees_of_mstores_return` are `EndpointAgrees` / `ExitAgrees` in
-- *conclusion* position for the whole loop, and
-- `pdrain1_xi_returns_fifo_prefix_of_mstores` is a complete-`Ξ` observation with
-- no `ExitAgrees` premise. None of these may report a `native_decide` receipt or
-- a project `axiom`. They reduce, and do not discharge, `A-ABSTRACT-TX`: the
-- window `AppendStores` proves is `n` aligned 32-byte words while
-- `concatReturned` records are 68/184 bytes, so `hwords` bridges the gap there.
#print axioms Eip8282.Audit.XiTransport.bytes_eq_map_data
#print axioms Eip8282.Audit.XiTransport.bytes_append
#print axioms Eip8282.Audit.XiTransport.byteArray_append_assoc
#print axioms Eip8282.Audit.XiTransport.readWithPadding_self
#print axioms Eip8282.Audit.XiTransport.memory_mstore_append
#print axioms Eip8282.Audit.XiTransport.memory_step_MSTORE_append
#print axioms Eip8282.Audit.XiTransport.size_concatWords
#print axioms Eip8282.Audit.XiTransport.bytes_concatWords
#print axioms Eip8282.Audit.XiTransport.AppendStores.runs
#print axioms Eip8282.Audit.XiTransport.memory_AppendStores
#print axioms Eip8282.Audit.XiTransport.byteArray_eq_empty_of_size_zero
#print axioms Eip8282.Audit.XiTransport.bytes_readWithPadding_of_appendStores
#print axioms Eip8282.Audit.XiTransport.appendStores_two
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_of_mstores_return
#print axioms Eip8282.Audit.XiTransport.exitAgrees_of_mstores_return
#print axioms Eip8282.Audit.XiTransport.pdrain1_xi_returns_fifo_prefix_of_mstores
-- R4: `hwords` itself, discharged for the exit layout. A 68-byte record stride
-- is not word aligned, so each store overwrites the previous record's overshoot;
-- `OverlapStores` allows that and `storedBytes_exitStores` computes the window
-- to be the model's `concatReturned` outright, inverting the model's big-endian
-- encoder with `toBeBytes_beBytes`. `endpointAgrees_of_exitStores_return` is
-- `EndpointAgrees` in *conclusion* position for that unaligned window and
-- `pdrain1_xi_returns_fifo_prefix_of_exitStores` is a complete-`Ξ` observation
-- carrying neither `hbytes` nor `hwords`. `overlapStores_exitRecord` inhabits
-- the predicate with real `MSTORE` opcodes and `exists_exitRecordWords` shows
-- the per-record scalar side conditions are satisfiable, so neither is vacuous.
-- None of these may report a `native_decide` receipt or a project `axiom`. They
-- do not discharge `A-ABSTRACT-TX`: reaching the loop is still assumed. The
-- 184-byte deposit layout is not covered by `OverlapStores`; it is carried by
-- the `MixedStores` block below.
#print axioms Eip8282.Audit.XiTransport.memory_mstore_overwrite
#print axioms Eip8282.Audit.XiTransport.memory_step_MSTORE_overwrite
#print axioms Eip8282.Audit.XiTransport.bytes_readWithPadding_prefix
#print axioms Eip8282.Audit.XiTransport.toBeBytes_beBytes
#print axioms Eip8282.Audit.XiTransport.toBeBytes_mul_pow
#print axioms Eip8282.Audit.XiTransport.OverlapStores.runs
#print axioms Eip8282.Audit.XiTransport.bytes_memory_OverlapStores
#print axioms Eip8282.Audit.XiTransport.storedBytes_exitRecord
#print axioms Eip8282.Audit.XiTransport.storedBytes_exitStores
#print axioms Eip8282.Audit.XiTransport.length_concatReturned_exitRecords
#print axioms Eip8282.Audit.XiTransport.bytes_readWithPadding_of_exitStores
#print axioms Eip8282.Audit.XiTransport.overlapStores_exitRecord
#print axioms Eip8282.Audit.XiTransport.exists_exitRecordWords
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_of_exitStores_return
#print axioms Eip8282.Audit.XiTransport.exitAgrees_of_exitStores_return
#print axioms Eip8282.Audit.XiTransport.pdrain1_xi_returns_fifo_prefix_of_exitStores
-- R4: `hstores` itself, for the exit layout. `overlapStores_exitRecord` inhabits
-- `OverlapStores` at one record on a fresh frame; the statements that consume
-- `hstores` quantify over a list, so that left the predicate's reachability open
-- at the lengths they are about. `overlapStores_exitRecord_step` runs one record
-- at an arbitrary covered base and `overlapStores_exitStores` iterates it to
-- every record count, re-establishing the coverage invariant at each stride.
-- `endpointAgrees_of_exitRun_return` / `exitAgrees_of_exitRun_return` are then
-- `EndpointAgrees` / `ExitAgrees` with the run *constructed*, not assumed: no
-- `hstores`, no `hbytes`, no `hwords`, no endpoint premise. None of these may
-- report a `native_decide` receipt or a project `axiom`. They do not discharge
-- `A-ABSTRACT-TX`: that the pinned bytecode places these operands on the stack
-- in this order is still assumed, and `EndpointAgrees` remains open in general.
#print axioms Eip8282.Audit.XiTransport.OverlapStores.trans
#print axioms Eip8282.Audit.XiTransport.overlapStores_one_of_stack
#print axioms Eip8282.Audit.XiTransport.overlapStores_exitRecord_step
#print axioms Eip8282.Audit.XiTransport.overlapStores_exitStores
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_of_exitRun_return
#print axioms Eip8282.Audit.XiTransport.exitAgrees_of_exitRun_return
-- R4: `hwords` discharged for the *deposit* layout — the 184-byte record the
-- `OverlapStores` block above cannot express. Six of the seven stores in the
-- drain loop are plain `MSTORE`s; the seventh is `%MSTORE64_le`, a byte-level
-- eight-byte little-endian splice into the middle of an already-stored word.
-- `MixedStores` admits `MSTORE` and `MSTORE8` in one loop, `Splice` /
-- `splicedBytes` fix the resolution order, and `splicedBytes_depositRecord`
-- computes the 184-byte stride to be the model's own `encodeReturned`.
-- `endpointAgrees_of_depositStores_return` is `EndpointAgrees` in *conclusion*
-- position for that mixed window and
-- `pdrain1_xi_returns_fifo_prefix_of_depositStores` is a complete-`Ξ`
-- observation carrying neither `hbytes` nor `hwords`. `mixedStores_one_byte` and
-- `mixedStores_depositPrefix` inhabit the predicate with real `MSTORE` /
-- `MSTORE8` opcodes and `exists_depositRecordWords` shows the per-record scalar
-- and little-endian side conditions are satisfiable, so none of it is vacuous.
-- None of these may report a `native_decide` receipt or a project `axiom`.
-- The `Splice` / `MixedStores` / `DepositRecordWords` type formers and the
-- `splicedBytes`, `byteRun`, `depositWord`, `DepositRecordWords.ok` / `.record`,
-- `depositRecordStores` and `depositStores` definitions take no receipts of
-- their own, matching the exit block above: each is referenced by a theorem
-- listed here, so an axiom reaching any of them would surface on these lines.
-- They do not discharge `A-ABSTRACT-TX`: nothing proves the pinned runtime
-- performs the `MixedStores` run, and the `%MSTORE64_le` expansion is a
-- hypothesis read off an unvendored include, never a conclusion.
#print axioms Eip8282.Audit.XiTransport.take_split
#print axioms Eip8282.Audit.XiTransport.drop_add
#print axioms Eip8282.Audit.XiTransport.slice_append_drop
#print axioms Eip8282.Audit.XiTransport.memory_mstore8_eq
#print axioms Eip8282.Audit.XiTransport.bytes_memory_mstore8
#print axioms Eip8282.Audit.XiTransport.memory_step_MSTORE8_eq
#print axioms Eip8282.Audit.XiTransport.size_mstore8Post
#print axioms Eip8282.Audit.XiTransport.bytes_memory_step_MSTORE8
#print axioms Eip8282.Audit.XiTransport.splicedBytes_append
#print axioms Eip8282.Audit.XiTransport.splicedBytes_word_append
#print axioms Eip8282.Audit.XiTransport.MixedStores.runs
#print axioms Eip8282.Audit.XiTransport.bytes_memory_MixedStores
#print axioms Eip8282.Audit.XiTransport.splicedBytes_byteRun
#print axioms Eip8282.Audit.XiTransport.toLeBytes_lt
#print axioms Eip8282.Audit.XiTransport.toBeBytes_depositWord
#print axioms Eip8282.Audit.XiTransport.length_encodeReturned_deposit
#print axioms Eip8282.Audit.XiTransport.splicedBytes_depositRecord
#print axioms Eip8282.Audit.XiTransport.splicedBytes_depositStores
#print axioms Eip8282.Audit.XiTransport.length_concatReturned_depositRecords
#print axioms Eip8282.Audit.XiTransport.bytes_readWithPadding_of_depositStores
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_of_depositStores_return
#print axioms Eip8282.Audit.XiTransport.exitAgrees_of_depositStores_return
#print axioms Eip8282.Audit.XiTransport.mixedStores_one_byte
#print axioms Eip8282.Audit.XiTransport.mixedStores_depositPrefix
#print axioms Eip8282.Audit.XiTransport.exists_depositRecordWords
#print axioms Eip8282.Audit.XiTransport.pdrain1_xi_returns_fifo_prefix_of_depositStores
-- R4: the adjacency hypothesis removed. Every statement in the two blocks above
-- requires the record's `MSTORE`s to be *consecutive*, and no pinned EIP-7002
-- runtime is shaped that way: `builder_exits` writes its window from the
-- `accum_loop` body (PC 247, back-jump at PC 300), so between the stores at PC
-- 274, 284 and 294 sit the `SLOAD` that reads the queue slot, the `ADD` / `MUL`
-- / `SHL` / `EQ` that build the operands, the `DUP` / `SWAP` / `POP` shuffling
-- and the `JUMPDEST` / `JUMP` / `JUMPI` that close the loop. Adjacency was
-- therefore not a presentational detail but a hypothesis the pinned bytecode
-- provably never satisfies, which left every `EndpointAgrees`-in-conclusion
-- statement above inapplicable to the real drain.
-- `memory_execBinOp`, `memory_dup`, `memory_swap` and `memory_unaryStateOp` are
-- the four EVMYulLean opcode-family frames this needs; `NeutralOp` names exactly
-- the non-`MSTORE` opcodes of that loop body and `memory_step_neutral`
-- discharges neutrality for each of them, generalising `memory_step_Push`.
-- `memory_Runs_neutral` closes it transitively, so `SpacedStores` can replace
-- adjacency with an arbitrary run between stores subject only to a *syntactic*
-- condition on the gap trace. `OverlapStores.spaced` embeds the old relation
-- with empty gaps, so nothing proved from adjacency is lost and none of the new
-- statements is weaker. `endpointAgrees_of_spacedExitStores_return` is
-- `EndpointAgrees` in *conclusion* position for a loop-written window and
-- `pdrain1_xi_returns_fifo_prefix_of_spacedExitStores` carries it to the
-- complete-`Ξ` observation. None of these may report a `native_decide` receipt
-- or a project `axiom`. The `NeutralOp` and `SpacedStores` type formers and
-- `IsNeutralStep` take no receipts of their own: each is referenced by a theorem
-- listed here, so an axiom reaching any of them would surface on these lines.
-- This does **not** discharge `A-ABSTRACT-TX`. What it removes from the residual
-- is the adjacency claim and the empty-memory claim `hfresh`, both of which were
-- false of the pinned runtime; what remains is unchanged in kind — nothing here
-- proves the pinned runtime reaches these stores at all, and `hstores` / `hok` /
-- `hlen` assert exactly that it does. `EndpointAgrees` stays OPEN in general.
#print axioms Eip8282.Audit.XiTransport.memory_execBinOp
#print axioms Eip8282.Audit.XiTransport.memory_dup
#print axioms Eip8282.Audit.XiTransport.memory_swap
#print axioms Eip8282.Audit.XiTransport.memory_unaryStateOp
#print axioms Eip8282.Audit.XiTransport.memory_step_neutral
#print axioms Eip8282.Audit.XiTransport.isPushStep_isNeutralStep
#print axioms Eip8282.Audit.XiTransport.memory_Runs_neutral
#print axioms Eip8282.Audit.XiTransport.SpacedStores.nil_neutral
#print axioms Eip8282.Audit.XiTransport.SpacedStores.cons_neutral
#print axioms Eip8282.Audit.XiTransport.SpacedStores.runs
#print axioms Eip8282.Audit.XiTransport.OverlapStores.spaced
#print axioms Eip8282.Audit.XiTransport.bytes_memory_SpacedStores
#print axioms Eip8282.Audit.XiTransport.bytes_readWithPadding_of_spacedExitStores
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_of_spacedExitStores_return
#print axioms Eip8282.Audit.XiTransport.exitAgrees_of_spacedExitStores_return
#print axioms Eip8282.Audit.XiTransport.pdrain1_xi_returns_fifo_prefix_of_spacedExitStores
-- R4: the same adjacency hypothesis removed on the *deposit* side. The block
-- above only reached the exit layout: `MixedStores`, which carries the
-- `%MSTORE64_le` byte splice the 184-byte deposit record needs, was still
-- requiring its `MSTORE`s and `MSTORE8`s to be consecutive, and
-- `builder_deposits` writes its window from a loop of its own exactly as
-- `builder_exits` does. The deposit half of P-DRAIN-1's non-empty window was
-- therefore still stated about a store shape the pinned runtime does not have.
-- `SpacedMixedStores` removes that requirement on both constructors under the
-- same syntactic gap condition: `nil_neutral`, `word_neutral` and
-- `byte_neutral` derive the gap's memory equation from `memory_Runs_neutral`,
-- so a caller asserts nothing about the intermediate states.
-- `MixedStores.spaced` embeds the adjacency relation with empty gaps, so
-- nothing proved from `MixedStores` is lost and none of these statements is
-- weaker; `bytes_memory_SpacedMixedStores` recomputes the byte image and
-- `endpointAgrees_of_spacedDepositStores_return` /
-- `exitAgrees_of_spacedDepositStores_return` put `EndpointAgrees` / `ExitAgrees`
-- in *conclusion* position for a loop-written deposit window, which
-- `pdrain1_xi_returns_fifo_prefix_of_spacedDepositStores` carries to the
-- complete-`Ξ` observation. Both drain layouts are now in that form. None of
-- these may report a `native_decide` receipt or a project `axiom`. The
-- `SpacedMixedStores` type former takes no receipt of its own: it is referenced
-- by the theorems listed here, so an axiom reaching it would surface on these
-- lines. This does **not** discharge `A-ABSTRACT-TX`, for the same reason as
-- the exit block: what it removes is a pair of hypotheses that were false of the
-- pinned runtime — adjacency and `hfresh` — and `hstores` / `hok` / `hlen` still
-- assert that the runtime performs these stores. `EndpointAgrees` stays OPEN in
-- general.
#print axioms Eip8282.Audit.XiTransport.SpacedMixedStores.nil_neutral
#print axioms Eip8282.Audit.XiTransport.SpacedMixedStores.word_neutral
#print axioms Eip8282.Audit.XiTransport.SpacedMixedStores.byte_neutral
#print axioms Eip8282.Audit.XiTransport.SpacedMixedStores.runs
#print axioms Eip8282.Audit.XiTransport.MixedStores.spaced
#print axioms Eip8282.Audit.XiTransport.bytes_memory_SpacedMixedStores
#print axioms Eip8282.Audit.XiTransport.bytes_readWithPadding_of_spacedDepositStores
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_of_spacedDepositStores_return
#print axioms Eip8282.Audit.XiTransport.exitAgrees_of_spacedDepositStores_return
#print axioms Eip8282.Audit.XiTransport.pdrain1_xi_returns_fifo_prefix_of_spacedDepositStores
-- R4: the pre-staged operand stack removed from the *constructed* exit drain.
-- The block above still assumes the run; `endpointAgrees_of_exitRun_return` and
-- `exitAgrees_of_exitRun_return` do build it, but only from `hstack`: all
-- `6·n + 2` operands of all the stores already on the stack before the first
-- `MSTORE`. `builder_exits` enters `accum_loop` (PC 247) with four words —
-- `i`, `count`, `head_idx`, `tail_idx` — and computes each record's offsets and
-- values inside the loop body, between the stores that consume them, so
-- pre-staging is a third hypothesis the pinned bytecode provably never
-- satisfies. `GapStores` replaces it: a memory-neutral gap before *every*
-- store, supplying only that store's offset and value, with the store's
-- post-state computed as `mstorePost` rather than assumed, and no memory-size
-- hypothesis anywhere in the relation. `StoresCovered` / `covered_exitStores`
-- recover the `hle` / `hcov` frontier conditions `SpacedStores.cons` asks for
-- from the 68-byte stride itself, so the caller supplies only
-- `pre.memory.size ≤ 32` in place of `hfresh : pre.memory.size = 0`.
-- `GapStores.spaced` transports the whole `SpacedStores` layer onto it, and
-- `gapStores_exitStores_of_stack` embeds the pre-staged run with every gap
-- empty — so the relation is inhabited by real opcodes at every record count
-- and no statement proved from it is weaker than the flat-stack ones.
-- `endpointAgrees_of_gapExitDrain_return` / `exitAgrees_of_gapExitDrain_return`
-- are `EndpointAgrees` / `ExitAgrees` in *conclusion* position for a drain
-- whose run is built, not assumed, and whose stack shape is the loop's own.
-- None of these may report a `native_decide` receipt or a project `axiom`. The
-- `GapStores` and `StoresCovered` type formers take no receipts of their own:
-- each is referenced by a theorem listed here, so an axiom reaching either
-- would surface on these lines. This does **not** discharge `A-ABSTRACT-TX`.
-- What it removes is the pre-staged stack; what remains is that the pinned
-- bytecode's loop body *is* one of these gaps — that the runtime reaches
-- `accum_loop` and reads the queue slots it claims. `EndpointAgrees` stays OPEN
-- in general. All six are carried as new conjuncts of the registered R4 parent
-- `pdrain1_xi_forall_parent`; no new guarantee ID, and the P-DRAIN-1 kill-line
-- still refutes it through `pdrain1_forall_parent`.
#print axioms Eip8282.Audit.XiTransport.covered_exitStores
#print axioms Eip8282.Audit.XiTransport.GapStores.spaced
#print axioms Eip8282.Audit.XiTransport.gapStores_cons_nogap
#print axioms Eip8282.Audit.XiTransport.gapStores_exitStores_of_stack
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_of_gapExitDrain_return
#print axioms Eip8282.Audit.XiTransport.exitAgrees_of_gapExitDrain_return
-- R4: the same three hypotheses removed from the *deposit* drain. The exit side
-- got `GapStores`; the deposit side was still on `SpacedMixedStores`, which asks
-- the caller, per store, for the state the store lands in, for a `StepOk`
-- witness, and for the frame conditions `off ≤ size ≤ off + 32` (word) and
-- `off < size` (byte). The third is the one that bites: `builder_deposits`
-- writes its 184-byte records from a loop of its own, so those are seven
-- assertions per record about the size of memory *between* two stores of a
-- runtime the caller does not control. `GapMixedStores` carries none of them:
-- a memory-neutral gap before every store — word or byte — supplying only that
-- store's offset and value, and the post-state computed as `mstorePost` /
-- `mstore8Post`. `SplicesCovered` / `splicesCovered_byteRun_append` /
-- `splicesCovered_depositRecord` / `covered_depositStores` recover the frontier
-- arithmetically at the offsets `main.eas` gives the seven stores — `+0`, `+32`,
-- `+64` walk the frame to `b + 96`, the eight `%MSTORE64_le` bytes at `+80 … +87`
-- land strictly inside it, `+96`, `+128`, `+160` walk it to `b + 192`, and the
-- next record's base `b + 184` is within one word of that — so the caller
-- supplies only `pre.memory.size ≤ 32` for the whole drain.
-- `GapMixedStores.spaced` transports the whole `SpacedMixedStores` layer onto
-- it, and `MixedStores.gap` embeds the adjacency-shaped relation with every gap
-- empty, so `mixedStores_depositPrefix` still inhabits it with real
-- `MSTORE` / `MSTORE8` opcodes and nothing proved from `MixedStores` is lost.
-- `endpointAgrees_of_gapDepositDrain_return` /
-- `exitAgrees_of_gapDepositDrain_return` are `EndpointAgrees` / `ExitAgrees` in
-- *conclusion* position for the deposit window at that shape. None of these may
-- report a `native_decide` receipt or a project `axiom`. The `GapMixedStores`
-- and `SplicesCovered` type formers take no receipts of their own: each is
-- referenced by a theorem listed here, so an axiom reaching either would surface
-- on these lines. This does **not** discharge `A-ABSTRACT-TX`. What it removes
-- is a frame hypothesis about intermediate states; what remains is that the
-- pinned bytecode's loop body *is* one of these gaps — that `builder_deposits`
-- reaches its store loop and reads the queue slots it claims. `EndpointAgrees`
-- stays OPEN in general. All nine are carried as new conjuncts of the registered
-- R4 parent `pdrain1_xi_forall_parent`; no new guarantee ID, and the P-DRAIN-1
-- kill-line still refutes it through `pdrain1_forall_parent`.
#print axioms Eip8282.Audit.XiTransport.splicesCovered_byteRun_append
#print axioms Eip8282.Audit.XiTransport.splicesCovered_depositRecord
#print axioms Eip8282.Audit.XiTransport.covered_depositStores
#print axioms Eip8282.Audit.XiTransport.GapMixedStores.spaced
#print axioms Eip8282.Audit.XiTransport.gapMixedStores_word_nogap
#print axioms Eip8282.Audit.XiTransport.gapMixedStores_byte_nogap
#print axioms Eip8282.Audit.XiTransport.MixedStores.gap
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_of_gapDepositDrain_return
#print axioms Eip8282.Audit.XiTransport.exitAgrees_of_gapDepositDrain_return
-- R4: the *epilogue* admitted between the last store and the `RETURN`. The two
-- blocks above put a memory-neutral gap before every store, but still required
-- the `RETURN` to follow the last store with nothing but that store's own gap in
-- between, and read the `RETURN` operands off the state the last store lands in.
-- The pinned runtimes do not have that shape either: after the window's last
-- `MSTORE` `builder_exits` runs `update_head` (PC 313), `reset_queue` and
-- `store_excess` (PC 450), and `builder_deposits` runs `update_head` (PC 483),
-- before returning. Those epilogues *write storage* —
-- `Footprint.exit_update_head_SSTORE`, `exit_reset_queue_SSTORE_head` and
-- `exit_store_excess_SSTORE_excess` read `.SSTORE` off the pinned image itself —
-- and `NeutralOp` did not admit `SSTORE`, so no gap containing a real epilogue
-- was a legal gap at all. `memory_binaryStateOp` discharges its neutrality the
-- same way `memory_unaryStateOp` discharges `SLOAD`'s: `EvmYul.State` has no
-- memory field, so a `binaryStateOp` that replaces `toState` wholesale cannot
-- move memory. `GapStores.append_neutral` / `GapMixedStores.append_neutral` then
-- append an arbitrary neutral run after the last store, and the four
-- `*_epilogue_return` theorems read the `RETURN` operands off the end of *that*
-- run rather than off the last store's post-state. None of these may report a
-- `native_decide` receipt or a project `axiom`. This does **not** discharge
-- `A-ABSTRACT-TX`. What it removes is the requirement that the `RETURN` be
-- welded to the last store; what remains is unchanged in kind — nothing here
-- proves the pinned runtime reaches the drain loop or that its epilogue is one
-- of these runs, and no `∀`-quantified correspondence over pinned traces is
-- claimed. `EndpointAgrees` stays OPEN in general. All six are carried as new
-- conjuncts of the registered R4 parent `pdrain1_xi_forall_parent`; no new
-- guarantee ID, and the P-DRAIN-1 kill-line still refutes it through
-- `pdrain1_forall_parent`.
#print axioms Eip8282.Audit.XiTransport.memory_binaryStateOp
#print axioms Eip8282.Audit.XiTransport.GapStores.append_neutral
#print axioms Eip8282.Audit.XiTransport.GapMixedStores.append_neutral
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_of_gapExitDrain_epilogue_return
#print axioms Eip8282.Audit.XiTransport.exitAgrees_of_gapExitDrain_epilogue_return
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_of_gapDepositDrain_epilogue_return
#print axioms Eip8282.Audit.XiTransport.exitAgrees_of_gapDepositDrain_epilogue_return
-- R4: the pinned `revert:` subroutine, `5b 5f 5f fd` at the tail of both
-- images. The two tail facts are `decide +kernel` against the pinned byte
-- arrays, so they must depend on *no* axioms at all — a `native_decide`
-- receipt appearing on either would mean the image check had silently become
-- a trace evaluation. `step_REVERT` is the `REVERT` step
-- inversion `EvmYul.EVM.Proof.MemoryStep` does not ship at the pinned
-- revision. `endpointAgrees_of_revertEpilogue` and its two branch instances
-- put `EndpointAgrees` in *conclusion* position with the run constructed and
-- memory universally quantified; the zero length operand is what makes that
-- possible without any memory or `NeutralOp` hypothesis. The two `_of_zeroTop`
-- forms narrow the complete-`Ξ` residual from two premises to one syntactic
-- fact about the exit stack. None of this discharges `A-ABSTRACT-TX`: nothing
-- below proves a `Ξ` run of a pinned runtime reaches the `revert:` `JUMPDEST`,
-- and `EndpointAgrees` stays OPEN. All are carried under the existing
-- P-SUBMIT-1 ID; no new guarantee or assumption ID is introduced, and the
-- P-SUBMIT-1 kill-line still refutes through `psubmit1_forall_parent`.
#print axioms Eip8282.Audit.XiTransport.deposit_tail_is_revert_subroutine
#print axioms Eip8282.Audit.XiTransport.exit_tail_is_revert_subroutine
#print axioms Eip8282.Audit.XiTransport.step_PUSH0
#print axioms Eip8282.Audit.XiTransport.step_REVERT
#print axioms Eip8282.Audit.XiTransport.H_return_step_REVERT
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_of_revertEpilogue
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_of_revertEpilogue_inhibited
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_of_revertEpilogue_rejected
#print axioms Eip8282.Audit.XiTransport.pop2_of_zeroTop
#print axioms Eip8282.Audit.XiTransport.zeroTop_push0_push0
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_inhibited_reverts_of_zeroTop
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_rejected_reverts_of_zeroTop
-- R4: the byte-offset → `decodeAt` bridge. `deposit_revert_decodes` /
-- `exit_revert_decodes` run EVMYulLean's own `decode` on the pinned images at
-- the four `revert:` offsets, `decide +kernel`, so they too must show no
-- receipt. `decodeAt_of_code_pc` transports a ground decode to any state at
-- that offset in that code, and `op_eq_REVERT_of_atRevertByte` turns the
-- `op = .REVERT` premise of the two `_of_zeroTop` forms into a *derived* fact.
-- The `_at_revertByte` forms are the result: one unproved antecedent fewer.
-- What replaces it, `AtRevertByte`, is a statement about where the exit is —
-- not a proof that any run puts it there. `A-ABSTRACT-TX` stays OPEN.
#print axioms Eip8282.Audit.XiTransport.deposit_revert_decodes
#print axioms Eip8282.Audit.XiTransport.exit_revert_decodes
#print axioms Eip8282.Audit.XiTransport.revertByte_decodes
#print axioms Eip8282.Audit.XiTransport.decodeAt_of_code_pc
#print axioms Eip8282.Audit.XiTransport.decodeAt_of_atRevertByte
#print axioms Eip8282.Audit.XiTransport.op_eq_REVERT_of_atRevertByte
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_inhibited_reverts_at_revertByte
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_rejected_reverts_at_revertByte
-- R4: running the subroutine instead of assuming its endpoint.
-- `revertSubroutine_decodes` is `decide +kernel` over all four `revert:` bytes
-- of each pinned image, so it must show no receipt for the same reason the two
-- tail facts must not. `Z_PUSH0` / `Z_REVERT` discharge EVMYulLean's gas and
-- stack-bound side condition, `xStepAt_PUSH0` is the `PUSH0` step, and
-- `runUntil_revertSubroutine` chains them into a `RunUntil` that *ends* at the
-- `REVERT` byte with the two zero words on the stack — so `AtRevertByte` and
-- the stack shape are now conclusions, not premises. `runUntil_of_xRuns` is the
-- composition lemma that lets an arbitrary prefix run precede it. The two
-- `_of_reaches_revert` forms are the payoff: they reach the same observation as
-- the `_at_revertByte` forms with `hat`, `htop`, `hdec`, `hZ` and `hstep` all
-- discharged, leaving one reachability premise plus two arithmetic side
-- conditions. This does **not** discharge `A-ABSTRACT-TX`: no `XRuns` prefix
-- landing in `AtRevertJumpdest` is constructed for either pinned image, so
-- `EndpointAgrees` stays OPEN. Carried under the existing P-SUBMIT-1 ID; no new
-- guarantee or assumption ID, and the P-SUBMIT-1 kill-line still refutes.
#print axioms Eip8282.Audit.XiTransport.revertSubroutine_decodes
#print axioms Eip8282.Audit.XiTransport.Z_PUSH0
#print axioms Eip8282.Audit.XiTransport.Z_REVERT
#print axioms Eip8282.Audit.XiTransport.xStepAt_PUSH0
#print axioms Eip8282.Audit.XiTransport.runUntil_revertSubroutine
#print axioms Eip8282.Audit.XiTransport.runUntil_of_xRuns
#print axioms Eip8282.Audit.XiTransport.revert_exit_of_reaches_revertJumpdest
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_inhibited_reverts_of_reaches_revert
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_rejected_reverts_of_reaches_revert
-- R4: reaching the `revert:` label instead of assuming it. The ten pinned
-- `PUSH2 @revert; JUMPI` sites are `decide +kernel` against the pinned byte
-- arrays -- `deposit_revertJumpi_decodes`, `exit_revertJumpi_decodes` and their
-- union `revertJumpi_sites_pinned` -- so, like every other image check above,
-- they must show *no* receipt; a `native_decide` here would mean the site
-- enumeration had silently become a trace evaluation. `revert_mem_table` is the
-- kernel check that the `revert:` offset is in the campaign's jumpdest table,
-- which is what lets `Z` admit the branch. `Z_JUMPI_taken` discharges
-- EVMYulLean's gas and stack-bound side condition and `step_JUMPI_taken` is the
-- taken-branch `pc` update; `xStepAt_JUMPI_taken` chains them into one `X`
-- iteration. The payoff is `atRevertJumpdest_of_atRevertJumpi`: the
-- `AtRevertJumpdest` premise that every `_of_reaches_revert` form above took on
-- trust is now *derived* from standing at a pinned branch into `revert:` and
-- taking it. `revert_exit_of_reaches_revertJumpi` and the two
-- `_of_reaches_revertJumpi` branch forms reach the same observation one
-- instruction earlier in the CFG. This does **not** discharge `A-ABSTRACT-TX`:
-- no `XRuns` prefix landing on any of the ten sites is constructed for either
-- image, and nothing here shows a site's branch is taken exactly on the
-- abstract refusal condition, so `EndpointAgrees` stays OPEN at HIGH. Carried
-- under the existing P-SUBMIT-1 ID; no new guarantee or assumption ID, and the
-- P-SUBMIT-1 kill-line still refutes through `psubmit1_forall_parent`.
#print axioms Eip8282.Audit.XiTransport.memoryExpansionCost_JUMPI
#print axioms Eip8282.Audit.XiTransport.C'_JUMPI
#print axioms Eip8282.Audit.XiTransport.Z_JUMPI_taken
#print axioms Eip8282.Audit.XiTransport.step_JUMPI_taken
#print axioms Eip8282.Audit.XiTransport.xStepAt_JUMPI_taken
#print axioms Eip8282.Audit.XiTransport.deposit_revertJumpi_decodes
#print axioms Eip8282.Audit.XiTransport.exit_revertJumpi_decodes
#print axioms Eip8282.Audit.XiTransport.revertJumpi_sites_pinned
#print axioms Eip8282.Audit.XiTransport.revert_mem_table
#print axioms Eip8282.Audit.XiTransport.atRevertJumpdest_of_atRevertJumpi
#print axioms Eip8282.Audit.XiTransport.revert_exit_of_reaches_revertJumpi
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_inhibited_reverts_of_reaches_revertJumpi
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_rejected_reverts_of_reaches_revertJumpi
-- R4: supplying the branch operand instead of assuming it. Nothing new is
-- decided about the images here -- the `PUSH2 @revert` immediate is the *same*
-- `decide +kernel` fact `revertJumpi_sites_pinned` already carried, now read in
-- conclusion position -- so every line below must likewise show *no* receipt.
-- `Z_PUSH2` discharges EVMYulLean's gas and stack-bound side condition for the
-- push and `step_PUSH2` is the `pc` update by `argWidth.succ`, the three bytes
-- that land the run exactly on the `JUMPI`; `xStepAt_PUSH2` chains them into one
-- `X` iteration. The payoff is `atRevertJumpi_of_atRevertPush`: the
-- `AtRevertJumpi` premise *and* the destination-operand equation that the
-- `_of_reaches_revertJumpi` forms above both took on trust are now derived from
-- standing three bytes earlier. `revert_exit_of_reaches_revertPush` and the two
-- `_of_reaches_revertPush` branch forms reach the same observation from a stack
-- premise naming only the branch condition. This does **not** discharge
-- `A-ABSTRACT-TX`: no `XRuns` prefix landing in `AtRevertPush` is constructed
-- for either image, the ten sites are still read forwards with no completeness
-- claim, and nothing here shows the branch is taken exactly on the abstract
-- refusal condition, so `EndpointAgrees` stays OPEN at HIGH. Carried under the
-- existing P-SUBMIT-1 ID; no new guarantee or assumption ID, and the P-SUBMIT-1
-- kill-line still refutes through `psubmit1_forall_parent`.
#print axioms Eip8282.Audit.XiTransport.ofNat_add_ofNat
#print axioms Eip8282.Audit.XiTransport.three_le_of_mem_revertJumpiSites
#print axioms Eip8282.Audit.XiTransport.memoryExpansionCost_PUSH2
#print axioms Eip8282.Audit.XiTransport.C'_PUSH2
#print axioms Eip8282.Audit.XiTransport.Z_PUSH2
#print axioms Eip8282.Audit.XiTransport.step_PUSH2
#print axioms Eip8282.Audit.XiTransport.xStepAt_PUSH2
#print axioms Eip8282.Audit.XiTransport.atRevertJumpi_of_atRevertPush
#print axioms Eip8282.Audit.XiTransport.revert_exit_of_reaches_revertPush
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_inhibited_reverts_of_reaches_revertPush
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_rejected_reverts_of_reaches_revertPush
-- R4: the fall-through half of the same branch. Every line above walks the
-- *taken* edge only; these walk the untaken one, so the pinned sites become a
-- two-way branch rather than a one-way claim. EVMYulLean conditions its
-- `BadJumpDestination` guard on the second stack word being nonzero, so
-- `Z_JUMPI_untaken` needs no `validJumps` premise at all; `step_JUMPI_untaken`
-- advances the `pc` by one instead of jumping; and
-- `succ_revertJumpiSite_ne_revertPc` is the same kind of `decide +kernel` fact
-- over the ten literals that the site table already carried -- the sites are all
-- below offset 205, `revert:` is at 624 and 454 -- so no line below may show a
-- receipt. `atRevertJumpdest_iff_cond_ne_zero` states both directions together:
-- the run reaches the `revert:` `JUMPDEST` from a pinned site exactly when the
-- condition word is nonzero. This does **not** discharge `A-ABSTRACT-TX`: no
-- `XRuns` prefix reaching a site is constructed and nothing ties the condition
-- word to the abstract refusal condition, so `EndpointAgrees` stays OPEN at
-- HIGH. Carried under the existing P-SUBMIT-1 ID with no new guarantee or
-- assumption ID.
#print axioms Eip8282.Audit.XiTransport.Z_JUMPI_untaken
#print axioms Eip8282.Audit.XiTransport.step_JUMPI_untaken
#print axioms Eip8282.Audit.XiTransport.xStepAt_JUMPI_untaken
#print axioms Eip8282.Audit.XiTransport.succ_revertJumpiSite_ne_revertPc
#print axioms Eip8282.Audit.XiTransport.not_atRevertJumpdest_of_atRevertJumpi_untaken
#print axioms Eip8282.Audit.XiTransport.atRevertJumpdest_iff_cond_ne_zero
-- R4, *Eight*: the nonpayable guard. `valueGuard_pinned` is `decide +kernel`
-- over the literals, so it must show no `native_decide` receipt. The chain
-- ties the condition word at deposit 148 / exit 147 to `Iᵥ`, hence to the
-- `value ≠ 0` clause of `Model.userCall` on empty calldata. It still does
-- **not** discharge `A-ABSTRACT-TX`: through *Eight* the `XRuns` prefix
-- reaching the guard is a hypothesis and the other nine sites branch on
-- unidentified words, so `EndpointAgrees` stays OPEN at HIGH. Carried under the
-- existing P-SUBMIT-1 ID with no new guarantee or assumption ID.
#print axioms Eip8282.Audit.XiTransport.valueGuard_pinned
#print axioms Eip8282.Audit.XiTransport.Z_CALLVALUE
#print axioms Eip8282.Audit.XiTransport.step_CALLVALUE
#print axioms Eip8282.Audit.XiTransport.xStepAt_CALLVALUE
#print axioms Eip8282.Audit.XiTransport.stack_callvaluePost
#print axioms Eip8282.Audit.XiTransport.atRevertPush_of_atValueGuard
#print axioms Eip8282.Audit.XiTransport.revert_exit_of_reaches_valueGuard
#print axioms Eip8282.Audit.XiTransport.psubmit1_exitAgrees_iff_paidGetter
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_paidGetter_reverts_of_reaches_valueGuard
#print axioms Eip8282.Audit.XiTransport.endpointAgrees_of_revertEpilogue_paidGetter
-- R4, *Nine*: the dispatch size guard and the first constructed prefix.
-- `sizeGuard_pinned` is `decide +kernel` / `decide` over the literals (opcode,
-- site membership, and `sizeGuardPc + 5 = valueGuardPc`), as is
-- `succ_sizeGuardJumpi_eq_valueGuardPc`, so neither may show a `native_decide`
-- receipt. `stack_calldatasizePost` is the equation identifying the condition
-- word at deposit 147 / exit 146 as `|I_d|` -- the second of the ten sites whose
-- word is not opaque. `atValueGuard_of_atSizeGuard` is the change of kind: the
-- three iterations `CALLDATASIZE`, `PUSH2 @revert`, untaken `JUMPI` are
-- constructed into an `XRuns` landing on the nonpayable guard, so *Eight*'s
-- `AtValueGuard` hypothesis becomes a conclusion. This still does **not**
-- discharge `A-ABSTRACT-TX`: reaching the *size* guard is itself a hypothesis
-- (the dispatch prefix from `c.entry` is not constructed), the other eight sites
-- branch on unidentified words, and only the empty-calldata fee-getter clause of
-- `userCall` is covered -- so `EndpointAgrees` stays OPEN at HIGH. Carried under
-- the existing P-SUBMIT-1 ID with no new guarantee or assumption ID.
#print axioms Eip8282.Audit.XiTransport.sizeGuard_pinned
#print axioms Eip8282.Audit.XiTransport.Z_CALLDATASIZE
#print axioms Eip8282.Audit.XiTransport.step_CALLDATASIZE
#print axioms Eip8282.Audit.XiTransport.xStepAt_CALLDATASIZE
#print axioms Eip8282.Audit.XiTransport.stack_calldatasizePost
#print axioms Eip8282.Audit.XiTransport.atRevertPush_of_atSizeGuard
#print axioms Eip8282.Audit.XiTransport.revert_exit_of_reaches_sizeGuard
#print axioms Eip8282.Audit.XiTransport.succ_sizeGuardJumpi_eq_valueGuardPc
#print axioms Eip8282.Audit.XiTransport.atValueGuard_of_atSizeGuard
#print axioms Eip8282.Audit.XiTransport.calldata_size_eq_zero_of_bytes_nil
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_paidGetter_reverts_of_reaches_sizeGuard
-- R4, *Ten*: the fee comparison and the rejected branch of `userCall`.
-- `feeGuard_pinned` is `decide +kernel` / `decide` over the literals (the
-- `CALLVALUE` at `pc`, the `LT` at `pc + 1`, and the membership of `pc + 5`), so
-- it must show no `native_decide` receipt. `stack_ltPost` is the equation
-- identifying the condition word at deposit 166 / exit 164 as the computed
-- comparison `UInt256.lt Iᵥ req` -- the third identified pair, and the first
-- word that is computed rather than lifted off the execution environment.
-- `admissible_eq_false_of_lt_requiredWei` is the abstract half: `requiredWei` is
-- the right-hand side of the value conjunct of `Model.admissible`, so
-- underpayment refutes admissibility in both images.
-- `psubmit1_xi_rejected_reverts_of_reaches_feeGuard` composes them and drops
-- three assumptions from `psubmit1_xi_rejected_reverts_of_reaches_revertPush`:
-- the `PUSH2 @revert` is reached, the branch condition is computed, and
-- inadmissibility is derived. This still does **not** discharge
-- `A-ABSTRACT-TX`: `hreq` -- that the staged word *is* `requiredWei`, i.e. the
-- `fake_exponential` output -- remains a hypothesis, arriving at the fee guard
-- remains a hypothesis, four sites (deposit 67, 190, 204 and exit 66) still
-- branch on unidentified words, and the well-formedness half of `admissible` is
-- untouched -- so `EndpointAgrees` stays OPEN at HIGH. Carried under the
-- existing P-SUBMIT-1 ID with no new guarantee or assumption ID.
#print axioms Eip8282.Audit.XiTransport.feeGuard_pinned
#print axioms Eip8282.Audit.XiTransport.Z_LT
#print axioms Eip8282.Audit.XiTransport.step_LT
#print axioms Eip8282.Audit.XiTransport.xStepAt_LT
#print axioms Eip8282.Audit.XiTransport.stack_ltPost
#print axioms Eip8282.Audit.XiTransport.atRevertPush_of_atFeeGuard
#print axioms Eip8282.Audit.XiTransport.revert_exit_of_reaches_feeGuard
#print axioms Eip8282.Audit.XiTransport.admissible_eq_false_of_lt_requiredWei
#print axioms Eip8282.Audit.XiTransport.lt_bne_zero_of_toNat_lt
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_rejected_reverts_of_reaches_feeGuard
-- R4, *Eleven*: the inhibitor comparison and the inhibited branch of `userCall`.
-- `inhibitGuard_pinned` is `decide +kernel` / `decide` over the literals (the
-- `PUSH32` at `pc` whose immediate is `INHIBITOR`, the `EQ` at `pc + 33`, and
-- the membership of `pc + 37`), so it must show no `native_decide` receipt.
-- `stack_eqPost` is the equation identifying the condition word at deposit 67 /
-- exit 66 as the computed comparison `UInt256.eq INHIBITOR excess` -- the fourth
-- identified pair. Unlike *Ten* there is no `hreq`-shaped bridge:
-- `Model.inhibited` is *defined* as `decide (storedExcess = inhibitor)` and the
-- `PUSH32` immediate is that same `inhibitor`, so
-- `inhibited_iff_storedExcess_eq_inhibitor` and
-- `eq_inhibitor_bne_zero_of_inhibited` derive the taken branch from the very
-- hypothesis `psubmit1_exitAgrees_iff` is stated on.
-- `psubmit1_xi_inhibited_reverts_of_reaches_inhibitGuard` composes them and
-- drops two assumptions from
-- `psubmit1_xi_inhibited_reverts_of_reaches_revertPush`: the `PUSH2 @revert` is
-- reached, and the branch condition is computed. This still does **not**
-- discharge `A-ABSTRACT-TX`: arriving at the inhibitor guard remains a
-- hypothesis, `hreq` is untouched, two sites (deposit 190 and
-- 204) still branch on unidentified words, and the well-formedness half of
-- `admissible` is untouched -- so `EndpointAgrees` stays OPEN at HIGH. Carried
-- under the existing P-SUBMIT-1 ID with no new guarantee or assumption ID.
#print axioms Eip8282.Audit.XiTransport.inhibitGuard_pinned
#print axioms Eip8282.Audit.XiTransport.Z_PUSH32
#print axioms Eip8282.Audit.XiTransport.step_PUSH32
#print axioms Eip8282.Audit.XiTransport.xStepAt_PUSH32
#print axioms Eip8282.Audit.XiTransport.Z_EQ
#print axioms Eip8282.Audit.XiTransport.step_EQ
#print axioms Eip8282.Audit.XiTransport.xStepAt_EQ
#print axioms Eip8282.Audit.XiTransport.stack_eqPost
#print axioms Eip8282.Audit.XiTransport.atRevertPush_of_atInhibitGuard
#print axioms Eip8282.Audit.XiTransport.revert_exit_of_reaches_inhibitGuard
#print axioms Eip8282.Audit.XiTransport.inhibited_iff_storedExcess_eq_inhibitor
#print axioms Eip8282.Audit.XiTransport.eq_bne_zero_of_toNat_eq
#print axioms Eip8282.Audit.XiTransport.eq_inhibitor_bne_zero_of_inhibited
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_inhibited_reverts_of_reaches_inhibitGuard
-- R4, *Twelve*: the excess load, so the inhibitor guard's word is read rather
-- than assumed. `excessLoad_pinned` is `decide +kernel` over the literals -- the
-- `PUSH0`, `SLOAD` and `DUP1` three bytes before the guard, and the fact that
-- the third lands exactly on `inhibitGuardPc`, so no offset is asserted -- and
-- must therefore show no `native_decide` receipt. `sloadCost_le` bounds the
-- symbolic access-list-dependent `Csload` above by `Gcoldsload`, which keeps the
-- downstream gas hypotheses literal. `sload_excess_of_represents` identifies the
-- loaded word with `model.storedExcess` by unfolding `toModel` over the pinned
-- account's packed storage at slot 0, not by hypothesis.
-- `atInhibitGuard_of_atExcessLoad` composes the three iterations onto the guard,
-- and `psubmit1_xi_inhibited_reverts_of_reaches_excessLoad` is *Eleven*'s
-- theorem with `hexc` deleted, replaced by `Represents` at the load site plus
-- `codeOwner = targetAddr kind`. This still does **not** discharge
-- `A-ABSTRACT-TX`: arriving at the load site remains a hypothesis, `Represents`
-- is assumed there rather than transported from `c.entry`, and everything
-- *Eleven* left open is still open -- so `EndpointAgrees` stays OPEN at HIGH.
-- Carried under the existing P-SUBMIT-1 ID with no new guarantee or assumption
-- ID.
#print axioms Eip8282.Audit.XiTransport.excessLoad_pinned
#print axioms Eip8282.Audit.XiTransport.sloadCost_le
#print axioms Eip8282.Audit.XiTransport.Z_SLOAD
#print axioms Eip8282.Audit.XiTransport.step_SLOAD
#print axioms Eip8282.Audit.XiTransport.xStepAt_SLOAD
#print axioms Eip8282.Audit.XiTransport.Z_DUP1
#print axioms Eip8282.Audit.XiTransport.step_DUP1
#print axioms Eip8282.Audit.XiTransport.xStepAt_DUP1
#print axioms Eip8282.Audit.XiTransport.sload_excess_of_represents
#print axioms Eip8282.Audit.XiTransport.atInhibitGuard_of_atExcessLoad
#print axioms Eip8282.Audit.XiTransport.psubmit1_xi_inhibited_reverts_of_reaches_excessLoad
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

/-! ## Node R2 — whole user-call `Ξ` composition

R2 uses the kernel-checked `RunUntil` / `XRuns` decomposition and lands on the
complete `Ξ` message call through R4's unconditional wrapper and jumpdest
bridges, from an R1 `Represents` world at the entry machine. It never runs `Ξ`
itself, so none of the lines below may report a `native_decide` receipt — each
must show only the three foundational axioms. The final observation premise is
deliberately visible while `A-ABSTRACT-TX` remains open; no theorem here
introduces a project axiom, and no new parent IDs are registered.

`XiCall.code_pinned` fixes the code image only, so the abstract user step is
pinned to the call being made by `UserCallEnv`: `codeOwner = targetAddr kind`,
`sender` is the abstract caller, `bytes env.calldata` is the abstract calldata,
`env.weiValue.toNat` is the abstract wei value, and `sender ≠ SYSTEM_ADDR`
selects the user side of the runtimes' opening dispatch gate. Without it the
correspondence would hold of a model step unrelated to `c.env`.
`caller_ne_systemAddress` transports that last condition to the model level, so
`userStep` cannot silently denote a system call. This narrows what
`A-ABSTRACT-TX` is asked to cover; it does not discharge it. -/

#print axioms Eip8282.Audit.UserXiCorrespondence.caller_ne_systemAddress
#print axioms Eip8282.Audit.UserXiCorrespondence.whole_user_call_success
#print axioms Eip8282.Audit.UserXiCorrespondence.whole_user_call_revert
#print axioms Eip8282.Audit.UserXiCorrespondence.whole_user_call_xi_correspondence

/-! ## R3 — whole SYSTEM-call `Ξ` observational composition

The endpoint premise is the existing named OPEN `A-ABSTRACT-TX`; it is a
theorem argument, not a project axiom. -/

#print axioms Eip8282.Audit.SystemXiCorrespondence.whole_system_call_success
#print axioms Eip8282.Audit.SystemXiCorrespondence.whole_system_call_revert
#print axioms Eip8282.Audit.SystemXiCorrespondence.whole_system_call_xi_correspondence
#print axioms Eip8282.Audit.SystemXiCorrespondence.registeredParents
#print axioms Eip8282.Audit.SystemXiCorrespondence.whole_system_call_registered_correspondence

/-! ## The universal `Ξ ↔ Model` boundary

`Eip8282.Audit.UniversalBoundary` states the universal claim
(`UniversalXiCorrespondence`) and its combined residual (`UniversalClosure`)
side by side and proves them **equivalent**. The target includes both the
complete-call observation and post-account/storage refinement. Read the lines
below as a negative result: none of them is evidence that `Ξ` agrees with
`Model.step`.

The guard is spelled out rather than conventional. `PreCallRepresents` relates
the pre-transfer model state to the `Ξ` entry world (and is ordinary
`Represents` on system calls). Its append-room condition is branch-dependent:
it is required only when `Model.userCall` takes the successful append branch,
so fee getters and rejected submissions remain covered at the maximum
well-formed tail. The target reads
`PreCallRepresents σ s call → AdmissibleCall σ call → …`. `AdmissibleCall`
makes the rest named fields — `env` (the abstract step is this message call:
`UserCallBinding` binds a canonical user caller below `2^160` to the immediate
`CALLER` source, not transaction origin `sender`; `SystemCallBinding`
binds the `CALLER` source to `SYSTEM_ADDR` (origin again free), zero value and
the system flag `!env.calldata.isEmpty`; system calls and user appends require the writable
`CALL` environment `env.perm = true`, while read-only user branches also admit
`STATICCALL`), `gas_ge` / `fuel_ge` (30M gas and the 300000-step
universal fuel bound), and no arithmetic side condition. `WordExactCall.noWrap`
(`StepNoWrap`) is a separate branch-sensitive word-exactness witness for the
R5 support lemmas, not a guard on the campaign target: the model computes in
unbounded `Nat`, the pinned
runtimes in 256-bit words, and `WellFormed` bounds only the pointers. An enabled
user step needs `FeeQuoteNoWrap` — the `bump_excess` fold `effectiveExcess`
below `2^256` and, through `fakeExpoFitsWord`, every `ADD`/`MUL` intermediate of
the `fake_expo` loop that computes `Model.currentFee` below `2^256` with the
loop reaching `accum = 0` before the model's 256-iteration fuel is spent, the
pinned loop exiting only on `accum = 0`; an inhibited user step reverts before
any arithmetic. An enabled empty-calldata system step needs
`SLOT_EXCESS + SLOT_COUNT < 2^256`, the sum `update_excess` forms before the
target comparison; the nonempty-calldata latch and the inhibited clear store a
constant. Without any bound the well-formed image `wrapExcessImage`, excess
`2^256 - 2` and count `10`, was admissible while `PostStateAgrees` was
unsatisfiable there for every `Ξ` result, so the target was refutable rather
than open; a bound on the stored result alone still admitted `wrapWindowImage`,
excess `2^256 - 5` and count `10`, whose sum `2^256 + 5` wraps although the
result `2^256 - 3` fits; and a bound on the folded excess alone still admitted
`wideExcessImage`, excess `2^252`, whose fee loop wraps at its first `MUL`).
These images remain admitted by the campaign boundary: the renamed
`*_not_wordExact` canaries show that the support witness is unavailable, so
they are an explicit blocker to closing `A-ABSTRACT-TX`, not a hidden exclusion.
Termination is deliberately outside `AdmissibleCall`: `TerminationClosure` is
the separate assumption that every guarded call has a `Nonempty (XiHalts c)`.
Nothing in this repository proves that bound. On success, `PostStateAgrees`
checks the `Ξ` result's account map at the pinned predeploy against the model
post-state, preserves every `UInt256` storage key outside the modeled write set
(`StorageFrameAgrees`, quantified over map keys so that no slot number aliases
a control word), pins the four control words a system step leaves behind to
`Reachable.applySystem` (`ControlWordsAgree` / `SystemControlAgrees`: the
frame only exempted them, and `toModel` reads the pointers through `queueOf`
alone, so a full drain that left `HEAD = TAIL = 5` in place used to pass; now
both must be reset), requires an appended item to be the canonical padded
record (`CanonicalAppendedItem`), and fixes the log series (`LogsAgree`: the
entry substate's series plus the one anonymous `LOG0` receipt an accepted
submission publishes — `appendLogData`, the 184-byte deposit calldata or the
20-byte caller followed by the 48-byte exit pubkey — and nothing on a fee
getter or a system call, so P-SUBMIT-1's receipt is part of the universal
obligation rather than a separate residual; `postStateAgrees_append_log` /
`postStateAgrees_system_logs` read it back, `logsAgree_of_receipt` shows the
intended receipt satisfies it, and `logsAgree_rejects_empty_deposit_receipt` /
`logsAgree_rejects_silent_append` are the `PSubmit1Mutant` `LOG0`-size mutant
and a silent append as canaries); on revert it requires the model's rollback
state. The projection lemmas printed alongside the closure theorems
(`user_pretransfer_balance_and_append_room`, `system_call_value_zero`,
`user_call_source`, `system_call_source`, `admissible_call_writable`,
`storageFrameAgrees_iff_loadU256`, `system_post_control_words`,
`postStateAgrees_system_storage`, `system_represents_fields`,
`nextExcess_lt_size_of_stepNoWrap`, `admissible_system_noWrap`) only read
those guards back out; `drainHyp_of_admissible` hands the system-step guard to
every lemma R5 states under `DrainHyp`.
`applySystem_storageFrameAgrees` and `applySystem_systemControlAgrees` show the
transition R5 states satisfies the strengthened relation, so it is not vacuous,
and `admissible_system_applySystem_toModel` shows that transition abstracts to
exactly `Model.step` at every represented system call that also carries the
word-exact witness `WordExactCall` — not at every admissible call:
`wrapExcessImage_applySystem_ne_step` proves the equality false on a
high-excess image the universal boundary retains;
`system_post_storage_eq_applySystem` shows the frame and the control words
together fix the committed system post-image at every key;
`system_full_drain_resets_pointers`, `full_drain_nonzero_pointer_rejected` and
the finite canary `stalePointerImage_rejected` are the regression for the
exempted-pointer ambiguity; `wrapExcessImage_wellFormed`,
`wrapExcessImage_not_noWrap`, `wrapExcessImage_nextExcess`,
`wrapExcessImage_applySystem_excess`, `wrapExcessImage_applySystem_ne_step`,
`wrapExcessImage_postState_unsatisfiable` and the canary
`wrapExcessImage_not_wordExact` is the regression for the excess-word
wraparound: the image is well-formed, the model's next excess is `2^256`, the
stored word is `0`, no `Ξ` result satisfies the post-state relation there, and
the separate word-exact witness now rejects the call; `wrapWindowImage_result_fits`,
`wrapWindowImage_not_noWrap` and the canary `wrapWindowImage_not_wordExact`
are the regression for the system-side intermediate, where the stored result
fits the word but the pinned `ADD` that computes it does not;
`wideExcessImage_excess_fits`, `wideExcessImage_not_noWrap` and the canary
`wideExcessImage_not_wordExact` are the regression for the fee loop's
intermediates, where the folded excess fits the word but the loop's first `MUL`
does not; `feeQuoteNoWrap_examples` shows the user-side guard admits the
specified deployment state and an ordinary enabled image, and
`fakeExpoFitsWord_fuel_boundary` that its fuel conjunct is load-bearing at
folded excess `1607` / `1608` without any word wrapping. None of them runs `Ξ`.

`universal_iff_endpointClosure` is the whole point, and it cuts both ways.
Left-to-right, the universal correspondence *entails* termination and the
endpoint/post-state residual, so
`A-ABSTRACT-TX` is not an artefact of how R2/R3/R4 staged their proofs and
cannot be routed around by restating the goal. `UniversalClosure` is not proved
here, and nothing in this repository proves it.

Each line must show only the three foundational axioms: no `native_decide`
receipt (nothing here runs `Ξ`), no `sorryAx`, no project axiom. `A-ABSTRACT-TX`
stays OPEN at HIGH and `A-PINNED-SOURCE` stays OPEN; no new parent ID is
registered. -/

#print axioms Eip8282.Audit.UniversalBoundary.user_pretransfer_balance_and_append_room
#print axioms Eip8282.Audit.UniversalBoundary.system_call_value_zero
#print axioms Eip8282.Audit.UniversalBoundary.user_call_source
#print axioms Eip8282.Audit.UniversalBoundary.system_call_source
#print axioms Eip8282.Audit.UniversalBoundary.admissible_call_writable
#print axioms Eip8282.Audit.UniversalBoundary.storageFrameAgrees_iff_loadU256
#print axioms Eip8282.Audit.UniversalBoundary.applySystem_storageFrameAgrees
#print axioms Eip8282.Audit.UniversalBoundary.applySystem_systemControlAgrees
#print axioms Eip8282.Audit.UniversalBoundary.system_post_storage_eq_applySystem
#print axioms Eip8282.Audit.UniversalBoundary.system_post_control_words
#print axioms Eip8282.Audit.UniversalBoundary.system_full_drain_resets_pointers
#print axioms Eip8282.Audit.UniversalBoundary.full_drain_nonzero_pointer_rejected
#print axioms Eip8282.Audit.UniversalBoundary.stalePointerImage_rejected
#print axioms Eip8282.Audit.UniversalBoundary.postStateAgrees_system_storage
#print axioms Eip8282.Audit.UniversalBoundary.postStateAgrees_append_log
#print axioms Eip8282.Audit.UniversalBoundary.postStateAgrees_system_logs
#print axioms Eip8282.Audit.UniversalBoundary.logsAgree_of_receipt
#print axioms Eip8282.Audit.UniversalBoundary.logsAgree_rejects_empty_deposit_receipt
#print axioms Eip8282.Audit.UniversalBoundary.logsAgree_rejects_silent_append
#print axioms Eip8282.Audit.UniversalBoundary.system_represents_fields
#print axioms Eip8282.Audit.UniversalBoundary.nextExcess_lt_size_of_stepNoWrap
#print axioms Eip8282.Audit.UniversalBoundary.admissible_system_noWrap
#print axioms Eip8282.Audit.UniversalBoundary.drainHyp_of_admissible
#print axioms Eip8282.Audit.UniversalBoundary.admissible_system_applySystem_toModel
#print axioms Eip8282.Audit.UniversalBoundary.wrapExcessImage_wellFormed
#print axioms Eip8282.Audit.UniversalBoundary.wrapExcessImage_not_noWrap
#print axioms Eip8282.Audit.UniversalBoundary.wrapExcessImage_nextExcess
#print axioms Eip8282.Audit.UniversalBoundary.wrapExcessImage_applySystem_excess
#print axioms Eip8282.Audit.UniversalBoundary.wrapExcessImage_applySystem_ne_step
#print axioms Eip8282.Audit.UniversalBoundary.wrapExcessImage_postState_unsatisfiable
#print axioms Eip8282.Audit.UniversalBoundary.wrapExcessImage_not_wordExact
#print axioms Eip8282.Audit.UniversalBoundary.wrapWindowImage_result_fits
#print axioms Eip8282.Audit.UniversalBoundary.wrapWindowImage_not_noWrap
#print axioms Eip8282.Audit.UniversalBoundary.wrapWindowImage_not_wordExact
#print axioms Eip8282.Audit.UniversalBoundary.wideExcessImage_excess_fits
#print axioms Eip8282.Audit.UniversalBoundary.wideExcessImage_not_noWrap
#print axioms Eip8282.Audit.UniversalBoundary.wideExcessImage_not_wordExact
#print axioms Eip8282.Audit.UniversalBoundary.feeQuoteNoWrap_examples
#print axioms Eip8282.Audit.UniversalBoundary.fakeExpoFitsWord_fuel_boundary
#print axioms Eip8282.Audit.UniversalBoundary.observation_of_halts
#print axioms Eip8282.Audit.UniversalBoundary.endpointObligation_iff_endpointAgrees
#print axioms Eip8282.Audit.UniversalBoundary.correspondence_iff_exitAgrees
#print axioms Eip8282.Audit.UniversalBoundary.xi_correspondence_of_admissible
#print axioms Eip8282.Audit.UniversalBoundary.universal_of_endpointClosure
#print axioms Eip8282.Audit.UniversalBoundary.endpointClosure_of_universal
#print axioms Eip8282.Audit.UniversalBoundary.universal_iff_endpointClosure

/-! ## ENTRY-REACH (Eip8282.Audit.EntryReach)

The symbolic-execution layer and the completed paths from `c.entry`. Every line
must show only the three foundational axioms. `SymExec.pureStep_sound` validates
the pure-opcode table against `EvmYul.step` once; `xRuns_symBlock` is the one
soundness theorem every generated block lemma goes through; the endpoint theorems
of `EntryReach.Deposit` / `EntryReach.Exit` chain those with the kernel-checked
decodes of the pinned images; `xiHalts_of_ends` and `observe_of_ends` turn a
completed path into the `XiHalts` witness and the whole-call observation with no
`EndpointAgrees` and no `hend`. `Deposit.halts` / `Exit.halts` cover the endpoint
partition. Their hypotheses — fee-loop termination on words (`FeeLoopEnds`), gas,
fuel and write permission — are the residual of this slice and are not closed
here; `A-ABSTRACT-TX` stays OPEN at HIGH and no new parent ID is registered. -/

#print axioms Eip8282.Audit.SymExec.pureStep_sound
#print axioms Eip8282.Audit.SymExec.xRuns_symBlock
#print axioms Eip8282.Audit.EntryReach.xiHalts_of_ends
#print axioms Eip8282.Audit.EntryReach.observe_of_ends
#print axioms Eip8282.Audit.EntryReach.Deposit.user_inhibited
#print axioms Eip8282.Audit.EntryReach.Deposit.user_badsize_reverts
#print axioms Eip8282.Audit.EntryReach.Deposit.user_paidGetter_reverts
#print axioms Eip8282.Audit.EntryReach.Deposit.user_getter_returns
#print axioms Eip8282.Audit.EntryReach.Deposit.user_underpay_reverts
#print axioms Eip8282.Audit.EntryReach.Deposit.user_amountFloor_reverts
#print axioms Eip8282.Audit.EntryReach.Deposit.user_stake_reverts
#print axioms Eip8282.Audit.EntryReach.Deposit.user_append_stops
#print axioms Eip8282.Audit.EntryReach.Deposit.system_returns
#print axioms Eip8282.Audit.EntryReach.Deposit.halts
#print axioms Eip8282.Audit.EntryReach.Deposit.observe_getter
#print axioms Eip8282.Audit.EntryReach.Deposit.observe_system
#print axioms Eip8282.Audit.EntryReach.Exit.user_inhibited
#print axioms Eip8282.Audit.EntryReach.Exit.user_badsize_reverts
#print axioms Eip8282.Audit.EntryReach.Exit.user_paidGetter_reverts
#print axioms Eip8282.Audit.EntryReach.Exit.user_getter_returns
#print axioms Eip8282.Audit.EntryReach.Exit.user_underpay_reverts
#print axioms Eip8282.Audit.EntryReach.Exit.user_append_stops
#print axioms Eip8282.Audit.EntryReach.Exit.system_returns
#print axioms Eip8282.Audit.EntryReach.Exit.halts
#print axioms Eip8282.Audit.EntryReach.Exit.observe_getter
#print axioms Eip8282.Audit.EntryReach.Exit.observe_system

/-! ## OPERANDS (Eip8282.Audit.EntryReach.Words / Fee / Operands)

The branch words of ENTRY-REACH read back as the model's operands. `Words`
reads `CALLER`, `CALLVALUE`, `CALLDATASIZE`, `CALLDATALOAD` and `SLOAD` off the
call's `ExecutionEnv` and entry account (definitional, plus the arithmetic of
words that do not wrap); `Fee` marches `Path.feeExit` alongside
`Model.fakeExponential.go` under `fakeExpoFitsWord`; `Operands` binds them
through `PreCallRepresents` / `AdmissibleCall`: `userWords`, `fee_of_noWrap`
(the `FeeLoopEnds` premise discharged from `WordExactCall`), `admissible_iff`,
`userCall_append`, and `halts_of_admissible` — every admissible, word-exact call
whose calldata fits a word halts, i.e. the `TerminationClosure` shape with those
two premises explicit. The system words `toNat_drainWord`, `full_drain_iff` and
`toNat_newExcess` read `drainCount` / `applySystem`'s pointer test /
`nextExcessOf` off the entry image. Every line must show only the three
foundational axioms; `A-ABSTRACT-TX` stays OPEN at HIGH and no new parent ID is
registered. -/

#print axioms Eip8282.Audit.EntryReach.toNat_calldataload
#print axioms Eip8282.Audit.EntryReach.toNat_amount
#print axioms Eip8282.Audit.EntryReach.callerW_eq_sysW_iff
#print axioms Eip8282.Audit.EntryReach.slotW_entry
#print axioms Eip8282.Audit.EntryReach.feeExit_of_fits
#print axioms Eip8282.Audit.EntryReach.Deposit.userWords
#print axioms Eip8282.Audit.EntryReach.Deposit.fee_of_noWrap
#print axioms Eip8282.Audit.EntryReach.Deposit.admissible_iff
#print axioms Eip8282.Audit.EntryReach.Deposit.userCall_append
#print axioms Eip8282.Audit.EntryReach.Deposit.halts_of_admissible
#print axioms Eip8282.Audit.EntryReach.Deposit.systemWords
#print axioms Eip8282.Audit.EntryReach.Deposit.toNat_drainWord
#print axioms Eip8282.Audit.EntryReach.Deposit.full_drain_iff
#print axioms Eip8282.Audit.EntryReach.Deposit.toNat_newExcess
#print axioms Eip8282.Audit.EntryReach.Exit.userWords
#print axioms Eip8282.Audit.EntryReach.Exit.fee_of_noWrap
#print axioms Eip8282.Audit.EntryReach.Exit.admissible_iff
#print axioms Eip8282.Audit.EntryReach.Exit.userCall_append
#print axioms Eip8282.Audit.EntryReach.Exit.halts_of_admissible
#print axioms Eip8282.Audit.EntryReach.Exit.systemWords
#print axioms Eip8282.Audit.EntryReach.Exit.toNat_drainWord
#print axioms Eip8282.Audit.EntryReach.Exit.full_drain_iff
#print axioms Eip8282.Audit.EntryReach.Exit.toNat_newExcess

/-! ## ENDPOINT (Eip8282.Audit.EntryReach.Endpoint)

The fee-getter `MSTORE 0 fee; RETURN 0 32` return slice is now connected to
the model's `toBeBytes fee 32` encoder. The inhibited, paid-getter,
malformed-calldata, underpaid, deposit amount-floor, and deposit stake user
branches are likewise connected to the model's empty-data revert; accepted
appends are connected to its empty success observation. These are
observation-only receipts;
the drain-record encoding and every committed post-state obligation remain open,
so `A-ABSTRACT-TX` stays OPEN at HIGH. -/

#print axioms Eip8282.Audit.EntryReach.Endpoint.getter_mstore_bytes
#print axioms Eip8282.Audit.EntryReach.Endpoint.deposit_system_drain_observes_width
#print axioms Eip8282.Audit.EntryReach.Endpoint.exit_system_drain_observes_width
#print axioms Eip8282.Audit.EntryReach.Endpoint.deposit_inhibited_observes_model
#print axioms Eip8282.Audit.EntryReach.Endpoint.exit_inhibited_observes_model
#print axioms Eip8282.Audit.EntryReach.Endpoint.deposit_paidGetter_observes_model
#print axioms Eip8282.Audit.EntryReach.Endpoint.exit_paidGetter_observes_model
#print axioms Eip8282.Audit.EntryReach.Endpoint.deposit_badsize_observes_model
#print axioms Eip8282.Audit.EntryReach.Endpoint.exit_badsize_observes_model
#print axioms Eip8282.Audit.EntryReach.Endpoint.deposit_underpay_observes_model
#print axioms Eip8282.Audit.EntryReach.Endpoint.exit_underpay_observes_model
#print axioms Eip8282.Audit.EntryReach.Endpoint.deposit_amountFloor_observes_model
#print axioms Eip8282.Audit.EntryReach.Endpoint.deposit_stake_observes_model
#print axioms Eip8282.Audit.EntryReach.Endpoint.deposit_append_observes_model
#print axioms Eip8282.Audit.EntryReach.Endpoint.exit_append_observes_model
#print axioms Eip8282.Audit.EntryReach.Endpoint.deposit_getter_observes_model
#print axioms Eip8282.Audit.EntryReach.Endpoint.exit_getter_observes_model

/-! ## Direct-guarantee components (9 September 2026)

These are new modular results, not replacements for the historical registered
parents. The complete three guarantees remain open as recorded in
`audit/DIRECT-CLOSURE.md`. These declarations must use only standard Lean axioms;
the historical finite native interpreter receipts above are separate.
-/
#print axioms Eip8282.Audit.EntryReach.quoteWithin_stable
#print axioms Eip8282.Audit.EntryReach.quoteWithin_unique
#print axioms Eip8282.Audit.EntryReach.quoteCompletes_deposit_fee_loop
#print axioms Eip8282.Audit.Integrator.MathFee.feeExitNat_terminates
#print axioms Eip8282.Audit.Integrator.MathFee.mathQuoteCompletes_existsUnique
#print axioms Eip8282.Audit.Integrator.MathFee.feeExit_corresponds
#print axioms Eip8282.Audit.Integrator.MathFee.quoteWithin_corresponds
#print axioms Eip8282.Audit.Integrator.ControlSpec.feeInput_toNat
#print axioms Eip8282.Audit.Integrator.ControlSpec.foldWord_toNat
#print axioms Eip8282.Audit.Integrator.ControlSpec.systemExcess_eq_nat_of_sum_lt
#print axioms Eip8282.Audit.Integrator.ControlSpec.wrap_before_subtract_counterexample
#print axioms Eip8282.Audit.Integrator.MessageCall.result_eq_settle
#print axioms Eip8282.Audit.Integrator.MessageCall.failure_restores_journal
#print axioms Eip8282.Audit.Integrator.ReachableCalls.transition_failure_journal
#print axioms Eip8282.Audit.Integrator.ReachableCalls.transition_not_outOfFuel
#print axioms Eip8282.Audit.Integrator.CallBridge.commits_endpoint
#print axioms Eip8282.Audit.Integrator.CallBridge.rolls_back_endpoint
#print axioms Eip8282.Audit.Integrator.EndpointState.deposit_getter_preserves_state
#print axioms Eip8282.Audit.Integrator.EndpointState.exit_getter_preserves_state
#print axioms Eip8282.Audit.Integrator.EndpointState.deposit_append_result
#print axioms Eip8282.Audit.Integrator.EndpointState.exit_append_result
#print axioms Eip8282.Audit.Integrator.EndpointState.deposit_system_result
#print axioms Eip8282.Audit.Integrator.EndpointState.exit_system_result
#print axioms Eip8282.Audit.Integrator.AppendSpec.deposit_submission_receipt
#print axioms Eip8282.Audit.Integrator.RejectionSpec.deposit_inhibited_call
#print axioms Eip8282.Audit.Integrator.RejectionSpec.exit_inhibited_call
#print axioms Eip8282.Audit.Integrator.SystemSpec.deposit_system_storage_result
#print axioms Eip8282.Audit.Integrator.SystemSpec.exit_system_storage_result
#print axioms Eip8282.Audit.Integrator.SystemSpec.expectedSlot_record
#print axioms Eip8282.Audit.Integrator.WorldNonempty.beq_empty_false_of_get_some
#print axioms Eip8282.Audit.Integrator.CommittedSystem.deposit_system_commits
#print axioms Eip8282.Audit.Integrator.CommittedSystem.exit_system_commits

-- Additional conditional complete-call and record evidence; public closure remains open.
#print axioms Eip8282.Audit.Integrator.GetterCall.deposit_getter
#print axioms Eip8282.Audit.Integrator.GetterCall.exit_getter
#print axioms Eip8282.Audit.Integrator.AppendStorage.deposit_storage_result
#print axioms Eip8282.Audit.Integrator.AppendStorage.exit_storage_result
#print axioms Eip8282.Audit.Integrator.ExitRecord.submission_receipt
#print axioms Eip8282.Audit.Integrator.ExitDrain.exit_system_fifo

#print axioms Eip8282.Audit.Integrator.CommittedAppend.deposit_append_commits
#print axioms Eip8282.Audit.Integrator.CommittedAppend.exit_append_commits
#print axioms Eip8282.Audit.Integrator.SubmissionCall.deposit_checks
#print axioms Eip8282.Audit.Integrator.SubmissionCall.deposit_submission
#print axioms Eip8282.Audit.Integrator.SubmissionCall.exit_submission
#print axioms Eip8282.Audit.Integrator.QueueArithmetic.deposit_system_queue
#print axioms Eip8282.Audit.Integrator.QueueArithmetic.exit_system_queue
#print axioms Eip8282.Audit.Integrator.DepositDrain.amount_reversed
#print axioms Eip8282.Audit.Integrator.DepositDrain.deposit_system_fifo
#print axioms Eip8282.Audit.Integrator.RejectionCases.deposit_invalid_input
#print axioms Eip8282.Audit.Integrator.RejectionCases.exit_invalid_input

#print axioms Eip8282.Audit.Integrator.Initialization.deposit_initializes
#print axioms Eip8282.Audit.Integrator.Initialization.exit_initializes
#print axioms Eip8282.Audit.Integrator.Initialization.deposit_enabled
#print axioms Eip8282.Audit.Integrator.Initialization.exit_inhibited
#print axioms Eip8282.Audit.Integrator.CallSuccess.codeCall_of_success
#print axioms Eip8282.Audit.Integrator.SuccessInversion.deposit_user_success_quote
#print axioms Eip8282.Audit.Integrator.SuccessInversion.exit_user_success_quote
#print axioms Eip8282.Audit.Integrator.SuccessfulQuote.deposit_quote_of_success
#print axioms Eip8282.Audit.Integrator.SuccessfulQuote.exit_quote_of_success
#print axioms Eip8282.Audit.Integrator.QueueInvariant.represents_append
#print axioms Eip8282.Audit.Integrator.QueueInvariant.represents_drain
#print axioms Eip8282.Audit.Integrator.QueueInvariant.source_width_append
#print axioms Eip8282.Audit.Integrator.QueueInvariant.deposit_system_fifo
#print axioms Eip8282.Audit.Integrator.QueueInvariant.exit_system_fifo
#print axioms Eip8282.Audit.Integrator.ResourceBounds.total_lt
#print axioms Eip8282.Audit.Integrator.ResourceBounds.appendFits_of_accounted
#print axioms Eip8282.Audit.Integrator.ResourceBounds.control_sum_fits

-- Actual-success necessities and an explicitly bounded mathematical tariff.
#print axioms Eip8282.Audit.Integrator.TransferFrame.entry_storage
#print axioms Eip8282.Audit.Integrator.TransferFrame.entry_existing_account
#print axioms Eip8282.Audit.Integrator.TransferFrame.codeCall_storage_invariant
#print axioms Eip8282.Audit.Integrator.TransferFrame.pinned_installed_at_entry
#print axioms Eip8282.Audit.Integrator.TransferFrame.pinned_codeCall_hasOwner
#print axioms Eip8282.Audit.Integrator.AdmissionInversion.deposit_user_success_inputs
#print axioms Eip8282.Audit.Integrator.AdmissionInversion.exit_user_success_inputs
#print axioms Eip8282.Audit.Integrator.AdmissionInversion.success_effect
#print axioms Eip8282.Audit.Integrator.AdmissionInversion.success_return_bytes
#print axioms Eip8282.Audit.Integrator.AdmissionInversion.deposit_getter_suffix
#print axioms Eip8282.Audit.Integrator.AdmissionInversion.exit_getter_suffix
#print axioms Eip8282.Audit.Integrator.AdmissionInversion.deposit_fee_exit
#print axioms Eip8282.Audit.Integrator.AdmissionInversion.exit_fee_exit
#print axioms Eip8282.Audit.Integrator.AdmissionInversion.deposit_guard
#print axioms Eip8282.Audit.Integrator.AdmissionInversion.exit_guard
#print axioms Eip8282.Audit.Integrator.AdmissionInversion.deposit_user_success
#print axioms Eip8282.Audit.Integrator.AdmissionInversion.exit_user_success
#print axioms Eip8282.Audit.Integrator.FeeSafeDomain.domain_certificate
#print axioms Eip8282.Audit.Integrator.FeeSafeDomain.safe_quote
#print axioms Eip8282.Audit.Integrator.FeeSafeDomain.any_quote_agrees
#print axioms Eip8282.Audit.Integrator.FeeSafeDomain.operational_quote_agrees
#print axioms Eip8282.Audit.Integrator.FeeSafeDomain.prefixFits_mono
#print axioms Eip8282.Audit.Integrator.FeeSafeDomain.completes_mono
#print axioms Eip8282.Audit.Integrator.FeeSafeDomain.upper_fits
#print axioms Eip8282.Audit.Integrator.FeeSafeDomain.upper_stops
#print axioms Eip8282.Audit.Integrator.FeeBoundary.natural_quote
#print axioms Eip8282.Audit.Integrator.FeeBoundary.word_quote
#print axioms Eip8282.Audit.Integrator.FeeBoundary.word_price_not_mathematical
#print axioms Eip8282.Audit.Integrator.FeeBoundary.local_fee_drop
#print axioms Eip8282.Audit.Integrator.FeeBoundary.operational_counterexample
#print axioms Eip8282.Audit.Integrator.SuccessfulUser.deposit_admission
#print axioms Eip8282.Audit.Integrator.SuccessfulUser.exit_admission
#print axioms Eip8282.Audit.Integrator.SuccessfulUser.deposit_getter_math
#print axioms Eip8282.Audit.Integrator.SuccessfulUser.exit_getter_math
#print axioms Eip8282.Audit.Integrator.GetterInversion.return_state
#print axioms Eip8282.Audit.Integrator.GetterInversion.deposit_xi_readonly
#print axioms Eip8282.Audit.Integrator.GetterInversion.exit_xi_readonly
#print axioms Eip8282.Audit.Integrator.GetterInversion.deposit_getter_readonly
#print axioms Eip8282.Audit.Integrator.GetterInversion.exit_getter_readonly
#print axioms Eip8282.Audit.Integrator.UniversalGate.deposit_inhibited
#print axioms Eip8282.Audit.Integrator.UniversalGate.exit_inhibited

#print axioms Eip8282.Audit.Integrator.CreationSettlement.result_eq_settle
#print axioms Eip8282.Audit.Integrator.CreationSettlement.failed_deposit_result
#print axioms Eip8282.Audit.Integrator.CreationSettlement.success_inversion
#print axioms Eip8282.Audit.Integrator.CreationSettlement.install_storage
#print axioms Eip8282.Audit.Integrator.CreationSettlement.entry_storage
#print axioms Eip8282.Audit.Integrator.CreationSettlement.deposit_creation
#print axioms Eip8282.Audit.Integrator.CreationSettlement.exit_creation

-- Actual append/rejection necessities and conditional invariant preservation.
#print axioms Eip8282.Audit.Integrator.AccountedState.initial
#print axioms Eip8282.Audit.Integrator.AccountedState.mono
#print axioms Eip8282.Audit.Integrator.AccountedState.append_fits
#print axioms Eip8282.Audit.Integrator.AccountedState.append
#print axioms Eip8282.Audit.Integrator.AccountedState.system_control
#print axioms Eip8282.Audit.Integrator.AccountedState.system
#print axioms Eip8282.Audit.Integrator.FundedDomain.boundary_price
#print axioms Eip8282.Audit.Integrator.FundedDomain.paid_append_safe
#print axioms Eip8282.Audit.Integrator.FundedDomain.system_safe
#print axioms Eip8282.Audit.Integrator.FundedDomain.expected_append_safe
#print axioms Eip8282.Audit.Integrator.FundedDomain.deposit_submission_safe
#print axioms Eip8282.Audit.Integrator.FundedDomain.exit_submission_safe
#print axioms Eip8282.Audit.Integrator.FundedDomain.deposit_system_safe
#print axioms Eip8282.Audit.Integrator.FundedDomain.exit_system_safe
#print axioms Eip8282.Audit.Integrator.UniversalRejection.deposit_feeInput
#print axioms Eip8282.Audit.Integrator.UniversalRejection.exit_feeInput
#print axioms Eip8282.Audit.Integrator.UniversalRejection.deposit_invalid
#print axioms Eip8282.Audit.Integrator.UniversalRejection.exit_invalid
#print axioms Eip8282.Audit.Integrator.UniversalRejection.deposit_amount_lt_one
#print axioms Eip8282.Audit.Integrator.AppendInversion.sstore_success
#print axioms Eip8282.Audit.Integrator.AppendInversion.mstore_success
#print axioms Eip8282.Audit.Integrator.AppendInversion.copy_success
#print axioms Eip8282.Audit.Integrator.AppendInversion.log_success
#print axioms Eip8282.Audit.Integrator.AppendInversion.stop_success
#print axioms Eip8282.Audit.Integrator.AppendInversion.deposit_suffix
#print axioms Eip8282.Audit.Integrator.AppendInversion.deposit_user_result
#print axioms Eip8282.Audit.Integrator.AppendInversion.deposit_user_receipt
#print axioms Eip8282.Audit.Integrator.AppendInversion.exit_suffix
#print axioms Eip8282.Audit.Integrator.AppendInversion.exit_user_result
#print axioms Eip8282.Audit.Integrator.AppendInversion.exit_user_receipt
#print axioms Eip8282.Audit.Integrator.SuccessfulAppend.commit_receipt
#print axioms Eip8282.Audit.Integrator.SuccessfulAppend.deposit_append
#print axioms Eip8282.Audit.Integrator.SuccessfulAppend.exit_append
#print axioms Eip8282.Audit.Integrator.SuccessfulAppend.deposit_paid_append
#print axioms Eip8282.Audit.Integrator.SuccessfulAppend.exit_paid_append

-- One-step invariants from actual completed user calls.
#print axioms Eip8282.Audit.Integrator.UserStateInvariant.exit_user
#print axioms Eip8282.Audit.Integrator.UserStateInvariant.deposit_user
#print axioms Eip8282.Audit.Integrator.UserQueueInvariant.preserves_prefix
#print axioms Eip8282.Audit.Integrator.UserQueueInvariant.deposit_user
#print axioms Eip8282.Audit.Integrator.UserQueueInvariant.exit_user
#print axioms Eip8282.Audit.Integrator.UserQueueInvariant.exit_source_width

-- Initial invariants, actual SYSTEM inversion, and conditional gas traces.
#print axioms Eip8282.Audit.Integrator.InitializedInvariant.zero_of_absent
#print axioms Eip8282.Audit.Integrator.InitializedInvariant.initial_invariant
#print axioms Eip8282.Audit.Integrator.InitializedInvariant.deposit_creation
#print axioms Eip8282.Audit.Integrator.InitializedInvariant.exit_creation
#print axioms Eip8282.Audit.Integrator.ActualAppendGas.accepted_gas
#print axioms Eip8282.Audit.Integrator.ActualAppendGas.accepted_step_debit
#print axioms Eip8282.Audit.Integrator.ActualAppendGas.success_log_debit
#print axioms Eip8282.Audit.Integrator.ActualAppendGas.xruns_debit
#print axioms Eip8282.Audit.Integrator.ActualAppendGas.exit_log_site
#print axioms Eip8282.Audit.Integrator.ActualAppendGas.deposit_log_site
#print axioms Eip8282.Audit.Integrator.ActualAppendGas.trace_log_debit
#print axioms Eip8282.Audit.Integrator.ActualAppendGas.success_final_step_debit
#print axioms Eip8282.Audit.Integrator.ActualAppendGas.xi_log_debit
#print axioms Eip8282.Audit.Integrator.ActualAppendGas.theta_log_debit
#print axioms Eip8282.Audit.Integrator.SystemInversion.exit_prefix
#print axioms Eip8282.Audit.Integrator.SystemInversion.exit_body
#print axioms Eip8282.Audit.Integrator.SystemInversion.exit_loop
#print axioms Eip8282.Audit.Integrator.SystemInversion.exit_head
#print axioms Eip8282.Audit.Integrator.SystemInversion.exit_store_return
#print axioms Eip8282.Audit.Integrator.SystemInversion.exit_excess
#print axioms Eip8282.Audit.Integrator.SystemInversion.exit_final
#print axioms Eip8282.Audit.Integrator.SystemInversion.exit_system_result
#print axioms Eip8282.Audit.Integrator.SystemInversion.exit_system_storage
#print axioms Eip8282.Audit.Integrator.SystemInversion.mstore8_success
#print axioms Eip8282.Audit.Integrator.SystemInversion.deposit_prefix
#print axioms Eip8282.Audit.Integrator.SystemInversion.deposit_body
#print axioms Eip8282.Audit.Integrator.SystemInversion.deposit_loop
#print axioms Eip8282.Audit.Integrator.SystemInversion.deposit_head
#print axioms Eip8282.Audit.Integrator.SystemInversion.deposit_store_return
#print axioms Eip8282.Audit.Integrator.SystemInversion.deposit_excess
#print axioms Eip8282.Audit.Integrator.SystemInversion.deposit_final
#print axioms Eip8282.Audit.Integrator.SystemInversion.deposit_system_result
#print axioms Eip8282.Audit.Integrator.SystemInversion.deposit_system_storage

-- Complete-call SYSTEM effects and concrete-history preservation.
#print axioms Eip8282.Audit.Integrator.SuccessfulSystem.owner_final
#print axioms Eip8282.Audit.Integrator.SuccessfulSystem.exit_system
#print axioms Eip8282.Audit.Integrator.SuccessfulSystem.deposit_system
#print axioms Eip8282.Audit.Integrator.SystemStateInvariant.exit_system
#print axioms Eip8282.Audit.Integrator.SystemStateInvariant.deposit_system
#print axioms Eip8282.Audit.Integrator.SystemStateInvariant.exit_state
#print axioms Eip8282.Audit.Integrator.SystemStateInvariant.deposit_state
#print axioms Eip8282.Audit.Integrator.ConcreteHistory.deposit_from_creation
#print axioms Eip8282.Audit.Integrator.ConcreteHistory.exit_from_creation
#print axioms Eip8282.Audit.Integrator.ConcreteHistory.forget
#print axioms Eip8282.Audit.Integrator.ConcreteHistory.transition_preserves
#print axioms Eip8282.Audit.Integrator.ConcreteHistory.preserves

-- Actual append gas bounds and transaction-refund observation.
#print axioms Eip8282.Audit.Integrator.AppendGasPath.traced_symBlock
#print axioms Eip8282.Audit.Integrator.AppendGasPath.traced_exit_fee
#print axioms Eip8282.Audit.Integrator.AppendGasPath.traced_exit_entry
#print axioms Eip8282.Audit.Integrator.AppendGasPath.exit_suffix_path
#print axioms Eip8282.Audit.Integrator.AppendGasPath.exit_log_path
#print axioms Eip8282.Audit.Integrator.AppendGasPath.exit_theta_debit
#print axioms Eip8282.Audit.Integrator.AppendGasPath.traced_deposit_fee
#print axioms Eip8282.Audit.Integrator.AppendGasPath.traced_deposit_entry
#print axioms Eip8282.Audit.Integrator.AppendGasPath.deposit_suffix_path
#print axioms Eip8282.Audit.Integrator.AppendGasPath.deposit_log_path
#print axioms Eip8282.Audit.Integrator.AppendGasPath.deposit_theta_debit
#print axioms Eip8282.Audit.Integrator.RefundAccounting.refund_toNat
#print axioms Eip8282.Audit.Integrator.RefundAccounting.returned_toNat
#print axioms Eip8282.Audit.Integrator.RefundAccounting.net_toNat
#print axioms Eip8282.Audit.Integrator.RefundAccounting.count_le_net
#print axioms Eip8282.Audit.Integrator.RefundAccounting.result_observation
#print axioms Eip8282.Audit.Integrator.RefundAccounting.result_inversion
#print axioms Eip8282.Audit.Integrator.RefundAccounting.entryGas_toNat
#print axioms Eip8282.Audit.Integrator.RefundAccounting.count_le_transaction_gas
#print axioms Eip8282.Audit.Integrator.RefundAccounting.count_le_transaction_gas_of_entry

-- Independent direct specifications and actual CALL gas settlement.
#print axioms Eip8282.Audit.Integrator.CallGasAccounting.call_child_result_gas
#print axioms Eip8282.Audit.Integrator.CallGasAccounting.accepted_call_child_debit
#print axioms Eip8282.Audit.Integrator.CallGasAccounting.call_denied_gas
#print axioms Eip8282.Audit.Integrator.CallDispatchGas.step_call_helper
#print axioms Eip8282.Audit.Integrator.CallDispatchGas.accepted_step_call_debit
#print axioms Eip8282.Audit.Integrator.CallDispatchGas.accepted_step_call_denied_debit
#print axioms Eip8282.Audit.Integrator.FundingBounds.credits_lt_funding
#print axioms Eip8282.Audit.Integrator.FundingBounds.flexible_credits_lt_funding
#print axioms Eip8282.Audit.Integrator.FundingBounds.value_lt_funding_of_credits
#print axioms Eip8282.Audit.Integrator.AppendDataSpec.expected_eq
#print axioms Eip8282.Audit.Integrator.AppendDataSpec.storagePost_iff
#print axioms Eip8282.Audit.Integrator.AppendDataSpec.authenticLog_iff
#print axioms Eip8282.Audit.Integrator.DirectAdmission.exit_admission
#print axioms Eip8282.Audit.Integrator.DirectAdmission.deposit_admission
#print axioms Eip8282.Audit.Integrator.DirectAdmission.paid_of_nonempty
#print axioms Eip8282.Audit.Integrator.SystemDataSpec.exit_system
#print axioms Eip8282.Audit.Integrator.SystemDataSpec.deposit_system
#print axioms Eip8282.Audit.Integrator.SystemDataSpec.projections

-- Composed conditional direct guarantees; not yet registered as protocol closure.
#print axioms Eip8282.Audit.Integrator.AuditedChildGas.context_result
#print axioms Eip8282.Audit.Integrator.AuditedChildGas.child_append_debit
#print axioms Eip8282.Audit.Integrator.AuditedChildGas.parent_append_debit
#print axioms Eip8282.Audit.Integrator.TransferFunding.funds_insert
#print axioms Eip8282.Audit.Integrator.TransferFunding.balance_le_funds
#print axioms Eip8282.Audit.Integrator.TransferFunding.entry_funds_le
#print axioms Eip8282.Audit.Integrator.TransferFunding.entry_funds_budget
#print axioms Eip8282.Audit.Integrator.DirectAppend.observed_of_receipt
#print axioms Eip8282.Audit.Integrator.DirectAppend.user_append
#print axioms Eip8282.Audit.Integrator.DirectControl.completed
#print axioms Eip8282.Audit.Integrator.DirectDrain.completed_call
#print axioms Eip8282.Audit.Integrator.DirectSubmit.completed
#print axioms Eip8282.Audit.Integrator.DirectSubmit.invalid_nonempty
#print axioms Eip8282.Audit.Integrator.DirectInitialization.pinned
#print axioms Eip8282.Audit.Integrator.SystemFrame.system_frame
#print axioms Eip8282.Audit.Integrator.SystemFrame.logs_preserved
#print axioms Eip8282.Audit.Integrator.SystemProgress.pinned
#print axioms Eip8282.Audit.Integrator.DirectGuarantees.psubmit1_direct
#print axioms Eip8282.Audit.Integrator.DirectGuarantees.pdrain1_direct
#print axioms Eip8282.Audit.Integrator.DirectGuarantees.pcontrol1_direct

-- Ordinary instruction gas: no new axioms. Mutants below reuse ONLY their
-- respective historical finite execution receipt, separately from the parents.
#print axioms Eip8282.Audit.Integrator.OrdinaryGas.accepted_step_debit
#print axioms Eip8282.Audit.Integrator.OrdinaryGas.ordinary_iff
#print axioms Eip8282.Audit.Integrator.OrdinaryGas.xruns_debit
#print axioms Eip8282.Tests.DirectThetaMutations.control_domain
#print axioms Eip8282.Tests.DirectThetaMutations.gate_refutes_pcontrol
#print axioms Eip8282.Tests.DirectThetaMutations.target_refutes_pcontrol

-- Actual family call accounting and independent Theta drain mutations.
#print axioms Eip8282.Tests.DirectThetaDrainMutations.deposit_cap_refutes_pdrain
#print axioms Eip8282.Tests.DirectThetaDrainMutations.deposit_stale_refutes_pdrain
#print axioms Eip8282.Tests.DirectThetaDrainMutations.exit_cap_refutes_pdrain
#print axioms Eip8282.Audit.Integrator.CallFamilyGas.step_helper
#print axioms Eip8282.Audit.Integrator.CallFamilyGas.accepted_step_debit
#print axioms Eip8282.Audit.Integrator.CallFamilyGas.accepted_denied_debit
#print axioms Eip8282.Audit.Integrator.CallFunding.call_entry_budget
#print axioms Eip8282.Audit.Integrator.CallFunding.family_entry_budget
#print axioms Eip8282.Audit.Integrator.CallFunding.call_step_entry
#print axioms Eip8282.Audit.Integrator.CallFunding.family_step_entry

-- Universal evaluator gas, actual transaction refund and ordinary funding.
#print axioms Eip8282.Audit.Integrator.CreationGas.step_child
#print axioms Eip8282.Audit.Integrator.CreationGas.accepted_child_debit
#print axioms Eip8282.Audit.Integrator.CreationGas.accepted_denied_debit
#print axioms Eip8282.Audit.Integrator.CreationGas.lambda_code_debit
#print axioms Eip8282.Audit.Integrator.ReturnedGas.all_bounds
#print axioms Eip8282.Audit.Integrator.ReturnedGas.theta_remaining
#print axioms Eip8282.Audit.Integrator.ReturnedGas.lambda_remaining
#print axioms Eip8282.Audit.Integrator.ReturnedGas.message_remaining
#print axioms Eip8282.Audit.Integrator.StorageFunding.sstore_preserves
#print axioms Eip8282.Audit.Integrator.StorageFunding.tstore_preserves
#print axioms Eip8282.Audit.Integrator.SelfdestructFunding.raw_nonincrease
#print axioms Eip8282.Audit.Integrator.OrdinaryFunding.accepted_step_nonincrease
#print axioms Eip8282.Audit.Integrator.TransactionGas.provisional_remaining
#print axioms Eip8282.Audit.Integrator.TransactionGas.result_debit
#print axioms Eip8282.Audit.Integrator.TransactionGas.count_le_used

-- Same-predicate direct mutation tests; never conjuncts of correctness parents.
#print axioms Eip8282.Tests.DirectThetaKills.submit_kill
#print axioms Eip8282.Tests.DirectThetaKills.drain_kills
#print axioms Eip8282.Tests.DirectThetaKills.control_kills

-- Actual recursive and transaction funding; independent admission, no post-state premise.
#print axioms Eip8282.Audit.Integrator.CallWorld.step_call_world
#print axioms Eip8282.Audit.Integrator.CallWorld.step_family_world
#print axioms Eip8282.Audit.Integrator.CreationFunding.entry_distinct
#print axioms Eip8282.Audit.Integrator.CreationFunding.alias_settle_world
#print axioms Eip8282.Audit.Integrator.CreationWorld.step_world
#print axioms Eip8282.Audit.Integrator.ExecutionFunding.all_bounds
#print axioms Eip8282.Audit.Integrator.ExecutionFunding.theta_funds
#print axioms Eip8282.Audit.Integrator.ExecutionFunding.lambda_funds
#print axioms Eip8282.Audit.Integrator.FinalizationFunding.credit_le
#print axioms Eip8282.Audit.Integrator.FinalizationFunding.cleanup_le
#print axioms Eip8282.Audit.Integrator.TransactionFunding.checkpoint_debit
#print axioms Eip8282.Audit.Integrator.TransactionFunding.result_equation
#print axioms Eip8282.Audit.Integrator.TransactionFunding.result_funds

-- Actual history funding and frame-local all-outcome event certificates.
#print axioms Eip8282.Audit.Integrator.FundingHistory.step_funds
#print axioms Eip8282.Audit.Integrator.FundingHistory.trace_funds
#print axioms Eip8282.Audit.Integrator.FundingHistory.message_value_lt
#print axioms Eip8282.Audit.Integrator.FundingHistory.transaction_value_lt
#print axioms Eip8282.Audit.Integrator.FundingHistory.xruns_funds
#print axioms Eip8282.Audit.Integrator.FrameEvents.sound
#print axioms Eip8282.Audit.Integrator.FrameEvents.extract
#print axioms Eip8282.Audit.Integrator.FrameEvents.gas_bound
#print axioms Eip8282.Audit.Integrator.FrameEvents.distinct
#print axioms Eip8282.Audit.Integrator.FrameEvents.deterministic
#print axioms Eip8282.Audit.Integrator.FrameEvents.contains_site
#print axioms Eip8282.Audit.Integrator.AppendEvents.successful_events

-- All-outcome child adapters and explicit induction-edge charge transport.
#print axioms Eip8282.Audit.Integrator.CallOutcome.step_call_equation
#print axioms Eip8282.Audit.Integrator.CallOutcome.step_family_equation
#print axioms Eip8282.Audit.Integrator.CallOutcome.step_call_error_iff
#print axioms Eip8282.Audit.Integrator.CallOutcome.step_family_error_iff
#print axioms Eip8282.Audit.Integrator.CallOutcome.accepted_call_allowance_le
#print axioms Eip8282.Audit.Integrator.CallOutcome.accepted_family_allowance_le
#print axioms Eip8282.Audit.Integrator.CreationOutcome.admitted_equation
#print axioms Eip8282.Audit.Integrator.CreationOutcome.denied_equation
#print axioms Eip8282.Audit.Integrator.CreationOutcome.finish_error_iff
#print axioms Eip8282.Audit.Integrator.CreationOutcome.accepted_allowance_le
#print axioms Eip8282.Audit.Integrator.RecursiveEventDebit.call_charge
#print axioms Eip8282.Audit.Integrator.RecursiveEventDebit.family_charge
#print axioms Eip8282.Audit.Integrator.RecursiveEventDebit.creation_charge

-- Structural occurrence IDs and actual execution-wrapper induction edges.
#print axioms Eip8282.Audit.Integrator.EventTree.occurrences_length
#print axioms Eip8282.Audit.Integrator.EventTree.occurrences_nodup
#print axioms Eip8282.Audit.Integrator.EventTree.mem_step_iff
#print axioms Eip8282.Audit.Integrator.WrapperEventDebit.xi_residual
#print axioms Eip8282.Audit.Integrator.WrapperEventDebit.theta_residual
#print axioms Eip8282.Audit.Integrator.WrapperEventDebit.lambda_residual
#print axioms Eip8282.Audit.Integrator.WrapperEventDebit.lambda_no_preimage
#print axioms Eip8282.Audit.Integrator.WrapperEventDebit.theta_charge
#print axioms Eip8282.Audit.Integrator.WrapperEventDebit.lambda_charge

-- Exact initialization success and complete all-outcome nested event budgets.
#print axioms Eip8282.Audit.Integrator.InitializerProgress.initializes_success
#print axioms Eip8282.Audit.Integrator.NestedFrameOwnership.owned_distinct
#print axioms Eip8282.Audit.Integrator.NestedFrameOwnership.owned_injective
#print axioms Eip8282.Audit.Integrator.NestedEvents.stepChild_fuel
#print axioms Eip8282.Audit.Integrator.NestedEvents.sound
#print axioms Eip8282.Audit.Integrator.NestedEvents.extract
#print axioms Eip8282.Audit.Integrator.NestedEvents.deterministic
#print axioms Eip8282.Audit.Integrator.NestedEvents.gas_bound
#print axioms Eip8282.Audit.Integrator.NestedEvents.extracted_bound
#print axioms Eip8282.Audit.Integrator.NestedEvents.extracted_gross_bound
#print axioms Eip8282.Audit.Integrator.NestedEvents.local_projection
#print axioms Eip8282.Audit.Integrator.NestedEvents.local_address
#print axioms Eip8282.Audit.Integrator.NestedEvents.successful_append_address
#print axioms Eip8282.Audit.Integrator.TransactionEventBounds.provisional_residual
#print axioms Eip8282.Audit.Integrator.TransactionEventBounds.transaction_events

-- Complete actual append invocation set and checked pinned opcode sites.
#print axioms Eip8282.Audit.Integrator.NestedEvents.XiAt.cert_top
#print axioms Eip8282.Audit.Integrator.NestedEvents.XiAt.sound_inner
#print axioms Eip8282.Audit.Integrator.NestedEvents.XiAt.frame_root
#print axioms Eip8282.Audit.Integrator.NestedEvents.XiAt.at_tree
#print axioms Eip8282.Audit.Integrator.NestedEvents.XiAt.identity
#print axioms Eip8282.Audit.Integrator.NestedAppendCount.owns_event
#print axioms Eip8282.Audit.Integrator.NestedAppendCount.distinct_events
#print axioms Eip8282.Audit.Integrator.NestedAppendCount.mem_frames_iff
#print axioms Eip8282.Audit.Integrator.NestedAppendCount.count_le_events
#print axioms Eip8282.Audit.Integrator.NestedAppendCount.transaction_appends
#print axioms Eip8282.Audit.Integrator.RuntimeOpcodeScope.deposit_checked
#print axioms Eip8282.Audit.Integrator.RuntimeOpcodeScope.exit_checked
#print axioms Eip8282.Audit.Integrator.RuntimeOpcodeScope.allowed_excludes
#print axioms Eip8282.Audit.Integrator.RuntimeOpcodeScope.deposit_jump_scope
#print axioms Eip8282.Audit.Integrator.RuntimeOpcodeScope.exit_jump_scope

-- Actual nested budget transport, runtime call exclusion and protected account frame.
#print axioms Eip8282.Audit.Integrator.NestedEvents.XiAt.compose
#print axioms Eip8282.Audit.Integrator.NestedAppendPrefix.count_le
#print axioms Eip8282.Audit.Integrator.NestedAppendPrefix.transaction_prefix
#print axioms Eip8282.Audit.Integrator.TransactionAppendBudget.tree_cert
#print axioms Eip8282.Audit.Integrator.TransactionAppendBudget.appends_le_used
#print axioms Eip8282.Audit.Integrator.TransactionAppendBudget.history_lt
#print axioms Eip8282.Audit.Integrator.OrdinaryWorldFrame.accepted_step_preserved
#print axioms Eip8282.Audit.Integrator.OrdinaryWorldFrame.existing_code_storage
#print axioms Eip8282.Audit.Integrator.EvaluationFuelBoundary.entry_to_erasure
#print axioms Eip8282.Audit.Integrator.EvaluationFuelBoundary.sstore_absent_owner
#print axioms Eip8282.Audit.Integrator.EvaluationFuelBoundary.final_error
#print axioms Eip8282.Audit.Integrator.RuntimeExecutionScope.opcode_allowed
#print axioms Eip8282.Audit.Integrator.RuntimeExecutionScope.accepted_next
#print axioms Eip8282.Audit.Integrator.RuntimeExecutionScope.cert_local
#print axioms Eip8282.Audit.Integrator.RuntimeExecutionScope.x_no_xi
#print axioms Eip8282.Audit.Integrator.RuntimeExecutionScope.xi_only_self

-- Nested funding, typed creation totality, actual journal and genesis input transport.
#print axioms Eip8282.Audit.Integrator.NestedFunding.theta_entry
#print axioms Eip8282.Audit.Integrator.NestedFunding.lambda_entry_distinct
#print axioms Eip8282.Audit.Integrator.NestedFunding.lambda_alias_invalid
#print axioms Eip8282.Audit.Integrator.NestedFunding.selected_child_funding
#print axioms Eip8282.Audit.Integrator.NestedFunding.admitted_request
#print axioms Eip8282.Audit.Integrator.NestedFunding.transaction_entry_funds
#print axioms Eip8282.Audit.Integrator.NestedFunding.invalid_has_no_audited_frame
#print axioms Eip8282.Audit.Integrator.NestedFunding.audited_entry_funds
#print axioms Eip8282.Audit.Integrator.NestedEvents.ThetaAt.cert_top
#print axioms Eip8282.Audit.Integrator.NestedEvents.ThetaAt.sound_top
#print axioms Eip8282.Audit.Integrator.NestedEvents.ThetaAt.sound_inner
#print axioms Eip8282.Audit.Integrator.NestedEvents.ThetaAt.x_nonempty
#print axioms Eip8282.Audit.Integrator.NestedEvents.ThetaAt.frame_root
#print axioms Eip8282.Audit.Integrator.NestedEvents.ThetaAt.at_tree
#print axioms Eip8282.Audit.Integrator.NestedEvents.ThetaAt.code_xi
#print axioms Eip8282.Audit.Integrator.NestedEvents.ThetaAt.identity
#print axioms Eip8282.Audit.Integrator.NestedFunding.invalid_has_no_call
#print axioms Eip8282.Audit.Integrator.NestedFunding.call_input_funds
#print axioms Eip8282.Audit.Integrator.NestedFunding.call_value_le_root
#print axioms Eip8282.Audit.Integrator.NestedFunding.transaction_call_value
#print axioms Eip8282.Audit.Integrator.NestedFunding.history_call_value_lt
#print axioms Eip8282.Audit.Integrator.GenesisFundingInput.allocation_count
#print axioms Eip8282.Audit.Integrator.GenesisFundingInput.allocation_addresses_fit
#print axioms Eip8282.Audit.Integrator.GenesisFundingInput.total_credit_exact
#print axioms Eip8282.Audit.Integrator.GenesisFundingInput.total_credit_lt_96
#print axioms Eip8282.Audit.Integrator.GenesisFundingInput.bounded_by_input_lt_96
#print axioms Eip8282.Audit.Integrator.GenesisFundingWorld.insertion_bound
#print axioms Eip8282.Audit.Integrator.GenesisFundingWorld.populate_bound
#print axioms Eip8282.Audit.Integrator.GenesisFundingWorld.initial_funds_le
#print axioms Eip8282.Audit.Integrator.GenesisFundingWorld.initial_funds_lt_96
#print axioms Eip8282.Audit.Integrator.RuntimeCodePreservation.raw_preserved
#print axioms Eip8282.Audit.Integrator.RuntimeCodePreservation.accepted_preserved
#print axioms Eip8282.Audit.Integrator.RuntimeCodePreservation.x_preserved
#print axioms Eip8282.Audit.Integrator.RuntimeCodePreservation.theta_existing_code
#print axioms Eip8282.Audit.Integrator.CodeStorageFrame.trans
#print axioms Eip8282.Audit.Integrator.CodeStorageFrame.of_preserved
#print axioms Eip8282.Audit.Integrator.CodeStorageFrame.ordinary
#print axioms Eip8282.Audit.Integrator.CodeStorageFrame.entry
#print axioms Eip8282.Audit.Integrator.FinalizationWorldFrame.credit_frame
#print axioms Eip8282.Audit.Integrator.FinalizationWorldFrame.erase_set_lookup
#print axioms Eip8282.Audit.Integrator.FinalizationWorldFrame.clearTransient_lookup
#print axioms Eip8282.Audit.Integrator.FinalizationWorldFrame.clear_transient_frame
#print axioms Eip8282.Audit.Integrator.FinalizationWorldFrame.nonempty_code_not_dead
#print axioms Eip8282.Audit.Integrator.FinalizationWorldFrame.cleanup_frame
#print axioms Eip8282.Audit.Integrator.FinalizationWorldFrame.cleanup_existing
#print axioms Eip8282.Audit.Integrator.CreationStorageFrame.entry_frame
#print axioms Eip8282.Audit.Integrator.CreationStorageFrame.install_away_frame
#print axioms Eip8282.Audit.Integrator.CreationStorageFrame.occupied_creation_fails
#print axioms Eip8282.Audit.Integrator.CreationPreimageTotal.context_total
#print axioms Eip8282.Audit.Integrator.CreationPreimageTotal.lambdaArgs_total
#print axioms Eip8282.Audit.Integrator.CreationPreimageTotal.creationArgs_total
#print axioms Eip8282.Audit.Integrator.CreationPreimageTotal.create2_salt_width
#print axioms Eip8282.Audit.Integrator.CreationErrorScope.context_error
#print axioms Eip8282.Audit.Integrator.CreationErrorScope.lambda_error
#print axioms Eip8282.Audit.Integrator.JournalInvariant.mono
#print axioms Eip8282.Audit.Integrator.JournalInvariant.frame
#print axioms Eip8282.Audit.Integrator.JournalInvariant.protected_call
#print axioms Eip8282.Audit.Integrator.JournalInvariant.failed_call
#print axioms Eip8282.Audit.Integrator.JournalInvariant.of_initialized
#print axioms Eip8282.Audit.Integrator.JournalInvariant.initializes

-- Chronological journal accounting, prefunding and actual protected-call composition.
#print axioms Eip8282.Audit.Integrator.CallOwnerCoherence.canonical_not_precompile
#print axioms Eip8282.Audit.Integrator.CallOwnerCoherence.installed_toExecute
#print axioms Eip8282.Audit.Integrator.CallOwnerCoherence.selected_theta
#print axioms Eip8282.Audit.Integrator.CallOwnerCoherence.pinned
#print axioms Eip8282.Audit.Integrator.JournalGuarantees.domains
#print axioms Eip8282.Audit.Integrator.JournalGuarantees.completed
#print axioms Eip8282.Audit.Integrator.JournalGuarantees.initializes
#print axioms Eip8282.Audit.Integrator.NestedCallDataFit.read_data_fit
#print axioms Eip8282.Audit.Integrator.NestedCallDataFit.selected_child_fit
#print axioms Eip8282.Audit.Integrator.NestedCallDataFit.call_data_fit
#print axioms Eip8282.Audit.Integrator.NestedJournalBudget.call_interval
#print axioms Eip8282.Audit.Integrator.NestedJournalBudget.events_le_used
#print axioms Eip8282.Audit.Integrator.NestedJournalBudget.transaction_call_interval
#print axioms Eip8282.Audit.Integrator.NestedJournalBudget.history_lt
#print axioms Eip8282.Audit.Integrator.NestedJournalBudget.bounded_call_interval
#print axioms Eip8282.Audit.Integrator.PrecompileWorldFrame.precompile_choice
#print axioms Eip8282.Audit.Integrator.PrecompileWorldFrame.theta_preserved
#print axioms Eip8282.Audit.Integrator.PrecompileWorldFrame.theta_frame
#print axioms Eip8282.Audit.Integrator.PrecompileWorldFrame.theta_exclusion
#print axioms Eip8282.Audit.Integrator.PrefundedInitialization.collision_fields
#print axioms Eip8282.Audit.Integrator.PrefundedInitialization.zero_of_no_collision
#print axioms Eip8282.Audit.Integrator.PrefundedInitialization.observed_of_success
#print axioms Eip8282.Audit.Integrator.PrefundedInitialization.deposit_guards
#print axioms Eip8282.Audit.Integrator.PrefundedInitialization.initializes_success
#print axioms Eip8282.Audit.Integrator.ProtectedJournalStep.executionRequest_eval
#print axioms Eip8282.Audit.Integrator.ProtectedJournalStep.successful_nonempty_size
#print axioms Eip8282.Audit.Integrator.ProtectedJournalStep.weight_le_events
#print axioms Eip8282.Audit.Integrator.ProtectedJournalStep.preserves
#print axioms Eip8282.Audit.Integrator.RecursiveJournalEdges.theta_returned
#print axioms Eip8282.Audit.Integrator.RecursiveJournalEdges.lambda_returned
#print axioms Eip8282.Audit.Integrator.RecursiveJournalEdges.denied_recursive
#print axioms Eip8282.Audit.Integrator.SubstateSelfdestructFrame.raw_without_selfdestruct
#print axioms Eip8282.Audit.Integrator.SubstateSelfdestructFrame.accepted_other_owner
#print axioms Eip8282.Audit.Integrator.SubstateSelfdestructFrame.accepted_runtime
#print axioms Eip8282.Audit.Integrator.SubstateSelfdestructFrame.x_runtime
#print axioms Eip8282.Audit.Integrator.SubstateSelfdestructFrame.xi_runtime
#print axioms Eip8282.Audit.Integrator.SubstateSelfdestructFrame.theta_runtime
#print axioms Eip8282.Audit.Integrator.SubstateSelfdestructFrame.theta_exclusion
#print axioms Eip8282.Audit.Integrator.NestedProtectedJournal.inputs_from_history
#print axioms Eip8282.Audit.Integrator.NestedProtectedJournal.atomic_call

-- Complete recursive journal preservation and constructive evaluator resources.
#print axioms Eip8282.Audit.Integrator.NestedEvents.RequestAt.cert_top
#print axioms Eip8282.Audit.Integrator.NestedEvents.RequestAt.cert_inner
#print axioms Eip8282.Audit.Integrator.NestedEvents.RequestAt.compose
#print axioms Eip8282.Audit.Integrator.NestedEvents.RequestAt.theta
#print axioms Eip8282.Audit.Integrator.NestedEvents.Every.descendant
#print axioms Eip8282.Audit.Integrator.NestedEvents.lambda_returns
#print axioms Eip8282.Audit.Integrator.OpcodeCostPositive.opcode_cost_positive
#print axioms Eip8282.Audit.Integrator.OpcodeCostPositive.nonhalting_of_H_none
#print axioms Eip8282.Audit.Integrator.OpcodeCostPositive.accepted_nonhalting_cost
#print axioms Eip8282.Audit.Integrator.RecursiveGasProgress.stipend_margin
#print axioms Eip8282.Audit.Integrator.RecursiveGasProgress.callgas_margin
#print axioms Eip8282.Audit.Integrator.RecursiveGasProgress.creation_cost
#print axioms Eip8282.Audit.Integrator.RecursiveGasProgress.creation_allowance_margin
#print axioms Eip8282.Audit.Integrator.RecursiveGasProgress.selected_child_fuel_exact
#print axioms Eip8282.Audit.Integrator.RecursiveGasProgress.selected_child_fuel_gap
#print axioms Eip8282.Audit.Integrator.RecursiveGasProgress.selected_child_gas_lt
#print axioms Eip8282.Audit.Integrator.RecursiveGasProgress.call_step
#print axioms Eip8282.Audit.Integrator.RecursiveGasProgress.family_step
#print axioms Eip8282.Audit.Integrator.RecursiveGasProgress.creation_step
#print axioms Eip8282.Audit.Integrator.RecursiveGasProgress.recursive_step_drop
#print axioms Eip8282.Audit.Integrator.FuelAdequacy.uniform_bound
#print axioms Eip8282.Audit.Integrator.FuelAdequacy.accepted_nonhalting_drop
#print axioms Eip8282.Audit.Integrator.FuelAdequacy.at_adequate
#print axioms Eip8282.Audit.Integrator.FuelAdequacy.no_out_of_fuel
#print axioms Eip8282.Audit.Integrator.FuelAdequacy.every_no_out_of_fuel
#print axioms Eip8282.Audit.Integrator.FuelAdequacy.actual_lambda_returns
#print axioms Eip8282.Audit.Integrator.RuntimeThetaExclusion.x_no_theta
#print axioms Eip8282.Audit.Integrator.RuntimeThetaExclusion.xi_no_theta
#print axioms Eip8282.Audit.Integrator.RuntimeThetaExclusion.invalid_no_success
#print axioms Eip8282.Audit.Integrator.RuntimeThetaExclusion.invalid_no_theta
#print axioms Eip8282.Audit.Integrator.WrapperJournalEdges.xi_success
#print axioms Eip8282.Audit.Integrator.WrapperJournalEdges.theta_code_world
#print axioms Eip8282.Audit.Integrator.WrapperJournalEdges.lambda_context_world
#print axioms Eip8282.Audit.Integrator.JournalChildEntry.selected_kind
#print axioms Eip8282.Audit.Integrator.JournalChildEntry.selected_theta_input
#print axioms Eip8282.Audit.Integrator.JournalChildEntry.selected_lambda_input
#print axioms Eip8282.Audit.Integrator.CreationCollisionScope.context_collision
#print axioms Eip8282.Audit.Integrator.CreationCollisionScope.selected_invalid
#print axioms Eip8282.Audit.Integrator.CreationCollisionScope.no_theta
#print axioms Eip8282.Audit.Integrator.CreationCollisionScope.no_success
#print axioms Eip8282.Audit.Integrator.JournalExecution.protected_done
#print axioms Eip8282.Audit.Integrator.JournalExecution.ordinary_done
#print axioms Eip8282.Audit.Integrator.JournalExecution.child_ready
#print axioms Eip8282.Audit.Integrator.JournalExecution.occupied_lambda_done
#print axioms Eip8282.Audit.Integrator.JournalExecution.preserves
#print axioms Eip8282.Audit.Integrator.JournalCheckpoints.call_ready
#print axioms Eip8282.Audit.Integrator.JournalCheckpoints.from_resources
#print axioms Eip8282.Audit.Integrator.JournalCheckpoints.observed

-- Actual transaction settlement, linked histories and chosen queue observations.
#print axioms Eip8282.Audit.Integrator.TransactionJournalEdges.checkpoint_frame
#print axioms Eip8282.Audit.Integrator.TransactionJournalEdges.settled_frame
#print axioms Eip8282.Audit.Integrator.TransactionJournalEdges.settled_codeAt_frame
#print axioms Eip8282.Audit.Integrator.TransactionJournalEdges.provisional_cases
#print axioms Eip8282.Audit.Integrator.TransactionJournal.ready
#print axioms Eip8282.Audit.Integrator.TransactionJournal.adequate
#print axioms Eip8282.Audit.Integrator.TransactionJournal.data_fit
#print axioms Eip8282.Audit.Integrator.TransactionJournal.provisional
#print axioms Eip8282.Audit.Integrator.TransactionJournal.settled
#print axioms Eip8282.Audit.Integrator.TransactionJournal.completed
#print axioms Eip8282.Audit.Integrator.TransactionJournal.observed
#print axioms Eip8282.Audit.Integrator.SystemJournal.other_runtime_frame
#print axioms Eip8282.Audit.Integrator.SystemJournal.preserves
#print axioms Eip8282.Audit.Integrator.ActualJournalHistory.funding
#print axioms Eip8282.Audit.Integrator.ActualJournalHistory.transaction_step
#print axioms Eip8282.Audit.Integrator.ActualJournalHistory.preserves
#print axioms Eip8282.Audit.Integrator.ActualJournalHistory.work_lt_of_blocks
#print axioms Eip8282.Audit.Integrator.ActualJournalHistory.initialized_history
#print axioms Eip8282.Audit.Integrator.JournalProvenanceInterface.represents_unique
#print axioms Eip8282.Audit.Integrator.JournalProvenanceInterface.completed_queue
#print axioms Eip8282.Audit.Integrator.JournalProvenanceInterface.completed_append
#print axioms Eip8282.Audit.Integrator.JournalProvenanceInterface.failed_checkpoint
#print axioms Eip8282.Audit.Integrator.JournalProvenanceInterface.chosen_source
#print axioms Eip8282.Audit.Integrator.JournalProvenanceInterface.chosen_frame
#print axioms Eip8282.Audit.Integrator.JournalProvenanceInterface.transition_preserves

-- All actual history positions, protected log frames and explicit credit arithmetic.
#print axioms Eip8282.Audit.Integrator.ActualHistoryCalls.transaction_prefix
#print axioms Eip8282.Audit.Integrator.ActualHistoryCalls.position_work
#print axioms Eip8282.Audit.Integrator.ActualHistoryCalls.observed
#print axioms Eip8282.Audit.Integrator.ActualHistoryCalls.observed_in_blocks
#print axioms Eip8282.Audit.Integrator.ProtectedLogFrame.push_away
#print axioms Eip8282.Audit.Integrator.ProtectedLogFrame.push_self
#print axioms Eip8282.Audit.Integrator.ProtectedLogFrame.raw_without_logs
#print axioms Eip8282.Audit.Integrator.ProtectedLogFrame.accepted_other_owner
#print axioms Eip8282.Audit.Integrator.ProtectedLogFrame.theta_failure
#print axioms Eip8282.Audit.Integrator.ProtectedLogFrame.transaction_projection
#print axioms Eip8282.Audit.Integrator.ProtocolCreditEnvelope.ledger_bound
#print axioms Eip8282.Audit.Integrator.ProtocolCreditEnvelope.numeric_envelope
#print axioms Eip8282.Audit.Integrator.ProtocolCreditEnvelope.below_ceiling
#print axioms Eip8282.Audit.Integrator.ProtocolCreditEnvelope.funding_budget

-- Actual queue-world replay, retained-call characterization and protocol input producers.
#print axioms Eip8282.Audit.Integrator.ProtocolTransfer.debit_funds
#print axioms Eip8282.Audit.Integrator.ProtocolTransfer.funds
#print axioms Eip8282.Audit.Integrator.ProtocolTransfer.debit_frame
#print axioms Eip8282.Audit.Integrator.ProtocolTransfer.frame
#print axioms Eip8282.Audit.Integrator.JournalWorldPaths.protected_path
#print axioms Eip8282.Audit.Integrator.JournalWorldPaths.theta_path
#print axioms Eip8282.Audit.Integrator.JournalWorldPaths.lambda_path
#print axioms Eip8282.Audit.Integrator.JournalWorldPaths.occupied_path
#print axioms Eip8282.Audit.Integrator.JournalWorldPaths.extract_at
#print axioms Eip8282.Audit.Integrator.JournalWorldPaths.extract
#print axioms Eip8282.Audit.Integrator.JournalPathQueues.occurrence_domain
#print axioms Eip8282.Audit.Integrator.JournalPathQueues.represented_replay
#print axioms Eip8282.Audit.Integrator.JournalPathQueues.final_queue_eq
#print axioms Eip8282.Audit.Integrator.JournalPathQueues.replay_origin
#print axioms Eip8282.Audit.Integrator.TransactionQueuePaths.provisional_path
#print axioms Eip8282.Audit.Integrator.TransactionQueuePaths.result_path
#print axioms Eip8282.Audit.Integrator.TransactionQueuePaths.receipt_replay
#print axioms Eip8282.Audit.Integrator.TransactionQueuePaths.history_replay
#print axioms Eip8282.Audit.Integrator.JournalRetainedCalls.theta_keep
#print axioms Eip8282.Audit.Integrator.JournalRetainedCalls.theta_empty_restore
#print axioms Eip8282.Audit.Integrator.JournalRetainedCalls.lambda_keep
#print axioms Eip8282.Audit.Integrator.JournalRetainedCalls.lambda_reject_restore
#print axioms Eip8282.Audit.Integrator.JournalRetainedCalls.Survives.actual
#print axioms Eip8282.Audit.Integrator.JournalRetainedCalls.Survives.identity
#print axioms Eip8282.Audit.Integrator.JournalRetainedCalls.retainedList_mem_iff
#print axioms Eip8282.Audit.Integrator.JournalRetainedCalls.retainedList_nodup
#print axioms Eip8282.Audit.Integrator.JournalRetainedCalls.retainedList_order
#print axioms Eip8282.Audit.Integrator.JournalRetainedCalls.retainedList_unique_call
#print axioms Eip8282.Audit.Integrator.ProtocolMigrationLedger.ledger
#print axioms Eip8282.Audit.Integrator.ProtocolMigrationLedger.funding
#print axioms Eip8282.Audit.Integrator.ProtocolMigrationLedger.frame
#print axioms Eip8282.Audit.Integrator.ProtocolMigrationLedger.recipient_add_bound
#print axioms Eip8282.Audit.Integrator.ProtocolMigrationLedger.checked_add_fits
#print axioms Eip8282.Audit.Integrator.ProtocolPowCount.difficulty_sum_lower
#print axioms Eip8282.Audit.Integrator.ProtocolPowCount.count_of_terminal_parent
#print axioms Eip8282.Audit.Integrator.ProtocolPowCount.maximum_lt_uint64
#print axioms Eip8282.Audit.Integrator.ProtocolPowCount.reward_count
#print axioms Eip8282.Audit.Integrator.ProtocolPowCount.counts
#print axioms Eip8282.Audit.Integrator.ProtectedCallLogSeries.completed
#print axioms Eip8282.Audit.Integrator.ProtectedCallLogSeries.projected
#print axioms Eip8282.Audit.Integrator.ProtectedCallLogSeries.transition

-- Actual surviving effects, complete final logs and initialized-history composition.
#print axioms Eip8282.Audit.Integrator.JournalRetainedPaths.list_xNext
#print axioms Eip8282.Audit.Integrator.JournalRetainedPaths.list_xHalt
#print axioms Eip8282.Audit.Integrator.JournalRetainedPaths.theta_exact
#print axioms Eip8282.Audit.Integrator.JournalRetainedPaths.lambda_exact
#print axioms Eip8282.Audit.Integrator.JournalRetainedPaths.extract_at
#print axioms Eip8282.Audit.Integrator.JournalRetainedPaths.extract
#print axioms Eip8282.Audit.Integrator.TransactionRetainedQueues.provisional_path
#print axioms Eip8282.Audit.Integrator.TransactionRetainedQueues.result_path
#print axioms Eip8282.Audit.Integrator.TransactionRetainedQueues.receipt_replay
#print axioms Eip8282.Audit.Integrator.TransactionRetainedQueues.history_replay
#print axioms Eip8282.Audit.Integrator.JournalRetainedWork.mem_submittedList_iff
#print axioms Eip8282.Audit.Integrator.JournalRetainedWork.submittedList_nodup
#print axioms Eip8282.Audit.Integrator.JournalRetainedWork.submitted_appendFrame
#print axioms Eip8282.Audit.Integrator.JournalRetainedWork.submitted_distinct_events
#print axioms Eip8282.Audit.Integrator.JournalRetainedWork.count_le_executed
#print axioms Eip8282.Audit.Integrator.JournalRetainedWork.count_le_events
#print axioms Eip8282.Audit.Integrator.JournalRetainedWork.transaction_count_le_used
#print axioms Eip8282.Audit.Integrator.RecursiveLogEdges.theta_returned
#print axioms Eip8282.Audit.Integrator.RecursiveLogEdges.lambda_returned
#print axioms Eip8282.Audit.Integrator.RecursiveLogEdges.denied_recursive
#print axioms Eip8282.Audit.Integrator.RecursiveLogEdges.xi_success_logs
#print axioms Eip8282.Audit.Integrator.RecursiveLogEdges.theta_code_logs
#print axioms Eip8282.Audit.Integrator.RecursiveLogEdges.lambda_context_logs
#print axioms Eip8282.Audit.Integrator.JournalLogInputs.selected_theta_input
#print axioms Eip8282.Audit.Integrator.JournalLogInputs.selected_lambda_input
#print axioms Eip8282.Audit.Integrator.JournalLogInputs.precompile_logs
#print axioms Eip8282.Audit.Integrator.JournalCommittedLogs.contribution_identity
#print axioms Eip8282.Audit.Integrator.JournalCommittedLogs.emitted_replay
#print axioms Eip8282.Audit.Integrator.JournalCommittedLogs.protected_logs
#print axioms Eip8282.Audit.Integrator.JournalCommittedLogs.theta_logs
#print axioms Eip8282.Audit.Integrator.JournalCommittedLogs.lambda_logs
#print axioms Eip8282.Audit.Integrator.JournalCommittedLogs.extract_at
#print axioms Eip8282.Audit.Integrator.JournalCommittedLogs.extract
#print axioms Eip8282.Audit.Integrator.TransactionCommittedEffects.provisional_logs
#print axioms Eip8282.Audit.Integrator.TransactionCommittedEffects.result_logs
#print axioms Eip8282.Audit.Integrator.TransactionCommittedEffects.receipt_effects
#print axioms Eip8282.Audit.Integrator.TransactionCommittedEffects.history_guarantees
#print axioms Eip8282.Audit.Integrator.TransactionCommittedEffects.history_in_blocks
#print axioms Eip8282.Audit.Integrator.JournalCommittedCardinality.submitted_iff
#print axioms Eip8282.Audit.Integrator.JournalCommittedCardinality.contribution_length
#print axioms Eip8282.Audit.Integrator.JournalCommittedCardinality.emitted_length
#print axioms Eip8282.Audit.Integrator.GenesisWorldFunding.funding_budget
#print axioms Eip8282.Audit.Integrator.GenesisWorldFunding.final_funds
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalCount.amount_exact
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalCount.amount_bounded
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalCount.guarded_length
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalCount.total_count
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalCount.dispatch_ledger
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalCount.dispatched_counts
#print axioms Eip8282.Audit.Integrator.HistoryCommittedGuarantees.exact_log_count
#print axioms Eip8282.Audit.Integrator.HistoryCommittedGuarantees.represented_queue
#print axioms Eip8282.Audit.Integrator.HistoryCommittedGuarantees.composed
#print axioms Eip8282.Audit.Integrator.HistoryCommittedGuarantees.from_genesis_ledger

-- Exact factory deployment receipts seed both bytecode history guarantees.
#print axioms Eip8282.Audit.Integrator.FactoryRuntimeEntry.entry_selects
#print axioms Eip8282.Audit.Integrator.FactoryRuntimeEntry.create_guard
#print axioms Eip8282.Audit.Integrator.FactoryRuntimeEntry.selected_create2
#print axioms Eip8282.Audit.Integrator.FactoryRuntimeEntry.salt_encoding
#print axioms Eip8282.Audit.Integrator.FactoryRuntimeEntry.reaches_create2
#print axioms Eip8282.Audit.Integrator.FactoryChildResources.entry_resources
#print axioms Eip8282.Audit.Integrator.FactoryChildResources.child_gas_exact
#print axioms Eip8282.Audit.Integrator.FactoryChildResources.child_gas_sufficient
#print axioms Eip8282.Audit.Integrator.FactoryChildResources.child_preimage
#print axioms Eip8282.Audit.Integrator.FactoryChildResources.child_domain
#print axioms Eip8282.Audit.Integrator.LedgerCreditSafety.CreditAt.prefix
#print axioms Eip8282.Audit.Integrator.LedgerCreditSafety.credit_at_fits
#print axioms Eip8282.Audit.Integrator.LedgerCreditSafety.genesis_credit_at
#print axioms Eip8282.Audit.Integrator.LedgerCreditSafety.batch_checked
#print axioms Eip8282.Audit.Integrator.LedgerCreditSafety.ledger_checked
#print axioms Eip8282.Audit.Integrator.LedgerCreditSafety.genesis_budget
#print axioms Eip8282.Audit.Integrator.LedgerCreditSafety.from_genesis
#print axioms Eip8282.Audit.Integrator.LedgerCreditSafety.migration_add_fits
#print axioms Eip8282.Audit.Integrator.ProtocolPowRewards.reward_bound
#print axioms Eip8282.Audit.Integrator.ProtocolPowRewards.batch
#print axioms Eip8282.Audit.Integrator.ProtocolPowRewards.ledger
#print axioms Eip8282.Audit.Integrator.ProtocolSystemCalls.completes
#print axioms Eip8282.Audit.Integrator.ProtocolSystemCalls.guarantees
#print axioms Eip8282.Audit.Integrator.ProtocolSystemCalls.empty_guarantees
#print axioms Eip8282.Audit.Integrator.FactoryPrefixGas.step_gas_nonincrease
#print axioms Eip8282.Audit.Integrator.FactoryPrefixGas.runs_gas_nonincrease
#print axioms Eip8282.Audit.Integrator.FactoryPrefixGas.reaches_gas_nonincrease
#print axioms Eip8282.Audit.Integrator.FactoryPrefixGas.atCreate_gas_le
#print axioms Eip8282.Audit.Integrator.FactoryPrefixGas.prefix_bounds
#print axioms Eip8282.Audit.Integrator.ReferenceTransferLogs.project_substate
#print axioms Eip8282.Audit.Integrator.ReferenceTransferLogs.address_ne_system
#print axioms Eip8282.Audit.Integrator.ReferenceTransferLogs.project_append
#print axioms Eip8282.Audit.Integrator.ReferenceTransferLogs.project_entry
#print axioms Eip8282.Audit.Integrator.ReferenceTransferLogs.project_emitted
#print axioms Eip8282.Audit.Integrator.ReferenceTransferLogs.frame
#print axioms Eip8282.Audit.Integrator.ReferenceTransferLogs.settle
#print axioms Eip8282.Audit.Integrator.ReferenceTransferLogs.project_flatMap
#print axioms Eip8282.Audit.Integrator.FactoryRuntimeReturn.reaches_return
#print axioms Eip8282.Audit.Integrator.FactoryRuntimeReturn.execution
#print axioms Eip8282.Audit.Integrator.CreationSettlementProgress.post_fields
#print axioms Eip8282.Audit.Integrator.CreationSettlementProgress.actual_child_gas
#print axioms Eip8282.Audit.Integrator.CreationSettlementProgress.word_guard
#print axioms Eip8282.Audit.Integrator.CreationSettlementProgress.settle_success
#print axioms Eip8282.Audit.Integrator.CreationSettlementProgress.post_gas
#print axioms Eip8282.Audit.Integrator.CreationSettlementProgress.step_success
#print axioms Eip8282.Audit.Integrator.FactoryReturnEncoding.output_word
#print axioms Eip8282.Audit.Integrator.FactoryReturnEncoding.address_word_bytes
#print axioms Eip8282.Audit.Integrator.FactoryReturnEncoding.output_address
#print axioms Eip8282.Audit.Integrator.FactoryReturnEncoding.output_size
#print axioms Eip8282.Audit.Integrator.InitializerJournalFields.logs
#print axioms Eip8282.Audit.Integrator.InitializerJournalFields.selfdestruct
#print axioms Eip8282.Audit.Integrator.InitializerJournalFields.completed
#print axioms Eip8282.Audit.Integrator.FactoryCallEntry.installed_toExecute
#print axioms Eip8282.Audit.Integrator.FactoryCallEntry.execution_eq
#print axioms Eip8282.Audit.Integrator.FactoryCallEntry.pair_balance_le
#print axioms Eip8282.Audit.Integrator.FactoryCallEntry.entry_target_account
#print axioms Eip8282.Audit.Integrator.FactoryCallEntry.entry_target_funded
#print axioms Eip8282.Audit.Integrator.FactoryCallEntry.entry_gates
#print axioms Eip8282.Audit.Integrator.FactoryInitializedExecution.initializes
#print axioms Eip8282.Audit.Integrator.FactoryInitializedCall.initializes
#print axioms Eip8282.Audit.Integrator.TransactionFactoryEntry.call_fuel
#print axioms Eip8282.Audit.Integrator.TransactionFactoryEntry.checkpoint_factory
#print axioms Eip8282.Audit.Integrator.TransactionFactoryEntry.selected_code
#print axioms Eip8282.Audit.Integrator.TransactionFactoryEntry.call_funding
#print axioms Eip8282.Audit.Integrator.TransactionFactoryEntry.call_world_bound
#print axioms Eip8282.Audit.Integrator.TransactionFactoryEntry.call_result
#print axioms Eip8282.Audit.Integrator.TransactionFactoryEntry.provisional_of_call
#print axioms Eip8282.Audit.Integrator.FactoryInitializedTransaction.initializes
#print axioms Eip8282.Audit.Integrator.InitializerWorldFrame.preserves
#print axioms Eip8282.Audit.Integrator.FactoryHistoryGuarantees.deployment_seed
#print axioms Eip8282.Audit.Integrator.FactoryHistoryGuarantees.funding_seed
#print axioms Eip8282.Audit.Integrator.FactoryHistoryGuarantees.from_genesis_deployment
#print axioms Eip8282.Audit.Integrator.FactoryHistoryGuarantees.two_seeds
#print axioms Eip8282.Audit.Integrator.FactoryHistoryGuarantees.from_genesis_both

-- Source-operation parity and actual sparse/rounded memory composition.
#print axioms Eip8282.Audit.Integrator.ReferenceWordOps.isZero_parity
#print axioms Eip8282.Audit.Integrator.ReferenceWordOps.isZero_step
#print axioms Eip8282.Audit.Integrator.ReferenceWordOps.value_parity
#print axioms Eip8282.Audit.Integrator.ReferenceWordOps.step_parity
#print axioms Eip8282.Audit.Integrator.ReferenceWordOps.python_binary
#print axioms Eip8282.Audit.Integrator.ReferenceValueTransfer.entry_lookup
#print axioms Eip8282.Audit.Integrator.ReferenceValueTransfer.checked
#print axioms Eip8282.Audit.Integrator.ReferenceValueTransfer.from_ledger
#print axioms Eip8282.Audit.Integrator.ReferenceStorageGas.charge_bounds
#print axioms Eip8282.Audit.Integrator.ReferenceStorageGas.funded_success
#print axioms Eip8282.Audit.Integrator.ReferenceStorageGas.conservative_success
#print axioms Eip8282.Audit.Integrator.ReferenceStorageGas.static_rejects
#print axioms Eip8282.Audit.Integrator.ReferenceCallEntry.apparent_value
#print axioms Eip8282.Audit.Integrator.ReferenceCallEntry.world_eq
#print axioms Eip8282.Audit.Integrator.ReferenceCallEntry.lookup
#print axioms Eip8282.Audit.Integrator.ReferenceCallEntry.disabled
#print axioms Eip8282.Audit.Integrator.ReferenceCallEntry.protected_logs
#print axioms Eip8282.Audit.Integrator.ReferenceCallEntry.from_ledger
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryView.buffer_size
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryView.read_eq_buffer
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryView.buffer_byte
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryView.buffer_congr
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryView.read_congr
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryView.return_output
#print axioms Eip8282.Audit.Integrator.ReferenceStorageView.key_injective
#print axioms Eip8282.Audit.Integrator.ReferenceStorageView.write_read
#print axioms Eip8282.Audit.Integrator.ReferenceStorageView.rollback_current
#print axioms Eip8282.Audit.Integrator.ReferenceStorageView.commit_read
#print axioms Eip8282.Audit.Integrator.ReferenceStorageView.write_transport
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryCapacity.expansion_bounds
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryCapacity.expansion_le
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryCapacity.mstore
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryCapacity.mstore8
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryCapacity.deposit_item_span
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryCapacity.exit_item_span
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryCapacity.cost_mono
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryCapacity.telescopes
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryCapacity.system_costs
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryWrite.write_byte
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryWrite.congr
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryOperations.extend_same
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryOperations.splice_eq
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryOperations.store_view
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryOperations.mstore
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryOperations.mstore8
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryOperations.return_output
#print axioms Eip8282.Audit.Integrator.ReferenceDecodeSites.scan_eq_sites
#print axioms Eip8282.Audit.Integrator.ReferenceDecodeSites.checked
#print axioms Eip8282.Audit.Integrator.ReferenceDecodeSites.jumps_eq
#print axioms Eip8282.Audit.Integrator.ReferenceDecodeSites.site_facts
#print axioms Eip8282.Audit.Integrator.ReferenceDecodeSites.decode_eq
#print axioms Eip8282.Audit.Integrator.ReferenceDecodeSites.truncated_push_differs

-- Actual complete SYSTEM traces, memory charges and sequential source-meter payment.
#print axioms Eip8282.Audit.Integrator.SystemTraceAnnotations.erase
#print axioms Eip8282.Audit.Integrator.SystemTraceAnnotations.trans
#print axioms Eip8282.Audit.Integrator.SystemTraceAnnotations.singleton
#print axioms Eip8282.Audit.Integrator.SystemTraceAnnotations.bounded_trace
#print axioms Eip8282.Audit.Integrator.SystemTraceAnnotations.ends_trace
#print axioms Eip8282.Audit.Integrator.SystemTraceAnnotations.weight_append
#print axioms Eip8282.Audit.Integrator.SystemTraceAnnotations.xRuns_symBlock_ops
#print axioms Eip8282.Audit.Integrator.ReferenceControlOps.next_pc
#print axioms Eip8282.Audit.Integrator.ReferenceControlOps.push_zero
#print axioms Eip8282.Audit.Integrator.ReferenceControlOps.push
#print axioms Eip8282.Audit.Integrator.ReferenceControlOps.pop
#print axioms Eip8282.Audit.Integrator.ReferenceControlOps.accepted_jump
#print axioms Eip8282.Audit.Integrator.ReferenceControlOps.jump
#print axioms Eip8282.Audit.Integrator.ReferenceControlOps.jumpi_taken
#print axioms Eip8282.Audit.Integrator.ReferenceControlOps.jumpi_zero
#print axioms Eip8282.Audit.Integrator.ReferenceControlOps.python_push_pop
#print axioms Eip8282.Audit.Integrator.ReferenceStackOps.dup_depth
#print axioms Eip8282.Audit.Integrator.ReferenceStackOps.swap_depth
#print axioms Eip8282.Audit.Integrator.ReferenceStackOps.source_index
#print axioms Eip8282.Audit.Integrator.ReferenceStackOps.source_dup_index
#print axioms Eip8282.Audit.Integrator.ReferenceStackOps.source_swap_indices
#print axioms Eip8282.Audit.Integrator.ReferenceStackOps.accepted_dup_capacity
#print axioms Eip8282.Audit.Integrator.ReferenceStackOps.accepted_swap_capacity
#print axioms Eip8282.Audit.Integrator.ReferenceStackOps.dup_step
#print axioms Eip8282.Audit.Integrator.ReferenceStackOps.swap_step
#print axioms Eip8282.Audit.Integrator.ReferenceStackOps.accepted_dup
#print axioms Eip8282.Audit.Integrator.ReferenceStackOps.accepted_swap
#print axioms Eip8282.Audit.Integrator.ReferenceStackOps.next_pc
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryStep.mstore
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryStep.mstore8
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryStep.return_output
#print axioms Eip8282.Audit.Integrator.SystemPathBudget.Reach.trans
#print axioms Eip8282.Audit.Integrator.SystemPathBudget.Reach.erase
#print axioms Eip8282.Audit.Integrator.SystemPathBudget.singleton
#print axioms Eip8282.Audit.Integrator.SystemPathBudget.singleton_result
#print axioms Eip8282.Audit.Integrator.SystemPathBudget.chain
#print axioms Eip8282.Audit.Integrator.SystemPathBudget.block_step
#print axioms Eip8282.Audit.Integrator.SystemExitTrace.gate
#print axioms Eip8282.Audit.Integrator.SystemExitTrace.system_prefix
#print axioms Eip8282.Audit.Integrator.SystemExitTrace.drain_body
#print axioms Eip8282.Audit.Integrator.SystemExitTrace.drain_loop
#print axioms Eip8282.Audit.Integrator.SystemExitTrace.update_head
#print axioms Eip8282.Audit.Integrator.SystemExitTrace.update_excess
#print axioms Eip8282.Audit.Integrator.SystemExitTrace.system_returns
#print axioms Eip8282.Audit.Integrator.SystemDepositTrace.gate
#print axioms Eip8282.Audit.Integrator.SystemDepositTrace.system_prefix
#print axioms Eip8282.Audit.Integrator.SystemDepositTrace.drain_body
#print axioms Eip8282.Audit.Integrator.SystemDepositTrace.drain_loop
#print axioms Eip8282.Audit.Integrator.SystemDepositTrace.update_head
#print axioms Eip8282.Audit.Integrator.SystemDepositTrace.update_excess
#print axioms Eip8282.Audit.Integrator.SystemDepositTrace.system_returns
#print axioms Eip8282.Audit.Integrator.SystemTraceWitness.deposit
#print axioms Eip8282.Audit.Integrator.SystemTraceWitness.exit
#print axioms Eip8282.Audit.Integrator.SystemTraceWitness.instantiate
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryMonotone.expansion_fit
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryMonotone.raw_bounds
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryMonotone.accepted
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryMonotone.runs
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryMonotone.suffix_bounds
#print axioms Eip8282.Audit.Integrator.SystemExecutionResources.complete
#print axioms Eip8282.Audit.Integrator.SystemExecutionResources.intermediate
#print axioms Eip8282.Audit.Integrator.SystemExecutionResources.deposit
#print axioms Eip8282.Audit.Integrator.SystemExecutionResources.exit
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryCharges.raw_expansion
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryCharges.accepted_expansion
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryCharges.of_runs
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryCharges.TraceCharges.telescopes
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryCharges.from_runs
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryCharges.bounded_from_runs
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryCharges.return_expansion
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryCharges.return_capacity
#print axioms Eip8282.Audit.Integrator.SystemMemoryResources.attach
#print axioms Eip8282.Audit.Integrator.SystemMemoryResources.deposit
#print axioms Eip8282.Audit.Integrator.SystemMemoryResources.exit
#print axioms Eip8282.Audit.Integrator.ReferenceEnvironmentOps.toList_eq
#print axioms Eip8282.Audit.Integrator.ReferenceEnvironmentOps.load_bytes
#print axioms Eip8282.Audit.Integrator.ReferenceEnvironmentOps.caller_value
#print axioms Eip8282.Audit.Integrator.ReferenceEnvironmentOps.caller_step
#print axioms Eip8282.Audit.Integrator.ReferenceEnvironmentOps.callvalue_step
#print axioms Eip8282.Audit.Integrator.ReferenceEnvironmentOps.calldatasize_value
#print axioms Eip8282.Audit.Integrator.ReferenceEnvironmentOps.calldatasize_step
#print axioms Eip8282.Audit.Integrator.ReferenceEnvironmentOps.calldataload_step
#print axioms Eip8282.Audit.Integrator.ReferenceEnvironmentOps.running_pc
#print axioms Eip8282.Audit.Integrator.ReferenceEnvironmentOps.python_load
#print axioms Eip8282.Audit.Integrator.ReferenceOrdinaryGas.excluded
#print axioms Eip8282.Audit.Integrator.ReferenceOrdinaryGas.defined_bound
#print axioms Eip8282.Audit.Integrator.ReferenceOrdinaryGas.charge
#print axioms Eip8282.Audit.Integrator.ReferenceOrdinaryGas.charge_bounded
#print axioms Eip8282.Audit.Integrator.ReferenceOrdinaryGas.list_bound
#print axioms Eip8282.Audit.Integrator.ReferenceOrdinaryGas.annotate
#print axioms Eip8282.Audit.Integrator.ReferenceMeterPath.pay_success
#print axioms Eip8282.Audit.Integrator.ReferenceMeterPath.payment
#print axioms Eip8282.Audit.Integrator.ReferenceMeterPath.budgets_append
#print axioms Eip8282.Audit.Integrator.ReferenceMeterPath.run_append
#print axioms Eip8282.Audit.Integrator.SystemMeterResources.edge
#print axioms Eip8282.Audit.Integrator.SystemMeterResources.from_charges
#print axioms Eip8282.Audit.Integrator.SystemMeterResources.pay_completed
#print axioms Eip8282.Audit.Integrator.SystemMeterResources.deposit
#print axioms Eip8282.Audit.Integrator.SystemMeterResources.exit
#print axioms Eip8282.Audit.Integrator.SystemMeterResources.envelopes

-- Same actual SYSTEM trace, source-shaped views, terminal and three receipt guarantees.
#print axioms Eip8282.Audit.Integrator.ReferenceAcceptedStack.bounds
#print axioms Eip8282.Audit.Integrator.ReferenceAcceptedStack.pop1
#print axioms Eip8282.Audit.Integrator.ReferenceAcceptedStack.pop2
#print axioms Eip8282.Audit.Integrator.ReferenceAcceptedStack.pop3
#print axioms Eip8282.Audit.Integrator.ReferenceAcceptedStack.dup_inputs
#print axioms Eip8282.Audit.Integrator.ReferenceAcceptedStack.swap_inputs
#print axioms Eip8282.Audit.Integrator.ReferenceStorageStep.store_metadata
#print axioms Eip8282.Audit.Integrator.ReferenceStorageStep.charged_related
#print axioms Eip8282.Audit.Integrator.ReferenceStorageStep.sload
#print axioms Eip8282.Audit.Integrator.ReferenceStorageStep.sstore
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeSites.sites_eq
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeSites.nonhalting_site
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeSites.decode_matches
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeSites.pc_fit
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeSites.jump_member
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeView.words_related
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeView.charged
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeView.owner_next
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeView.initial_related
#print axioms Eip8282.Audit.Integrator.ReferenceStorageViewAction.sload
#print axioms Eip8282.Audit.Integrator.ReferenceStorageViewAction.sstore
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryViewAction.mstore
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryViewAction.mstore8
#print axioms Eip8282.Audit.Integrator.ReferenceReturnView.terminal
#print axioms Eip8282.Audit.Integrator.ReferenceReturnView.halted
#print axioms Eip8282.Audit.Integrator.ReferenceReturnSlice.output_eq_extract
#print axioms Eip8282.Audit.Integrator.ReferenceDecodeShape.no_argument
#print axioms Eip8282.Audit.Integrator.ReferenceDecodeShape.argument_width
#print axioms Eip8282.Audit.Integrator.ReferenceDecodeShape.fixed
#print axioms Eip8282.Audit.Integrator.ReferencePureAction.classify_sound
#print axioms Eip8282.Audit.Integrator.ReferencePureAction.raw_dispatch
#print axioms Eip8282.Audit.Integrator.ReferencePureAction.related_advance
#print axioms Eip8282.Audit.Integrator.ReferencePureAction.related_jump
#print axioms Eip8282.Audit.Integrator.ReferencePureAction.binary
#print axioms Eip8282.Audit.Integrator.ReferencePureEnvironment.accepted
#print axioms Eip8282.Audit.Integrator.ReferencePureControl.pop
#print axioms Eip8282.Audit.Integrator.ReferencePureControl.jump
#print axioms Eip8282.Audit.Integrator.ReferencePureControl.jumpi
#print axioms Eip8282.Audit.Integrator.ReferencePureControl.push
#print axioms Eip8282.Audit.Integrator.ReferencePureControl.dup
#print axioms Eip8282.Audit.Integrator.ReferencePureControl.swap
#print axioms Eip8282.Audit.Integrator.ReferencePureControl.accepted
#print axioms Eip8282.Audit.Integrator.ReferencePureComplete.family
#print axioms Eip8282.Audit.Integrator.ReferencePureComplete.accepted
#print axioms Eip8282.Audit.Integrator.ReferenceSystemAction.cases_of_nonhalting
#print axioms Eip8282.Audit.Integrator.ReferenceSystemAction.step
#print axioms Eip8282.Audit.Integrator.ReferenceTerminalDecode.nonstop_site
#print axioms Eip8282.Audit.Integrator.ReferenceTerminalDecode.decode_matches
#print axioms Eip8282.Audit.Integrator.ReferenceTerminalDecode.decode_some
#print axioms Eip8282.Audit.Integrator.ReferenceTerminalDecode.return_decode
#print axioms Eip8282.Audit.Integrator.ReferenceSystemTrace.Viewed.erase
#print axioms Eip8282.Audit.Integrator.ReferenceSystemTrace.from_runs
#print axioms Eip8282.Audit.Integrator.ReferenceSystemTrace.attach
#print axioms Eip8282.Audit.Integrator.ReferenceSystemEntry.attach
#print axioms Eip8282.Audit.Integrator.ReferenceSystemEntry.deposit
#print axioms Eip8282.Audit.Integrator.ReferenceSystemEntry.exit
#print axioms Eip8282.Audit.Integrator.ReferenceSystemEndpoint.xi_result
#print axioms Eip8282.Audit.Integrator.ReferenceSystemEndpoint.nonempty
#print axioms Eip8282.Audit.Integrator.ReferenceSystemEndpoint.commits
#print axioms Eip8282.Audit.Integrator.ReferenceSystemGuarantees.attach
#print axioms Eip8282.Audit.Integrator.ReferenceSystemGuarantees.system

-- Source readings/warmth on the same SYSTEM paid trace, and local calldata copy.
#print axioms Eip8282.Audit.Integrator.ReferenceSourceReadings.reading_eq
#print axioms Eip8282.Audit.Integrator.ReferenceSourceReadings.original_readTracked
#print axioms Eip8282.Audit.Integrator.ReferenceSourceReadings.original_write
#print axioms Eip8282.Audit.Integrator.ReferenceStorageWarmth.accepted_warm
#print axioms Eip8282.Audit.Integrator.ReferenceActionMetadata.pure_storage
#print axioms Eip8282.Audit.Integrator.ReferenceActionMetadata.pure_reads
#print axioms Eip8282.Audit.Integrator.ReferenceActionMetadata.created
#print axioms Eip8282.Audit.Integrator.ReferenceSystemReadingsTrace.source_price
#print axioms Eip8282.Audit.Integrator.ReferenceSystemReadingsTrace.priced_runs
#print axioms Eip8282.Audit.Integrator.ReferenceSystemReadingsTrace.Coupled.priced
#print axioms Eip8282.Audit.Integrator.ReferenceSystemReadingsTrace.Coupled.viewed
#print axioms Eip8282.Audit.Integrator.ReferenceSystemReadingsTrace.from_priced
#print axioms Eip8282.Audit.Integrator.ReferenceSystemSourcePayment.attach
#print axioms Eip8282.Audit.Integrator.ReferenceSystemSourcePayment.Whole.observed
#print axioms Eip8282.Audit.Integrator.ReferenceSystemSourcePayment.Whole.paid
#print axioms Eip8282.Audit.Integrator.ReferenceSystemSourceEntry.attach
#print axioms Eip8282.Audit.Integrator.ReferenceSystemSourceEntry.deposit
#print axioms Eip8282.Audit.Integrator.ReferenceSystemSourceEntry.exit
#print axioms Eip8282.Audit.Integrator.ReferenceSystemSourceEntry.guarantees
#print axioms Eip8282.Audit.Integrator.ReferenceCopyMemory.copySlice_size_le
#print axioms Eip8282.Audit.Integrator.ReferenceCopyMemory.write_size_le
#print axioms Eip8282.Audit.Integrator.ReferenceCopyMemory.padded_write
#print axioms Eip8282.Audit.Integrator.ReferenceCopyMemory.copy_related
#print axioms Eip8282.Audit.Integrator.ReferenceCalldataCopy.accepted

-- Complete runtime views, resource-derived memory bounds and the same actual receipt.
#print axioms Eip8282.Audit.Integrator.ReferenceLogView.data_slice
#print axioms Eip8282.Audit.Integrator.ReferenceLogView.accepted
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeAction.step
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeTrace.Viewed.erase
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeTrace.from_runs
#print axioms Eip8282.Audit.Integrator.ReferenceRevertView.terminal
#print axioms Eip8282.Audit.Integrator.ReferenceRevertView.halted
#print axioms Eip8282.Audit.Integrator.RuntimeRevertTrace.revert_step
#print axioms Eip8282.Audit.Integrator.RuntimeRevertTrace.revert_trace
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryFunding.expansion_cost
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryFunding.accepted_energy
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryFunding.runs_energy
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryFunding.capacity_of_energy
#print axioms Eip8282.Audit.Integrator.RuntimeMemoryFunding.runs_capacity
#print axioms Eip8282.Audit.Integrator.ReferenceStopView.terminal
#print axioms Eip8282.Audit.Integrator.ReferenceAllDecode.decode_matches
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeCompletion.success
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeCompletion.revert
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeEndpoint.nonempty
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeEndpoint.xi_success
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeEndpoint.theta_success
#print axioms Eip8282.Audit.Integrator.CallRevert.false_cases
#print axioms Eip8282.Audit.Integrator.CallRevert.xi_revert_X
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeReceipt.xi_revert
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeReceipt.observe
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeReceipt.guarantees

-- Exact source readings and complete runtime resource certificates on the same receipt.
#print axioms Eip8282.Audit.Integrator.ReferenceCopyLogGas.ceil_words
#print axioms Eip8282.Audit.Integrator.ReferenceCopyLogGas.copy_source
#print axioms Eip8282.Audit.Integrator.ReferenceCopyLogGas.defined
#print axioms Eip8282.Audit.Integrator.ReferenceCopyLogGas.accepted_copy
#print axioms Eip8282.Audit.Integrator.ReferenceCopyLogGas.accepted_log
#print axioms Eip8282.Audit.Integrator.ReferenceCopyLogGas.related_cost
#print axioms Eip8282.Audit.Integrator.ReferenceCopyLogGas.related_event
#print axioms Eip8282.Audit.Integrator.ReferenceCopyLogGas.charge
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeReadings.created
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeReadings.Coupled.viewed
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeReadings.from_viewed
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimePriceBounds.accepted
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimePayment.state_total
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimePayment.execution_bound
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimePayment.payment
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeTerminalPayment.success_cost
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeTerminalPayment.revert_cost
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeTerminalPayment.success
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeTerminalPayment.revert
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeResourceReceipt.strengthen
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeResourceReceipt.guarantees

-- Intrinsic admission produces calldata fit; exact initialized history extends through ordered SYSTEM calls.
#print axioms Eip8282.Audit.Integrator.TransactionCalldataAdmission.data_cost
#print axioms Eip8282.Audit.Integrator.TransactionCalldataAdmission.intrinsic_bound
#print axioms Eip8282.Audit.Integrator.TransactionCalldataAdmission.calldata_fit
#print axioms Eip8282.Audit.Integrator.ProtocolSystemSequence.completes
#print axioms Eip8282.Audit.Integrator.ProtocolSystemSequence.append
#print axioms Eip8282.Audit.Integrator.ProtocolSystemSequence.extends_history
#print axioms Eip8282.Audit.Integrator.FactorySystemSequence.from_genesis_both
#print axioms Eip8282.Audit.Integrator.TransactionAdmissionHistory.append
#print axioms Eip8282.Audit.Integrator.TransactionAdmissionHistory.receipt_effects

-- Source calldata admission and split-pool payment on the same complete receipt.
#print axioms Eip8282.Audit.Integrator.ReferenceCalldataAdmission.floor_bound
#print axioms Eip8282.Audit.Integrator.ReferenceCalldataAdmission.data_fit
#print axioms Eip8282.Audit.Integrator.ReferenceCalldataAdmission.boundary
#print axioms Eip8282.Audit.Integrator.ReferenceIntrinsicGap.source_floor_gates
#print axioms Eip8282.Audit.Integrator.ReferenceIntrinsicGap.old_intrinsic
#print axioms Eip8282.Audit.Integrator.ReferenceIntrinsicGap.no_floor_implication
#print axioms Eip8282.Audit.Integrator.ReferenceAdmissionHistory.append
#print axioms Eip8282.Audit.Integrator.ReferenceAdmissionHistory.receipt_effects
#print axioms Eip8282.Audit.Integrator.ReferenceTransactionGas.allocation
#print axioms Eip8282.Audit.Integrator.ReferenceTransactionGas.floor_paid
#print axioms Eip8282.Audit.Integrator.ReferenceTransactionGas.settlement
#print axioms Eip8282.Audit.Integrator.ReferenceSharedPayment.pay_success
#print axioms Eip8282.Audit.Integrator.ReferenceSharedPayment.payment
#print axioms Eip8282.Audit.Integrator.ReferenceTransactionPayment.payment
#print axioms Eip8282.Audit.Integrator.ReferenceTransactionPayment.below_cap
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeTransactionPayment.success
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeTransactionPayment.revert
#print axioms Eip8282.Audit.Integrator.ReferenceAllocatedReceipt.strengthen
#print axioms Eip8282.Audit.Integrator.ReferenceAllocatedReceipt.guarantees

-- Actual storage state-credit balance, same-receipt net gas and frame-meter rollback.
#print axioms Eip8282.Audit.Integrator.ReferenceStoragePotential.step
#print axioms Eip8282.Audit.Integrator.ReferenceStoragePotential.telescope
#print axioms Eip8282.Audit.Integrator.ReferenceStoragePotential.from_original
#print axioms Eip8282.Audit.Integrator.ReferenceStorageFlow.action_delta
#print axioms Eip8282.Audit.Integrator.ReferenceStorageFlow.charges_balance
#print axioms Eip8282.Audit.Integrator.ReferenceStorageFlow.of_coupled
#print axioms Eip8282.Audit.Integrator.ReferenceMeterRollback.commit_accounting
#print axioms Eip8282.Audit.Integrator.ReferenceMeterRollback.restore_accounting
#print axioms Eip8282.Audit.Integrator.ReferenceMeterRollback.restore_nonnegative
#print axioms Eip8282.Audit.Integrator.ReferenceMeterRollback.entry_accounting
#print axioms Eip8282.Audit.Integrator.ReferenceMeterConservation.pay_balance
#print axioms Eip8282.Audit.Integrator.ReferenceMeterConservation.run_balance
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeStateBalance.action_balance
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeStateBalance.of_coupled
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeStateBalance.empty_potential
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeStateBalance.nonnegative
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeStateBalance.from_empty
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeGasBalance.log_cost
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeGasBalance.balance
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeGasBalance.through_terminal
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeGasBalance.fresh_transaction
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeGasCertificate.success
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeGasCertificate.revert
#print axioms Eip8282.Audit.Integrator.ReferenceAccountedReceipt.strengthen
#print axioms Eip8282.Audit.Integrator.ReferenceAccountedReceipt.guarantees
#print axioms Eip8282.Audit.Integrator.ReferenceMeterBoundary.accounting
#print axioms Eip8282.Audit.Integrator.ReferenceMeterBoundary.rollback_accounting
#print axioms Eip8282.Audit.Integrator.ReferenceMeterBoundary.reverted_logs

-- Source CALL grants, child settlement and failed protected-frame gas.
#print axioms Eip8282.Audit.Integrator.ReferenceChildMeter.init_fields
#print axioms Eip8282.Audit.Integrator.ReferenceChildMeter.settled_failure_guards
#print axioms Eip8282.Audit.Integrator.ReferenceChildMeter.exceptional_order
#print axioms Eip8282.Audit.Integrator.ReferenceChildMeter.repay_accounting
#print axioms Eip8282.Audit.Integrator.ReferenceChildMeter.incorporate_accounting
#print axioms Eip8282.Audit.Integrator.ReferenceChildMeter.failed_incorporation
#print axioms Eip8282.Audit.Integrator.ReferenceCallGrant.split_accounting
#print axioms Eip8282.Audit.Integrator.ReferenceCallGrant.charged_split
#print axioms Eip8282.Audit.Integrator.ReferenceCallChildBoundary.completes
#print axioms Eip8282.Audit.Integrator.ReferenceCallChildBoundary.failed_logs

-- Execution-potential ledger and actual completed append instruction costs.
#print axioms Eip8282.Audit.Integrator.ReferenceExecutionPotential.paid_work
#print axioms Eip8282.Audit.Integrator.ReferenceExecutionPotential.executed_logs
#print axioms Eip8282.Audit.Integrator.ReferenceExecutionPotential.restore_preserves
#print axioms Eip8282.Audit.Integrator.ReferenceExecutionPotential.commit_preserves
#print axioms Eip8282.Audit.Integrator.ReferenceExecutionPotential.entry_preserves
#print axioms Eip8282.Audit.Integrator.ReferenceExecutionPotential.settle_nonincrease
#print axioms Eip8282.Audit.Integrator.ReferenceExecutionPotential.incorporate_preserves
#print axioms Eip8282.Audit.Integrator.ReferenceExecutionPotential.credit_preserves
#print axioms Eip8282.Audit.Integrator.ReferenceExecutionPotential.split_potential
#print axioms Eip8282.Audit.Integrator.ReferenceCallPotential.execution_debit
#print axioms Eip8282.Audit.Integrator.ReferenceCallPotential.state_preserves
#print axioms Eip8282.Audit.Integrator.ReferenceCallPotential.prepared_debit
#print axioms Eip8282.Audit.Integrator.ReferenceCallPotential.overhead_exact
#print axioms Eip8282.Audit.Integrator.ReferenceCallPotential.call_work
#print axioms Eip8282.Audit.Integrator.ReferenceExecutionLedger.work_cast
#print axioms Eip8282.Audit.Integrator.ReferenceExecutionLedger.creation_potential
#print axioms Eip8282.Audit.Integrator.ReferenceExecutionLedger.creation_work
#print axioms Eip8282.Audit.Integrator.ReferenceExecutionLedger.bounded
#print axioms Eip8282.Audit.Integrator.ReferenceTransactionWork.allocated_work
#print axioms Eip8282.Audit.Integrator.ReferenceTransactionWork.appends_le_execution_charge
#print axioms Eip8282.Audit.Integrator.ReferenceTransactionWork.floor_execution
#print axioms Eip8282.Audit.Integrator.ReferenceAppendOccurrences.Marked.erase
#print axioms Eip8282.Audit.Integrator.ReferenceAppendOccurrences.Marked.selected_le
#print axioms Eip8282.Audit.Integrator.ReferenceAppendOccurrences.store_one
#print axioms Eip8282.Audit.Integrator.ReferenceAppendOccurrences.exit_suffix
#print axioms Eip8282.Audit.Integrator.ReferenceAppendOccurrences.deposit_suffix
#print axioms Eip8282.Audit.Integrator.ReferenceTraceAgreement.blocked_of_stop
#print axioms Eip8282.Audit.Integrator.ReferenceTraceAgreement.blocked_of_terminal
#print axioms Eip8282.Audit.Integrator.ReferenceTraceAgreement.complete_unique
#print axioms Eip8282.Audit.Integrator.ReferenceAppendEntry.exit_entry
#print axioms Eip8282.Audit.Integrator.ReferenceAppendEntry.deposit_entry
#print axioms Eip8282.Audit.Integrator.ReferenceCoupledPrefix.same_fuel
#print axioms Eip8282.Audit.Integrator.ReferenceCoupledPrefix.split_at
#print axioms Eip8282.Audit.Integrator.ReferenceAppendPrice.marker_price
#print axioms Eip8282.Audit.Integrator.ReferenceAppendPrice.selected_cost
#print axioms Eip8282.Audit.Integrator.ReferenceAppendPrice.exact_marker_costs
#print axioms Eip8282.Audit.Integrator.ReferenceAppendCompletedCost.align_success
#print axioms Eip8282.Audit.Integrator.ReferenceAppendCompletedCost.exit_cost
#print axioms Eip8282.Audit.Integrator.ReferenceAppendCompletedCost.deposit_cost
#print axioms Eip8282.Audit.Integrator.ReferenceSelectedAppendWork.ProtectedPaid.cost
#print axioms Eip8282.Audit.Integrator.ReferenceSelectedAppendWork.ProtectedPaid.run
#print axioms Eip8282.Audit.Integrator.ReferenceSelectedAppendWork.Selected.accounted
#print axioms Eip8282.Audit.Integrator.ReferenceSelectedAppendWork.transaction_count

-- Reverse protected effects and constructed guarded replay; source extraction remains explicit.
#print axioms Eip8282.Audit.Integrator.ReferenceReplayCost.opcode_ratio
#print axioms Eip8282.Audit.Integrator.ReferenceActionDeterminism.deterministic
#print axioms Eip8282.Audit.Integrator.ReferenceActionDeterminism.unchecked_caller
#print axioms Eip8282.Audit.Integrator.ReferenceActionDeterminism.full_stack_caller_rejected
#print axioms Eip8282.Audit.Integrator.ReferenceSourceStackAdmission.pop_length
#print axioms Eip8282.Audit.Integrator.ReferenceSourceStackAdmission.push_length
#print axioms Eip8282.Audit.Integrator.ReferenceSourceStackAdmission.run_bounded
#print axioms Eip8282.Audit.Integrator.ReferenceSourceStackAdmission.popMany_length
#print axioms Eip8282.Audit.Integrator.ReferenceSourceStackAdmission.pushMany_length
#print axioms Eip8282.Audit.Integrator.ReferenceSourceStackAdmission.admission
#print axioms Eip8282.Audit.Integrator.ReferenceSourceStackAdmission.old_admission
#print axioms Eip8282.Audit.Integrator.ReferenceSourceStackAdmission.from_empty
#print axioms Eip8282.Audit.Integrator.ReferenceSourceStackAdmission.injected_overfull_push
#print axioms Eip8282.Audit.Integrator.ReferencePureReverseEnvironment.raw
#print axioms Eip8282.Audit.Integrator.ReferencePureReverseBinary.raw
#print axioms Eip8282.Audit.Integrator.ReferenceReplayMemoryCost.raw_memory
#print axioms Eip8282.Audit.Integrator.ReferenceReplayMemoryCost.memory_component
#print axioms Eip8282.Audit.Integrator.ReferenceReplayMemoryCost.total_ratio
#print axioms Eip8282.Audit.Integrator.ReferenceReplayMemoryCost.word_fit
#print axioms Eip8282.Audit.Integrator.ReferencePureReverseControl.raw
#print axioms Eip8282.Audit.Integrator.ReferenceStorageReverse.load
#print axioms Eip8282.Audit.Integrator.ReferenceStorageReverse.store
#print axioms Eip8282.Audit.Integrator.ReferenceActionStackBounds.balance
#print axioms Eip8282.Audit.Integrator.ReferenceActionStackBounds.admission
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryReverse.mstore
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryReverse.mstore8
#print axioms Eip8282.Audit.Integrator.ReferencePureReverseComplete.family
#print axioms Eip8282.Audit.Integrator.ReferencePureReverseComplete.raw
#print axioms Eip8282.Audit.Integrator.ReferenceCopyLogReverse.copy
#print axioms Eip8282.Audit.Integrator.ReferenceCopyLogReverse.log
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeReverse.raw
#print axioms Eip8282.Audit.Integrator.ReferenceActionControlAdmission.jump_member
#print axioms Eip8282.Audit.Integrator.ReferenceActionControlAdmission.jump_guards
#print axioms Eip8282.Audit.Integrator.ReferenceActionControlAdmission.static_guard
#print axioms Eip8282.Audit.Integrator.ReferenceActionControlAdmission.other_guards
#print axioms Eip8282.Audit.Integrator.ReferenceReplayAdmission.base_charged
#print axioms Eip8282.Audit.Integrator.ReferenceReplayAdmission.base_replay
#print axioms Eip8282.Audit.Integrator.ReferenceReplayAdmission.z
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeReplay.step
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeReplay.priced_step

-- Arbitrary finite source-shaped complete replay and paid append leaf producers.
#print axioms Eip8282.Audit.Integrator.ReferenceActionMemoryBounds.computed
#print axioms Eip8282.Audit.Integrator.ReferenceActionMemoryBounds.preserves_alignment
#print axioms Eip8282.Audit.Integrator.ReferenceActionMemoryBounds.monotone
#print axioms Eip8282.Audit.Integrator.ReferenceActionMemoryBounds.positive_endpoint
#print axioms Eip8282.Audit.Integrator.ReferenceActionMemoryBounds.empty_aligned
#print axioms Eip8282.Audit.Integrator.ReferenceSourceReplayTrace.host_of_cost
#print axioms Eip8282.Audit.Integrator.ReferenceSourceReplayTrace.Run.memory_le
#print axioms Eip8282.Audit.Integrator.ReferenceSourceReplayTrace.Run.stack_bound
#print axioms Eip8282.Audit.Integrator.ReferenceSourceReplayTrace.replay
#print axioms Eip8282.Audit.Integrator.ReferenceTerminalReplay.returned
#print axioms Eip8282.Audit.Integrator.ReferenceTerminalReplay.reverted
#print axioms Eip8282.Audit.Integrator.ReferenceTerminalReplay.stop
#print axioms Eip8282.Audit.Integrator.ReferenceSourceReplayEntry.gas_exact
#print axioms Eip8282.Audit.Integrator.ReferenceSourceReplayEntry.context
#print axioms Eip8282.Audit.Integrator.ReferenceSourceReplayEntry.from_entry
#print axioms Eip8282.Audit.Integrator.ReferenceSourceReplayCompletion.stop
#print axioms Eip8282.Audit.Integrator.ReferenceSourceReplayCompletion.returned
#print axioms Eip8282.Audit.Integrator.ReferenceSourceReplayCompletion.reverted
#print axioms Eip8282.Audit.Integrator.ReferenceSourceAppendCost.exit_cost
#print axioms Eip8282.Audit.Integrator.ReferenceSourceAppendCost.deposit_cost
#print axioms Eip8282.Audit.Integrator.ReferenceSourcePaidAppend.exit
#print axioms Eip8282.Audit.Integrator.ReferenceSourcePaidAppend.deposit

-- Checked source handlers and nested resource/protocol context producers.
#print axioms Eip8282.Audit.Integrator.ReferenceResourceEntryBound.call_entry
#print axioms Eip8282.Audit.Integrator.ReferenceResourceEntryBound.creation_entry
#print axioms Eip8282.Audit.Integrator.ReferenceResourceEntryBound.EntryAt.sound_top
#print axioms Eip8282.Audit.Integrator.ReferenceResourceEntryBound.EntryAt.potential_le
#print axioms Eip8282.Audit.Integrator.ReferenceResourceEntryBound.EntryAt.cap
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedBinaryStep.success
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedBinaryStep.empty
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedBinaryStep.one
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedBinaryStep.out_of_gas
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedBinaryStep.overflow
#print axioms Eip8282.Audit.Integrator.ReferenceNestedSourceAppend.transaction_entry
#print axioms Eip8282.Audit.Integrator.ReferenceNestedSourceAppend.exit
#print axioms Eip8282.Audit.Integrator.ReferenceNestedSourceAppend.deposit
#print axioms Eip8282.Audit.Integrator.ReferenceParentEquivalence.flatten_equivalent
#print axioms Eip8282.Audit.Integrator.ReferenceParentEquivalence.current_eq
#print axioms Eip8282.Audit.Integrator.ReferenceParentEquivalence.original_eq
#print axioms Eip8282.Audit.Integrator.ReferenceParentEquivalence.reading_eq
#print axioms Eip8282.Audit.Integrator.ReferenceParentEquivalence.action
#print axioms Eip8282.Audit.Integrator.ReferenceParentEquivalence.price
#print axioms Eip8282.Audit.Integrator.ReferenceParentEquivalence.run
#print axioms Eip8282.Audit.Integrator.ReferenceParentEquivalence.commit_equivalent
#print axioms Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction.meter_unchecked
#print axioms Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction.keyOf_toByteArray
#print axioms Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction.frame_call
#print axioms Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction.mandatory_call
#print axioms Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction.frame_pinned
#print axioms Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction.xi_callerW
#print axioms Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction.xi_slots
#print axioms Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction.xi_owner
#print axioms Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction.xi_warm
#print axioms Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction.source_whole
#print axioms Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction.source_guarantees
#print axioms Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction.mandatory_pair
#print axioms Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction.source_pair
#print axioms Eip8282.Audit.Integrator.ReferenceAdmissionExtraction.calldataFloor_eq
#print axioms Eip8282.Audit.Integrator.ReferenceAdmissionExtraction.effectivePrice_le_feeCap
#print axioms Eip8282.Audit.Integrator.ReferenceAdmissionExtraction.priorityFee_le_effectivePrice
#print axioms Eip8282.Audit.Integrator.ReferenceAdmissionExtraction.upfront_le
#print axioms Eip8282.Audit.Integrator.ReferenceAdmissionExtraction.admission
#print axioms Eip8282.Audit.Integrator.ReferenceAdmissionExtraction.gate
#print axioms Eip8282.Audit.Integrator.ReferenceAdmissionExtraction.append
#print axioms Eip8282.Audit.Integrator.ReferenceAdmissionExtraction.receipt_effects
#print axioms Eip8282.Audit.Integrator.ReferenceAdmissionExtraction.AdmissionExtractionTest.dynamic_pricing
#print axioms Eip8282.Audit.Integrator.ReferenceAdmissionExtraction.AdmissionExtractionTest.floor_ne_old_intrinsic
#print axioms Eip8282.Audit.Integrator.ProtocolSlotExtraction.accepted_pairwise
#print axioms Eip8282.Audit.Integrator.ProtocolSlotExtraction.accepted_nodup
#print axioms Eip8282.Audit.Integrator.ProtocolSlotExtraction.accepted_count
#print axioms Eip8282.Audit.Integrator.ProtocolSlotExtraction.projected_nodup
#print axioms Eip8282.Audit.Integrator.ProtocolSlotExtraction.el_nodup
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalExtraction.queueStage_guarded
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalExtraction.guarded_of_length
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalExtraction.sweepStage_guarded
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalExtraction.items_bounded
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalExtraction.total_count
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalExtraction.total_blocks
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalExtraction.dispatched_counts
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalStageExtraction.pendingStage_guarded
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalStageExtraction.pendingStage_bound
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalStageExtraction.block_slot
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalStageExtraction.items_bounded
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalStageExtraction.total_count
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalExpectationState.expected_bounded
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalExpectationState.update_bounded
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalExpectationState.retained
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalExpectationState.payload_slots
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalExpectationState.total_count
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalExpectationState.dispatched_counts
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalExpectationState.candidate_total_count
#print axioms Eip8282.Audit.Integrator.ProtocolWithdrawalExpectationState.candidate_dispatched_counts

-- Checked runtime handler/trace/terminal producers: audited local source interfaces.
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeWorkLength.positive
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeWorkLength.length_le_work
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeWorkLength.paid_length
#print axioms Eip8282.Audit.Integrator.ReferenceRuntimeWorkLength.no_infinite_paid
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedEnvironmentStep.underflow
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedEnvironmentStep.size_overflow
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedEnvironmentStep.finish_out_of_gas
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedEnvironmentStep.finish_overflow
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedEnvironmentStep.success
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedStackControlStep.success
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedStorageStep.load_out_of_gas
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedStorageStep.store_static
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedStorageStep.store_one
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedStorageStep.store_sentry
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedStorageStep.load_success
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedStorageStep.store_success
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryExpansionSource.ceil_eq
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryExpansionSource.aligned
#print axioms Eip8282.Audit.Integrator.ReferenceMemoryExpansionSource.zero
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedMemoryStore.success
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedCopyLogStep.expanded_capacity
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedCopyLogStep.expanded_slice
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedCopyLogStep.success
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedCopyLogStep.log_static
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedRuntimeTrace.Step.sound
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedRuntimeTrace.runFull_append
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedRuntimeTrace.Run.extract
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedRuntimeTrace.Run.length_bound
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedAppend.exit
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedAppend.deposit
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedTerminalStep.stop
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedTerminalStep.slice
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedTerminalStep.out_of_gas
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDecode.padded_eq_buffer
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDecode.decode_width
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDecode.stack_control
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDecode.nonpush

-- Computed source dispatch/evaluator and exact terminal observation consumers.
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedCompletion.paid_bound
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedCompletion.stop
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedCompletion.slice
#print axioms Eip8282.Audit.Integrator.ReferenceSourceOpcodeTable.tags_nodup
#print axioms Eip8282.Audit.Integrator.ReferenceSourceOpcodeTable.source_count
#print axioms Eip8282.Audit.Integrator.ReferenceSourceOpcodeTable.invalid_examples
#print axioms Eip8282.Audit.Integrator.ReferenceSourceOpcodeTable.extended_valid
#print axioms Eip8282.Audit.Integrator.ReferenceSourceOpcodeTable.known_valid
#print axioms Eip8282.Audit.Integrator.ReferenceSourceOpcodeTable.protected_count
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatch.select_facts
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatch.read_eof
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatch.read_handler
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatch.read_opcode
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatch.runHandler_step
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatch.step
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatchTerminal.terminal
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatchTerminal.runtime_coverage
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedEvaluator.extract
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedEvaluator.progress
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedEvaluator.sufficient
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedEvaluator.completes
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedExecution.terminal
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedExecution.transaction_terminal
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedExecution.final_site_or_eof

-- Computed EOF/fault, exact frame projection, log prefix and child meter consumers.
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedEOF.lookup
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedEOF.fields
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedEOF.execution
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedFaultClass.caught_iff
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedFaultClass.conversion_classes
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedFaultClass.assertion_class
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedFaultClass.caught_class
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatchMetadata.binary
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatchMetadata.environment
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatchMetadata.stackControl
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatchMetadata.memoryStore
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatchMetadata.copyLog
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatchMetadata.load
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatchMetadata.store
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatchMetadata.terminal
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatchMetadata.handler
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedDispatchMetadata.run_metadata
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedFrameOutcome.success_logs
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedFrameOutcome.failed
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedFrameOutcome.uncaught
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedFrameOutcome.reverted
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedFrameOutcome.failed_evaluation
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedLogContext.action_suffix
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedLogContext.trace_suffix
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedLogContext.success_contribution
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedLogContext.terminal_logs
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedLogContext.terminal_contribution
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedFrameMeter.evaluated
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedFrameMeter.initialized
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedFrameMeter.failed_child
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedFrameMeter.reverted_child

-- Exact scoped release exports.
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedTheta.context
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedTheta.terminal
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedTheta.eof
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedPrefix.action_env
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedPrefix.trace_env
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedPrefix.evaluated_bounds
#print axioms Eip8282.Audit.Integrator.ReleaseCandidate.invariants
#print axioms Eip8282.Audit.Integrator.ReleaseCandidate.installed_call
#print axioms Eip8282.Audit.Integrator.ReleaseCandidate.call
#print axioms Eip8282.Audit.Integrator.ReleaseCandidate.composed
#print axioms Eip8282.Audit.Integrator.ReleaseCandidate.enabled_numerator
#print axioms Eip8282.Audit.Integrator.ReleaseCandidate.checked_terminal
#print axioms Eip8282.Audit.Integrator.ReleaseCandidate.checked_eof
#print axioms Eip8282.Audit.Integrator.ReleaseGetterProgress.after_history
#print axioms Eip8282.Audit.Integrator.ReleaseSubmitProgress.after_history
#print axioms Eip8282.Audit.Integrator.ReleaseInhibitionCycle.after_history

-- Post-release account-aware source projection and same-outcome consumers.
#print axioms Eip8282.Audit.Integrator.ReferenceAccountLookup.tracked_peek
#print axioms Eip8282.Audit.Integrator.ReferenceAccountLookup.deletion_masks
#print axioms Eip8282.Audit.Integrator.ReferenceAccountLookup.read_recorded
#print axioms Eip8282.Audit.Integrator.ReferenceAccountLookup.rollback_lookup
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedAccountDispatch.result
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedAccountDispatch.writes
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedAccountDispatch.lookup
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedAccountDispatch.continued
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedAccountEvaluator.projection
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedAccountEvaluator.writes
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedAccountEvaluator.evaluated
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedAccountEvaluator.sufficient
#print axioms Eip8282.Audit.Integrator.ReferenceAccountGuarantees.terminal
#print axioms Eip8282.Audit.Integrator.ReferenceAccountGuarantees.eof

-- Derived protected failure classification and projected settlement.
#print axioms Eip8282.Audit.Integrator.ReferenceCodeAccountPresence.absent_empty
#print axioms Eip8282.Audit.Integrator.ReferenceCodeAccountPresence.nonempty_present
#print axioms Eip8282.Audit.Integrator.ReferenceCodeAccountPresence.fresh_system_owner
#print axioms Eip8282.Audit.Integrator.ReferenceAccountFaults.dispatch_no_owner
#print axioms Eip8282.Audit.Integrator.ReferenceAccountFaults.evaluated_no_owner
#print axioms Eip8282.Audit.Integrator.ReferenceAccountFaults.code_fetch_no_owner
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedStackControlStep.prepare_pc
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedStackControlStep.prepare_no_conversion
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedStackControlStep.operate_no_conversion
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedStackControlStep.run_no_conversion
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedConversionSafety.dispatch
#print axioms Eip8282.Audit.Integrator.ReferenceDerivedFailure.caught
#print axioms Eip8282.Audit.Integrator.ReferenceDerivedFailure.settled
#print axioms Eip8282.Audit.Integrator.ReferenceHistoryFailure.settled

-- Source guarded transfer and pre-transfer snapshot failure consumer.
#print axioms Eip8282.Audit.Integrator.ReferenceSourceValueTransfer.modify_hash
#print axioms Eip8282.Audit.Integrator.ReferenceSourceValueTransfer.modify_protected_storage
#print axioms Eip8282.Audit.Integrator.ReferenceSourceValueTransfer.move_hash
#print axioms Eip8282.Audit.Integrator.ReferenceSourceValueTransfer.move_protected_storage
#print axioms Eip8282.Audit.Integrator.ReferenceSourceValueTransfer.enter_hash
#print axioms Eip8282.Audit.Integrator.ReferenceSourceValueTransfer.enter_protected_storage
#print axioms Eip8282.Audit.Integrator.ReferenceSourceValueTransfer.enter_code
#print axioms Eip8282.Audit.Integrator.ReferenceSourceValueTransfer.enter_reads
#print axioms Eip8282.Audit.Integrator.ReferenceSourceValueTransfer.loaded_nonempty_hash
#print axioms Eip8282.Audit.Integrator.ReferenceSourceValueTransfer.enter_load
#print axioms Eip8282.Audit.Integrator.ReferenceSourceValueTransfer.enter_loaded_reads
#print axioms Eip8282.Audit.Integrator.ReferenceTransferredFailure.caught
#print axioms Eip8282.Audit.Integrator.ReferenceTransferredFailure.restore_fields
#print axioms Eip8282.Audit.Integrator.ReferenceTransferredFailure.settled

-- Candidate funded source entry and same-outcome guarantee/failure compositions.
#print axioms Eip8282.Audit.Integrator.ReferenceSourceTransferFunding.modify_balance
#print axioms Eip8282.Audit.Integrator.ReferenceSourceTransferFunding.debit_balance
#print axioms Eip8282.Audit.Integrator.ReferenceSourceTransferFunding.enter_success
#print axioms Eip8282.Audit.Integrator.ReferenceSourceTransferFunding.after_history
#print axioms Eip8282.Audit.Integrator.ReferenceSourceTransferFunding.represented_balances
#print axioms Eip8282.Audit.Integrator.ReferenceSourceTransferFunding.represented_success
#print axioms Eip8282.Audit.Integrator.ReferenceSourceFundedEntry.prepared
#print axioms Eip8282.Audit.Integrator.ReferenceSourceFundedFailure.settled
#print axioms Eip8282.Audit.Integrator.ReferenceSourceFundedGuarantees.terminal
#print axioms Eip8282.Audit.Integrator.ReferenceSourceFundedGuarantees.eof

-- Candidate same-receipt source balances; canonical frame extraction remains open.
#print axioms Eip8282.Audit.Integrator.ReferenceSourceBalanceTransport.move_balances
#print axioms Eip8282.Audit.Integrator.ReferenceSourceBalanceTransport.enter_balances
#print axioms Eip8282.Audit.Integrator.ReferenceSourceBalanceTransport.after_history
#print axioms Eip8282.Audit.Integrator.ReferenceSourceBalanceOutcome.same_writes
#print axioms Eip8282.Audit.Integrator.ReferenceSourceBalanceOutcome.evaluated
#print axioms Eip8282.Audit.Integrator.ReferenceSourceBalanceOutcome.restored
#print axioms Eip8282.Audit.Integrator.RuntimeBalancePreservation.raw_preserved
#print axioms Eip8282.Audit.Integrator.RuntimeBalancePreservation.accepted_preserved
#print axioms Eip8282.Audit.Integrator.RuntimeBalancePreservation.x_preserved
#print axioms Eip8282.Audit.Integrator.RuntimeBalancePreservation.execution_preserved
#print axioms Eip8282.Audit.Integrator.RuntimeBalancePreservation.theta_balances
#print axioms Eip8282.Audit.Integrator.ReferenceSourceCompletedBalances.of_completed
#print axioms Eip8282.Audit.Integrator.ReferenceSourceCompletedBalances.original
#print axioms Eip8282.Audit.Integrator.ReferenceSourceBalancedGuarantees.terminal
#print axioms Eip8282.Audit.Integrator.ReferenceSourceBalancedGuarantees.eof
#print axioms Eip8282.Audit.Integrator.ReferenceSourceBalancedFailure.settled

-- Candidate actual transaction checkpoint domain and same source receipt.
#print axioms Eip8282.Audit.Integrator.ReferenceCheckpointCall.domain
#print axioms Eip8282.Audit.Integrator.ReferenceCheckpointCall.pinned
#print axioms Eip8282.Audit.Integrator.ReferenceCheckpointCall.selected_code
#print axioms Eip8282.Audit.Integrator.ReferenceCheckpointCall.selected_request
#print axioms Eip8282.Audit.Integrator.ReferenceCheckpointCall.call_result
#print axioms Eip8282.Audit.Integrator.ReferenceSourcePreparedBounds.prepared
#print axioms Eip8282.Audit.Integrator.ReferenceCheckpointGuarantees.terminal
#print axioms Eip8282.Audit.Integrator.ReferenceCheckpointGuarantees.eof
#print axioms Eip8282.Audit.Integrator.ReferencePinnedFailure.caught
#print axioms Eip8282.Audit.Integrator.ReferencePinnedFailure.settled
#print axioms Eip8282.Audit.Integrator.ReferenceCheckpointFailure.settled

-- Candidate ordered source prepayment and nonblob before-transaction consumers.
#print axioms Eip8282.Audit.Integrator.ReferenceSourcePrepayment.increment_form
#print axioms Eip8282.Audit.Integrator.ReferenceSourcePrepayment.increment_account
#print axioms Eip8282.Audit.Integrator.ReferenceSourcePrepayment.successful_account
#print axioms Eip8282.Audit.Integrator.ReferenceSourcePrepayment.fields
#print axioms Eip8282.Audit.Integrator.ReferenceSourcePrepayment.successful_hash
#print axioms Eip8282.Audit.Integrator.ReferenceSourcePrepayment.successful_load
#print axioms Eip8282.Audit.Integrator.ReferenceSourcePrepaidCheckpoint.funded
#print axioms Eip8282.Audit.Integrator.ReferenceSourcePrepaidCheckpoint.success
#print axioms Eip8282.Audit.Integrator.ReferenceSourcePrepaidCheckpoint.balances
#print axioms Eip8282.Audit.Integrator.ReferenceSourcePrepaidCheckpoint.fields
#print axioms Eip8282.Audit.Integrator.ReferenceSourcePrepaidCheckpoint.loaded
#print axioms Eip8282.Audit.Integrator.ReferenceSourcePrepaidCheckpoint.bindings
#print axioms Eip8282.Audit.Integrator.ReferencePrepaidGuarantees.terminal
#print axioms Eip8282.Audit.Integrator.ReferencePrepaidGuarantees.eof
#print axioms Eip8282.Audit.Integrator.ReferencePrepaidFailure.settled

-- Candidate computed initial access-list warmth and scanned destinations.
#print axioms Eip8282.Audit.Integrator.ReferenceInitialAccess.warm_member
#print axioms Eip8282.Audit.Integrator.ReferenceInitialAccess.access_contains
#print axioms Eip8282.Audit.Integrator.ReferenceInitialAccess.related
#print axioms Eip8282.Audit.Integrator.ReferenceInitialAccess.scanned_context
#print axioms Eip8282.Audit.Integrator.ReferenceInitializedGuarantees.terminal
#print axioms Eip8282.Audit.Integrator.ReferenceInitializedGuarantees.eof
#print axioms Eip8282.Audit.Integrator.ReferenceInitializedFailure.settled

-- Candidate source dispatch, allocated meter and derived admission consumers.
#print axioms Eip8282.Audit.Integrator.ReferenceSourceDispatch.loaded_alive
#print axioms Eip8282.Audit.Integrator.ReferenceSourceDispatch.ready
#print axioms Eip8282.Audit.Integrator.ReferenceSourceDispatch.pinned_ordinary
#print axioms Eip8282.Audit.Integrator.ReferenceSourceDispatch.ready_fetched
#print axioms Eip8282.Audit.Integrator.ReferenceSourceDispatch.allocated_bound
#print axioms Eip8282.Audit.Integrator.ReferenceAllocatedEntry.zeroes_fit
#print axioms Eip8282.Audit.Integrator.ReferenceAllocatedEntry.admission
#print axioms Eip8282.Audit.Integrator.ReferenceAllocatedEntry.allocated
#print axioms Eip8282.Audit.Integrator.ReferenceAllocatedEntry.dispatched
#print axioms Eip8282.Audit.Integrator.ReferenceAllocatedEntry.entered_eq
#print axioms Eip8282.Audit.Integrator.ReferenceAllocatedGuarantees.terminal
#print axioms Eip8282.Audit.Integrator.ReferenceAllocatedGuarantees.eof
#print axioms Eip8282.Audit.Integrator.ReferenceAllocatedFailure.settled

-- Candidate exhaustive same-run allocated-call safety, no supplied endpoint.
#print axioms Eip8282.Audit.Integrator.ReferenceSupportedOutcome.site_table
#print axioms Eip8282.Audit.Integrator.ReferenceSupportedOutcome.read_supported
#print axioms Eip8282.Audit.Integrator.ReferenceSupportedOutcome.handler_supported
#print axioms Eip8282.Audit.Integrator.ReferenceSupportedOutcome.run_supported
#print axioms Eip8282.Audit.Integrator.ReferenceSupportedOutcome.evaluated
#print axioms Eip8282.Audit.Integrator.ReferenceSupportedOutcome.account_evaluated
#print axioms Eip8282.Audit.Integrator.ReferenceAllocatedExecution.prepared
#print axioms Eip8282.Audit.Integrator.ReferenceAllocatedExecution.completed
#print axioms Eip8282.Audit.Integrator.ReferenceAllocatedTotal.verified

-- Full emitted current-frame logs: exact same evaluation and settlement.
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedStackControlStep.push_definition
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixHandlers.binary
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixHandlers.environment
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixHandlers.memoryStore
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixHandlers.copyLog
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixHandlers.load
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixHandlers.store
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixHandlers.terminal
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixHandlers.prepare
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixHandlers.operate
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixHandlers.stackControl
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixEvaluation.handler
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixEvaluation.dispatch
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixEvaluation.assertion
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixEvaluation.account
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixEvaluation.eval
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixSettlement.settled
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixSettlement.successful
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixSettlement.failed
#print axioms Eip8282.Audit.Integrator.ReferenceLogPrefixSettlement.unchanged
#print axioms Eip8282.Audit.Integrator.ReferenceFullLogExecution.fresh
#print axioms Eip8282.Audit.Integrator.ReferenceFullLogExecution.initial_eq
#print axioms Eip8282.Audit.Integrator.ReferenceFullLogExecution.transport
#print axioms Eip8282.Audit.Integrator.ReferenceFullLogExecution.extracted
#print axioms Eip8282.Audit.Integrator.ReferenceFullLogTotal.verified

-- Same full-frame transaction gas settlement with derived fresh-journal guards.
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedStateGas.source_balance
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedStateGas.checked_balance
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedStateGas.terminal_balance
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedStateGas.fresh_guards
#print axioms Eip8282.Audit.Integrator.ReferenceFreshStorageEntry.enter
#print axioms Eip8282.Audit.Integrator.ReferenceFreshStorageEntry.probe
#print axioms Eip8282.Audit.Integrator.ReferenceFreshStorageEntry.allocated
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedRefund.class_bounds
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedRefund.action_balance
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedRefund.source_balance
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedRefund.empty_potential
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedRefund.nonnegative
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedRefund.delta_upper
#print axioms Eip8282.Audit.Integrator.ReferenceRefundCounter.pay_refund
#print axioms Eip8282.Audit.Integrator.ReferenceRefundCounter.run_refund
#print axioms Eip8282.Audit.Integrator.ReferenceRefundCounter.full_refund
#print axioms Eip8282.Audit.Integrator.ReferenceRefundCounter.fresh_prefix
#print axioms Eip8282.Audit.Integrator.ReferenceRefundCounter.fresh_terminal
#print axioms Eip8282.Audit.Integrator.ReferenceMeterMetadata.handler
#print axioms Eip8282.Audit.Integrator.ReferenceMeterMetadata.dispatch
#print axioms Eip8282.Audit.Integrator.ReferenceOutcomeGas.paid_valid
#print axioms Eip8282.Audit.Integrator.ReferenceOutcomeGas.terminal
#print axioms Eip8282.Audit.Integrator.ReferenceOutcomeGas.eof
#print axioms Eip8282.Audit.Integrator.ReferenceOutcomeGas.failed
#print axioms Eip8282.Audit.Integrator.ReferenceTransactionSettlement.settled
#print axioms Eip8282.Audit.Integrator.ReferenceFullGasTotal.verified

#print axioms Eip8282.Audit.Integrator.ReferenceSourceFeeCredit.successful
#print axioms Eip8282.Audit.Integrator.ReferenceSourceFeeCredit.hash
#print axioms Eip8282.Audit.Integrator.ReferenceSourceFeeCredit.protected_storage
#print axioms Eip8282.Audit.Integrator.ReferenceSourceFeeCredit.fields
#print axioms Eip8282.Audit.Integrator.ReferenceSourceFeeDisbursement.funded
#print axioms Eip8282.Audit.Integrator.ReferenceSourceFeeDisbursement.protected_storage
#print axioms Eip8282.Audit.Integrator.ReferenceSourceFeeAmounts.price_base
#print axioms Eip8282.Audit.Integrator.ReferenceSourceFeeAmounts.partition
#print axioms Eip8282.Audit.Integrator.ReferenceSourceFeeAmounts.actual
#print axioms Eip8282.Audit.Integrator.ReferenceSettledAccountJournal.storage
#print axioms Eip8282.Audit.Integrator.ReferenceSettledAccountJournal.balances
#print axioms Eip8282.Audit.Integrator.ReferenceSettledAccountJournal.hash
#print axioms Eip8282.Audit.Integrator.ReferenceSettledAccountJournal.derived
#print axioms Eip8282.Audit.Integrator.ReferenceSourceFeeFinalization.actual
#print axioms Eip8282.Audit.Integrator.ReferenceFullFeeTotal.verified

#print axioms Eip8282.Audit.Integrator.ReferenceOutcomeGas.terminal_paid
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedSystemEntry.code
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedSystemEntry.constructed
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedSystemEntry.ready
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedSystemEntry.bindings
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedSystemExecution.computed
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedSystemExecution.extracted
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedSystemOutcome.proved
#print axioms Eip8282.Audit.Integrator.ReferenceSystemOutputMeter.facts
#print axioms Eip8282.Audit.Integrator.ReferenceSystemOutputMeter.fresh_paid
#print axioms Eip8282.Audit.Integrator.ReferenceSystemOutputReceipt.settled
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedSystemJournal.unchanged
#print axioms Eip8282.Audit.Integrator.ReferenceCheckedSystemTotal.verified
