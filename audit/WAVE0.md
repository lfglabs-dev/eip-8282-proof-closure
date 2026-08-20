# Wave 0 — load-bearing review (2026-08-19)

Bar: a registered parent is load-bearing only if
1. its conclusion is not a tautology / restated hypothesis / definitional fact,
2. a kill-line mutant refutes *that parent*, not a sibling or disconnected model,
3. YAML/report scope matches what Lean actually proves,
4. the execution plane is **pinned EIP-8282 bytecode** under **EVMYulLean `EVM.Ξ`**,
   not an abstract `userCall`/`systemCall` model.

Live `main` at `739a4e7` (and this foundation commit) **fails the bar for all three IDs**.
P-SUBMIT-1, P-CONTROL-1 and P-DRAIN-1 have since been re-registered on the
pinned bytecode.

## P-SUBMIT-1 — DEFECTIVE (addressed; see below)

> **Wave 1 status.** The registered parent is now
> `PSubmit1.psubmit1_bytecode_parent`, which executes
> `pinned/bytecode/builder_{deposits,exits}/main.hex` under `EVM.Ξ`. The
> kill-line `Eip8282.Tests.PSubmit1Mutant.mutant_refutes_parent` flips one
> byte of the deposit runtime and refutes that same parent. Bar items 1, 2
> and 4 are met; item 3 holds for the declared scope, which is concrete
> traces at one storage image (`A-EVM-WORLD`), not a universally quantified
> claim. `native_decide` is forced by `D_J_aux` being `partial`
> (`A-NATIVE-DECIDE`).
>
> **Wave 4 status.** The same parent now also asserts the anonymous `LOG0`
> the write path actually emits. After a paid deposit, `Ξ` pushes one log
> with zero topics and 184 data bytes equal to the calldata; after a paid
> exit, one log with zero topics and 68 data bytes equal to
> `msg.sender || pubkey`. `EvmRunner` projects `Aₗ` from the successful
> `Ξ` `Substate` (topics length, data size, data bytes) — it does not
> invent a receipt. The kill-line additionally flips the user-path
> `PUSH1 RECORD_SIZE` at deposit offset 274 (`0xb8` → `0x00`), so the
> paid append still writes six words but `LOG0` data size is 0 and the
> same `submitFacts` is false. The calldatacopy size at 269, the `LOG0`
> opcode at 276, the exit user-path size at 215, and P-DRAIN-1's system
> `RETURN` size at exit 450 are left alone.
> `log_mutant_leaves_siblings_intact` proves the new mutant leaves
> `PDrain1.drainFacts` and `PControl1.controlFacts` **true**.

Registered parent: `success_count_and_balance`.
It unfolds `userCall` and `simp`s `appendRecord`. The conclusion restates the
definition of the abstract interpreter. Mutants in `Eip8282/Tests/Mutants.lean`
are examples about the same interpreter (`capOf = 64`, fee-getter revert);
none is a kill-line against a bytecode parent.

YAML claims 184-byte admission, authentic append, `sourceAddress = caller`.
Lean does not execute `pinned/bytecode/builder_deposits/main.hex`.

## P-DRAIN-1 — DEFECTIVE (addressed; see below)

> **Wave 1 status.** The registered parent is now
> `PDrain1.pdrain1_bytecode_parent`, which executes
> `pinned/bytecode/builder_{deposits,exits}/main.hex` under `EVM.Ξ` via
> `EvmRunner.runDepositSystem` / `runExitSystem`. The kill-line
> `Eip8282.Tests.PDrain1Mutant.mutant_refutes_parent` flips two drain-only
> bytes of the exit runtime — the `MAX_PER_BLOCK` clamp at offset 244 and
> the system `RECORD_SIZE` multiplier at offset 450 — and refutes that same
> `drainFacts`. Bar items 1, 2 and 4 are met; item 3 holds for the declared
> scope, which is concrete traces at a handful of queue depths
> (`A-EVM-WORLD`), not a universally quantified claim. `native_decide` is
> forced by `D_J_aux` being `partial` (`A-NATIVE-DECIDE`).
>
> On bar item 2 specifically,
> `drain_mutants_leave_siblings_intact` proves both mutants leave
> `PSubmit1.submitFacts` and `PControl1.controlFacts` **true**: these bytes
> are invisible to the sibling guarantees (P-SUBMIT-1 never calls from
> `SYSTEM_ADDR`; P-CONTROL-1 holds an empty queue), so the P-DRAIN-1 parent
> is carrying weight nothing else in this repository carries.
>
> **Wave 2 status.** The same parent now also exercises the deposit
> per-block cap of 64 (65 queued deposits → 64 records / 11776 bytes,
> `QUEUE_HEAD = 64`, `QUEUE_TAIL = 65`) and the empty-queue deposit drain
> as a separate conjunct. The kill-line additionally flips the deposit
> `MAX_PER_BLOCK` clamp at offset 304 (`PUSH1 64` → `PUSH1 32`) and
> refutes the extended `drainFacts`. The comparison immediate at offset
> 296 is left alone, so under-cap deposit drains stay true. Sibling
> independence is re-proved for the new mutant.
>
> **Wave 3 status.** Stale-slot non-erasure is now load-bearing for more
> than deposit item 0's first word. After the 64-record deposit drain the
> parent asserts the remaining five words of item 0, the first word of
> drained item 63, and the first word of still-queued item 64. After the
> 16-record exit drain it asserts the first two words of item 0 and the
> first word of item 15 (`QUEUE_HEAD = 16`, `QUEUE_TAIL = 17`). The
> kill-line additionally flips the partial-drain `QUEUE_HEAD` SSTORE
> immediate at deposit offset 483 (`PUSH1 2` → `PUSH1 9`), so the
> advanced head value 64 is written into slot 9 (last remaining word of
> drained item 0) instead of slot 2; `staleDepositRestIs 0` fails and
> the same `drainFacts` is false. The empty-queue reset operand at offset 494 is
> left alone, so under-cap full drains stay true. Sibling independence
> is re-proved for the new mutant.

Registered parent was `fifo_bounded` = `systemCall s b |>.state.queue = s.queue.drop (capOf s.kind)`.
Definitional. `system_always_succeeds` is `rfl` on `.success`. No mutant
refuted a drain of the real runtime. YAML claimed SYSTEM_ADDRESS, 30M gas,
LE amount conversion; none was an `EVM.Ξ` fact.

## P-CONTROL-1 — DEFECTIVE (addressed; see below)

> **Wave 1 status.** The registered parent is now
> `PControl1.pcontrol1_bytecode_parent`, which executes
> `pinned/bytecode/builder_{deposits,exits}/main.hex` under `EVM.Ξ`. System
> calls reach the runtimes through `EvmRunner.runDepositSystem` /
> `runExitSystem`, which differ from the user runners only in `msg.sender`, so
> the caller gate is exercised by two runs of the same bytes rather than
> assumed. Bar items 1, 2 and 4 are met; item 3 holds for the declared scope,
> which is concrete traces over a fixed family of storage images at an empty
> queue (`A-EVM-WORLD`), not a universally quantified claim.
>
> The kill-line `Eip8282.Tests.PControl1Mutant.mutant_refutes_parent` cuts
> three single bytes — the `EQ` at offset 22 of each runtime, which compares
> `CALLER` against `SYSTEM_ADDR`, and the `TARGET_PER_BLOCK` operand at offset
> 571 of the deposit runtime, inside the `compute_excess` block only the system
> subroutine reaches — and refutes that same `controlFacts`. On bar item 2
> specifically, `control_mutants_leave_psubmit1_intact` proves both deposit
> mutants leave `PSubmit1.submitFacts` **true**: these bytes are invisible to
> the sibling guarantee, so the P-CONTROL-1 parent is carrying weight nothing
> else in this repository carries.
>
> Still open after Wave 1 and recorded in `audit/guarantees.yaml`: the
> empty-queue parent left the drain/excess interaction unexercised,
> `fake_exponential` is pinned only relationally, and `initial_gating` is
> still abstract because the exits ctor is not executed.
>
> **Wave 5 status.** The registered parent is now
> `PControl1.pcontrol1_nonempty_bytecode_parent`. The same pinned runtimes
> run under `EVM.Ξ`, but against nonempty queue images (`QUEUE_HEAD = 0`,
> `QUEUE_TAIL ∈ {2,17,65}`) with distinctive 6-slot deposit / 3-slot exit
> records. A system call must *both* drain (`2*184=368`, `64*184=11776`,
> `2*68=136`, `16*68=1088`) *and* fold `SLOT_EXCESS` via
> `max(0, excess+count-TARGET)` (`100+5-8=97` / `100+5-2=103`) or latch
> `INHIBITOR`. A fee quote on the same image leaves `HEAD 0 TAIL 2`
> untouched. Those return sizes and pointer moves are false on an empty
> queue, so the claim is not a restatement of Wave 1.
>
> The kill-line `Eip8282.Tests.PControl1Mutant.wave5_mutant_refutes_nonempty_parent`
> feeds two system-side `TARGET_PER_BLOCK` cuts to the same
> `nonemptyControlFacts`: deposit offset 571 (`PUSH1 8` → `9`) and exit
> offset 401 (`PUSH1 2` → `3`). With the deposit cut, `depositQueue 2`
> stores excess 96 not 97; with the exit cut, `exitQueue 2` stores 102
> not 103. The Wave-1 gate cut at offset 22 also falsifies the nonempty
> parent. `wave5_mutants_leave_psubmit1_intact` proves both new cuts
> leave `PSubmit1.submitFacts` **true**. `nonempty_is_not_empty` shows
> the under-cap nonempty fact is not the empty-queue observation
> (`368` vs `0` return bytes).

Registered parent was `empty_updates_excess`, which unfolds `nextExcess`.
`targets` is `rfl`. `initial_gating` is `rfl` on abstract constructors, not on
`exitInit` bytecode (`PUSH 0xff..ff; SSTORE slot 0`). YAML claimed
`fake_exponential` and reversible inhibition of the deployed contracts; Lean
never ran the hex.

## Foundation this wave adds (not a closed guarantee)

- Pin `bytecode/*/main.hex` and `ctor.hex` with sha256 in `audit/artifacts.lock.json`.
- `Eip8282.Audit.Bytecode` — hex literals matching those files.
- `Eip8282.Audit.EvmRunner` — `EVM.Ξ` driver.
- `lakefile.lean` requires `EVMYulLean@f7e4ee0dc8f8d5265ce822a937ab5be771f182e9`.

Next: one writer per ID, one branch, one draft PR. Re-register the parent as a
theorem about `EvmRunner.runDeposit` / `runExit` / `runDepositSystem` /
`runExitSystem`. Kill-line must mutate the **bytecode or the runner observation
of that bytecode**, not `Model.userCall`. No `sorry`. No abstract-model CHECKED
as a substitute for bytecode CHECKED. P-DRAIN-1's draft follows that same
recipe.
