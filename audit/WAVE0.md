# Wave 0 — load-bearing review (2026-08-19)

Bar: a registered parent is load-bearing only if
1. its conclusion is not a tautology / restated hypothesis / definitional fact,
2. a kill-line mutant refutes *that parent*, not a sibling or disconnected model,
3. YAML/report scope matches what Lean actually proves,
4. the execution plane is **pinned EIP-8282 bytecode** under **EVMYulLean `EVM.Ξ`**,
   not an abstract `userCall`/`systemCall` model.

Live `main` at `739a4e7` (and this foundation commit) **fails the bar for all three IDs**.

## P-SUBMIT-1 — DEFECTIVE (addressed; see below)

> **Wave 1 status.** The registered parent is now
> `PSubmit1.psubmit1_bytecode_parent`, which executes
> `pinned/bytecode/builder_{deposits,exits}/main.hex` under `EVM.Ξ`. The
> kill-line `Eip8282.Tests.PSubmit1Mutant.mutant_refutes_parent` flips one
> byte of the deposit runtime and refutes that same parent. Bar items 1, 2
> and 4 are met; item 3 holds for the declared scope, which is concrete
> traces at one storage image (`A-EVM-WORLD`), not a universally quantified
> claim. `native_decide` is forced by `D_J_aux` being `partial`
> (`A-NATIVE-DECIDE`). P-DRAIN-1 and P-CONTROL-1 remain as written below.

Registered parent: `success_count_and_balance`.
It unfolds `userCall` and `simp`s `appendRecord`. The conclusion restates the
definition of the abstract interpreter. Mutants in `Eip8282/Tests/Mutants.lean`
are examples about the same interpreter (`capOf = 64`, fee-getter revert);
none is a kill-line against a bytecode parent.

YAML claims 184-byte admission, authentic append, `sourceAddress = caller`.
Lean does not execute `pinned/bytecode/builder_deposits/main.hex`.

## P-DRAIN-1 — DEFECTIVE

Registered parent: `fifo_bounded` = `systemCall s b |>.state.queue = s.queue.drop (capOf s.kind)`.
Definitional. `system_always_succeeds` is `rfl` on `.success`. No mutant
refutes a drain of the real runtime. YAML claims SYSTEM_ADDRESS, 30M gas,
LE amount conversion; none is an `EVM.Ξ` fact.

## P-CONTROL-1 — DEFECTIVE

`empty_updates_excess` unfolds `nextExcess`. `targets` is `rfl`.
`initial_gating` is `rfl` on abstract constructors, not on `exitInit` bytecode
(`PUSH 0xff..ff; SSTORE slot 0`). YAML claims `fake_exponential` and reversible
inhibition of the deployed contracts; Lean never runs the hex.

## Foundation this wave adds (not a closed guarantee)

- Pin `bytecode/*/main.hex` and `ctor.hex` with sha256 in `audit/artifacts.lock.json`.
- `Eip8282.Audit.Bytecode` — hex literals matching those files.
- `Eip8282.Audit.EvmRunner` — `EVM.Ξ` driver.
- `lakefile.lean` requires `EVMYulLean@f7e4ee0dc8f8d5265ce822a937ab5be771f182e9`.

Next: one writer per ID, one branch, one draft PR. Re-register the parent as a
theorem about `EvmRunner.runDeposit` / `runExit` / `runDepositSystem` /
`runExitSystem`. Kill-line must mutate the **bytecode or the runner observation
of that bytecode**, not `Model.userCall`. No `sorry`. No abstract-model CHECKED
as a substitute for bytecode CHECKED.
