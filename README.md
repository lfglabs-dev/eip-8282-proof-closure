# EIP-8282 Proof Closure

This repo holds Lean evidence for **three** EIP-8282 predeploy guarantees,
against pinned `ethereum/sys-asm@83f9801245ff56878a450b5625801101b9a225a1`
and the working EIP text at `lfglabs-dev/EIPs@b759aae8` (PR
[ethereum/EIPs#12120](https://github.com/ethereum/EIPs/pull/12120), stacked
diff [lfglabs-dev/EIPs#1](https://github.com/lfglabs-dev/EIPs/pull/1)).

Lean theorems decide what is proved. `audit/guarantees.yaml` only classifies
them.

Each guarantee is evidenced in two layers:

1. **Abstract Lean 4 model** — the high-level algorithm. Supporting, not a substitute for bytecode.
2. **Pinned runtime bytecode under `EvmYul.EVM.Ξ`** — the real bytes, really executed. This is the load-bearing layer.

| # | ID | Abstract Lean | Pinned bytecode (Ξ) |
| --- | --- | --- | --- |
| 1 | `P-SUBMIT-1` | CHECKED | CHECKED (concrete traces) |
| 2 | `P-DRAIN-1` | CHECKED | CHECKED (concrete traces) |
| 3 | `P-CONTROL-1` | CHECKED | CHECKED (concrete traces) |

### What the bytecode layer does and does not say

`Eip8282.Audit.Guarantees.PSubmit1.psubmit1_bytecode_parent` runs the bytes of
`pinned/bytecode/builder_{deposits,exits}/main.hex` inside `EvmYul.EVM.Ξ` —
not an abstraction of them — and checks the fee getter, the value-bearing
rejection, the paid append (calldata verbatim for deposits, `msg.sender` first
for exits), the anonymous `LOG0` on each write (184-byte deposit calldata /
68-byte exit `msg.sender || pubkey`, zero topics), inhibited reverts, and
underpay: a well-formed 184-byte deposit / 48-byte exit whose `msg.value` is
strictly below the quoted fee reverts with no observable storage write. The
same write-path facts are re-run at a second reachable-shaped image
(`excess=50 count=3 head=2 tail=6`).

It is **a finite set of concrete traces at two storage images**, not a
universally quantified theorem. What makes it load-bearing rather than
decorative is `Eip8282.Tests.PSubmit1Mutant`: flipping **one byte** of the
pinned deposit runtime (offset 158, `RETURN` → `REVERT`) makes the *same*
`submitFacts` the parent is registered against evaluate to `false`;
flipping the user-path `LOG0` size at offset 274 (`PUSH1 184` → `PUSH1 0`)
leaves the six-word append intact but empties the log; and flipping the
handle_input fee `CALLVALUE` at offset 161 (`CALLVALUE` → `GAS`) lets an
underpaying 184-byte deposit succeed and write, so the underpay freeze
fails on both images. The mutation is to bytecode, not to a model function.
`log_mutant_leaves_siblings_intact` and
`underpay_mutant_leaves_siblings_intact` prove those cuts leave
`PDrain1.drainFacts` and `PControl1.controlFacts` true.

`Eip8282.Audit.Guarantees.PControl1.pcontrol1_nonempty_bytecode_parent` is the
registered P-CONTROL-1 parent. It still executes the pinned runtimes under
`EvmYul.EVM.Ξ` via `EvmRunner.runDeposit` / `runDepositSystem` /
`runExitSystem`, which differ from the user runners *only in `msg.sender`*.
Wave 1's empty-queue `pcontrol1_bytecode_parent` remains checked. Wave 5
adds nonempty images (`QUEUE_HEAD = 0`, `QUEUE_TAIL ∈ {2,17,65}`): a system
call must drain (`368` / `11776` deposit bytes, `136` / `1088` exit bytes)
*and* fold `SLOT_EXCESS` to `97` / `103` (or latch `INHIBITOR` / clear to
`0`), while a fee quote on the same image leaves the queue pointers
untouched. Those return sizes and `HEAD`/`TAIL` moves are false if the
queue were empty, so the parent is not a restatement of Wave 1.

`Eip8282.Audit.Guarantees.PDrain1.pdrain1_bytecode_parent` is the FIFO drain
itself: a `SYSTEM_ADDR` call against a seeded queue returns the oldest
`min(length, cap)` records as a contiguous `RECORD_SIZE` buffer (68-byte
exits / 184-byte deposits), advances `QUEUE_HEAD` by that many (or zeroes
both pointers on a full drain), and recodes only the deposit amount field
from big-endian storage to little-endian return bytes. The user fee-getter
on the same image does not consume the queue.

P-CONTROL-1's Wave-5 kill-line, `Eip8282.Tests.PControl1Mutant.wave5_mutant_refutes_nonempty_parent`,
feeds two system-side `TARGET_PER_BLOCK` cuts to the same `nonemptyControlFacts`
the parent is registered against: builder_deposits offset 571 (`PUSH1 8` →
`9`) and builder_exits offset 401 (`PUSH1 2` → `3`). With the deposit cut,
`depositQueue 2` stores excess `96` not `97`; with the exit cut, `exitQueue 2`
stores `102` not `103`. The Wave-1 gate `EQ` at offset 22 also falsifies the
nonempty parent. `wave5_mutants_leave_psubmit1_intact` proves both new cuts
leave `PSubmit1.submitFacts` **true**. P-SUBMIT-1 never calls from
`SYSTEM_ADDR` and never reaches `compute_excess`, so the nonempty parent is
not a restatement of a sibling.

P-DRAIN-1's kill-line, `Eip8282.Tests.PDrain1Mutant`, cuts six drain-only
bytes: the exit `MAX_PER_BLOCK` clamp at offset 244 (`PUSH1 16` → `PUSH1 8`),
the exit system `RECORD_SIZE` multiplier at offset 450 (`PUSH1 68` →
`PUSH1 64`), the deposit `MAX_PER_BLOCK` clamp at offset 304
(`PUSH1 64` → `PUSH1 32`), the partial-drain `QUEUE_HEAD` store at
deposit offset 483 (`PUSH1 2` → `PUSH1 9`), the same deposit store
retargeted onto slot 196 (`PUSH1 2` → `PUSH1 196`, first word of drained
item 32), and the exit partial-drain `QUEUE_HEAD` store at offset 313
(`PUSH1 2` → `PUSH1 25`, src word of drained exit item 7). Each makes the
*same* `drainFacts` evaluate to `false`. With the exit-cap cut, seventeen
queued exits return 8 records and the head advances to 8; the under-cap
two-record drain is untouched. With the deposit-cap cut, sixty-five
queued deposits return 32 records and the head advances to 32; the
empty-queue and under-cap deposit drains are untouched. With the
Wave-3 head-slot cut, the 64-record drain still returns 11776 bytes but
writes the new head `64` into slot 9 (last remaining word of drained
item 0) instead of `QUEUE_HEAD`, so the remaining-word conjunct fails.
With the Wave-6 deposit head-slot cut, that same `64` is written into
slot 196 so `staleDepositPk1Is 32` fails. With the Wave-6 exit head-slot
cut, the new head `16` is written into slot 25 so `staleExitSrcIs 7`
fails. After the same traces the parent also pins leftover storage: all
six words of deposit item 0, all five remaining words of deposit item 1,
the first word of deposit item 32, all six words of deposit item 63,
still-queued deposit item 64, and all three words of exit items 0, 7 and
15. `drain_mutants_leave_siblings_intact` proves all six mutants leave
`PSubmit1.submitFacts` and `PControl1.controlFacts` **true**:
P-SUBMIT-1 never calls from `SYSTEM_ADDR`, and P-CONTROL-1's empty-queue
facts hold `QUEUE_HEAD = QUEUE_TAIL = 0`, so the partial-drain head
stores are never taken and `0 * RECORD_SIZE` is still 0.

Two disclosed costs, both in `audit/assumptions.yaml`:

- `A-NATIVE-DECIDE` — `Ξ` reaches `D_J_aux`, a `partial def`, so the kernel
  cannot reduce a concrete trace. `native_decide` is forced; the Lean compiler
  and the EVMYulLean interpreter join the trusted base. `Eip8282.Audit.Trust`
  prints exactly which theorems carry it.
- `A-EVM-WORLD` — the world is synthetic (two accounts, a fixed family of
  storage images).

Deployment provenance and the constructor bytecode are out of the current claim.

The three IDs are the smallest coherent audit surface:

1. **submission** — admission, money, atomic rejection, authentic append, caller binding;
2. **drain** — FIFO conservation, caps, encoding, queue reuse;
3. **control state** — fee, count, initial gating, reversible inhibition.

Wording, assumptions, source spans, next gates: `audit/guarantees.yaml`.

## Reproduce

Needs [elan](https://github.com/leanprover/elan) and Lean 4.31.0.

```bash
make audit-check
make prove
make check
```

`make prove` first runs `lake build EvmYul.FFI.ffi:dynlib`. That is not
optional: `native_decide` runs the compiled EVMYulLean interpreter, which
needs the keccak/sha2 FFI as shared objects. `lakefile.lean` passes both to
`lean` via `--load-dynlib`, `libleanffi.so` first (otherwise `memset_zero` is
unresolved).

One guarantee, plus its kill-line:

```bash
lake build EvmYul.FFI.ffi:dynlib
lake build Eip8282.Audit.Guarantees.PSubmit1 Eip8282.Tests.PSubmit1Mutant
```

## Layout

- `Eip8282/Audit/` — abstract model, `Bytecode` pins, the `EvmRunner` Ξ driver,
  guarantee modules, trust report, facade
- `Eip8282/Tests/` — model mutants and the P-SUBMIT-1 / P-DRAIN-1 / P-CONTROL-1 bytecode kill-lines; not public guarantees
- `audit/` — registry, source map, assumptions, pins
- `pinned/` — frozen sys-asm sources, bytecode and EIP text (sha256-locked;
  `scripts/audit_metadata.py` also checks the Lean hex literals against them)
- `scripts/` — fail-closed checks

## Scope

In scope: Builder Deposit `0x0000bFF46984e3725691FA540a8C7589300D8282` and
Builder Exit `0x000064D678505ad48F8cCb093BC65613800E8282`.

Out of scope: EIP-7732 bidding, consensus-layer handling, BLS validity,
EIP-7685 wrapping, and on-chain deployment identity.
