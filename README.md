# EIP-8282 Proof Closure

This repo holds Lean evidence for **three** EIP-8282 predeploy guarantees,
against pinned `ethereum/sys-asm@83f9801245ff56878a450b5625801101b9a225a1`
and the working EIP text at `lfglabs-dev/EIPs@b759aae8` (PR
[ethereum/EIPs#12120](https://github.com/ethereum/EIPs/pull/12120), stacked
diff [lfglabs-dev/EIPs#1](https://github.com/lfglabs-dev/EIPs/pull/1)).

Lean theorems decide what is proved. `audit/guarantees.yaml` only classifies
them.

Each guarantee is intended in these layers:

1. **Abstract Lean 4 model** — the high-level algorithm, used to prove the invariant.
2. **Pinned runtime bytecode under `EvmYul.EVM.Ξ`** — the real bytes, really executed.
3. **Verity Lean library** — a Lean program of the assembly control flow. **OPEN.**
4. **Verity Executable Contract** — the same logic over a `ContractState`. **OPEN.**

| # | ID | Abstract Lean | Pinned bytecode (Ξ) | Verity Executable Contract |
| --- | --- | --- | --- | --- |
| 1 | `P-SUBMIT-1` | CHECKED | CHECKED (concrete traces) | OPEN |
| 2 | `P-DRAIN-1` | CHECKED | OPEN | OPEN |
| 3 | `P-CONTROL-1` | CHECKED | OPEN | OPEN |

### What the bytecode layer does and does not say

`Eip8282.Audit.Guarantees.PSubmit1.psubmit1_bytecode_parent` runs the bytes of
`pinned/bytecode/builder_{deposits,exits}/main.hex` inside `EvmYul.EVM.Ξ` —
not an abstraction of them — and checks the fee getter, the value-bearing
rejection, the paid append (calldata verbatim for deposits, `msg.sender` first
for exits), and inhibited reverts.

It is **a finite set of concrete traces at one storage image**, not a
universally quantified theorem. What makes it load-bearing rather than
decorative is `Eip8282.Tests.PSubmit1Mutant`: flipping **one byte** of the
pinned deposit runtime (offset 158, `RETURN` → `REVERT`) makes the *same*
`submitFacts` the parent is registered against evaluate to `false`. The
mutation is to bytecode, not to a model function.

Two disclosed costs, both in `audit/assumptions.yaml`:

- `A-NATIVE-DECIDE` — `Ξ` reaches `D_J_aux`, a `partial def`, so the kernel
  cannot reduce a concrete trace. `native_decide` is forced; the Lean compiler
  and the EVMYulLean interpreter join the trusted base. `Eip8282.Audit.Trust`
  prints exactly which theorems carry it.
- `A-EVM-WORLD` — the world is synthetic (two accounts, one storage image).

`verity.status: OPEN` remains intentional. Deployment provenance and the
constructor bytecode are out of the current claim.

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
- `Eip8282/Tests/` — model mutants and the P-SUBMIT-1 bytecode kill-line; not public guarantees
- `audit/` — registry, source map, assumptions, pins
- `pinned/` — frozen sys-asm sources, bytecode and EIP text (sha256-locked;
  `scripts/audit_metadata.py` also checks the Lean hex literals against them)
- `scripts/` — fail-closed checks

## Scope

In scope: Builder Deposit `0x0000bFF46984e3725691FA540a8C7589300D8282` and
Builder Exit `0x000064D678505ad48F8cCb093BC65613800E8282`.

Out of scope: EIP-7732 bidding, consensus-layer handling, BLS validity,
anonymous logs, EIP-7685 wrapping, and on-chain deployment identity.
