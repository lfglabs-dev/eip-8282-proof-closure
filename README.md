# EIP-8282 Proof Closure

This repo holds Lean evidence for **three** EIP-8282 predeploy guarantees,
against pinned `ethereum/sys-asm@83f9801245ff56878a450b5625801101b9a225a1`
and the working EIP text at `lfglabs-dev/EIPs@b759aae8` (PR
[ethereum/EIPs#12120](https://github.com/ethereum/EIPs/pull/12120), stacked
diff [lfglabs-dev/EIPs#1](https://github.com/lfglabs-dev/EIPs/pull/1)).

Lean theorems decide what is proved. `audit/guarantees.yaml` only classifies
them.

Each guarantee is intended in three layers:

1. **Abstract Lean 4 model** — the high-level algorithm, used to prove the invariant.
2. **Verity Lean library** — a Lean program of the assembly control flow. **OPEN.**
3. **Verity Executable Contract** — the same logic over a `ContractState`. **OPEN.**

We do not claim to have verified the bytecode. `CHECKED` on the abstract
column means the named Lean theorem builds. `verity.status: OPEN` is
intentional. Yul, EVM, runtime bytecode, and deployment provenance are out
of the current claim.

| # | ID | Abstract Lean | Verity Executable Contract |
| --- | --- | --- | --- |
| 1 | `P-SUBMIT-1` | CHECKED | OPEN |
| 2 | `P-DRAIN-1` | CHECKED | OPEN |
| 3 | `P-CONTROL-1` | CHECKED | OPEN |

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

One guarantee:

```bash
lake build Eip8282.Audit.Guarantees.PSubmit1
```

## Layout

- `Eip8282/Audit/` — abstract model, guarantee modules, trust report, facade
- `Eip8282/Tests/` — mutants; not a public guarantee
- `audit/` — registry, source map, assumptions, pins
- `pinned/` — frozen sys-asm sources and EIP text (sha256-locked)
- `scripts/` — fail-closed checks

## Scope

In scope: Builder Deposit `0x0000bFF46984e3725691FA540a8C7589300D8282` and
Builder Exit `0x000064D678505ad48F8cCb093BC65613800E8282`.

Out of scope: EIP-7732 bidding, consensus-layer handling, BLS validity,
anonymous logs, EIP-7685 wrapping, and on-chain deployment identity.
