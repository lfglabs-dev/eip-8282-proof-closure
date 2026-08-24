# EIP-8282 Proof Closure

Lean evidence for three EIP-8282 predeploy guarantees, against pinned
`ethereum/sys-asm@83f9801245ff56878a450b5625801101b9a225a1` and the working
EIP text at `lfglabs-dev/EIPs@b759aae8` (PR
[ethereum/EIPs#12120](https://github.com/ethereum/EIPs/pull/12120)).

IDs: `P-SUBMIT-1`, `P-DRAIN-1`, `P-CONTROL-1`. Lean theorems decide what is
proved. `audit/guarantees.yaml` only classifies them.

## Status

We have a Lean spec (`userCall` / `systemCall`) and proofs about pinned
bytecode. They are not yet proved equal (the goal is to prove they are).
We also check that a bytecode theorem actually depends on a chosen
instruction: change one byte of the pinned runtime and the same facts no
longer hold.

## Specs and models

`userCall` and `systemCall` are functions on an abstract state (queue as a
list). Theorems about them say those functions match the product rules
(paid append, FIFO cap, excess fold). They do not run the predeploy bytes,
so we call them **abstract theorems**.

We then have two kinds of theorems about the pinned hex:

- **Universal theorems (CFG ∀).** For every `WellFormed` queue (slots 0–3
  packed, `HEAD ≤ TAIL`), a named fragment of the hex (caller gate, drain
  loop, excess `SSTORE`) has the stated effect. The proof engine here is a
  small Lean interpreter we wrote: it steps one opcode at one program
  counter. It is not `EvmYul.EVM.Ξ`, which runs a full message call
  (stack, memory, jumpdests, halt).
- **Concrete traces (Ξ traces).** `Ξ` on one fixed call. An instance, not
  a `∀`.

## Goal

Prove the abstract specs match the pinned bytecode, i.e. under
`WellFormed` and enough gas:

```
Ξ(hex, call) = CFG stepper = Model
```

Then a Model `∀` would be an EVM `∀`. That equality is still open
(`A-ABSTRACT-TX`).

## Build

```bash
make prove
python3 scripts/audit_metadata.py
```

`make prove` first runs `lake build EvmYul.FFI.ffi:dynlib`. That is not
optional: `native_decide` runs the compiled EVMYulLean interpreter.

## Scope

In scope: Builder Deposit `0x0000bFF46984e3725691FA540a8C7589300D8282` and
Builder Exit `0x000064D678505ad48F8cCb093BC65613800E8282`.

Out of scope: EIP-7732 bidding, consensus-layer handling, BLS validity,
EIP-7685 wrapping, and on-chain deployment identity.

Plan: `audit/CAMPAIGN.md`.
