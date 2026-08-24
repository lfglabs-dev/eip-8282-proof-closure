# EIP-8282 Proof Closure

I wanted a proof I could hand to the Ethereum Foundation without a campaign log attached.

This repo is that proof, for three predeploy guarantees: P-SUBMIT-1, P-DRAIN-1, P-CONTROL-1. The bytes are `ethereum/sys-asm@83f9801`. The working EIP text is `lfglabs-dev/EIPs@b759aae8` ([ethereum/EIPs#12120](https://github.com/ethereum/EIPs/pull/12120)). Lean decides what holds. `audit/guarantees.yaml` only classifies it.

## What I proved, and what I did not

I wrote a Lean spec (`userCall` / `systemCall`) and I proved things about the pinned hex. Those two are not yet the same object. The goal is, under a well-formed queue and enough gas:

```
Ξ(hex, call) = CFG stepper = Model
```

Then a Model forall would be an EVM forall. That equality is still open (`A-ABSTRACT-TX`).

I also check that a bytecode theorem actually cares about an instruction. Change one byte of the pinned runtime. The same facts must become false.

## Three layers

**Abstract theorems.** `userCall` and `systemCall` are functions on a small state (the queue is a list). Theorems about them say those functions match the product rules: paid append, FIFO cap, excess fold. They do not run the predeploy bytes.

**Universal theorems (CFG forall).** For every well-formed queue (slots 0-3 packed, `HEAD ≤ TAIL`), a named fragment of the hex does what I claim: the caller gate, the drain loop, the excess `SSTORE`. The engine is a Lean stepper I wrote. It takes one opcode at one program counter. It is not `EvmYul.EVM.Ξ`. `Ξ` runs a full message call (stack, memory, jumpdests, halt).

**Concrete traces (Ξ traces).** `Ξ` on one fixed call. An instance, not a forall.

## Build

```bash
make prove
python3 scripts/audit_metadata.py
```

`make prove` builds `EvmYul.FFI.ffi:dynlib` first. `native_decide` still needs that shared object.

## Out of scope

EIP-7732 bidding, consensus-layer handling, BLS validity, EIP-7685 wrapping, on-chain deployment identity.

Addresses: deposit `0x0000bFF46984e3725691FA540a8C7589300D8282`, exit `0x000064D678505ad48F8cCb093BC65613800E8282`.
