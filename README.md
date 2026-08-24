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

**Universal theorems (CFG forall).** For every well-formed queue (slots 0-3 packed, `HEAD ≤ TAIL`), named claims hold. Some of those claims are opcode-at-PC steps on a fragment I wrote (caller gate, excess `SSTORE`). Some are algebraic: FIFO count and pointer motion over helpers such as `drainN`, amount recoding over `encodeReturned`, `fakeExponential` as a recurrence. The stepper is not `EvmYul.EVM.Ξ`. `Ξ` runs a full message call (stack, memory, jumpdests, halt). Algebraic lemmas are not stepped bytecode.

**Concrete traces (Ξ traces).** `Ξ` on one fixed call. An instance, not a forall. Those theorems are discharged with `native_decide`, which adds a compiler-generated axiom per theorem. The Lean compiler and the EVMYulLean interpreter join the trusted base (`A-NATIVE-DECIDE`). A green `make prove` is not kernel-checked evaluation of the traces.

## Build

```bash
make prove
python3 scripts/audit_metadata.py
```

`make prove` builds `EvmYul.FFI.ffi:dynlib` first. `native_decide` needs that shared object.

## Out of scope

EIP-7732 bidding, consensus-layer handling, BLS validity, EIP-7685 wrapping, on-chain deployment identity.

Addresses: deposit `0x0000bFF46984e3725691FA540a8C7589300D8282`, exit `0x000064D678505ad48F8cCb093BC65613800E8282`.
