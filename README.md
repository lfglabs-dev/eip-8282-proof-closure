# EIP-8282 Proof Closure

This repository covers three guarantees: `P-SUBMIT-1`, `P-DRAIN-1`, and `P-CONTROL-1`. The bytes come from `ethereum/sys-asm@83f9801`. The working EIP text is `lfglabs-dev/EIPs@b759aae8` ([ethereum/EIPs#12120](https://github.com/ethereum/EIPs/pull/12120)). Lean decides what holds. `audit/guarantees.yaml` only classifies it.

## What is proved, and what is not

The repository contains an executable Lean specification (`userCall` / `systemCall`) and proofs about the pinned hex. They are not yet proved equal. The remaining goal is, under a well-formed queue and enough gas:

```
Ξ(hex, call) = CFG stepper = Model
```

If that equality is proved, a universal Model theorem becomes a universal EVM theorem. It is still open as `A-ABSTRACT-TX`.

Each bytecode guarantee is also checked against a one-byte mutant of the pinned runtime. The same parent fact must become false. These mutants are the kill-lines.

## Three kinds of evidence

**Abstract theorems.** `userCall` and `systemCall` are functions on a small state where the queue is a list. Their theorems cover the product rules: paid admission, FIFO caps, and the excess fold. They do not execute the predeploy bytes.

**Universal theorems.** For every well-formed queue (slots 0-3 packed, `HEAD ≤ TAIL`), named claims hold. Some claims execute one opcode at one program counter in a small CFG stepper. Others are algebraic, such as FIFO pointer motion, amount encoding, and `fakeExponential`. Algebraic lemmas are not stepped bytecode.

The jumpdest tables used by those CFG proofs are now kernel-checked as the same `D_J` tables computed from the pinned bytes by `EvmYul.EVM.Ξ`. This removed four uses of `native_decide`. It did not prove the full equality above.

**Concrete Ξ traces.** `Ξ` executes one fixed call against one fixed storage image. This is an instance, not a universal theorem. These traces still use `native_decide`, which adds a compiler-generated axiom per theorem. The Lean compiler and EVMYulLean interpreter therefore remain in the trusted base for those facts (`A-NATIVE-DECIDE`).

## Constructor evidence

The full pinned deposit and exit init images are also executed under `Ξ`. The proof checks that each returns the pinned runtime byte for byte, and that the exit constructor writes `INHIBITOR` to slot 0.

This closes the constructor-to-runtime half of provenance. It does not identify deployed chain state. `A-PINNED-SOURCE` remains open until the live predeploy codehashes can be compared with the pinned runtimes.

## Build and test

```bash
# Check the Lean toolchain.
make bootstrap

# Build the full proof project.
make prove

# Build the proof project and all model/bytecode mutant tests.
make test

# Run every local gate: metadata, proofs, and mutant tests.
make check
```

Successful runs end with:

```text
prove ok: abstract model, three guarantees, and the P-SUBMIT-1 / P-DRAIN-1 / P-CONTROL-1 bytecode parents built
test ok: model mutants and the P-SUBMIT-1 / P-DRAIN-1 / P-CONTROL-1 bytecode kill-lines compiled
check ok
```

`make check` is the simplest way to reproduce the full CI gate locally. The GitHub Actions `prove` job runs the same build, kill-line modules, and metadata check on every pull request.

## Out of scope

EIP-7732 bidding, consensus-layer handling, BLS validity, EIP-7685 wrapping, and on-chain deployment identity.

Addresses: deposit `0x0000bFF46984e3725691FA540a8C7589300D8282`, exit `0x000064D678505ad48F8cCb093BC65613800E8282`.
