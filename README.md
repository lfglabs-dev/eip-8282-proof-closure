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

## Ξ transport and reachability

`Eip8282.Audit.XiTransport` carries the three registered parents from the CFG layer to complete-`Ξ` observations. Three layers there are unconditional: the `X` → `Ξ` observation wrapper, the jumpdest agreement (`Ξ` derives the kernel-checked `D_J` tables from the pinned bytes itself), and the exit-instruction layer — the call observes exactly the halting instruction the run exits on, and `RETURN` / `REVERT` publish exactly the memory slice their own operands select.

What is still assumed is the endpoint: `ExitAgrees` — that `Ξ` on the pinned runtime realises `userCall` / `systemCall` — remains an explicit hypothesis. It is the same premise previously called `EndpointAgrees`. Four branches now discharge that residual outright rather than assume it: `P-SUBMIT-1`'s inhibited and accepting paths, `P-DRAIN-1`'s empty-window branch, and `P-CONTROL-1`'s paid fee-getter branch. The universal endpoint proof, over every user and system path, is not there. `A-ABSTRACT-TX` stays open.

`Eip8282.Audit.UserXiCorrespondence` and `Eip8282.Audit.SystemXiCorrespondence` compose whole user-call and SYSTEM-call `Ξ` observations against `Model.step`. The user side is joined to the packed world by `Eip8282.Audit.Represents`; the SYSTEM side carries its own minimal relation over the pinned predeploy account rather than reusing that API. What they compare is an observation — status and return bytes — not equality of EVM and model states, and they too take the endpoint premise explicitly. They narrow what is assumed without discharging it, and they introduce no parent IDs.

`Eip8282.Audit.Reachable` closes the coverage direction inside the packed-storage layer: the constructor post-images are `WellFormed` and map to `Model.Reachable`, and both an append and a system call preserve that. So every reachable image satisfies the guard the three parents quantify over, and `A-REACHABLE` is no longer assumed for coverage. This layer never runs `Ξ`, so it does not discharge `ExitAgrees` either; the realisation gap stays under `A-ABSTRACT-TX`.

## Constructor evidence

The full pinned deposit and exit init images are also executed under `Ξ`. The proof checks that each returns the pinned runtime byte for byte, and that the exit constructor writes `INHIBITOR` to slot 0.

This closes the constructor-to-runtime half of provenance. It does not identify deployed chain state. `A-PINNED-SOURCE` remains open until the live predeploy codehashes can be compared with the pinned runtimes.

## Build and test

Needs [elan](https://github.com/leanprover/elan) and Lean 4.31.0.

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

## Snapshot status

This snapshot is `main` at `25036b8`. Verified against GitHub on 2026-09-01:

| Work | PR | Merge commit | State |
| --- | --- | --- | --- |
| Node 3 — jumpdest tables as `Ξ`'s own `D_J` | [#18](https://github.com/lfglabs-dev/eip-8282-proof-closure/pull/18) | `7204723` | merged into `main` |
| R5 — reachable `WellFormed` storage closure | [#25](https://github.com/lfglabs-dev/eip-8282-proof-closure/pull/25) | `8693add` | merged into `main` |
| R4 — transport the three parents to complete-`Ξ` `∀` | [#24](https://github.com/lfglabs-dev/eip-8282-proof-closure/pull/24) | `0ddb6c4` | merged into `main` |
| R4 — discharge `P-SUBMIT-1`'s rejected branch | [#26](https://github.com/lfglabs-dev/eip-8282-proof-closure/pull/26) | `f1bd9d0` | merged into `main` |
| R3 — whole SYSTEM-call `Ξ` correspondence | [#23](https://github.com/lfglabs-dev/eip-8282-proof-closure/pull/23) | `10bab70` | merged into `main` |
| Node 4 — C4 code-deposit half under `Ξ` | [#19](https://github.com/lfglabs-dev/eip-8282-proof-closure/pull/19) | `18227b9` | merged into `main` |
| R2 — whole user-call `Ξ` correspondence | [#22](https://github.com/lfglabs-dev/eip-8282-proof-closure/pull/22) | `25036b8` | merged into `main` |
| R1 — packed EVM world to `Model.State` | [#21](https://github.com/lfglabs-dev/eip-8282-proof-closure/pull/21) | — | closed unmerged; superseded by #22 |

Every line of work described above is now on `main`. `R1` was closed without merging: its `Represents` relation reached `main` through `R2` instead, so `Eip8282.Audit.Represents` is present even though `#21` is not.

That the correspondence PRs merged does not mean the endpoint premise is proved. `R2` and `R3` compose whole-call observations *under* `ExitAgrees`; none of them discharges it universally.

Two `HIGH` assumptions remain open, and this snapshot does not close either:

- `A-ABSTRACT-TX` — no universal proof that `Ξ` agrees with `Model.userCall` / `systemCall`. R4 makes the `X` → `Ξ`, jumpdest, and exit-instruction layers unconditional and discharges four named branches; R2 and R3 compose whole calls under the same explicit premise; R5 works on the packed-storage side only. The `∀`-endpoint proof is absent.
- `A-PINNED-SOURCE` — the pinned files are snapshots, not observed chain state. Node 4 closes the ctor-to-runtime half within the pin; no deployed codehash is claimed. It stays open until chain activation lets the live codehashes be observed.

Pinned references: `ethereum/sys-asm@83f9801`, `lfglabs-dev/EIPs@b759aae8`, EVMYulLean `b6258665`.

## Out of scope

EIP-7732 bidding, consensus-layer handling, BLS validity, EIP-7685 wrapping, and on-chain deployment identity.

Addresses: deposit `0x0000bFF46984e3725691FA540a8C7589300D8282`, exit `0x000064D678505ad48F8cCb093BC65613800E8282`.
