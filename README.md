# EIP-8282 Proof Closure

To check the pinned bytecode, rebuild the proofs, or verify a live
deployment, start at **[VERIFY.md](VERIFY.md)**.

Lean evidence for exactly three Ethereum Foundation audit guarantees, against
pinned `ethereum/sys-asm@83f9801245ff56878a450b5625801101b9a225a1`, working
EIP text `lfglabs-dev/EIPs@b759aae8`, and EVMYulLean
`b62586650b4f96cc6da25f36574aaa8f329a6420`.

**The three conditional direct theorems are proved. Applying them to every
protocol-reachable call remains open.** Lean statements are authoritative;
[audit/guarantees.yaml](audit/guarantees.yaml) records their exact scope.

| ID | Registered theorem in `Integrator.DirectGuarantees` | Complete-call result |
|---|---|---|
| P-SUBMIT-1 | `psubmit1_direct` | Actual paid admission, one authentic stored/logged record, getter preservation and failure rollback |
| P-DRAIN-1 | `pdrain1_direct` | Actual capped FIFO bytes, pointer updates, stale-slot preservation and no user consumption |
| P-CONTROL-1 | `pcontrol1_direct` | Actual fee/count/excess/inhibition behavior, successful constructor installation, and SYSTEM progress with sufficient resources |

The [scoped release](audit/release/REPORT.md) strengthens these parents:
`ReleaseCandidate.call` derives their internal invariants, structural budget,
installed account and safe fee input from exact initialization and a finite
actual history with explicit credit/admission/block conditions. It also proves
successful getters, funded paid submissions and inhibition cycles with stated
resources. Original clauses and material restrictions are preserved in the
[clause map](audit/release/CLAUSE-MAP.md). These are complete conditional results;
canonical Ethereum satisfaction of their domain remains open.

Each registered local theorem covers both contract kinds. It quantifies actual completed Θ calls
at arbitrary gas/fuel under explicit, code-independent input conditions. These
include an existing target account, ordinary real/apparent value equality,
word-sized calldata, a queue/control budget below 2^128, and a safe mathematical
fee numerator. Drain additionally assumes physical queue representation and exit
source width. Initialization and SYSTEM progress have separate domains and
resource bounds. A paid user input is not promised to succeed with insufficient
gas. See [the Lean predicates](Eip8282/Audit/Integrator/DirectGuarantees.lean).

The mathematical tariff has **untruncated semantics**. Agreement with EVM word
arithmetic is proved for every numerator ≤2892; a kernel-checked counterexample
at 2893 refutes unrestricted agreement. The terminating proof witness is not a
256-iteration definition of the fee. Global equivalence with the old Model is
historical supporting work, not a prerequisite or a claimed result.

All six required byte mutations now refute these same direct predicates at the
actual Θ boundary. The LOG0 witness is genuinely funded and verified through 158
small kernel-checked instruction certificates. Five other finite refutations
retain their corresponding old native execution receipts. **The universal
correctness parents use only Lean's standard axioms**, with no native execution
receipt conjunct. These tests do not assert universal independence of the three
guarantees: some clauses intentionally overlap.

Recent supporting proofs establish remaining-gas monotonicity throughout the
actual mutually recursive evaluator, the actual transaction refund/net-gas
formula, and nonincrease of account funds through actual recursive execution
and complete transactions under independent prepayment, nonce and fee
conditions. These components are now composed in the pinned Lean semantics by
`FactoryHistoryGuarantees.from_genesis_both` and `ReleaseCandidate.call`.
Their application to actual Ethereum source execution, canonical credits,
transaction/block admission and deployment remains open. A valid local theorem or
finite injected-state test does not by itself prove protocol reachability.

The clause-level evidence map and current gates are in
[audit/DIRECT-CLOSURE.md](audit/DIRECT-CLOSURE.md). Assumptions are separated in
[audit/assumptions.yaml](audit/assumptions.yaml); exact-source builds and reviews
are in [audit/receipts](audit/receipts). The registered source `9d44bcf` passed isolated `make check`; its exact-source
receipt is `audit/receipts/direct-registration-build-20260909.json`. The later
recursive/transaction funding source `c92e0f8` also passed isolated `make check`;
its receipt is `audit/receipts/direct-recursive-funding-build-20260909.json`.
Further isolated checks passed for actual linked funding histories and unique
frame-local events (`c0c6bea`), then all-outcome recursive child adapters and
explicit child-charge induction edges (`b0af68d`). Their receipts are
`direct-local-events-build-20260909.json` and
`direct-child-outcomes-build-20260909.json` under `audit/receipts`.

```sh
make check
```

This builds the required FFI libraries, checks metadata/artifact pins, compiles
Lean proofs and the direct and historical kill-lines. For a smaller correctness-only
build, use `make prove`; `make candidates` builds the separate historical and
protocol/history library. [Library layout](audit/MODULE-LAYOUT.md) documents
the complete partition and module moves. `make direct-regressions`
optionally runs finite Anvil/revm corroboration; the saved results include engine,
fork, bytecode and input bindings. They are separate from the Lean proofs.

Historical CFG/model parents and tests remain unchanged in Lean. Their old
metadata and detailed development narrative are preserved in
[audit/history](audit/history). No main merge, normative repin, deployment or
external audit certification follows from these local checks.

## Readable resource assumptions

The history-facing wrappers derive the numerical fee/counter conditions from
ETH supply below 10^50 ETH and conservative executed work below 2^128 events,
starting from verified initialization and a linked admitted history. See
[the exact assumptions and remaining protocol limits](audit/release/RESOURCE-ASSUMPTIONS.md).
