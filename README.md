# EIP-8282 Proof Closure

Lean proofs for three guarantees about the pinned builder deposit and exit contracts.
Start with [VERIFY.md](VERIFY.md) to check the bytecode and rebuild the proofs.

**The three conditional guarantees are proved. Connecting their assumptions to
canonical Ethereum execution remains open.**

| Guarantee | What it establishes |
| --- | --- |
| P-SUBMIT-1 | Successful user submissions are well formed and paid, append one authentic record and emit its LOG0. Getters preserve state; failed calls roll back. |
| P-DRAIN-1 | SYSTEM drains the oldest records up to the cap and updates the queue pointers. Users cannot remove records. Drained record slots remain unchanged. |
| P-CONTROL-1 | Calls follow the specified fee, count and inhibition rules. Constructors install the runtime with deposits enabled and exits inhibited. SYSTEM completes with the stated gas and evaluator fuel. |

The authoritative statements are in
[DirectGuarantees.lean](Eip8282/Audit/Integrator/DirectGuarantees.lean).
The [clause map](audit/DIRECT-CLOSURE.md) links their details and conditions.

The history-facing [resource proof](audit/release/RESOURCE-ASSUMPTIONS.md)
derives the numerical fee and counter conditions from ETH supply below 10^50 ETH
and fewer than 2^128 counted execution events, including rolled-back work.
It also requires verified initialization and a linked admitted execution history.
Those history inputs are not yet derived from canonical Ethereum blocks.

```sh
make check
```

This validates pins and metadata, builds all retained proofs and tests, and checks
the theorem axioms. `make prove` builds only the registered correctness closure.
`make candidates` builds the separate resource/history and source-adapter support.
See [the library map](audit/MODULE-LAYOUT.md) for the partition and module moves.

The correctness theorems and the funded LOG0 refutation use only Lean's standard
axioms. Five finite drain/control refutations retain native-evaluation axioms,
disclosed in [assumptions.yaml](audit/assumptions.yaml). Refutations are separate
from correctness proofs. Optional `make direct-regressions`,
`make nested-regressions` and `make factory-regressions` run finite Anvil checks.

Bytecode, source and interpreter pins remain unchanged in
[artifacts.lock.json](audit/artifacts.lock.json). Source archives needed by the
retained adapters and regression inputs remain in [audit/receipts](audit/receipts).
Obsolete campaign logs and snapshots are available in Git history; the
[cleanup inventory](audit/CLEANUP.md) explains deletions and retained dependencies.
