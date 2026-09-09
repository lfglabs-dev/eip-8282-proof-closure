# Direct closure of the three agreed guarantees

Implementation of Thomas's approved 9 September 2026 plan. This document is an
evidence map, not a replacement for the structured sandboxed.sh task ledger.
The only public IDs remain P-SUBMIT-1, P-DRAIN-1 and P-CONTROL-1.

## Target and acceptance

The initial implementation base is `f14791d482690c64b71c17f63024d78459d15939`.
Bytecode, EIP and EVMYulLean pins remain those in `artifacts.lock.json` and
`lake-manifest.json`. Current EIP wording must not silently change this target.

The live objective is a theorem about each complete pinned EVM call and its
committed effects. Global equality with the old natural-number Model is no
longer a prerequisite. That historical target is not proved, and the arithmetic
counterexamples remain valid; changing the objective does not close it.

The agreed mathematical excess and fee clauses remain obligations on a
justified domain. Additional monotonicity and super-linear-growth properties
are separate findings, not additional conditions for closing the three IDs.
Word-exact semantics alone does not establish the agreed mathematical clauses.

An intermediate dossier is not completion. No existing public parent is
reclassified solely because a new definition, helper or local theorem builds.

## Architecture

* **Execution:** reuse EntryReach/SymExec and pinned EVMYulLean. Do not build
  another interpreter. Keep exact memory, storage, logs and failure behavior.
* **Small specifications:** FIFO as a list, independent record encoding,
  precise word control operations and an untruncated natural fee recurrence.
* **Arithmetic:** separate successful completion, word fit and EVM gas. No
  256-iteration constant in the new fee semantics. No arbitrary no-wrap or
  funding bound presented as a derived protocol invariant.
* **Message calls:** `Ξ` begins after value transfer. `Θ` performs transfer and
  settlement. REVERT/exception restores the pre-call world and substate;
  interpreter OutOfFuel propagates. This does not refund transaction fees.
* **Histories:** bind both worlds to actual `Θ` results. A history parameterised
  by an initial world is not yet evidence about the exact constructor or about
  valid Ethereum blocks.

## Implementation evidence and limits

All names in this section identify source obligations; compilation and review
receipts are required before accepting the corresponding evidence.

| Module | Result to validate | What it does not establish |
|---|---|---|
| `EntryReach/FeeQuote` | Completed word quote, stability and uniqueness for arbitrary finite budgets; candidate originated at `ee7c3f869052bf52259b59d664422631f67949ea` | Success of an EVM call, sufficient gas, or the natural tariff |
| `EntryReach/FeeQuotePath` | Completed quote to the actual deposit fee-loop exit at PC 127; source `34c319eb9890d1bf56221df4310c14b52b21be8d` | Full getter result or successful-call inversion |
| `Integrator/MathFee` | Natural recurrence terminates for every numerator and defines a unique price; arbitrary finite-prefix correspondence under explicit intermediate bounds | Word-loop termination or that arithmetic bounds hold on protocol histories |
| `Integrator/ControlSpec` | Word control operations, relation to entry operands and bounded natural formulas | Committed control state for a whole call |
| `Integrator/EndpointState` | Whole `Ξ` success payload from execution witnesses; getter account-map/log preservation | Inversion of every possible successful call, append/drain content postconditions, or `Θ` settlement |
| `Integrator/AppendSpec` | Independent deposit receipt authenticity, anonymous-log cardinality, other-account preservation | Authentic queue storage or exit address/pubkey byte identification |
| `Integrator/MessageCall` | Actual `Θ` settlement, including rollback, value-transfer order and OutOfFuel propagation | Authorization, sufficient funds, transaction gas accounting or a predeploy path |
| `Integrator/ReachableCalls` | Calls link actual pre/post worlds; failed calls cannot select a new world; OutOfFuel cannot extend the history | Exact initialization, protocol reachability, slot integrity or economic bounds |
| `Integrator/CallBridge` | Pinned code frame uses actual transferred world and correct Θ/Ξ/X fuel offsets; endpoint settlement | A new execution-path or independent storage specification |
| `Integrator/RejectionSpec` | Inhibited paths compose with actual Θ rollback, under explicit resources | A complete arbitrary-gas rejection partition |
| `Integrator/SystemSpec` | Actual successful Ξ world satisfies independent excess/count/head/tail formulas; every record slot ≥4 preserved; owner remains present | Natural queue length on malformed pointers, FIFO bytes, or a derived protocol invariant |
| `Integrator/WorldNonempty` | An existing account disproves the actual empty-world BEq test without a LawfulBEq Account assumption | Owner existence without an execution/initial-state proof |
| `Integrator/CommittedSystem` | SYSTEM storage specification and actual return bytes committed by Θ; derives absence of empty-world fallback | FIFO byte identification, actual gas scheduling, or justified protocol histories |

`MessageCall` retains the upstream empty-account-map fallback on successful
settlement. A consumer claiming direct identity with the `Ξ` post-world must
prove the surviving world is nonempty; it must not drop the fallback silently.

The legacy Model and its existing theorems remain reproducible. The new direct
parents must not depend logically on the legacy 256-fuel price. Merely importing
an existing module which also defines `Model.Kind` is not a fee dependency.

## Clause coverage required before public closure

| ID | Clause | Required complete-call evidence |
|---|---|---|
| P-SUBMIT-1 | Only allowed users submit | Caller/inhibitor gate, every rejection, and no effects on failure |
| P-SUBMIT-1 | Paid and well-formed | Actual completed fee, exact calldata size, minimum deposit and fee plus stake checks |
| P-SUBMIT-1 | One authentic record | Exact append window, count/tail updates, preservation outside the write set |
| P-SUBMIT-1 | One anonymous receipt | Existing log series plus exactly one log at the predeploy, no topics, authentic payload |
| P-DRAIN-1 | Only SYSTEM consumes | Complete caller partition and user/getter pointer preservation |
| P-DRAIN-1 | Oldest capped records | Content and length of the real return memory, cap 64/16, FIFO order |
| P-DRAIN-1 | Encoding | Deposit amount LE conversion; exit source address followed by pubkey |
| P-DRAIN-1 | Pointers and stale slots | Full reset versus partial head advance; all old slots from 4 preserved |
| P-CONTROL-1 | Dispatch and inhibition | CALLER alone; inhibited users rejected; SYSTEM still operates; pinned reversible semantics |
| P-CONTROL-1 | Getter and append | Getter fee/readonly effects; accepted append increments count and preserves excess |
| P-CONTROL-1 | SYSTEM updates | Drain first, nonempty latch/empty unlock or excess fold, count reset |
| P-CONTROL-1 | Constructors | Exact initializer execution and installed runtime/storage; deployment identity separate |
| P-CONTROL-1 | Mathematical formulas | Correct fee numerator versus next excess; untruncated tariff agreement on justified domain |

Endpoint observations and fragment proofs are supporting evidence. They do not
alone close the rows involving committed records, logs or storage.

### Present coverage of the agreed clauses

| Agreed clause | Implemented evidence | Remaining limitation |
|---|---|---|
| Inhibited users cannot commit effects | `RejectionSpec.deposit_inhibited_call` / `exit_inhibited_call` bind the pinned path to Θ rollback | Explicit gas/fuel bounds; arbitrary-resource failure classification remains |
| Paid, well-formed submission | `EndpointState.*_append_result` executes the actual word checks and preserves the successful state | Completion/resources are premises; converse classification of all successful calls remains |
| Authentic record and one LOG0 | `AppendSpec.deposit_submission_receipt` proves the actual Ξ log is exactly the 184-byte calldata; both append helpers have one anonymous log | Record storage, exit address/pubkey identification and dedicated Θ receipt composition remain |
| Only SYSTEM consumes | SYSTEM path and getter account-map preservation are established separately | Full user append pointer/frame result needs no-alias justification |
| Oldest capped records and encoding | `CommittedSystem` retains the actual staged return buffer; cap operands come from pinned paths | Independent FIFO/list and deposit LE / exit concatenation correspondence remain |
| Full/partial pointers and old record slots | `SystemSpec` and `CommittedSystem` prove exact word pointer updates and every slot ≥4 unchanged | Converting modular length/pointers to ordinary queue arithmetic needs queue invariants |
| Caller dispatch and inhibition | `ControlSpec` caller operand equivalence, pinned path theorems and actual inhibited rollback | Exhaustive arbitrary-resource dispatch/success theorem remains |
| Getter read-only; append count/excess | `EndpointState.*_getter_preserves_state` preserves all accounts and logs at Ξ | Full Θ getter and independent append control-slot result remain |
| SYSTEM count reset, latch/unlock/fold | `CommittedSystem.*_system_commits` proves all control-slot effects at Θ; `ControlSpec` gives bounded natural agreement | Protocol justification of intermediate-sum bounds remains |
| Constructors | Historical `Ctor` CFG and `CtorXi` finite init execution evidence retained | Full initialized protocol-history binding remains; do not promote finite traces |
| Correct mathematical fee numerator/tariff | `ControlSpec` exact numerator; `MathFee` total unique natural tariff and conditional arbitrary-prefix correspondence; `FeeQuotePath` actual loop adapter | Deriving completion from arbitrary successful execution and a justified arithmetic/economic domain remain |

## Remaining proof obligations and owners

| Obligation | Dependency | Owner | Next verifiable result |
|---|---|---|---|
| Full getter from completed quote | Reviewed/compiled FeeQuotePath `34c319eb` | Hermes fee lane | FeeQuoteGetter with retained remaining-gas bound and concrete returned fee |
| Derive quote completion from successful runtime execution | EntryReach loop inversion | Direct integrator/fee lane with disjoint files | Theorem with no assumed completion or model agreement |
| Append storage and log postconditions | Endpoint state + existing append path | Direct integrator | Both pinned runtimes' actual success payloads satisfy record/frame specification |
| Drain contents and FIFO | CommittedSystem already covers word pointers and every stale slot | Queue lane, consumed by integrator | Actual returned bytes equal independent concatenated oldest records |
| Remaining call composition | SYSTEM storage and inhibited rollback already at Θ | Direct integrator | Full submission receipt/storage and getter Θ results; arbitrary-resource failure partition |
| Exact initialization and protocol history | Pinned constructors + versioned EL/CL rules | Integrator/protocol lane | Bound initializer world and valid-block transitions, including enclosing rollback |
| Structural bounds | Accounted positive gas per committed append | Queue/protocol lane | Joint pointer/count/excess/no-alias induction without assumed conclusions |
| Mathematical tariff domain | Independent natural recurrence + justified resource/funding bounds | Fee/protocol lane | Bound on every intermediate and required execution resources |
| Final normative version/inhibition | Author clarification draft | Thomas | Explicit chosen versions and intended inhibition behavior |

No numeric effort estimate is certified by this inventory. Calibrate new proofs
from bounded attempts and actual compiler/reviewer results; separate integration
work, new lemmas and external decisions. The most uncertain items are successful
execution inversion, validated block accounting, and the mathematical-fee domain.

## Verification and delivery

Run the FFI prerequisite, targeted module builds, axiom reports, relevant
mutation modules, metadata validation and `make check` on the final candidate.
Keep a single heavy build on this Mac and separate mutable build caches.

Finite differential tests must retain engine version, bytecode hashes,
pre-states, inputs and results. Injected storage is not protocol reachability.
Test-budget exhaustion is not out-of-gas. Existing kill-lines remain, and new
direct postconditions must detect the corresponding semantic mutations.

`make direct-regressions` runs the optional local Anvil corroboration. The saved
`audit/receipts/direct-semantics-20260909.json` records the script SHA-256,
Anvil/revm client version, Prague hardfork, pinned code hashes, exact injected
states, results and timestamps. Its ten fee/getter cases and seven other
transactions passed. Getter checks include actual committed transactions and
nonempty traces without writes/logs; `eth_call` alone would not establish that.
The enclosing-revert case checks successful inner append instructions before
rollback and distinguishes refunded call value from transaction gas paid.
These are finite observations on injected states, not protocol reachability.

Before integration, an independent reviewer receives the exact commit and its
full dependencies. No merge to main, external transmission, normative change
or publication is implied by a successful local build.
