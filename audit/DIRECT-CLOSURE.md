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

### Further direct evidence (continuation, 9 September)

The following additional sources passed standalone Lean compilation and the
full `make check` at `5e9f63f`; the exact source bindings and independent reviews
are recorded in `direct-continuation-build-20260909.json` and
`direct-continuation-reviews-20260909.md`. The older build receipt does not cover
these additions. Subsequent components listed below require their own receipt.

* `EntryReach/FeeQuoteGetter`, cherry-picked from remote `d191d4f` as
  `0ccf3d3`, carries a completed deposit quote through its getter endpoint with
  explicit remaining gas and fuel. The pinned main branch remains `f14791d`.
* `Integrator/GetterCall` proves both actual Θ getters return the exact quoted
  32-byte word, preserving all account lookups, logs and created accounts.
  It proves zero-value transfer neutrality and handles both empty-world
  settlement branches. Quote completion and sufficient resources remain premises.
* `Integrator/AppendStorage` proves both actual Ξ append outcomes have the
  independent calldata/caller record words, count and tail increments, unchanged
  head/excess and preservation outside the write set. Record-window and counter
  bounds are explicit assumptions, not established protocol invariants.
* `Integrator/ExitRecord` identifies the actual exit LOG0 payload as the
  immediate caller's twenty bytes followed by exactly forty-eight calldata bytes.
* `Integrator/ExitDrain` proves every iteration of the actual exit memory writer,
  then composes with Θ: returned bytes are exactly the independent concatenation
  of the oldest capped, word-indexed records. It accounts for the overlapping
  MSTORE writes and excludes the final sixteen-byte overhang. The 160-bit width
  of stored source addresses is a premise; ordinary queue arithmetic and its
  preservation from initialization still require proof.

Further components passed `make check` at `8b9e562`; source hashes and reviews
are in `direct-data-build-20260909.json` and `direct-data-reviews-20260909.md`:

* `CommittedAppend` joins storage and receipt witnesses by equality of the
  actual Ξ result, then commits both in one Θ result. Owner existence excludes
  the empty-world fallback. Other accounts are compared to the transferred
  entry world, so balance transfer is not silently erased.
* `SubmissionCall` binds apparent CALLVALUE to actual transferred value and
  replaces payment word comparisons with fee-plus-stake inequalities over
  naturals. The actual uint64 amount extraction proves the stake product cannot
  wrap; it is not an assumed arithmetic bound. Quote completion and local
  storage-window bounds remain premises.
* `QueueArithmetic` proves the cap is `min(TAIL-HEAD,64/16)` in naturals and
  commits full reset/partial advance with all stale slots unchanged, assuming
  entry `HEAD≤TAIL`. It does not assume post-pointer equations.
* `DepositDrain` identifies the entire actual Θ return as the word-indexed FIFO,
  including exact reversal of amount bytes 80–87 and exclusion of the final
  eight-byte memory overhang. No record-encoding agreement is assumed.
* `RejectionCases` exhausts every invalid input branch after a completed quote
  and proves actual Θ rollback of the pre-transfer world and log journal.
  Its word-level input predicate and sufficient resource bounds remain visible.

Additional results passed isolated `make check` at `018cd2d`; exact source
hashes and reviews are in `direct-inversion-build-20260909.json` and
`direct-inversion-reviews-20260909.md`:

* `SuccessInversion` derives actual steps, exact fee-loop cycles and quote
  completion from a successful user Ξ call, at arbitrary gas and fuel. Inhibition
  is ruled out by inverting the actual REVERT branch. `CallSuccess` and
  `SuccessfulQuote` lift this necessity to actual Θ success and derive positive
  evaluator fuel. No completed-quote premise or fixed iteration cutoff remains
  in these necessity theorems. The further admission/return results below
  extend this evidence.
* `Initialization` executes both pinned init byte strings universally, returns
  their exact runtimes, and proves their storage effects. Initial control values
  follow from explicit zero-control inputs. CREATE/code installation and
  protocol activation are not established by returned bytes alone.
* `QueueInvariant` supplies the small FIFO abstraction: append extends the list,
  drain returns its capped prefix and retains its suffix, tied to actual Θ
  results. Source-width preservation for exits follows from the caller's
  inherent address width and list append/drop. Local capacity bounds remain
  explicit; initialized protocol-history preservation remains open.
* `ResourceBounds` proves the finite-slot/gas arithmetic implication to fewer
  than 2^128 appends and hence capacity/control fit given an explicit accounting
  bridge. Actual gas/refund accounting and actual-state bounds are not assumed
  proved. See `PROTOCOL-BOUNDARY.md` for immutable references and open bindings.
* `Tests/DirectMutations` reuses six existing finite mutant receipts to refute
  the very same direct storage/log predicates. It adds no native evaluation and
  has no impossible mutant-code pin premise. Its dependencies retain exactly
  the disclosed legacy native receipt axioms; the new universal proofs do not.

Further sources passed isolated `make check` at `f52112e`; exact bindings are
in `direct-admission-build-20260909.json` and independent source reviews in
`direct-admission-reviews-20260909.md`:

* `CreationSettlement` unfolds actual Lambda creation settlement, retaining
  address encoding, collision behavior, all code-deposit checks and remaining
  gas. Both pinned constructors are connected to installed runtime/storage in
  an actual successful creation. Canonical deployment identity, transaction
  validity and sufficient resources for creation remain separate obligations.
* `TransferFrame` proves that actual Θ credit/debit preserves every storage read
  and code observation, including self-calls and initially missing accounts. An
  existing pre-call owner survives transfer; unchanged balances are not claimed.
* `AdmissionInversion` and `SuccessfulUser` derive inhibition exclusion, a
  completed operational quote, and the exact getter/submission input partition
  from actual success at arbitrary gas/fuel. Natural calldata lengths require
  the explicit size bound `<2^256`; ordinary calls bind apparent to actual value.
  The actual getter output is the same quoted price, encoded in 32 bytes.
* `GetterInversion` derives zero value and preservation of every pre-call account
  lookup, logs and created accounts from actual successful empty-calldata user Θ
  calls. Neither quote completion nor sufficient gas is a premise.
* `UniversalGate` proves every completed inhibited user Θ call has failure flag
  and restores the entire pre-call world, substate and created-account journal.
  Evaluator OutOfFuel remains an error, not a completed call result.
* `FeeSafeDomain` universally proves word/natural agreement for every numerator
  ≤2892. A kernel-checked trajectory at the upper bound plus monotonicity proves
  all intermediate products fit and all smaller trajectories complete. The 462
  steps are a certificate witness, not a cutoff in the fee definition. Any
  completed word budget yields the same mathematical tariff.
* `SuccessfulUser.*_getter_math` binds that tariff to actual Θ return bytes using
  the independent PRE-CALL natural numerator `excess+max(0,count-TARGET)≤2892`.
  This bound remains external until initialized protocol/funding preservation
  is established.
* `FeeBoundary` proves the untruncated word and natural fees differ at numerator
  2893, and the word fee decreases relative to 2892. These are exact terminating
  computations plus uniqueness, not observations at an arbitrary cutoff. It
  does not prove that a funded protocol history reaches that numerator.

Further sources passed isolated `make check` at `cc78419`; exact source
bindings are in `direct-append-build-20260909.json`, and reviews in
`direct-append-reviews-20260909.md`:

* `AppendInversion` follows every actual SSTORE/memory/LOG0/STOP step in both
  successful append suffixes. It derives the concrete state and empty return
  from actual successful user Ξ execution, without resource/completion premises.
* `SuccessfulAppend` transports the independent storage and authentic single
  receipt to the same actual Θ result. Its paid variants also derive the same
  completed operational quote and natural payment checks. Owner existence and
  local record/counter fit remain explicit; gas, permission and fee completion
  are derived from success rather than assumed.
* `UniversalRejection` proves arbitrary-resource failure plus whole-journal
  rollback for malformed lengths, paid getters, the deposit amount floor and
  underpayment. A known-price underpayment witness may use any completed word
  quote of the pre-transfer input; uniqueness identifies the executed price.
* `AccountedState` maintains HEAD≤TAIL≤budget, count≤budget and, when enabled,
  excess+count≤budget across the independently proved append/SYSTEM slot maps.
  It derives AppendFits from an independent budget<2^128 BEFORE using the
  append postcondition. Monotone budgets can cover restored older journals;
  actual event extraction and gas accounting remain open.
* `FundedDomain` proves the safe numerator≤2892 is preserved by paid appends
  below an explicit funding ceiling (the fee at 2892), and by all SYSTEM
  latch/unlock/fold cases. It composes with the existing sufficient-resource
  Θ results. Neither the ceiling nor initialized-history preservation is
  asserted to be a derived protocol fact.

One-step user invariant modules passed isolated `make check` at `f1e2c57`;
exact bindings and reviews are in `direct-user-invariants-build-20260909.json`
and `direct-user-invariants-reviews-20260909.md`:

* `UserStateInvariant` handles every actual completed ordinary user Θ result.
  Failure/getter preserves bounds; successful nonempty input contributes exactly
  one event and preserves the structural budget and funded safe fee domain.
  AppendFits is derived from the pre-call budget before using the actual receipt.
  No sufficient resources, quote completion or post-state agreement is assumed.
* `UserQueueInvariant` proves the actual user post-world represents either the
  same list or that list extended by exactly the authentic input record. The
  choice depends only on actual success and calldata emptiness. Thus the prior
  FIFO is a prefix of the resulting FIFO, and exit source width is preserved.
  This needs the independent structural budget, without any fee-domain or
  funding ceiling premise.

The next modules passed isolated `make check` at `ebfe8af`; source bindings
and reviews are in `direct-system-inversion-build-20260909.json` and
`direct-system-inversion-reviews-20260909.md`:

* `InitializedInvariant` derives installed runtime, Bounded0, EnabledSafe and
  an empty represented FIFO from actual successful Lambda creation at an
  independently absent target. Deposit starts enabled; exit starts inhibited.
  Canonical deployment identity and transaction validity remain separate.
* `SystemInversion` derives both entire SYSTEM Ξ outcomes from actual success,
  including capped loops, memory, full/partial pointers, latch/unlock/fold and
  both final stores/RETURN. No gas/fuel/permission premise is needed. The
  independent all-slot specification additionally requires an input owner.
* `ActualAppendGas` extracts real memory/opcode debits from accepted Z/step,
  proves the actual LOG0 charges (919 exit; 1847 deposit), and telescopes real
  supported traces through the gas returned by Θ. The whole-call debit theorem
  still requires an actual `LogPath` witness: extracting that trace from every
  successful append remains open. It does not assume a desired final gas value.

These results advance the coverage rows below without closing any of the three
public IDs. Arbitrary-resource SYSTEM Θ composition, initialized protocol
histories, execution-event accounting and the justified mathematical tariff domain
remain. Existing and reused direct-spec mutation checks remain finite corroboration;
final public-parent strength and sibling independence must still be reviewed.

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
| Inhibited users cannot commit effects | `UniversalGate` derives failure and whole-journal rollback from any actual completed Θ result | Evaluator OutOfFuel is not a completed result; deployment/code pin remains explicit |
| Paid, well-formed submission | `SuccessfulUser.*_admission` derives actual quote, exact length/payment and getter output from arbitrary-resource Θ success | Ordinary CALLVALUE equality and calldata size fit are explicit; mathematical tariff domain remains separate |
| Authentic record and one LOG0 | `AppendSpec.deposit_submission_receipt` proves the actual Ξ log is exactly the 184-byte calldata; both append helpers have one anonymous log | `AppendStorage` now covers record storage under local bounds; `ExitRecord` identifies exit bytes. `CommittedAppend` now joins storage/logs at Θ; `SuccessfulAppend` now derives those effects from arbitrary-resource success; history-derived bounds remain |
| Only SYSTEM consumes | `UserQueueInvariant` derives preservation/one-record extension for every actual completed user call; prior FIFO remains a prefix | Input queue representation and independent budget bound must be derived from initialized protocol histories |
| Oldest capped records and encoding | `CommittedSystem` retains the actual staged return buffer; cap operands come from pinned paths | `ExitDrain` now identifies exit FIFO bytes at Θ under source-width bounds; `DepositDrain` identifies deposit FIFO/LE; history-derived bounds remain |
| Full/partial pointers and old record slots | `SystemSpec` and `CommittedSystem` prove exact word pointer updates and every slot ≥4 unchanged | `QueueArithmetic` supplies natural length/pointers under HEAD≤TAIL; derivation of that entry invariant remains |
| Caller dispatch and inhibition | `ControlSpec` caller operand equivalence, pinned path theorems and actual inhibited rollback | Exhaustive arbitrary-resource dispatch/success theorem remains |
| Getter read-only; append count/excess | `GetterInversion` proves Θ getter preservation from actual success without resources/completion premises | `SuccessfulAppend` proves independent append controls from arbitrary-resource success under local fit; history-derived fit remains |
| SYSTEM count reset, latch/unlock/fold | `CommittedSystem.*_system_commits` proves all control-slot effects at Θ; `ControlSpec` gives bounded natural agreement | Protocol justification of intermediate-sum bounds remains |
| Constructors | `InitializedInvariant` derives installed runtime, exact gating and initial empty FIFO/bounds from actual successful Lambda creation at an absent target | Explicit creation resource conditions; canonical deployment identity and valid protocol-history binding remain |
| Correct mathematical fee numerator/tariff | `SuccessfulUser.*_getter_math` proves actual Θ price agreement for independent pre-call numerator≤2892; `MathFee` is untruncated | Protocol/funding justification of the domain remains; `FeeBoundary` refutes unrestricted agreement at 2893 |

## Remaining proof obligations and owners

| Obligation | Dependency | Owner | Next verifiable result |
|---|---|---|---|
| Full getter from actual success | GetterInversion + SuccessfulUser | Validated at f52112e | Actual Θ output and read-only effects without assumed completion; mathematical tariff has explicit domain |
| Derive quote completion from successful runtime execution | SuccessInversion + SuccessfulQuote | Validated at 018cd2d | Actual successful user Θ implies a completed operational quote, without a gas bound |
| Append storage and log postconditions | SuccessfulAppend + UserQueueInvariant | Implemented with independent domain bounds | Actual Θ effects derive from success; initial representation and accounted budget remain to justify |
| Drain contents and FIFO | CommittedSystem already covers word pointers and every stale slot | Queue lane, consumed by integrator | Actual returned bytes equal independent concatenated oldest records |
| Remaining call composition | User Θ and both SYSTEM Ξ success now at arbitrary resources | Direct integrator | Transport SYSTEM necessity through Θ and compose state/FIFO invariants; existing SYSTEM sufficiency results remain valid |
| Exact initialization and protocol history | Pinned constructors + versioned EL/CL rules | Integrator/protocol lane | Bound initializer world and valid-block transitions, including enclosing rollback |
| Structural bounds | AccountedState local preservation + independent execution-event budget | Queue/protocol lane | Actual initialized-history induction, including locally successful events later rolled back, and real gas/refund bridge |
| Mathematical tariff domain | Independent natural recurrence + justified resource/funding bounds | Fee/protocol lane | Bound on every intermediate and required execution resources |
| Final normative version/inhibition | Author clarification draft | Thomas | Explicit chosen versions and intended inhibition behavior |

No numeric effort estimate is certified by this inventory. Calibrate new proofs
from bounded attempts and actual compiler/reviewer results; separate integration
work, new lemmas and external decisions. The most uncertain items are validated block accounting, initialized-history
preservation, and protocol justification of the mathematical-fee domain.

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
