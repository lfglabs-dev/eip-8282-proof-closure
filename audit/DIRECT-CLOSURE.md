# Direct closure of the three agreed guarantees

Implementation of Thomas's approved 9 September 2026 plan. This document is an
evidence map, not a replacement for the structured sandboxed.sh task ledger.
The only public IDs remain P-SUBMIT-1, P-DRAIN-1 and P-CONTROL-1.

## Current local candidate: ordinary transaction block incorporation

`ReferenceFullFeeBlockTotal.verified` takes the same fee-finalized ordinary
source journal that `ReferenceFullFeeTotal.verified` produces and incorporates
it into the source block. One actual computation supplies the three
conditional claims, the exact frame receipt, full logs/rollback/meter, ordered
fee credits and the checked sender nonce. The final journal has a finite,
duplicate-free account write enumeration over sender, contract and beneficiary
and a finite storage write enumeration over the contract; code hashes are
unchanged and the code write overlay stays empty.

Account BAL updates precede storage BAL updates and both compare against the
unmerged block parent. The U32 index is preserved, the sender nonce converts
through the checked U64 path, every other nonce is unchanged, cumulative
account/storage reads are merged, and the returned transaction journal is
fresh. Post-incorporation account reads agree with the settled journal;
contract storage reads agree with the receipt and foreign storage is untouched.

Two initial conditions are explicit additions to the balance-only fee domain:
the source sender nonce read equals the admitted old sender nonce, and the
initial account/code write overlays are fresh. Final support, conversions,
successful merge and the fresh reset are conclusions, not premises.

Source `f2ab5eb37c8a436c4cf2e74059dd71520e0ad73a` passes frozen `make check`
(3608 jobs, `check ok`), 28 production axiom checks and eight targeted
nonce/merge-order/alias mutations. Only `propext`, `Classical.choice` and
`Quot.sound` occur. See the
[bundle](receipts/direct-ordinary-block-bundle-20260911.json),
[build](receipts/direct-ordinary-block-build-20260911.json),
[axioms](receipts/direct-ordinary-block-axioms-20260911.json) and
[rechecked complete source provenance](receipts/direct-ordinary-block-sources-20260911.json).
The SYSTEM block pair `cb65536`, SYSTEM success `a612bbb` and ordinary fee
settlement `eec2142` remain included without changing their proved domains.

| Original clause family | Current composed consumer | Domain and material limit | Source commit |
| --- | --- | --- | --- |
| P-SUBMIT-1 admission, authentic record/log and local failure | `ReferenceFullFeeBlockTotal.verified`; SYSTEM exclusion also in `ReferenceCheckedSystemBlock.verified` | Represented nonblob ordinary transaction admission, initialized History and explicit initial nonce correspondence; full local logs/fees and block incorporation, not canonical ancestry | `f2ab5eb`, `cb65536` |
| P-DRAIN-1 SYSTEM FIFO/caps/output/storage and user exclusion | `ReferenceCheckedSystemBlock.verified` plus `ReferenceFullFeeBlockTotal.verified` | Mandatory empty-data SYSTEM pair succeeds within source grants with derived block-parent composition. Complete canonical block applicability remains open | `cb65536`, `f2ab5eb` |
| P-CONTROL-1 quote/append updates and SYSTEM empty-data update/unlock | Same two consumers | Exact ordered word operations and existing mathematical agreement domain. Nonempty SYSTEM/inhibition clauses retain earlier conditional evidence; no schedule or policy adoption | `cb65536`, `f2ab5eb` |

The source functions are audited functional transcriptions with complete
archived bodies rehashed at this commit: transaction-state journals and
incorporation order, nonce validation and check, sender-state update and fee
finalization order, and the BAL balance/nonce/code/storage update rules. No
Python exception-state rollback, whole-container insertion-order/serialization
refinement, whole-block BAL size/read admission or final block validation is
claimed. Nonce fixtures in the mutation module are injected projection
witnesses, not canonical counterexamples.

Canonical Ethereum production of the initialized funded History, the
next-transaction History after this incorporation, complete admission,
deployment, SYSTEM authorization, inhibition and upgrade applicability remain
open. Synthetic replay gas is never source gas; there is no 256-iteration
ceiling; the tariff agreement domain (numerator ≤2892) and the 2893 divergence
remain explicit. The structured task ledger is the only roadmap.

[Independent exact review](receipts/direct-ordinary-block-review-status-20260911.json)
is unavailable until the reviewer quota returns on 17 September. PR20 remains
`c3f3c1d`, confirmed by a fresh API and remote read at recording time;
prepared documentation `7e2ef006` is unpushed. No unreviewed proof extension,
external message or normative policy has been promoted.

## Funded History lifecycle constructors — candidate

`ReferenceFundedHistoryLifecycle.initial` and `.next` package the existing
`ReleaseCandidate.History` structure so downstream consumers can name an
initial funded History and its one-transaction extension. `initial` takes the
factory deployment inputs, the linked-worlds condition, a prior funding trace
from `GenesisFundingWorld.world` to `deposit.call.world`, a genesis-to-exit
credit ledger accumulating exactly `baseCredits`, and count admission. Its
receipts and block list are empty; the internal `Nat.add_zero` collapses the
ledger's `baseCredits+0` back to `baseCredits`. `next` extends a
`History deposit exit before` by one further actual Υ receipt whose call
world equals `before`, together with independently admitted admission,
data-size fit, evaluator-fuel resources, a fresh block slot and admitted
per-block gas. The new receipt sits in a fresh one-transaction block; slot
uniqueness is enforced by the `freshSlot` premise.

Neither constructor asserts canonical Ethereum production of its ingredient
records. Factory deployment justification, funding-trace provenance,
credit-ledger provenance, block-slot admission and per-block gas admission
remain distinct obligations declared elsewhere in the audit. Synthetic
replay gas is never source gas; local frame effects are not ancestor
commitment. The lifecycle module does not compose the ordinary block
incorporation with the History extension — it exposes the constructor that
the block-level composition can call once its Υ receipt is in hand.

Auxiliary lemmas `receipts_extend`, `blocks_extend`, `depositInputs_stable`,
`exitInputs_stable`, `initial_receipts_empty` and `initial_blocks_empty`
give downstream consumers direct access to the extension shape without
pattern-matching on the `History` structure.

Source pending final frozen `make check`; `Eip8282.Audit.Integrator` and
`Eip8282.Audit.Trust` include the new module. All eight declarations depend
only on `propext`, `Classical.choice` and `Quot.sound`. See the
[bundle](receipts/direct-funded-history-lifecycle-bundle-20260911.json),
[build](receipts/direct-funded-history-lifecycle-build-20260911.json),
[axioms](receipts/direct-funded-history-lifecycle-axioms-20260911.json) and
[source references](receipts/direct-funded-history-lifecycle-sources-20260911.json).

Independent exact review is now CLEAN: fresh-context reviewer, not the
author; zero blocking findings; one advisory noting a cosmetic field-count
phrasing in the bundle receipt (corrected in place, module SHA-256 unchanged).
See [report](reviews/spark-review-8f76438.md) and
[status receipt](receipts/direct-funded-history-lifecycle-review-status-20260911.json).
No proof extension, external message or normative policy has been promoted.
PR20 remains `c3f3c1d`; prepared documentation `7e2ef006` remains unpushed.
The existing structured task ledger remains the sole roadmap.

## Preserved SYSTEM candidate: ordered checked SYSTEM block pair

`ReferenceCheckedSystemBlock.verified` composes the two successful mandatory
SYSTEM drains with their actual storage incorporation. Deposit's returned
journal becomes Exit's source parent. The same intermediate replay world
supplies Exit's three predicates; global storage reads at every address agree
with that world and then with the final world. Both protected invariants at
these boundaries are derived from the initial history.

The source BAL update compares final writes against the **unmerged** parent,
checks key length before big-endian conversion, and retains the incoming U32
index. Its enumeration contains every actual write, no extra write and no
repeated key. Complete account/code write journals are proved empty, cumulative
account/storage reads are merged, and the transaction journals are cleared.
Source events, meters, terminal, logs, output, account reads and final warmth
remain tied to the same checked trace and receipt.

The intermediate parent/world relation, Exit invariant, finite write support,
key-conversion success, empty account/code writes and trace-consistent warmth
are conclusions. No independent intermediate equality, successful endpoint,
final meter, final journal or new funded History at Exit entry is assumed.

Source `cb655365674ef9173e1e4587ee89ad4291024163` passes frozen `make check`
(session 95447, collected exit 0), 35 production axiom checks and six targeted
mutations. Only `propext`, `Classical.choice` and `Quot.sound` occur. See the
[bundle](receipts/direct-system-block-bundle-20260911.json),
[build](receipts/direct-system-block-build-20260911.json),
[axioms](receipts/direct-system-block-axioms-20260911.json) and
[rechecked complete source provenance](receipts/direct-system-block-sources-20260911.json).
The preceding same-evaluator SYSTEM success `a612bbb` and ordinary fee
settlement `eec2142` remain included without changing their proved domains.

| Original clause family | Current composed consumer | Domain and material limit | Source commit |
| --- | --- | --- | --- |
| P-SUBMIT-1 admission, authentic record/log and local failure | `ReferenceFullFeeTotal.verified`; SYSTEM exclusion also in `ReferenceCheckedSystemBlock.verified` | Represented nonblob ordinary transaction admission and initialized History; full local logs/fees, not canonical ancestry | `eec2142`, `cb65536` |
| P-DRAIN-1 SYSTEM FIFO/caps/output/storage and user exclusion | `ReferenceCheckedSystemBlock.verified` plus `ReferenceFullFeeTotal.verified` | Mandatory empty-data SYSTEM pair succeeds within source grants; actual storage/receipt/block-parent composition is derived. Complete canonical block applicability remains open | `cb65536`, `eec2142` |
| P-CONTROL-1 quote/append updates and SYSTEM empty-data update/unlock | Same two consumers | Exact ordered word operations and existing mathematical agreement domain. Nonempty SYSTEM/inhibition clauses retain earlier conditional evidence; no schedule or policy adoption | `cb65536`, `eec2142` |

The initial domain is the existing initialized `ReleaseCandidate.History`
before this pair, the represented initial storage world, successful fresh
source code loads for both pinned runtimes, and source account/code parents,
cumulative read sets and a BAL builder with U32 index. History's constructor,
financing, credit-count and block-slot conditions remain explicit; their
canonical Ethereum production has not been established.

At the audited EL pin, these adjacent calls occur in
`process_general_purpose_requests`, after the withdrawal/consolidation request
calls. The earlier `apply_body` step sets the post-execution index to checked
`U32(transaction_count+1)`. The theorem starts at the pair entry and preserves
its input index; it does not derive that preceding block execution or the
final whole-block BAL size/admission checks.

The source functions are audited functional transcriptions, with complete
archived bodies and checked hashes. Mechanical Python/bytes/dictionary
refinement, insertion-order/BAL serialization and full account/code payload
correspondence remain trust boundaries. The failure marker in the successful
BAL projection does not model partial Python builder mutations on exceptions;
derived valid keys exclude that branch in this consumer.

The original guarantees, author draft, tariff divergences and earlier
conditional results remain in `audit/release/`. The mathematical tariff is
not silently replaced: the agreement domain (numerator ≤2892) and the 2893 divergence
remain explicit. There is no 256-iteration ceiling. Synthetic replay gas is
never source gas, and local returned effects are not ancestor commitment.
Canonical funded histories, complete call-tree occurrence accounting/global
gas, deployment, SYSTEM authorization, inhibition and upgrade applicability
remain open. The structured task ledger is the only roadmap.

[Independent exact review](receipts/direct-system-block-review-status-20260911.json)
is unavailable. PR20 remains `c3f3c1d`, confirmed by the 01:26 API and later
remote read; prepared documentation `7e2ef006` is unpushed. No unreviewed proof
extension, external message or normative policy has been promoted.

## Preserved ordinary-call candidate: same-frame guarantees, gas and fee balances

`ReferenceFullFeeTotal.verified` preserves the exhaustive three-guarantee,
full-log and source-gas certificate and derives ordered fee disbursement from
that same settled receipt. The initial history and fee debit fund both credits;
no final balance budget, overflow guard or disbursement success is assumed.
All account balance changes are exact natural amounts, including equal payer
and beneficiary. Queue/control storage is identical to the settled receipt.
Refund, tip and calculated base-fee burn partition the upfront execution fee.

Source `eec2142d7bbc97b4d03fff5d912bb8953a485b5c` passes frozen `make check`,
15 production axiom checks and four ordered-credit/zero/overflow mutations.
The first source `54d884e` failed the aggregate import-order check; the fix and
new successful check are recorded explicitly. See the
[bundle](receipts/direct-source-fee-finalization-bundle-20260910.json),
[build](receipts/direct-source-fee-finalization-build-20260910.json),
[axioms](receipts/direct-source-fee-finalization-axioms-20260910.json) and
[source excerpts](receipts/direct-source-fee-finalization-sources-20260910.json).
Prior full-gas `20783d3` and full-log `9e79b3f` evidence remains included.

The domain is unchanged from FullGasTotal: represented nonblob ordinary calls,
selected source admission conditions and before-transaction history/source
correspondences, plus a fresh storage overlay/read/created journal. The parent
chain storage may be nonempty. These conditions are not canonical Ethereum
reachability. The exact EVM-word tariff and mathematical agreement domain are
unchanged, with no 256-iteration ceiling. Synthetic replay and source gas remain
separate; frame log eligibility is distinct from ancestor commitment.

Full Python/dictionary/byte/hash refinement, source block incorporation and
next-transaction history, complete call-tree commitment, deployment, SYSTEM,
inhibition and upgrade applicability remain open. Fee balance observations do
not assert equality of full source account payloads with old replay worlds.

Independent exact review is unavailable. No unreviewed extension is promoted.
PR20 remains `c3f3c1d`; prepared documentation `7e2ef006` remains unpushed.
Checked SYSTEM execution, successful source payment, the ordered SYSTEM
block-parent/world composition and ordinary transaction block incorporation
are now composed above. Next-transaction history remains open.
The existing structured task ledger remains the sole roadmap.

The following sections identify earlier theorem layers and their original
verification domains. Their remaining gaps are evaluated against the current
candidate above, not treated as new parallel work.

## Exhaustive computed allocated-call certificate — candidate

`ReferenceAllocatedTotal.verified` no longer assumes an evaluator endpoint.
From the same explicit allocated-entry domain, it constructs sufficient
computational fuel and an actual supported result. Terminal/EOF supply the
same three-predicate receipt and source settled balances; exceptional failure
supplies the same complete local rollback receipt. The conclusion excludes
unsupported/unfinished cases using reached pinned-runtime sites and actual
evaluator extraction. Computational completion is distinct from EVM success.

`Started` and `Result` name conclusions, never additional input premises.
The earlier arbitrary finite outcome-specific theorems remain unchanged.
Source gas and synthetic replay gas, local frame effects and ancestor commitment,
and source transcriptions and canonical Python/Ethereum applicability remain
distinct. This earlier API exposes protected-owner logs only; the current
full-frame transport is composed above, while Python extraction remains open.

Source `245e02bcee5bf0c205562ba3f1e793758345d29f` passes frozen `make check`,
nine production axiom checks and two mutations; see the
[build](receipts/direct-allocated-total-build-20260910.json) and
[bundle](receipts/direct-allocated-total-bundle-20260910.json).
Independent exact review is unavailable and there is no promotion.

## Computed source dispatch and allocated meter — candidate

`ReferenceAllocatedGuarantees.terminal/eof` and `ReferenceAllocatedFailure.settled`
start the same checked evaluator from the computed dispatch/value-entry journal
and source split allocation. Actual pinned code reads derive the ready dispatch
branch and exact accumulated account reads. Selected source nonce/fee/floor
checks plus explicit sender presence derive funding admission and calldata fit.
The computed call intrinsic and its two explicit admission checks derive pool
conservation and executable potential at most16777216; a free30000000 bound is
no longer an input to these APIs.

This domain is represented nonblob ordinary calls without authorizations, with
before-transaction initialized history and source observations as before.
Charged/delegated preparation continuations remain separate prefix results;
full Python construction/extraction, canonical validation/history and complete
source logs are not established. Prior APIs remain unchanged. See the
[bundle](receipts/direct-dispatch-allocation-bundle-20260910.json).
Source `b8de01363430e093ef3211b162e11cec7d5adb85` passes frozen `make check`,
thirteen production axiom checks and four mutations; see the
[build](receipts/direct-dispatch-allocation-build-20260910.json).
Independent exact review is unavailable; no promotion.

## Constructed initial access sets and jump destinations — candidate

`ReferenceInitializedGuarantees.terminal/eof` and
`ReferenceInitializedFailure.settled` consume storage warmth constructed from the
represented transaction access list and destinations scanned from the same
pinned code. `WarmRelated` and `DestinationContext` are derived. Transfer mode
is specialized to source top-level `True`; the previous APIs remain unchanged.
This is not a proof of complete `create_evm` preparation or Python extraction.
Source meter, calldata fit and the earlier before-journal/history/admission
conditions remain explicit. Protected-owner logs remain distinct from source
transfer logs at SYSTEM_ADDRESS.

Source `c9a8066a1455d88f046d41b881113b95c00dfeed` passes frozen `make check`,
seven production axiom checks and four mutations. See the
[build](receipts/direct-initial-access-build-20260910.json) and
[bundle](receipts/direct-initial-access-bundle-20260910.json).
Independent review remains unavailable; this contribution is not promoted.
The next consumer connection is actual dispatch preparation and allocated gas.

## Source prepayment from the before-transaction journal — candidate

[The prepayment candidate](receipts/direct-source-prepayment-bundle-20260910.json)
adds `ReferencePrepaidGuarantees.terminal/eof` and
`ReferencePrepaidFailure.settled`. Its input journal is now before gas
prepayment: the ordered source operation derives successful prepayment and
all checkpoint code, slot and balance bindings. The same complete receipt still
carries all three predicates and source settled balances. A failed call restores
the computed post-prepayment snapshot, retaining fee debit and nonce increment.

This stronger connection has an explicit additional domain: represented
legacy/access/dynamic transactions, excluding blobs. Their source and old blob
charges are both zero; the differing blob tariff formulas are not identified.
The earlier checkpoint APIs remain unchanged. Source type4, full constructor/
preparation/gas/warm binding and canonical admission/history remain open.

Source `eb373cd2654dc018c685cd55d882dd4c451d172d` passes frozen `make check`,
fifteen production axiom checks and four mutations; see
[build](receipts/direct-source-prepayment-build-20260910.json).
Independent review is unavailable; no promotion or PR update is made. The
mutations cover nonce-before-fee ordering and retained nonce effects on fee
underflow, using explicitly injected finite journals rather than canonical
reachability claims. Every new helper is consumed by these complete-call APIs.

## Before-transaction history at the actual checkpoint — candidate

The [checkpoint composition](receipts/direct-checkpoint-bundle-20260910.json)
adds `ReferenceCheckpointGuarantees.terminal/eof` and
`ReferenceCheckpointFailure.settled`. They derive the selected call's invariant,
work bound, code and funding from history **before the transaction** and its
explicit admission. They no longer require a separate history after prepayment
or an independently funded call. The same replay receipt still carries all
three guarantees and settled source balance observations.

Call rollback restores the snapshot after gas prepayment and nonce increment,
before transferring call value. It does not refund all transaction fees. A
mutation with30001wei initially,30000wei prepaid and1wei call value detects
substituting the before-transaction world for the actual selected checkpoint.
This injected fixture is not a canonical transaction/history certificate.

Source `be85ecff8e639fe9bbfb1cc888ec081ce3ffaa0e` passes frozen `make check`,
eleven production axiom checks and two mutations; see
[build](receipts/direct-checkpoint-build-20260910.json). Independent exact
review is unavailable and there is no promotion. Source checkpoint representation is
still an input to those APIs; the nonblob prepayment extension above derives it.
The old admission interface does not establish Amsterdam blob tariff equality,
source frame/gas identity or type4 semantics. These boundaries are unchanged.

## Same-receipt source balances candidate — not promoted

The current proof workspace strengthens the source-funding candidate with
[16 balance/composition exports](receipts/direct-source-balance-bundle-20260910.json).
`ReferenceSourceBalancedGuarantees.terminal/eof` compose the three predicates
with balance observations of the **same settled receipt world**. The source
transfer, finite checked execution, old pinned runtime balance preservation
and frame rollback supply the connection. No post-balance equality is assumed.
`ReferenceSourceBalancedFailure.settled` recovers the original balances alongside
the same failed-frame storage/write/log/output/meter receipt.

These stronger terminal/EOF results additionally require ordinary transfer mode
(`shouldTransfer = true`) or zero actual value. Previous funded APIs are unchanged.
Initial balance/code/slot representation and caller funding remain explicit;
canonical source-frame/admission/history producers remain open. This does not
identify source gas with replay resources, prove optional-account identity,
or turn local success into ancestor commitment.

Source `8cea382d101eebb3b54f8e357fb306dac6c57edd` passes frozen `make check`,
16 production axiom checks and the two new balance mutations; see
[build](receipts/direct-source-balance-build-20260910.json).
[Independent exact review is unavailable](receipts/direct-source-balance-review-status-20260910.json);
this candidate has not entered the reviewed branch or PR.
The publication PR is still #20 at `c3f3c1d644d9e641585dfc5143100123729fd0e4`.
A separate refresh at `7e2ef006c0e3bfafaf98f40eb9768560ad03fe16` contains only the
reviewed snapshot `12806f9` and current publication documents. Its 433 proof/build
inputs match the prior verified source; exact document review is unavailable
because the existing reviewer exhausted quota. It has not been pushed.

## Funded source entry candidate — final review pending

Source `8e92a8bc783862fec9ef602151743fff66eb43a6` on the separate
`codex/source-funding-candidate-20260910` branch adds
[the source funding candidate](receipts/direct-source-funding-bundle-20260910.json).
The reviewed source branch remains at `12806f9`; the timed release is unchanged.
`ReferenceSourceTransferFunding.after_history` derives successful checked
source transfer from initial balance observations and caller funding, with the
wealth bound supplied by the initialized ledger. It handles self-transfers and
zero-balance account cleanup without asserting account-object identity.

`ReferenceSourceFundedEntry.prepared` supplies entry admission and runtime
slots to both all-three terminal/EOF consumers and the failed-frame consumer.
An independent `entered` premise and independent post-transfer slot binding
are removed from these new public APIs. A concrete account-field image proves
the balance relation for represented replay; actual Python PreState/frame
correspondence and canonical sender admission remain open.

Ten production exports and two added funding mutations pass target compilation.
Full frozen `make check` passes, including standard-only axioms for all ten new
exports and the source funding mutations; see [build](receipts/direct-source-funding-build-20260910.json).
Component source review was clean, but the
existing reviewer exhausted its quota before final exact-commit review; see
[review status](receipts/direct-source-funding-review-status-20260910.json).
This candidate is not promoted to the independently reviewed release. Work on
independent proof obligations continues without new worker jobs or spending.

## Guarded source transfer and pre-transfer rollback

Proof commit `f9c7953771129f05c4b1b4c72f12f5dbc588c425` adds
[the source transfer bundle](receipts/direct-source-transfer-bundle-20260910.json).
`ReferenceSourceValueTransfer` preserves exact checked debit/credit order,
empty-account cleanup, self-transfers, source transfer guard and partial errors.
It represents the endpoint of each `modify_state`: its temporary updated-account
write and repeated emptiness-check read collapse to the final overlay/read set.
It does not assert an account-write event trace.
For a nonempty code hash, the protected code and storage survive. Its read
preservation lets the consumer reuse the actual fetch before transfer without
inventing a second read effect.

`ReferenceTransferredFailure.settled` consumes pre-transfer code and slots,
derives the runtime entry relations and fault classification, and restores the
same pre-transfer journal. Account/storage/code/transient writes return to that
snapshot; live account/storage reads and created metadata remain. The new
kernel mutation rejects unconditional storage preservation for empty-code
self-transfers. The older `ReferenceValueTransfer` account-map parity proofs
remain byte-for-byte unchanged.

The 14 production and two mutation exports pass targeted compilation. Frozen
full verification and exact independent review PASS; evidence is recorded in
[build](receipts/direct-source-transfer-build-20260910.json) and
[review](receipts/direct-source-transfer-review-20260910.json).
Source transfer success, actual account payload/world representation,
code-address/current-target/should-transfer construction, source LOG3/context
binding, full Python frame identity and canonical admission are still open.
These additions are outside the unchanged timed release.

## Derived source failure classification

Proof commit `af027e8bdfefe1f0bea92737dd3b0862c35dd3d1` adds the
[derived failure bundle](receipts/direct-derived-failure-bundle-20260910.json).
The same failed account-aware evaluation now derives its final calldata/PC
conversion bounds and excludes the owner assertion using its nonempty code
fetch. `ReferenceHistoryFailure.settled` obtains the old replay owner from the
initialized history, then proves projected storage rollback, zero parent logs,
empty exceptional output and the ordered meter settlement. No independent
`caught` classification or old `HasOwner` is supplied by this history consumer.

All 14 new exports compile with standard Lean axioms; the exact isolated
`make check` passes, including existing mutation checks. Evidence:
[build](receipts/direct-derived-failure-build-20260910.json) and
[review](receipts/direct-derived-failure-review-20260910.json).
Actual source entry construction, code-address/current-target identity,
account/value-transfer state and full saved snapshot binding remain open.
In particular, source `process_call` transfers value before opcodes and may
emit a SYSTEM-address LOG3; `modify_state` may delete a newly empty account.
The opcode projection does not silently discard or justify these source effects.
The frozen timed release under `audit/release/` is unchanged.

## Post-release source account composition

The frozen release remains `58c2a60` (proofs `d46fa07`). Work continues on
`codex/source-account-composition-20260910` toward Ethereum applicability.
The [account bundle](receipts/direct-account-bundle-20260910.json) adds literal
optional-account lookup, post-charge SSTORE account reads and a complete
account-aware checked evaluator. Every finite evaluation projects to the same
checked result, including computational exhaustion and exceptional outcomes;
completed outcomes preserve account writes. Its terminal/EOF outputs now feed
the same three history-derived guarantees without an independent owner Bool.

Source dictionary/current-target identity, account payload/value-transfer and
full frame/ancestor snapshot restoration remain open. This is a local source
projection, not a canonical source-world or gas equivalence theorem. Fourteen
exports pass target checks with standard axioms; isolated full check and
independent exact-commit review pass at `f5f7a36`
([build](receipts/direct-account-build-20260910.json),
[review](receipts/direct-account-source-review-20260910.json)). No released claim or EIP/protocol policy is changed.

## Scoped release of 10 September 2026

The user authorized revised audit claims on a precise domain, without EIP or
protocol-policy changes. [Release claims](release/CLAIMS.md) and the
[clause map](release/CLAUSE-MAP.md) compose actual factory/history invariants
into the next complete call, sufficient-resource getter/submission and a real
inhibition cycle. The [release report](release/REPORT.md) records full compilation,16 new
standard-axiom exports, mutation checks and independent review PASS at d46fa07. Ethereum applicability remains open; this conditional release does not
close that broader roadmap. Earlier snapshots below are historical evidence.

## Current snapshot

The registered direct parents for all three IDs are checked under explicit
local input domains; all six required mutations refute those same predicates.
Protocol coverage remains PARTIAL/OPEN. Correctness parents and the new
supporting proofs use standard Lean axioms only; five historical finite mutant
witnesses retain their disclosed native receipts.

The [checked outcome bundle](receipts/direct-checked-outcomes-bundle-20260910.json)
adds six modules and 31 exports. Genuine EOF is connected to the same pinned
execution only after deriving the absent code byte; source PC is unchanged.
Caught exceptional failures and REVERT have distinct projected storage, meter,
output and log effects. Builtin conversion and owner-assertion faults remain
explicitly uncaught at the pinned source boundary.

All evaluated outcomes preserve the same baseline and committed spill. Literal
child initialization now supplies the failed-child incorporation assertions,
including after a partially executed failing opcode. The log context carries a
fixed incoming prefix; the checked trace and terminal produce the new suffix,
which alone may be forwarded. Failed/reverted frames retain internal logs for
executed-effect accounting but contribute no logs to their parent.

These are exact local source projections. Actual full account/code/transient
snapshot restoration, source initial log/value-transfer bindings, parent/frame
identity, complete retained occurrence coverage and canonical funded histories
remain open. Component checks, full frozen check and exact-commit review pass at
`fe81dc501fad4fee657a44935c5648855c51a1d0`; see
[build](receipts/direct-checked-outcomes-build-20260910.json) and
[review](receipts/direct-checked-outcomes-review-20260910.json). No protocol decision was adopted.

Source `778f2d5` adds the [computed evaluator bundle](receipts/direct-checked-evaluator-bundle-20260910.json)
adds six modules and 24 exports. The dispatcher computes a handler from current
code/PC, using the complete pinned 153-tag Ops table. Invalid opcode, EOF and a
valid unsupported opcode have distinct outcomes. The evaluator produces its
own checked prefix and exact last result. Initial potential plus one is a
sufficient computation budget from bounded stack/aligned entry; no fixed loop
ceiling is imposed and failure remains separate from success.

The computed terminal result now produces actual pinned bytecode evaluation
with the same environment, storage, logs, stack, memory and output. Numerical
nested transaction location derives the replay resource cap. Actual source
frame/world bindings, complete occurrence identity, source journal restoration,
canonical funded history and unresolved protocol decisions remain open. Genuine
EOF is retained; REVERT observations are internal. Component builds and reciprocal
reviews pass, together with [full frozen validation](receipts/direct-checked-evaluator-build-20260910.json)
and [exact-commit review](receipts/direct-checked-evaluator-review-20260910.json).

The newly fetched Hermes FeeQuoteLoop helper is [reviewed here](receipts/direct-hermes-feequote-loop-review-20260910.json).
Its dependencies are identical to the integrated originals; existing quote
consumers already use their facts. No alias-only refactor was introduced. One
misleading vacuous zero-budget lemma name remains a review objection.

Source `da1c6f7` adds the [checked runtime bundle](receipts/direct-checked-runtime-bundle-20260910.json)
adds 11 modules and 37 exports. All 41 protected nonterminal handler variants
now produce actions, exact ordered prices, payment and stack bounds from their
literal checked result. One finite trace threads these same states and meters;
alignment and all intermediate bounds are derived from empty entry. Deposit
and Exit append consumers use that trace and the existing nested allocation
bound. STOP, RETURN and REVERT have literal terminal handlers with distinct
revert and out-of-gas outcomes. Source STOP advances PC; replay STOP does not,
so no equality of those terminal PCs is claimed.

The decoder supplies complete PUSH immediates from the same code/PC. Its finite
byte-table proof is not an iteration limit. Paid running length is bounded by
the same resource potential for arbitrary finite traces. Actual source dispatch
(including invalid opcode versus EOF), frame initialization, owner lookup,
outer rollback, complete occurrence identity and protocol histories remain
open. Component builds and reciprocal independent reviews pass, together with
[full frozen validation](receipts/direct-checked-runtime-build-20260910.json)
and [exact-commit review](receipts/direct-checked-runtime-review-20260910.json).

Source `823f37b` adds the [context-producer bundle](receipts/direct-context-producers-bundle-20260910.json):
checked binary handlers, a transaction-derived potential bound at nested
CALL/CREATE entries, and concrete paid-append consumers. Parent storage read
equivalence preserves original/current values and exact actions/prices across
pending block-write overlays. Ten component targets and reciprocal independent
reviews pass, with 69 standard-or-less exports, together with [full frozen validation](receipts/direct-context-producers-build-20260910.json)
and [independent exact-commit review](receipts/direct-context-producers-review-20260910.json).

Retrieved Hermes sources now supply explicit SYSTEM dispatcher fields and the
ordered pair, represented admission checks, and accepted-slot/withdrawal guards.
The admission interface was corrected after independent review: the old blob
tariff differs from Amsterdam, so old-consumer compatibility is separately
required. It is not silently inferred from source admission. The new inherited
withdrawal-stage producer derives both previous guard inputs. The cache producer
starts at exact Gloas upgrade initialization and retains expected withdrawals
on empty parents, counting every payload list without assuming each computed
list is used at most once.

[Adapter findings and the pending cryptographic proposal](receipts/direct-protocol-adapter-findings-20260910.md)
record the exact remaining source/engine/canonical history bindings. Eleven
complete CL files have been verified against the immutable Git tree. No fork,
inhibition, upgrade or cryptographic proposal has been adopted automatically.
The actual source occurrence coverage, full source handler/interpreter binding,
canonical funded histories and final three-guarantee closure remain open.

Source `7fe5e3d` adds the [source-completion bundle](receipts/direct-source-completion-bundle-20260910.json)
reconstructs an entire finite protected execution from the same ordered
source-shaped actions and prices. Memory capacity and host bounds are derived
from those actions and cumulative costs. Entry starts with empty stack/memory;
synthetic gas and fuel are constructed, preserving the call's world and context.
STOP, RETURN and REVERT produce actual evaluator outcomes and exact terminal
gas debits. REVERT's terminal storage/log observations remain internal.

The same completed source event list now derives the mandatory append costs
(1419 Exit, 2647 Deposit) and produces the existing paid append resource leaf.
Old execution success, an old trace, per-step memory caps and an instruction
count are no longer supplied to this leaf producer. Its work bound comes from
the same literal paid resource run and the frame's initial execution potential.
Seven component targets and independent component reviews pass, with 22
standard-or-less exports, together with [full frozen validation](receipts/direct-source-completion-build-20260910.json)
and [independent exact-commit review](receipts/direct-source-completion-review-20260910.json).

Actual source execution/price/context extraction, the protocol-derived initial
frame potential, source occurrence identity and all-survivor coverage, outer
failure/rollback, canonical funding/deployment/block context and pending policy
decisions remain open. The finite action history and its halt are still inputs
from source extraction; unconditional source termination is not established here.

Source `b7c927d` adds the [protected-replay bundle](receipts/direct-protected-replay-bundle-20260910.json)
constructs an actually admitted pinned EVM step from the same successful
source-shaped action. It covers every nonterminal instruction of both fixed
runtimes, with stack, memory, storage, logs, environment and PC related. Stack
underflow, DUP/SWAP depth, jump validity and static-mode guards are derived.
The source-produced output stack bound remains explicit.

Memory and opcode charges yield a conservative synthetic budget of 222 times
the same source event's execution cost, plus a 2301 reserve for the SSTORE
sentry. This budget is used for effect replay; actual source gas remains the
resource ledger's measure. The proof handles the actual charge order and has
no fee-loop iteration ceiling. All sixteen component targets and independent
component reviews pass, together with [full frozen validation](receipts/direct-protected-replay-build-20260910.json)
and [independent exact-commit review](receipts/direct-protected-replay-review-20260910.json).

This closes local reverse effects and guarded single-step construction.
Actual source instruction/price extraction, memory bounds from the source
ledger, whole finite trace and terminal replay, source occurrence coverage,
canonical funding/deployment/block context and policy decisions remain open.
Unchecked actions alone do not justify stack admission; the injected stack
counterexample is preserved and is not presented as a reachable contract bug.

Source `f11f001` adds the [execution-work bundle](receipts/direct-execution-work-bundle-20260910.json), which
derives mandatory append costs from the same actual completed user trace:
Exit costs at least 1419 execution gas; Deposit at least 2647. The last store
is counted after LOG0, so this is a completed-append bound, not a bound inferred
from an arbitrary executed log. Actual entry and fee-loop inversion, ordered
instruction markers, terminal trace uniqueness and source-priced prefix
splitting remove the supplied structural-count premise.

The finite recursive resource ledger tracks execution plus outstanding and
committed state spill. State credits and rollback preserve this potential;
exceptional forfeiture decreases it. CALL overhead subtracts its stipend once;
CREATE's opcode overhead is paid separately. Selected actual completed leaf
payments derive the transaction count bound from source allocation and calldata
floor without requiring global nonnegative net state use. Eleven targets and
43 standard-or-less axiom exports pass, with component reviews,
[full frozen validation](receipts/direct-execution-work-build-20260910.json) and
[independent exact-commit review](receipts/direct-execution-work-review-20260910.json).

This selection is explicitly a subset. Resource threading does not prove
source occurrence identity or coverage. Actual source frame/payment/journal
extraction, inclusion of every retained append, same-transaction settlement,
canonical deployment/funding/block context and policy decisions remain open.
The complete pinned 49-file gas audit is archived; it establishes the source
mutation inventory, not Python execution or canonical reachability.

Source `d85afb0` adds the [CALL boundary bundle](receipts/direct-call-boundary-bundle-20260910.json), which
constructs literal child gas grants after CALL precharges, keeps the value
stipend explicit, and derives failed-child meter guards from its actual paid
protected-runtime run. Parent incorporation and the failed new-account refund
stay tied to that same split and child result. Executed LOG0 costs remain bounded
by parent pool loss; cancelled logs are not treated as retained records.
Actual source early checks, state predicates, caller/child journal extraction,
other state-credit paths and recursive transaction/block composition remain
open. Three targets, ten standard-or-less axiom exports and component reviews
pass, together with [full frozen validation](receipts/direct-call-boundary-build-20260910.json)
and [independent exact-commit review](receipts/direct-call-boundary-review-20260910.json).

Source `949d49d` adds the [state accounting bundle](receipts/direct-state-accounting-bundle-20260910.json), which
derives source state-gas credits from the same actual storage actions, first
per slot and then across the full EVM address/key space using a symbolic finite
sum. Successful literal meter payments telescope to exact execution costs and
state-potential change. The same actual receipt retains all three guarantees
and a bound on executed LOG0 costs, with the initial credit potential retained
for nested frames. These logs are not identified with retained queue records.
Full-meter rollback preserves earlier committed charges, cancels this frame's
state balance at its baseline and leaves executed work paid. Actual source
child/outer journal pairing, grants, final refunds/block accounting and canonical
protocol context remain open. Nine component targets, 28 standard-or-less
axiom exports and component reviews pass, together with
[full frozen validation](receipts/direct-state-accounting-build-20260910.json) and
[independent exact-commit review](receipts/direct-state-accounting-review-20260910.json).

Source `e9be8e9` adds the [source admission bundle](receipts/direct-source-admission-bundle-20260910.json)
uses Amsterdam's own calldata floor to derive the size premise of the actual
transaction-history consumer. It does not infer the different pinned intrinsic
admission gate; the [divergence dossier](receipts/direct-reference-divergences-20260910.md)
records an unsigned local counterexample to that floor-only implication.
Source allocation and ordered reservoir-first spill now pay the same actual
runtime event list through STOP/RETURN/REVERT under sufficient cap/total-gas
inequalities. The same full receipt retains all three guarantee observations.
These quantified allocations are not yet bound to actual transaction or child
call grants. Settlement arithmetic is proved with explicit frame-input guards;
canonical admission, returned pools/refunds, source execution and block-history
extraction remain open. Eight component targets and 19 standard-or-less axiom
exports pass, together with [frozen full validation](receipts/direct-source-admission-build-20260910.json)
and [independent exact-commit review](receipts/direct-source-admission-review-20260910.json).

Source `e79530b` adds the [admission and ordered SYSTEM bundle](receipts/direct-admission-system-bundle-20260910.json)
derives root calldata fit from actual intrinsic-gas admission and connects it
to the existing transaction-history and committed-effect consumers. It also
constructs empty Deposit then Exit SYSTEM calls in the same actual history.
Both entry invariants and the work/funding bounds come from the two real factory
deployments and the linked history/ledger/block inputs. Each call retains its
three guarantee observations. Canonical validation/dispatch extraction and
acceptance of this schedule remain open. Four targets, nine standard-axiom
exports and component reviews pass, along with
[full frozen validation](receipts/direct-admission-system-build-20260910.json) and
[independent exact-commit review](receipts/direct-admission-system-review-20260910.json).

Source `e720558` adds the [runtime resource bundle](receipts/direct-runtime-resource-bundle-20260910.json)
adds closed source readings and COPY/LOG0 prices to the same actual user or
SYSTEM trace. Its complete success/REVERT certificates include terminal payment,
with memory charged once across the trace and a state reserve based on executed
SSTORE occurrences. All three guarantees consume the same receipt together
with these certificates. The resource statement is deliberately conditional:
its sufficient initial grants still need a protocol producer. It does not
assert admitted user progress or source exceptional replay. Six targets and
21 standard-axiom exports pass with component reviews,
[isolated full validation](receipts/direct-runtime-resource-build-20260910.json), and
[independent exact-commit review](receipts/direct-runtime-resource-review-20260910.json).

Source `f17ab237` adds the [runtime receipt bundle](receipts/direct-runtime-receipt-bundle-20260910.json)
now derives source-shaped actions for every actual completed user or SYSTEM
execution, including LOG0, COPY, STOP, RETURN and REVERT. Memory capacities
follow from an invariant on gas plus memory cost and an explicit initial
resource/host threshold. The same actual Theta receipt feeds all three
registered guarantee predicates and these runtime observations. Successful
terminal owner preservation discharges the empty-world fallback; failed calls
restore the whole pre-transfer journal and distinguish REVERT from exceptional
failure. No post-state capacity, global write permission, or 256-iteration cap
is assumed. The twelve component targets and reviews pass, as do the
[isolated full check](receipts/direct-runtime-receipt-build-20260910.json) and
[independent exact-commit review](receipts/direct-runtime-receipt-review-20260910.json). Initial source bindings, source user and
outer-frame payment, canonical history extraction and protocol choices remain
open; this bundle does not establish executable reference-interpreter parity.

Source `90f02e9` adds the [source-reading payment bundle](receipts/direct-source-payment-bundle-20260910.json)
removes the arbitrary storage-reading function from both SYSTEM constructors.
Each actual priced edge now carries its evolving source view, independent
warm-access set, source original/current/new values, and exact memory-cost
difference. The same event list pays through RETURN and retains post-RETURN
warmth, output and the three actual receipt guarantees. The initial source
storage/access/context binding and historical invariant remain explicit inputs;
executable reference interpretation is still open. CALLDATACOPY also has a
complete local effect adapter at arbitrary source offsets, including zero
length; user-path resources and full instruction/rollback composition remain.
All eight targets, 24 standard-axiom exports and component reviews pass, as do
[isolated full validation](receipts/direct-source-payment-build-20260910.json) and
[independent exact-commit review](receipts/direct-source-payment-review-20260910.json).
Exact lock-selected numeric sources show gas is nonnegative unbounded Uint,
so a fixed-width gas upper-bound obligation would be spurious. U256 operand
checks, nonnegative meter subtraction and initial source typing remain distinct.

Source `2f0c142` adds the [SYSTEM view composition bundle](receipts/direct-system-views-bundle-20260910.json)
constructs every source-shaped instruction action along the actual SYSTEM
trace, including RETURN and its extended-memory output slice. Accepted stack
operands, fixed-image decoder agreement, natural PC bounds, intermediate owner
and memory-capacity facts are derived from that execution. Deposit and Exit
entry constructors produce one witness carrying both these views and the
sequential source-meter payment. Its exact full Xi endpoint and Theta commit
then feed all three guarantee parents and SYSTEM invariant preservation in
`ReferenceSystemGuarantees.system`. No independent receipt is supplied.
All 19 targets, 61 new standard-axiom Trust exports, component reviews,
[isolated full validation](receipts/direct-system-views-build-20260910.json) and
[independent exact-commit review](receipts/direct-system-views-review-20260910.json)
pass. Initial storage/context bindings and
the historical invariant remain inputs to this adapter. Arbitrary storage-gas
readings are not yet coupled to the source views, and a source-shaped Lean
action is not an executable reference-interpreter trace. Canonical deployment,
admission, scheduling, fork and inhibition decisions remain open. The linked
producer inventory records these dependencies; the structured ledger remains
the only roadmap.

Source `64eddfb` adds the [SYSTEM resource bundle](receipts/direct-system-resources-bundle-20260910.json)
with sixteen modules and 100 Trust exports. Its [isolated full validation](receipts/direct-system-resources-build-20260910.json)
and [independent exact-commit review](receipts/direct-system-resources-review-20260910.json)
passed, including all 100 Trust exports and existing kill lines. Both
actual SYSTEM executions now retain their complete trace, terminal RETURN,
operation count, at most four SSTOREs and intermediate memory bounds. Word-fit
for memory expansion is derived from operand types, without a no-wrap premise.
The source memory-cost sum is constructed from those same actual states for an
arbitrary finite trace, including the terminal operation. Sequential source-meter
payment is then derived from initial resources, with every sentry and payment
condition proved and no reliance on future refunds. Under the proposed 30M
execution/16*97920 reservoir grant, conservative execution envelopes are
17,902,012 for Deposit and 1,730,623 for Exit, with 391,680 state gas each.

`SystemMeterResources.deposit/exit` retain the same actual successful evaluator
result and priced events. They do not establish execution by the proposed
reference interpreter: its instruction/state/checked-type adapter, mandatory
SYSTEM scheduling and canonical history remain open. Local control/stack,
arbitrary-offset CALLDATALOAD and charged memory-operation adapters also gained
proofs. The [producer inventory](receipts/direct-system-resources-bundle-20260910.json)
identifies each consumer, dependency and owner; the structured task ledger
remains the sole roadmap. No protocol variant or inhibition policy is adopted.

The preceding frozen source `8173c79` passed isolated `make check` and independent exact-commit review. Supporting
results now include universal remaining-gas bounds, recursive and whole-Υ
funding conservation under independent admission, linked funding histories,
all-outcome local event extraction, actual recursive error adapters, structural
occurrence uniqueness and child-charge transport through steps and wrappers.

Source `8173c79` adds ten modules and 52 Trust exports for reference operation
transport. Full account entry lookup, apparent/actual value and synthetic-log
guards, source-shaped storage layers and SSTORE charging, and five-image
PUSH/jump decoding are checked. Actual sparse memory writes compose with eager
reference slice replacement, deriving post-memory coherence, rounded capacity
and RETURN bytes. [Full validation](receipts/direct-reference-operations-build-20260910.json)
and [exact-commit review](receipts/direct-reference-operations-review-20260910.json)
passed. The [producer inventory](receipts/direct-reference-operations-bundle-20260910.json)
keeps source interpretation, full reference traces, bounds, gas accounting and
canonical protocol inputs open. The [divergence analysis](receipts/direct-reference-divergences-20260910.md)
records truncated-PUSH foreign-code mismatch, sparse memory and refund/state
boundaries. The tighter physical-store capacities give costs 1372/107; the new complete
trace producer conservatively uses 400/40 words and costs 1512/123. Reference
execution transport remains required. This is not Ethereum context closure.

Source `7f55526` derives both initial invariants from two linked actual factory
transactions. Exact salt/initializer copying, selected-child fuel, CREATE2 gas
settlement, constructor code deposit, the factory return, Θ value transfer and
Υ finalization are composed on the same worlds. The second deployment preserves
the first contract’s code/storage/control invariant. `FactoryHistoryGuarantees.from_genesis_both`
uses this committed seed for all three guarantees and the same retained queue/log
effects at every later receipt position; it does not assume an initialized seed.
The literal genesis/credit ledger derives the numerical funds bound. All 18
modules and 74 Trust exports passed [full validation](receipts/direct-factory-history-build-20260910.json)
and [exact-commit review](receipts/direct-factory-history-review-20260910.json).
[Finite factory regressions](receipts/direct-factory-deployment-regressions-20260910.json)
cover both deployments, admissible prefunding, collision retries and gas-failure
rollback, with complete traces and explicitly injected Prague setup.

The remaining protocol inputs are explicit in the
[producer inventory](receipts/direct-factory-history-bundle-20260910.json): canonical
factory installation and deployment admission/hash/collision state; the actual
prior genesis-to-deployment funding trace; canonical credit-ledger/count and
block/slot extraction; reference EVM opcode/rollback/gas and mandatory SYSTEM
scheduling/resources; and Thomas’s fork, inhibition and upgrade decisions.
The 30M pinned SYSTEM counterpart and synthetic SYSTEM-emitter log projection
are proved, but do not establish the reference dispatcher’s dual-pool liveness.
These conditional results do not close or adopt an Ethereum protocol context.

Source `d71706d` composes journal preservation over the complete actual recursive
evaluator, including failed wrappers and ancestor rollback. Every nested call's
input invariant is derived from the initial journal and real preceding steps;
its three local observations bind to the same actual receipt. A constructive
`5 * (request.gas + 1)` evaluator-fuel bound discharges all-node fuel exhaustion,
including caught creation children. This is separate from EVM gas success and
reference Ethereum semantic transport. All ten modules passed
[isolated full validation](receipts/direct-recursive-journal-build-20260910.json)
and [independent exact-commit review](receipts/direct-recursive-journal-review-20260910.json).
Actual transaction settlement, initialized linked histories, external-credit
provenance, committed-record/log survival and protocol obligations remain open.

Source `40b6095` adds actual Υ checkpoint/provisional/settlement composition,
including failed status, refunds and cleanup. A linked history of the same
transaction receipts, either canonical SYSTEM runtime and literal credits
derives intermediate invariants and funding from one seed. The exact ordered
receipt list feeds the admitted block work envelope. Chosen physical queues
are unique and actual local append couples the queue extension to authentic
LOG0; a false-status call restores its checkpoint. These five modules passed
[isolated full validation](receipts/direct-actual-history-build-20260910.json)
and [independent exact-commit review](receipts/direct-actual-history-review-20260910.json).
Seed deployment/funding, protocol extraction, external-credit provenance and
bounds, plus occurrence identity and survival through ancestor rollback remain
required consumers. Local queue uniqueness does not identify equal-byte submissions.

Source `7cc3d0a` derives the actual prehistory at every transaction list
position, then uses its seed-derived funding/invariant for all three nested
observations. Protected-address log frames preserve all topics/payloads and
actual order through ordinary other-owner instructions and Υ finalization.
A literal credit ledger supplies a symbolic funding envelope; the numerical
specialization remains conditional on protocol-derived PoW/withdrawal counts,
migration coverage and genesis correspondence. All three modules passed
[isolated full validation](receipts/direct-history-observations-build-20260910.json)
and [independent exact-commit review](receipts/direct-history-observations-review-20260910.json).
These results do not yet prove complete committed occurrence/log survival or
reference protocol/deployment coverage.

Source `baf38a4` ties actual transaction/history queue replay to extracted
protected-call world paths and proves record-source provenance. It separately
specifies a unique ordered list of calls surviving the literal wrapper guards;
the exact list-to-path bridge and final log equation are the next consumers.
Literal conserving transfers now enter the funding and execution histories,
and sequential full-balance sweeps derive their receiver arithmetic bound.
A source-verified minimum-difficulty/terminal-parent calculation supplies the
PoW count arithmetic, with canonical-chain and reward linkage still explicit.
All supporting targets passed [isolated full validation](receipts/direct-queue-provenance-build-20260910.json)
and [independent exact-commit review](receipts/direct-queue-provenance-review-20260910.json).
The three [nested rollback regressions](receipts/direct-nested-rollback-regressions-20260910.json)
separate executed append work from committed records/logs, including a caught
inner out-of-gas. They use an injected Prague state, not protocol reachability.

Source `22a886b` closes the pinned-evaluator composition of actual surviving
call IDs, final queue replay and final protected-emitter logs. The same canonical
list has no duplicate invocation IDs; the final log count equals the surviving
successful nonempty non-SYSTEM submission count, bounded by actual executed
marked work and reported transaction gas. It is not the final queue length.
`HistoryCommittedGuarantees.composed` derives the physical prequeue from the
actual initialized prefix and combines these committed effects with all three
local observations at every transaction position, including nested calls later
rolled back. Its genesis-ledger specialization discharges the numeric initial
funding bound using the complete constructed genesis world. Literal withdrawal
dispatch counts every list item, including Gloas builders, and typed accepted
payload lists at distinct beacon slots derive the withdrawal count bound.
All eleven modules passed [isolated full validation](receipts/direct-committed-effects-build-20260910.json)
and [independent exact-commit review](receipts/direct-committed-effects-review-20260910.json).

This is still conditional Ethereum coverage. The [transitive producer inventory](receipts/direct-committed-effects-bundle-20260910.json)
keeps exact factory/deployment/parent-commit initialization, canonical genesis
and credit classification/chronology, reference semantics and resource pools,
transaction admission, block/slot and SYSTEM dispatch/progress, inhibition and
upgrades open. The supplied ledger matches genesis, final world and credit
total; step-by-step correspondence with the actual reference history is a
separate obligation. No protocol variant has been silently accepted.

The new modules derive full nested-event extraction, tree uniqueness
and aggregate gas for every finite evaluator fuel and every outcome. Descendants
remain counted after errors or ancestor rollback. A successful audited append
is tied to a local event in the same certificate. The actual Υ child selection
and capped refund now derive `tree.count ≤ usedGas` without a supplied aggregate
charge. Exact initializer success is also derived with code-deposit resources.
All additions passed frozen full validation, including the existing mutation
targets; the [build receipt](receipts/direct-nested-event-composition-build-20260909.json)
records exact sources and dependencies. This is modular evidence, not closure
of the three guarantees over protocol histories.

Sources `39b3e02` and `413176a` add the complete set of actual locally successful append
frames. `XiAt.identity` proves that each structural path denotes unique full
inputs and result; `NestedAppendCount.mem_frames_iff` proves the finite set
omits no qualifying invocation. Its count is bounded by actual Υ reported gas,
including reverted descendants. All nine new modules passed isolated full validation and independent source
reviews; the [build receipt](receipts/direct-append-history-bridge-build-20260910.json)
and [exact-commit review](receipts/direct-append-history-bridge-review-20260910.json)
identify the validated sources. Runtime
clones and delegated execution of the pinned bytes are conservatively included.
The opcode tables and actual dynamic execution scope now prove that both
runtimes have no child invocations. Ordinary instructions executed at another
owner preserve existing protected account code/storage, including SELFDESTRUCT
with that account as beneficiary. Nested subtree counts and actual transaction
receipts feed the typed block budget; protocol gas admission remains explicit.
A kernel-certified CREATE/zero-evaluation-fuel prefix erases the temporary world
and ultimately errors. This diagnoses a proof-evaluator boundary, not a
successful Ethereum transaction or a security exploit.

Source `b341047` additionally derives funding ceilings at every actual nested
Theta transfer from the linked funding history, including reverted ancestors.
Typed CREATE encoding is total; Lambda errors are classified as evaluator
OutOfFuel. Exact creation/message/ordinary/finalization code and storage frames
compose with the protected call's queue/control invariant on the same receipt.
The full pinned genesis input has 8893 allocations whose sum and constructed
account-map bound are kernel checked. These 16 modules and their Trust exports
passed [full validation](receipts/direct-funding-journal-build-20260910.json)
and [independent exact-commit review](receipts/direct-funding-journal-review-20260910.json).
The genesis input is not yet bound to the reference loader or admitted protocol
history. The legacy initializer consumer exposes target absence; the newer
prefunding-compatible producer is now connected to the journal invariant. Complete call-owner/code
coherence, selfdestruct exclusion and adequate evaluator fuel remain open.

Source `bd62a07` composes all three local runtime observations on the same
actual protected Theta receipt. Its public queue/control domains are derived
from one journal invariant; the actual selected code and value are bound to
that receipt. Chronological executed-event intervals and the append weight
use the same nested certificate. Prefunded initialization, nested calldata
width, recursive step world/set projections, and runtime/precompile deletion
frames are now connected consumers. Ten modules passed [full validation](receipts/direct-protected-journal-build-20260910.json)
and [exact independent review](receipts/direct-protected-journal-review-20260910.json).
This establishes the atomic step needed by the global journal induction. It
still consumes the input invariant and does not establish protocol history
reachability or sufficient SYSTEM resources. The runtime control component is
not misrepresented as the full initialization-and-progress PControl conjunction.

The next missing composition is **committed storage and intermediate journals**.
Locally successful appends are a work metric, not a persistent-record count.
Valid protocol-history extraction, external credit provenance, every
intermediate domain, deployment, block accounting and scheduling remain to justify. Final normative version/inhibition remains an
explicit report decision. No intermediate supporting result closes these
obligations by itself. The sections below retain the evidence chronology.

The resumed closure review expands the public transitive premises into 46
explicit obligations, attached to the four existing structured tasks (5 fee,
11 queue/event, 27 protocol/initialization, 3 global-composition obligations).
The [premise inventory](receipts/direct-public-premises-20260909.json) and
[task-write receipt](receipts/direct-premises-roadmap-20260909.json) are review
snapshots, not another roadmap or acceptance of those obligations.
Seven additional reference-interpreter adequacy obligations are attached to
the existing protocol task in the [structured progress receipt](receipts/direct-structured-progress-20260910.json).
The [semantic inventory](receipts/direct-semantics-adequacy-20260910.md) and
[focused adapter proposal](receipts/direct-runtime-adapter-interface-20260910.md)
identify dual gas pools, transaction type 4, transfer LOG3, code protection and
sufficient evaluator fuel as concrete remaining bindings. They do not claim
that the pinned evaluator already implements the proposed Amsterdam reference.
The [current-version review](receipts/direct-protocol-current-20260909.md)
checks byte identity, deployment preimages and report provenance; its proposed
protocol choices and authors draft remain unadopted and unsent. In particular,
canonical deployment still needs the actual factory transaction and ancestor
commit, beyond the new local initialization-success theorem, and the runtime domain must be derived
at nested intermediate states as well as committed transaction boundaries.

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
* `FundedDomain` proves the safe numerator ≤2892 is preserved by paid appends
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
  requires an actual `LogPath` witness, discharged by `AppendGasPath` below.
  It does not assume a desired final gas value.

The following complete-call/history modules passed isolated `make check` at
`586bb1c`; source bindings and reviews are in `direct-history-build-20260909.json`
and `direct-history-reviews-20260909.md`:

* `SuccessfulSystem` transports both arbitrary-resource SYSTEM success results
  to actual Θ storage and output, deriving owner survival/nonempty settlement.
* `SystemStateInvariant` covers actual completed SYSTEM results: success returns
  exactly the capped FIFO prefix and keeps its suffix; failure preserves the
  queue and makes no return-byte claim. Structural budget and enabled fee safety
  are preserved in both cases, with exit source width retained. Scalar-only
  wrappers need no logical queue witness.
* `ConcreteHistory` links real full pre/post worlds through actual Θ transitions
  and counts events from success, caller and input. Its policy contains only
  calldata-size and user-funding constraints. An independent total-event bound
  supplies all prefix bounds; no invariant or AppendFits is a history-constructor
  premise. Actual successful creation supplies the initial invariant, with
  canonical address equality explicit. The conclusion preserves budget, fee
  safety and an existential represented FIFO (including exit source width).
  It does not extract arbitrary transactions/ancestor rollbacks, connect gas
  totals, or impose inter-call header/originalWorld/substate coherence.

The following gas modules passed isolated `make check` at `749a1c0`; exact
bindings and reviews are in `direct-gas-build-20260909.json` and
`direct-gas-reviews-20260909.md`:

* `AppendGasPath` extracts the genuine supported trace from every actual
  successful append and discharges `ActualAppendGas.LogPath`. The resulting Θ
  theorems prove returnedGas+919≤inputGas for exits and +1847 for deposits.
  No path witness, gas bound, fee completion, owner or storage fit is supplied.
  These are lower bounds on internal execution cost, not total transaction gas.
* `RefundAccounting` projects actual Υ transaction execution/finalization onto
  its true provisional Θ/Lambda result and exact refund expression. It derives
  all word-fit conditions from remaining≤limit and proves count≤reported net
  gas when the independently counted events satisfy 919*count≤gross gas. It
  includes failed transactions. The aggregate charge and valid remaining-gas
  inputs still need a real, nonduplicated call-tree accounting proof.

These results advance the coverage rows below without closing any of the three
public IDs. Extraction of initialized protocol histories, execution-event
accounting and the justified mathematical tariff domain
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
| Oldest capped records and encoding | `SystemStateInvariant` identifies actual returned bytes and dropped suffix from arbitrary-resource Θ success | Input FIFO/source-width follows local concrete-history induction; valid protocol history extraction remains |
| Full/partial pointers and old record slots | `SystemSpec` and `CommittedSystem` prove exact word pointer updates and every slot ≥4 unchanged | `QueueArithmetic` supplies natural length/pointers under HEAD≤TAIL; derivation of that entry invariant remains |
| Caller dispatch and inhibition | User/SYSTEM inversion covers both actual caller classes; UniversalGate proves inhibited user rollback | Conditional direct parent implemented; protocol authorization/scheduling and mutation-based registration remain |
| Getter read-only; append count/excess | `GetterInversion` proves Θ getter preservation from actual success without resources/completion premises | `SuccessfulAppend` proves independent append controls from arbitrary-resource success under local fit; history-derived fit remains |
| SYSTEM count reset, latch/unlock/fold | `SuccessfulSystem` derives all word controls from actual Θ success; Bounded gives the natural sum bound | Budget accounting must be justified by valid protocol executions; natural calldata nonemptiness also needs size-word fit |
| Constructors | `InitializedInvariant` derives installed runtime, exact gating and initial empty FIFO/bounds from actual successful Lambda creation at an absent target | Explicit creation resource conditions; canonical deployment identity and valid protocol-history binding remain |
| Correct mathematical fee numerator/tariff | `SuccessfulUser.*_getter_math` proves actual Θ price agreement for independent pre-call numerator ≤2892; `MathFee` is untruncated | Protocol/funding justification of the domain remains; `FeeBoundary` refutes unrestricted agreement at 2893 |

## Direct specification and accounting continuation

The frozen candidate at `5c3da89` adds code-independent data specifications and
actual CALL accounting. Isolated `make check` passed; exact source bindings and
reviews are in `direct-specs-build-20260909.json` and
`direct-specs-reviews-20260909.md`.

* `DirectAdmission` derives the untruncated mathematical price and the checks
  paid by the same successful user call. Its predicate contains no original-code
  pin; only the correctness proof does. The pre-call enabled-safe domain remains
  explicit. Deposit admission includes the actual minimum amount of 10^9 gwei.
* `AppendDataSpec` factors authentic record words, exact storage overlay, natural
  controls and one anonymous receipt into pure data specifications. Correspondence
  theorems recover the existing append specifications without weakening them.
* `SystemDataSpec` derives a code-independent four-slot overlay from actual Θ
  success, then separates natural control and drain/stale-slot projections using
  independent input bounds. These predicates can also be tested against mutants.
* `CallGasAccounting` and `CallDispatchGas` bind actual accepted CALL dispatch to
  its literal child Θ invocation and returned gas. The natural debit includes
  overhead minus stipend plus memory expansion; denied calls have no child event.
  Child remaining-gas monotonicity and a nonduplicated full execution tree remain
  separate obligations. CALLCODE/DELEGATECALL/STATICCALL/CREATE are not covered here.
* `FundingBounds` proves conditional external-credit envelopes below 2^163 (16
  withdrawals per payload) or 2^223 (a looser list bound), both below the certified
  fee ceiling. The input lists, genesis bound, actual admission and conservation
  are not established as protocol facts by this arithmetic theorem.

The reviewed next steps are archived in
`direct-parent-packaging-next-20260909.md` and
`direct-funding-domain-next-20260909.md`. In particular, final mutation refutations
must satisfy independent domains and execute actual Θ; the existing Ξ mutant
receipts alone do not refute the complete-call parents. The three public IDs
remain open. Versioned funding references are supporting research, not changes
to the normative pins or a certified mainnet genesis state.

## Composed conditional direct guarantees

The frozen candidate at `6fde5fc` passed isolated `make check`; bindings and
reviews are in `direct-parents-build-20260909.json` and
`direct-parents-reviews-20260909.md`. `DirectGuarantees` supplies exactly three parameter-code
predicates and pinned universal instances for both contract kinds:

* `psubmit1_direct`: actual nonempty user success implies the enabled, paid
  mathematical admission and the same authentic record/storage/log result.
  Getters are read-only. SYSTEM adds no log and preserves every record slot.
  Actual failure restores the journal. No signature check is claimed.
* `pdrain1_direct`: actual SYSTEM success returns the encoded oldest capped
  prefix and leaves the represented suffix, with exact natural pointers and
  stale-slot preservation. User calls preserve HEAD and either keep the queue
  or append exactly one independently specified record; failures consume none.
* `pcontrol1_direct`: actual caller partitions control effects, with inhibition,
  natural getter fee, count/excess updates and natural SYSTEM latch/unlock/fold.
  It includes the separately quantified initializer and a SYSTEM progress clause:
  owner presence, write permission, 2.5M gas and fuel≥8503 suffice for success on
  either runtime, with **no enabled-storage premise**. Arbitrary-resource safety
  remains separate from this sufficient-resource success clause.

The input domains are pre-call owner/value/size observations, independent budget
and safe-fee invariants; drain also takes a represented queue and exit source
width. No original-code constraint occurs inside those domains. The standalone
call predicates do not require an external funding ceiling. `ConcreteHistory`
still requires funding and event bounds to preserve their preconditions.

`DirectInitialization`, `DirectSubmit`, `DirectAppend`, `DirectControl`,
`DirectDrain` and `SystemFrame` compose existing execution proofs into these
observations. Getter preservation concerns created accounts, account lookups,
logs and zero value; access bookkeeping may change, as recorded in the archived
getter erratum. No full-substate getter equality is claimed.

`AuditedChildGas` now derives a successful audited child's 919/1847 charge and
includes it once in the actual parent CALL debit without a supplied child-gas
bound or path. `TransferFunding` observes the real finite AccountMap balance
sum and proves that actual funded Θ entry transfer cannot increase it, including
alias and absent-account cases. General execution conservation, transaction
admission, nonduplicated event accounting and block/history extraction remain.

The three new predicates are **conditional direct candidates**, not yet replacements
for the public Registry/YAML parents. Same-predicate actual-Θ mutation witnesses,
reviewed registration and protocol-domain justification remain acceptance gates.

## Same-predicate Θ control mutations and ordinary gas

The frozen candidate at `0469f9c` passed isolated `make check`; exact source
bindings and reviews are in `direct-theta-control-build-20260909.json` and
`direct-theta-control-reviews-20260909.md`. `DirectThetaMutations` refutes **the exact new `PControl` predicate**
for both the caller-dispatch and TARGET mutations, with parameter-code domains
proved independently (budget 105), actual installed mutant code and actual
successful Θ results. A zero-value adapter proves exact equality with the old Ξ
runner inputs and derives the account witness that excludes empty settlement.
There is no new native execution evaluation: each finite refutation retains only
its corresponding historical native receipt axiom. The new universal parents
remain dependent only on standard Lean axioms. The other four Θ mutation
transports remain open, so public registration is still pending.

`OrdinaryGas` covers exact accepted-step debit for every opcode except the six
recursive CALL/CREATE-family instructions, including GAS and SELFDESTRUCT.
INVALID is excluded by actual Z acceptance, not by trusting raw fallback behavior.
Actual ordinary prefixes and final successful halts are accounted; recursive
frames and full extraction/aggregation remain separate.

## Five actual-Θ mutation refutations and CALL-family accounting

The frozen candidate at `778f4f5` passed isolated `make check`; bindings and
reviews are in `direct-theta-drain-build-20260909.json` and
`direct-theta-drain-reviews-20260909.md`. `DirectThetaDrainMutations` adds the exact new `PDrain` refutations for
both cap mutations and the stale-slot overwrite. Physical pre-queues and domains
are proved independently for arbitrary code; exit source width covers all 17
entries, including the remaining one. Actual zero-value Θ calls reuse their old
Ξ receipts after exact entry/environment transport. Only the corresponding old
native receipt axiom remains in each finite refutation.

Together with the two control refutations, five of the six required same-predicate
Θ mutants are implemented. The funded LOG0 witness remains open: an attempted
monolithic kernel evaluation of a zero-excess actual Θ fixture was killed with
exit 137 and produced no certificate. Its untracked draft is excluded from the
frozen validation candidate; work continues on smaller kernel-checked fragments.
No new native execution axiom is introduced to close it.

`CallFamilyGas` extends real dispatch/child/gas/denied-branch accounting to
CALLCODE, DELEGATECALL and STATICCALL with their distinct stack layouts, source,
storage recipient, code target, real/apparent value and permissions. The local
child remaining-gas bound remains explicit for permitted calls. `CallFunding`
derives sufficient real transfer funds from those actual call gates, and binds
the entry budget to the exact child invocation extracted from StepOk. Neither
lemma assumes conservation of the world returned after child code execution.

## Universal remaining gas and ordinary funding

The frozen candidate `d7de3a0` passed isolated `make check`; exact source hashes
and reviews are in `direct-recursive-gas-build-20260909.json` and
`direct-recursive-gas-reviews-20260909.md`.
`ReturnedGas` proves, by mutual strong induction on arbitrary evaluator fuel,
that completed X, Ξ, Θ and Λ results and every accepted actual step return no
more gas than they receive. This includes REVERT, both Θ/Λ statuses, the ten
precompiles, all six recursive instructions and CREATE's actual caught-error
branch. No child-gas bound, code pin or finite iteration cutoff remains in the
universal theorem's premises. Interpreter errors have no invented endpoint.
`CreationGas` supplies literal CREATE/CREATE2 dispatch and code-deposit debits.

`TransactionGas` now derives the real Υ provisional remaining-gas bound and its
exact natural capped-refund/net-gas formula from execution. Its count-to-net-gas
corollary still requires an independently established aggregate append charge;
it does not manufacture event counting or protocol transaction validation.

`StorageFunding`, `SelfdestructFunding` and `OrdinaryFunding` prove that actual
accepted nonrecursive instructions cannot increase the finite AccountMap sum
of balances. Persistent/transient writes preserve it; SELFDESTRUCT handles both
same-address policies, absent accounts and possible modular-credit loss. There
is no assumed supply ceiling or predicted post-state. Recursive funding,
transaction escrow/settlement, external credits and protocol history remain.

## Registered conditional direct parents and six Θ refutations

The frozen registration source `9d44bcf` passed isolated `make check`. Its
exact source hashes and log are in `direct-registration-build-20260909.json`;
independent metadata and mutation reviews are recorded alongside it. The public
YAML now selects exactly `DirectGuarantees.psubmit1_direct`, `pdrain1_direct`
and `pcontrol1_direct`, for both contract kinds. Scope is explicitly
`THETA_CONDITIONAL_FORALL`: the local theorem is checked and overall protocol
closure stays PARTIAL/OPEN. AllGuarantees checks these exact predicate instances.
No finite receipt is conjoined into a universal correctness parent. Original
CFG/model parents, kill-lines and metadata remain in Lean and `audit/history`.
The earlier sections saying registration is pending describe prior snapshots.

`DirectThetaSubmitMutation` certifies all 158 actual instruction steps of a
zero-excess funded LOG0 mutant, then the same Ξ and settled Θ result.
`DirectThetaSubmitCounterexample` independently proves its budget-0 domain,
real sender funding and two-ETH pre-world total, and refutes exactly PSubmit.
The complete wrapper now compiles; the earlier monolithic/normalization memory
failures produced no accepted result and were replaced by small proved steps
and finite-map funding identities. No new native evaluation axiom is used.
`DirectThetaKills` gathers the six exact predicate negations for metadata only.

The five control/drain witnesses keep their disclosed historical native receipt
axioms. Their sibling Boolean regression checks do not establish universal
independence. The new guarantees deliberately overlap: SYSTEM stale-slot
corruption contradicts both drain preservation and the PSubmit record frame.
No clause was weakened to manufacture a disjoint test matrix. The independent
registration review records the conservative cross-impact matrix; only the six
named same-predicate refutations are advertised as compiled test conclusions.

Protocol-domain coverage, actual nested-event aggregation and initialized valid
history extraction remain separate obligations. Registering this stronger
conditional evidence does not complete the agreed audit.

## Actual recursive execution and transaction funding

The frozen funding source `c92e0f8` passed isolated `make check`. Exact hashes
and the successful log are in `direct-recursive-funding-build-20260909.json`;
independent reviews are in `direct-recursive-funding-reviews-20260909.md`.

`CallWorld` and `CreationWorld` extract the literal child invocation and returned
world from actual accepted recursive steps, including denied calls and CREATE's
caught-error/empty-world branch. `CreationFunding` handles nonce changes and
code installation. It treats sender/creation-address aliasing separately:
Λ's intermediate debit/credit can increase the map sum in that case, but the
actual nonzero nonce selects INVALID code and the completed creation restores
the input world. No hash-injectivity assumption hides this case.

`ExecutionFunding` proves by mutual strong induction on arbitrary evaluator
fuel that completed execution cannot increase the finite sum of balances.
X/Ξ cover successful states; Θ and Λ cover both statuses and the actual rollback
rules, with funded input transfer and, for Λ, an existing nonzero sender nonce.
Accepted steps derive child funding and nonce facts from their actual gates.
The proof includes every recursive opcode and all ten precompiles; no child
conservation result or predicted post-world bound is an input hypothesis.

`FinalizationFunding` proves actual modular credits, account deletion folds
and transient-storage cleanup bounds. `TransactionFunding` then proves an exact
Υ settlement equation and nonincrease of the whole transaction's world funds.
Its independent admission conditions require the existing sender, sufficient
natural balance for upfront gas/blob fees plus value, bounded pre-increment
nonce, and priority price no greater than effective price. They are not yet
extracted from a protocol validation implementation. The proof uses the actual
provisional execution, refund cap, beneficiary credit and cleanup, for either
returned status. No new native execution receipt or project axiom is used.

These endpoint results do not themselves establish every intermediate call's
budget, nested append counting, external issuance/withdrawal accounting, or a
valid initialized protocol history. Those obligations remain open.

## Linked funding history and all-outcome local events

The frozen source `c0c6bea` passed isolated `make check`. The exact-source
receipt is `direct-local-events-build-20260909.json`; independent reviews are
in `direct-local-events-reviews-20260909.md`. New proofs use only standard
Lean axioms.

`FundingHistory` links actual Υ transactions, zero-value SYSTEM Θ calls and
literal AccountMap credits. Its constructors assume independent input admission
and actual execution receipts, never a post-world funding bound. The proof
derives each resulting world's budget from initial funds plus accumulated
explicit credits. It also bounds every actual XRuns prefix, including prefixes
whose later execution reverts or errors. Protocol provenance of those credits
and transactions and a bound on the initial-plus-credit sum remain required.

`FrameEvents` extracts certificates from every actual X outcome: successful
halt, REVERT, guard rejection, failed step and OutOfFuel. Its marked events are
actually completed LOG0 instructions with actual length at least 68 bytes.
The proof derives `residual + 919 * localEventCount <= entryGas`; an error has
accounting residual zero, without inventing an actual error gas field. The
local list is unique and has no duplicate occurrences even through PC loops.
Existing XRuns prefixes embed in that same certificate. `AppendEvents` binds
both successful audited append paths to occurrences in this unique list.

This is frame-local accounting: recursive instructions are actual opaque steps
and their descendant events are not counted yet. Fuel labels distinguish local
occurrences only; they cannot serve as globally unique call-tree IDs. Full
nested counting needs actual child/error extraction and disjoint structural
paths, including events before a child or ancestor error. The implementation
proposal in `audit/receipts/direct-event-accounting-design-20260909.md` lists
these remaining adapters and the eventual actual-Υ/refund composition.

## Recursive error adapters and child-charge induction edges

The frozen source `b0af68d` passed isolated `make check`. Its exact-source
receipt is `direct-child-outcomes-build-20260909.json`; independent reviews
are in `direct-child-outcomes-reviews-20260909.md`.

`CallOutcome` gives exact CALL-family step/helper equations for all outcomes,
including error equivalence to the admitted literal child Θ error, no-child
denied results and the zero/one-fuel boundaries. Actual Z alone bounds the
stipend-inclusive allowance. `CreationOutcome` exposes the literal Λ child and
CREATE/CREATE2 settlement for all outcomes. It retains catch of every child
error, including OutOfFuel, and the post-child word-addition guard that can
reject a final step. It does not replace that guard by a natural inequality or
assume a successful parent.

`RecursiveEventDebit` transports a charge on the same actual child to its actual
parent step. This covers both returned statuses, propagated errors, caught
creation errors and post-child guard rejection, with no double charging of
CALL's forwarding allowance. **These are induction edges:** the child's
`residual + charge <= allowance` bound is still an explicit hypothesis. They
are not yet the universal nested-event theorem. A mutual actual trace
extraction, structurally distinct child/continuation occurrence paths, and
composition with the actual Υ refund and valid block accounting remain open.

## Structural occurrence trees and execution-wrapper charge edges

The frozen source `68c083a` passed isolated `make check`. Its exact-source
receipt is `direct-event-tree-edges-build-20260909.json`; independent reviews
are in `direct-event-tree-edges-reviews-20260909.md`.

`EventTree` supplies fixed structural addresses: the local marked occurrence is
at `[]`, child addresses start with `false`, and continuation addresses start
with `true`. Its occurrence list has no duplicates and its length equals its
count. Repeated PC values, reused fuel in different frames and identical
subtrees do not collapse these structural addresses. This is pure structural
support, with no evaluator or gas claim by itself.

`WrapperEventDebit` proves that actual Ξ preserves the X accounting residual,
and that the actual code Θ and Λ settlement can only reduce their own selected
execution's residual, including rollback and error outcomes. Failed creation
address encoding has zero residual and no selected init execution. Explicit
child-charge hypotheses transport through those wrappers. These proofs do not
yet provide the mutual nested-event certificate or its extraction, and the
raw precompile/zero-fuel wrapper cases still need their tree adapters. The
structural and wrapper results supply parts of that remaining composition;
they do not discharge it by definition.

## Remaining proof obligations and owners

| Obligation | Dependency | Owner | Next verifiable result |
|---|---|---|---|
| Full getter from actual success | GetterInversion + SuccessfulUser | Validated at f52112e | Actual Θ output and read-only effects without assumed completion; mathematical tariff has explicit domain |
| Derive quote completion from successful runtime execution | SuccessInversion + SuccessfulQuote | Validated at 018cd2d | Actual successful user Θ implies a completed operational quote, without a gas bound |
| Append storage and log postconditions | SuccessfulAppend + UserQueueInvariant | Implemented with independent domain bounds | Actual Θ effects derive from success; initial representation and accounted budget remain to justify |
| Drain contents and FIFO | CommittedSystem already covers word pointers and every stale slot | Queue lane, consumed by integrator | Actual returned bytes equal independent concatenated oldest records |
| Remaining call composition | User and SYSTEM Θ at arbitrary resources; state/FIFO preservation | Implemented locally | Three direct predicates and all six same-predicate Θ mutants are implemented; registration validated at 9d44bcf; protocol-domain closure remains |
| Exact initialization and protocol history | InitializedInvariant + ConcreteHistory + versioned EL/CL references | Integrator/protocol lane | Extract actual transaction/block histories, including ancestor rollback and external frames, and justify address/scheduling |
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
