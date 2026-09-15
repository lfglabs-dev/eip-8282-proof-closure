# Dated direct-closure candidate log

Archived from `audit/DIRECT-CLOSURE.md` during repository cleanup. These entries
record candidate milestones through 12 September 2026; their status language is
historical. See the [current evidence map](../DIRECT-CLOSURE.md) for the
registered guarantees and [resource assumptions](../release/RESOURCE-ASSUMPTIONS.md)
for the later supply/work derivation.

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
[bundle](../receipts/direct-ordinary-block-bundle-20260911.json),
[build](../receipts/direct-ordinary-block-build-20260911.json),
[axioms](../receipts/direct-ordinary-block-axioms-20260911.json) and
[rechecked complete source provenance](../receipts/direct-ordinary-block-sources-20260911.json).
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

Independent exact review on the ordinary block candidate is now CLEAN:
[report](../reviews/spark-review-f2ab5eb.md) covers `a612bbb`, `5cd0fe5`,
`cb65536` and `f2ab5eb` together (fresh-context reviewer, not the author),
with zero blocking and zero advisory findings. The earlier
[review-status receipt](../receipts/direct-ordinary-block-review-status-20260911.json)
recorded the quota outage that preceded this review. Local promotion is
recorded here only; PR20 remains `c3f3c1d`, and prepared documentation
`7e2ef006` stays unpushed. No external message or normative policy has been
promoted.

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
[bundle](../receipts/direct-funded-history-lifecycle-bundle-20260911.json),
[build](../receipts/direct-funded-history-lifecycle-build-20260911.json),
[axioms](../receipts/direct-funded-history-lifecycle-axioms-20260911.json) and
[source references](../receipts/direct-funded-history-lifecycle-sources-20260911.json).

Independent exact review is now CLEAN: fresh-context reviewer, not the
author; zero blocking findings; one advisory noting a cosmetic field-count
phrasing in the bundle receipt (corrected in place, module SHA-256 unchanged).
See [report](../reviews/spark-review-8f76438.md) and
[status receipt](../receipts/direct-funded-history-lifecycle-review-status-20260911.json).
No proof extension, external message or normative policy has been promoted.
PR20 remains `c3f3c1d`; prepared documentation `7e2ef006` remains unpushed.
The existing structured task ledger remains the sole roadmap.
## History non-receipt extensions — SYSTEM and transfer candidate

`ReferenceHistoryNonReceiptExtensions.next_system` and `.next_transfer`
complete the History extension coverage started by
`ReferenceFundedHistoryLifecycle.next`. Where `.next` appends one
ordinary Υ receipt, these two constructors extend a
`History deposit exit before` by one further world change that does not
add a receipt: a mandatory SYSTEM Θ (empty data, zero value) via the
`Trace.system` constructor, and a bare protocol-level balance transfer
via `Trace.transfer`. Together with `.next` they cover the three
zero-credit extensions of `ActualJournalHistory.Trace`; the `credit`
constructor is left to the caller because its exact classification
(PoW / withdrawal / migration) is a protocol-level distinction.

Both extensions preserve the receipt list, block list, `baseCredits`,
`credits`, `pow`, `withdrawals`, `migrations` and `counts` fields
exactly. Only the pre-world advances. The internal ledger extension
routes through `ProtocolCreditEnvelope.Ledger.conserving` on the
corresponding `FundingHistory.Step.system` / `.transfer`.

Six auxiliary stability lemmas (`.receipts_stable`, `.blocks_stable`,
`.credits_stable` for each extension) expose the preserved fields
without pattern matching on the `History` structure.

Neither extension asserts canonical Ethereum machinery has authorized
the SYSTEM Θ or scheduled the transfer; the caller/zero-value/data-fit
conditions and the `funded` premise are inputs matching exactly what
`Trace.system` and `Trace.transfer` accept.

Source `spark/eip-history-nonreceipt-extensions-20260911`. All eight
declarations depend only on `propext`, `Classical.choice` and
`Quot.sound`. See the
[bundle](../receipts/direct-history-nonreceipt-extensions-bundle-20260911.json),
[build](../receipts/direct-history-nonreceipt-extensions-build-20260911.json),
[axioms](../receipts/direct-history-nonreceipt-extensions-axioms-20260911.json) and
[source references](../receipts/direct-history-nonreceipt-extensions-sources-20260911.json).

Independent exact review is now CLEAN: fresh-context reviewer, not the
author; zero blocking findings; two advisory findings noting
doc-comment cross-references to modules on other spark branches
(`ReferenceCanonicalHooks.SystemAuthorization` and
`ReferenceFundedHistoryLifecycle.next`). These are documentation
signposts of intended composition, not Lean imports; no proof-surface
impact. See [report](../reviews/spark-review-e673707.md) and
[status receipt](../receipts/direct-history-nonreceipt-extensions-review-status-20260911.json).
## History withdrawal extension candidate

`ReferenceHistoryWithdrawalExtension.next_withdrawal` completes the
extension coverage for the fourth `ActualJournalHistory.Trace`
constructor. Where `ReferenceFundedHistoryLifecycle.next` handled the
ordinary Υ (transaction) case, and
`ReferenceHistoryNonReceiptExtensions.next_system` / `.next_transfer`
handled the two zero-credit non-receipt cases, `next_withdrawal`
handles the credit-carrying withdrawal case by chaining the ledger via
`ProtocolCreditEnvelope.Ledger.withdrawal` and the trace via
`ActualJournalHistory.Trace.credit`.

The extension accepts a recipient, a `UInt256` amount admitted by
`Ledger.withdrawal` (`amount.toNat ≤ withdrawalMaximum`), and a
caller-supplied count admission `withdrawals + 1 ≤ 16 * 2^64`. It
increments the withdrawal counter and the credit total by
`amount.toNat` while preserving `pow`, `migrations`, `baseCredits`,
receipts and blocks. Four stability/accounting lemmas expose the exact
shape.

Neither the extension nor its lemmas assert consensus-level scheduling,
a withdrawal index or fork identification; the caller-supplied bounds
match exactly what `Ledger.withdrawal` and `Trace.credit` accept.

Source `spark/eip-history-withdrawal-extension-20260911`. All five
declarations depend only on `propext`, `Classical.choice` and
`Quot.sound`. See the
[bundle](../receipts/direct-history-withdrawal-extension-bundle-20260911.json),
[build](../receipts/direct-history-withdrawal-extension-build-20260911.json),
[axioms](../receipts/direct-history-withdrawal-extension-axioms-20260911.json) and
[source references](../receipts/direct-history-withdrawal-extension-sources-20260911.json).

Independent exact review is now CLEAN: fresh-context reviewer, not the
author; zero blocking, zero advisory. See
[report](../reviews/spark-review-b61009e.md) and
[status receipt](../receipts/direct-history-withdrawal-extension-review-status-20260911.json).
## History PoW-batch extension candidate

`ReferenceHistoryPowBatchExtension.next_pow_batch` completes the
`ProtocolCreditEnvelope.Ledger` constructor coverage: transaction /
system / transfer use `Ledger.conserving`; `next_withdrawal` uses
`Ledger.withdrawal`; this candidate uses `Ledger.pow` on a
`ProtocolCreditEnvelope.CreditBatch` for a full PoW-style batch of
credits.

The extension takes an existing `History deposit exit before`, a
`CreditBatch before amount after` witness (each `.cons` step credits
one recipient by a `UInt256` amount), the aggregate bound
`amount ≤ powMaximum` and a caller-supplied count admission
`pow + 1 ≤ 2^64`. A private helper `extend_trace_batch` inducts on the
batch to thread one `ActualJournalHistory.Trace.credit` step per batch
entry, so the trace's credit count grows by the aggregate. The ledger
is chained via `Ledger.pow`, incrementing the `pow` counter and the
credit total by `amount`. `withdrawals`, `migrations`, `baseCredits`,
receipts and blocks are preserved literally. Four
stability/accounting lemmas expose the exact shape.

Neither the extension nor its lemmas assert consensus-level scheduling
of the PoW batch, do not identify a particular fork and do not name a
canonical batch source; the caller-supplied bounds and the
`CreditBatch` witness match exactly what `Ledger.pow` and
`Trace.credit` accept.

Source `spark/eip-history-pow-batch-extension-20260911`. All five
declarations depend only on `propext`, `Classical.choice` and
`Quot.sound`. See the
[bundle](../receipts/direct-history-pow-batch-extension-bundle-20260911.json),
[build](../receipts/direct-history-pow-batch-extension-build-20260911.json),
[axioms](../receipts/direct-history-pow-batch-extension-axioms-20260911.json) and
[source references](../receipts/direct-history-pow-batch-extension-sources-20260911.json).

Together with `next` / `next_system` / `next_transfer` /
`next_withdrawal`, all four zero-or-nonzero-credit Ledger constructors
that admit a Counts assignment are now reachable through named
lifecycle APIs. The migration constructor remains constrained to
`amount = 0` by `Counts.migration_conserving = 0` and is left uncovered
as a distinct decision.

Independent exact review is now CLEAN: fresh-context reviewer, not the
author; zero blocking, one advisory (the migration-uncovered note
appears in the bundle receipt and commit message but not in this
section — non-blocking). See
[report](../reviews/spark-review-da43958.md) and
[status receipt](../receipts/direct-history-pow-batch-extension-review-status-20260911.json).
## History→funds ceiling bridge candidate

`ReferenceHistoryFundsBridge.worldFunds_lt_ceiling` and
`.worldBalance_lt_ceiling` bridge
`ProtocolCreditEnvelope.funding_budget` and
`GenesisFundingWorld.initial_funds_le` into a single named consumer
lemma keyed on the `ReleaseCandidate.History` structure.

Given any `h : History deposit exit before`, the bridge proves:

* `funding_trace_from_genesis` — a
  `FundingHistory.Trace GenesisFundingWorld.world (h.baseCredits + h.credits) before`
  reifying the accumulated funding history.
* `worldFunds_lt_ceiling` —
  `TransferFunding.worldFunds before < FundedDomain.fundingCeiling`.
* `worldBalance_lt_ceiling` — for every `address`,
  `TransferFunding.worldBalance before address < FundedDomain.fundingCeiling`,
  by composing `TransferFunding.balance_le_funds` with the world bound.

Neither lemma adopts a new premise: they specialize existing conditional
theorems to the concrete `History` fields, so a consumer that already
has an `h` can obtain the funding-ceiling bound directly without
re-threading the ledger, counts and genesis premise at every call site.

Source `spark/eip-history-funds-bridge-20260911`. All three
declarations depend only on `propext`, `Classical.choice` and
`Quot.sound`. See the
[bundle](../receipts/direct-history-funds-bridge-bundle-20260911.json),
[build](../receipts/direct-history-funds-bridge-build-20260911.json),
[axioms](../receipts/direct-history-funds-bridge-axioms-20260911.json) and
[source references](../receipts/direct-history-funds-bridge-sources-20260911.json).

Independent exact review is now CLEAN: fresh-context reviewer, not the
author; zero blocking, zero advisory. See
[report](../reviews/spark-review-afcd3c2.md) and
[status receipt](../receipts/direct-history-funds-bridge-review-status-20260911.json).
## Named invariant aliases from ReleaseCandidate.invariants — candidate

`ReferenceHistoryInvariantsAliases.deposit_success` /
`.exit_success` / `.work_lt` / `.invariant_at` expose each of the four
facts inside `ReleaseCandidate.invariants h` under its own name.
Consumers that need only one facet no longer have to destructure the
four-way conjunction at every call site.

* `deposit_success h : h.deposit.success = true`.
* `exit_success h : h.exit.success = true`.
* `work_lt h : ActualJournalHistory.work h.receipts < 2^128`.
* `invariant_at h kind : JournalInvariant.Invariant kind (work h.receipts) before`.

No new premise; no new axiom. Each alias is a direct projection of the
existing conditional theorem `ReleaseCandidate.invariants`.

Source `spark/eip-history-invariants-aliases-20260911`. All four
declarations depend only on `propext`, `Classical.choice` and
`Quot.sound`. See the
[bundle](../receipts/direct-history-invariants-aliases-bundle-20260911.json),
[build](../receipts/direct-history-invariants-aliases-build-20260911.json),
[axioms](../receipts/direct-history-invariants-aliases-axioms-20260911.json) and
[source references](../receipts/direct-history-invariants-aliases-sources-20260911.json).

Independent exact review is now CLEAN: fresh-context reviewer, not the
author; zero blocking; one advisory noting that the docstring/prose
phrases the deposit/exit facts using `h.deposit.success` where
`deposit` and `exit` are implicit parameters of `History` (the
theorem statements themselves are correct). See
[report](../reviews/spark-review-f356794.md) and
[status receipt](../receipts/direct-history-invariants-aliases-review-status-20260911.json).
## History slots/listed alias candidate

`ReferenceHistorySlotsAlias.slots_nodup` /
`.listed_flatMap` / `.work_lt_from_slots` expose the block-slot
uniqueness field and the receipts-as-flatMap field of any funded
History, plus the derived
`ActualJournalHistory.work_lt_of_blocks` consequence. Consumers can
quote a single named theorem rather than `h.slots` / `h.listed` at
every call site.

* `slots_nodup h : (h.blocks.map slot).Nodup`.
* `listed_flatMap h : h.receipts = h.blocks.flatMap (·.receipts)`.
* `work_lt_from_slots h : ActualJournalHistory.work h.receipts < 2^128`.

No new premise; no new axiom. Each alias is a direct projection.

Source `spark/eip-history-slots-alias-20260911`. All three
declarations depend only on `propext`, `Classical.choice` and
`Quot.sound`. See the
[bundle](../receipts/direct-history-slots-alias-bundle-20260911.json),
[build](../receipts/direct-history-slots-alias-build-20260911.json),
[axioms](../receipts/direct-history-slots-alias-axioms-20260911.json) and
[source references](../receipts/direct-history-slots-alias-sources-20260911.json).

Independent exact review is now CLEAN: fresh-context reviewer, not the
author; zero blocking, zero advisory. See
[report](../reviews/spark-review-6663875.md) and
[status receipt](../receipts/direct-history-slots-alias-review-status-20260911.json).
No proof extension, external message or normative policy has been
promoted. PR20 remains `c3f3c1d`; prepared documentation `7e2ef006`
remains unpushed. The existing structured task ledger remains the sole
roadmap.
## Nested CALL boundary — uniform pool accounting candidate

`ReferenceNestedCallSettlement.finish_pools_success` and `.finish_pools`
extend `ReferenceCallChildBoundary.completes` — which previously stated the
parent-pool accounting only for reverted and exceptional outcomes — with the
success case, then package a single per-outcome equation covering the three
outcomes. `finish_deterministic` records that the `finish` result is
Option-injective in its inputs, which downstream consumers of
`NestedEvents.ThetaAt.identity` can quote when reasoning about nested-call
identity across two derivations of the same Θ result.

On a successful nested CALL the post-finish parent's `pools` equal
`pools s.parent + pools child`: `refill` is the identity because
`failed .success = false`, and `incorporate` uses `repay (absorb ...)`
which preserves `pools` (via `ReferenceChildMeter.repay_accounting`). On
the reverted and exceptional outcomes the parent additionally reclaims the
`stateCost hasValue deadRecipient` new-account charge; the combined equation
reads
`pools post = pools s.parent + pools (settle outcome child) + (if outcome = .success then 0 else stateCost hasValue deadRecipient)`.

This is a corollary of already-audited pieces: `ReferenceCallGrant.split`
and `.charged_split` govern the caller charge and grant split;
`ReferenceMeterRollback.restore` and `ReferenceChildMeter.incorporate_accounting`
fix the child settle and absorb/repay outcomes;
`ReferenceCallChildBoundary.completes` already supplies the paid-child guard
on `committedSpill`. The uniform statement is the missing outcome-case
symmetry — it does not weaken the domain, does not add a new premise and
does not claim identity of any foreign interpreter. Journal-side rollback
preservation and the outer `Coupled` trace remain handled by their existing
modules; no adopted protocol admission or canonical scheduling is implied.

Source `spark/eip-nested-call-identity-20260911`; the module compiles and
all three declarations depend only on `propext`, `Classical.choice` and
`Quot.sound`. See the
[bundle](../receipts/direct-nested-call-settlement-bundle-20260911.json),
[build](../receipts/direct-nested-call-settlement-build-20260911.json),
[axioms](../receipts/direct-nested-call-settlement-axioms-20260911.json) and
[source references](../receipts/direct-nested-call-settlement-sources-20260911.json).

Independent exact review is now CLEAN: fresh-context reviewer, not the
author; zero blocking findings; zero advisory findings. See
[report](../reviews/spark-review-4c4dabe.md) and
[status receipt](../receipts/direct-nested-call-settlement-review-status-20260911.json).
## Block-level gas envelope — capacity candidate

`ReferenceBlockGasCapacity.totalGas_le`, `.totalGas_lt`,
`.totalAppends_le_totalGas` and `.uniform_envelope` extend
`ResourceBounds.total_lt` — which currently bounds only the aggregate
append count by `2^128` under distinct 64-bit slots — with the analogous
bound on the aggregate gas capacity itself, and the pointwise inequality
`totalAppends blocks ≤ totalGas blocks`. Consumers that need one bound
covering both resources can quote `uniform_envelope`.

The proof reuses exactly the same shape as `ResourceBounds.total_lt`: from
`BlockUsage.gas : Fin (2^64)` and slot uniqueness (`length ≤ 2^64`), the
sum is bounded by `2^64 * (2^64 - 1) < 2^128`. `totalAppends_le_totalGas`
is a direct consequence of the per-block `charged : appends ≤ gas.val`
field.

The candidate does not assert that arbitrary Θ histories satisfy these
envelopes: the input `BlockUsage` list must be produced from actual
transaction gas accounting, including nested calls and refunds, before
these bounds become protocol invariants. The bound is a corollary on typed
resources plus finite distinct slots; canonical Ethereum production of the
input list, block-slot admission and per-block gas admission remain
distinct obligations, as also declared in `PROTOCOL-BOUNDARY.md`.

Source `spark/eip-block-capacity-20260911`. All four declarations depend
only on `propext`, `Classical.choice` and `Quot.sound`; `totalGas_le` and
`totalAppends_le_totalGas` use only `propext` and `Quot.sound`. See the
[bundle](../receipts/direct-block-gas-capacity-bundle-20260911.json),
[build](../receipts/direct-block-gas-capacity-build-20260911.json),
[axioms](../receipts/direct-block-gas-capacity-axioms-20260911.json) and
[source references](../receipts/direct-block-gas-capacity-sources-20260911.json).

Independent exact review is now CLEAN: fresh-context reviewer, not the
author; zero blocking findings; zero advisory findings. See
[report](../reviews/spark-review-5c99d47.md) and
[status receipt](../receipts/direct-block-gas-capacity-review-status-20260911.json).
## Canonical-producer hook interfaces — declaration candidate

`ReferenceCanonicalHooks` declares three `structure` bundles for the
canonical Ethereum-semantic raccordements listed in remaining obligation
4: complete admission, deployment, SYSTEM authorization. Each structure
names the *interface* a canonical producer must supply; each is followed
by a small projection theorem exposing the interior fields in the exact
shape the downstream conditional theorems already accept as separate
arguments.

* `CompleteAdmission tx kind sender` bundles `SourceChecks`,
  `TransactionFunding.Admission`, the sender read, the represented
  recipient equality and the `Nonblob` marker. Complete Ethereum admission
  (signature recovery, full blob validation, capacity, type-4
  authorization) remains OPEN and must widen this structure.

* `Deployment deposit exit` bundles the two `FactoryHistoryGuarantees.Inputs`
  records and the linked-worlds condition. Type-valued because `Inputs`
  carries data fields (steps, sender account, factory account); the
  data fields are directly accessible as `.depositInputs` and
  `.exitInputs`, and `.linked_hypothesis` re-exposes the world equation.

* `SystemAuthorization c` bundles the three empty-data zero-value SYSTEM
  guards `ActualJournalHistory.Trace.system` accepts (`caller = sysAddr`,
  `value = 0`, `calldata.size < UInt256.size`). No schedule is adopted;
  no authorization source is identified; no automatic SYSTEM invocation
  is asserted for the pinned reference.

* `AllHooks` combines the three above; `.propHooks` projects the two
  Prop-valued hooks (Complete admission and SYSTEM authorization) and
  the Type-valued `Deployment` is directly accessible as `.deployment`.

The module adds no axiom, adopts no protocol policy, and does not claim
that any canonical producer exists. It makes the exact interface auditable
at a single site so that when canonical Ethereum production becomes
available it hooks into the existing conditional theorems by passing a
witness of the appropriate structure.

Source `spark/eip-canonical-hooks-20260911`. All four theorems depend
only on `propext`, `Classical.choice` and `Quot.sound`. See the
[bundle](../receipts/direct-canonical-hooks-bundle-20260911.json),
[build](../receipts/direct-canonical-hooks-build-20260911.json),
[axioms](../receipts/direct-canonical-hooks-axioms-20260911.json) and
[source references](../receipts/direct-canonical-hooks-sources-20260911.json).

Independent exact review is now CLEAN: fresh-context reviewer, not the
author; zero blocking findings; one advisory noting an interface-widening
choice (CompleteAdmission carries an explicit Admission field even though
ReferenceFullFeeBlockTotal.verified could derive it in-pipeline). See
[report](../reviews/spark-review-b8fa66b.md) and
[status receipt](../receipts/direct-canonical-hooks-review-status-20260911.json).
No proof extension, external message or normative policy has been promoted.
## CreditBatch kill-lines candidate

`ReferenceCreditBatchKillLines` adds nine standalone theorem-style
mutation kill-lines exercising the aggregate accounting inside
`ProtocolCreditEnvelope`: exact-value literals for `powMaximum` and
`withdrawalMaximum`, the `envelope` expansion, zero / one-pow /
one-withdrawal specialisations, and three `CreditBatch` constructor
witnesses (nil identity, single-cons aggregation, and a
two-zero-amount witness). A mutation swapping operand order,
replacing `+` with `*`, dropping a factor, or teleporting worlds
inside `nil` would flip a statement.

The kill-lines do not require instantiating a `Ledger` or a `History`,
so downstream `native_decide` fixtures are unnecessary. All nine
theorems depend only on subsets of `{propext, Classical.choice,
Quot.sound}` (`powMaximum_value` uses no axioms at all).

Source `spark/eip-credit-batch-kill-lines-20260911`. See the
[bundle](../receipts/direct-credit-batch-kill-lines-bundle-20260911.json),
[build](../receipts/direct-credit-batch-kill-lines-build-20260911.json),
[axioms](../receipts/direct-credit-batch-kill-lines-axioms-20260911.json) and
[source references](../receipts/direct-credit-batch-kill-lines-sources-20260911.json).

Independent exact review is now CLEAN: fresh-context reviewer, not the
author; zero blocking, zero advisory. See
[report](../reviews/spark-review-946b3bf.md) and
[status receipt](../receipts/direct-credit-batch-kill-lines-review-status-20260911.json).
PR20 remains `c3f3c1d`; prepared documentation `7e2ef006` remains unpushed.
The existing structured task ledger remains the sole roadmap.

## External candidate — Grok slot/withdrawal extraction

`ProtocolSlotExtraction`, `ProtocolWithdrawalExtraction` and
`Eip8282/Tests/ProtocolSlotWithdrawalMutants` were produced on
`grok/eip-slot-withdrawal-extraction-20260911` by an independent Grok
agent (Cursor Agent, co-authored by Thomas). The contribution spans 40
commits organized into 20 lots totalling ~6,400 insertions across the
three files, with 20 per-lot receipts under
`audit/receipts/direct-grok-slot-withdrawal-extraction-lean-*.json`.

Each receipt is classified `compiled_additive_extraction_not_adoption_not_guarantee_closure`
and pins file SHA-256, spec-body SHA-256 (phase0/gloas/electra beacon
chain, fork-choice, fork.md, Amsterdam fork.py and state_tracker.py),
base commit and toolchain. No parallel framework is introduced: the
extraction consumes the existing `total_count` / `items_bounded` / slot
`Nodup` from the base modules. No file outside the stated scope is
modified. No adoption of a specific normative fork is claimed; the
extraction is arithmetic transcription of the archived Python.

Independent exact review on `c39bd18` is CLEAN
(fresh-context reviewer, not the author): zero blocking, zero advisory.
See [report](../reviews/spark-review-c39bd18.md) and
[status receipt](../receipts/direct-grok-slot-withdrawal-review-status-20260911.json).
Local promotion is recorded on `spark/eip-grok-integration-20260911`,
which fast-forwards from the grok HEAD and adds only the review-status
receipt, the review report and this DIRECT-CLOSURE.md entry. The grok
branch itself is untouched.

`make check` on `c39bd18` passes at 3608 jobs, with the caveat that
`Eip8282.Tests.ProtocolSlotWithdrawalMutants` is not included in
`make check`'s explicit test target list; the mutants file compiles
correctly on demand via `lake build` (1221 jobs, all axioms in
`{propext, Classical.choice, Quot.sound}`). Adding the mutants file to
`make check`'s explicit test list is a separate integration decision
left to Thomas. PR20 remains `c3f3c1d`; prepared documentation
`7e2ef006` remains unpushed. No external message or normative policy
has been promoted.

## External candidate — Grok slot/withdrawal extraction (through lot 26)

`ProtocolSlotExtraction`, `ProtocolWithdrawalExtraction` and
`Eip8282/Tests/ProtocolSlotWithdrawalMutants` are produced on
`grok/eip-slot-withdrawal-extraction-20260911` by an independent Grok
agent (Cursor Agent, co-authored by Thomas). Through lot 26, the
contribution spans 52 commits (26 lots) totalling ~8,600 insertions
across the three files, with 26 per-lot receipts under
`audit/receipts/direct-grok-slot-withdrawal-extraction-lean-*.json`.

Each receipt is classified `compiled_additive_extraction_not_adoption_not_guarantee_closure`
and pins file SHA-256, spec-body SHA-256 (phase0/gloas/electra beacon
chain, fork-choice, fork.md, Amsterdam fork.py and state_tracker.py),
base commit and toolchain. No parallel framework is introduced: the
extraction consumes the existing `Ledger` / `Counts` / `Dispatch` /
`applyTagged` / `ElCredit` framework. No file outside the stated scope
is modified. No adoption of a specific normative fork is claimed.

Independent exact review on the head `09a15ec` is CLEAN
(fresh-context reviewer, not the author): zero blocking, zero advisory
on the whole set through lot 26. The earlier CLEAN review on `c39bd18`
(lots 1-20) is preserved as
[report](../reviews/spark-review-c39bd18.md); the delta review on
`c39bd18..09a15ec` (lots 21-26) is
[report](../reviews/spark-review-09a15ec.md); status receipts under
[receipts/direct-grok-slot-withdrawal-review-status-20260911.json](../receipts/direct-grok-slot-withdrawal-review-status-20260911.json)
and [delta receipt](../receipts/direct-grok-slot-withdrawal-delta-review-status-20260911.json).

Local promotion is recorded on `spark/eip-grok-integration-delta-20260911`,
which fast-forwards from grok HEAD `09a15ec` and adds only this delta
review-status receipt, the delta review report and this
DIRECT-CLOSURE.md entry. The grok branch itself is untouched.

`lake build` on the delta modules passes at 1221 jobs with all listed
axioms in `{propext, Classical.choice, Quot.sound}`; `make check`
inclusion of `Eip8282.Tests.ProtocolSlotWithdrawalMutants` in the
explicit test list remains a separate integration decision left to
Thomas. PR20 remains `c3f3c1d`; prepared documentation `7e2ef006`
remains unpushed. No external message or normative policy has been
promoted.

## External candidate — Grok slot/withdrawal extraction (through lot 28)

`ProtocolSlotExtraction`, `ProtocolWithdrawalExtraction` and
`Eip8282/Tests/ProtocolSlotWithdrawalMutants` are produced on
`grok/eip-slot-withdrawal-extraction-20260911` by an independent Grok
agent (Cursor Agent, co-authored by Thomas). Through lot 28, the
contribution spans 56 commits (28 lots) totalling ~9,600 insertions
across the three files, with 28 per-lot receipts under
`audit/receipts/direct-grok-slot-withdrawal-extraction-lean-*.json`.

Each receipt is classified `compiled_additive_extraction_not_adoption_not_guarantee_closure`
and pins file SHA-256, spec-body SHA-256 (phase0/gloas/electra beacon
chain, fork-choice, fork.md, Amsterdam fork.py and state_tracker.py),
base commit and toolchain. No parallel framework is introduced: the
extraction consumes the existing `Ledger` / `Counts` / `Dispatch` /
`applyTagged` / `ElCredit` framework. No file outside the stated scope
is modified. No adoption of a specific normative fork is claimed.

Independent exact review of the delta `09a15ec..8a25e44` (lots 27-28,
4 commits, ~1,000 insertions) is CLEAN with zero blocking and zero
advisory findings. See
[report](../reviews/spark-review-8a25e44.md) and
[status receipt](../receipts/direct-grok-slot-withdrawal-delta2-review-status-20260911.json).
Earlier CLEAN reviews on `c39bd18` (lots 1-20) and the delta
`c39bd18..09a15ec` (lots 21-26) remain in effect via their own review
files. Local promotion is recorded on
`spark/eip-grok-integration-delta2-20260911`, which fast-forwards from
grok HEAD `8a25e44` and adds only this delta review-status receipt,
the delta review report and this DIRECT-CLOSURE.md entry.

`lake build` on the delta modules passes at 1221 jobs with all listed
axioms in `{propext, Classical.choice, Quot.sound}`; `make check`
inclusion of `Eip8282.Tests.ProtocolSlotWithdrawalMutants` in the
explicit test list remains a separate integration decision left to
Thomas. PR20 remains `c3f3c1d`; prepared documentation `7e2ef006`
remains unpushed. No external message or normative policy has been
promoted.

## External candidate — Grok slot/withdrawal extraction (through lot 32)

`ProtocolSlotExtraction`, `ProtocolWithdrawalExtraction` and
`Eip8282/Tests/ProtocolSlotWithdrawalMutants` are produced on
`grok/eip-slot-withdrawal-extraction-20260911 = 15d04df` by an
independent Grok agent (Cursor Agent, co-authored by Thomas). Through
lot 32, the contribution spans 64 commits (32 lots) totalling ~10,900
insertions across the three files, with 32 per-lot receipts.

Each receipt is classified `compiled_additive_extraction_not_adoption_not_guarantee_closure`
and pins file SHA-256, spec-body SHA-256, base commit and toolchain.
No parallel framework is introduced. No file outside the stated scope
is modified.

Independent exact review of the delta `8a25e44..15d04df` (lots 29-32,
8 commits, ~1300 insertions) is CLEAN with zero blocking and zero
advisory findings. See
[report](../reviews/spark-review-15d04df.md) and
[status receipt](../receipts/direct-grok-slot-withdrawal-delta3-review-status-20260911.json).
Earlier CLEAN reviews on `c39bd18` (lots 1-20), `09a15ec` (lots 21-26)
and `8a25e44` (lots 27-28) remain in effect via their own review
files. Local promotion recorded on
`spark/eip-grok-integration-delta3-20260911`, fast-forwarding from
grok HEAD `15d04df`; grok branch untouched.

`lake build` on the delta modules passes at 1221 jobs, all axioms
in `{propext, Classical.choice, Quot.sound}`. Inclusion of
`Eip8282.Tests.ProtocolSlotWithdrawalMutants` in the explicit test
target remains a separate integration decision left to Thomas.
PR20 remains `c3f3c1d`; prepared documentation `7e2ef006` remains
unpushed. No external message or normative policy has been promoted.

## External candidate — Grok slot/withdrawal extraction (through lot 34)

`ProtocolSlotExtraction`, `ProtocolWithdrawalExtraction` and
`Eip8282/Tests/ProtocolSlotWithdrawalMutants` are produced on
`grok/eip-slot-withdrawal-extraction-20260911 = ee5cdc4` by an
independent Grok agent. Through lot 34, the contribution spans 68
commits (34 lots) totalling ~11,700 insertions across the three
files, with 34 per-lot receipts. Each receipt pins file/spec SHA-256,
base commit and toolchain; no parallel framework; no file outside
scope; no adoption of a specific normative fork.

Independent exact review of the delta `15d04df..ee5cdc4` (lots 33-34,
4 commits, ~750 insertions) is CLEAN with zero blocking and zero
advisory findings. See
[report](../reviews/spark-review-ee5cdc4.md) and
[status receipt](../receipts/direct-grok-slot-withdrawal-delta4-review-status-20260911.json).
Earlier CLEAN reviews on `c39bd18` / `09a15ec` / `8a25e44` /
`15d04df` remain in effect via their own review files. Local
promotion recorded on `spark/eip-grok-integration-delta4-20260911`,
fast-forwarding from grok HEAD `ee5cdc4`; grok branch untouched.

`lake build` on the delta modules passes at 1221 jobs, all axioms in
`{propext, Classical.choice, Quot.sound}`. Inclusion of
`Eip8282.Tests.ProtocolSlotWithdrawalMutants` in the `make check`
test target list remains a separate integration decision left to
Thomas. PR20 remains `c3f3c1d`; prepared documentation `7e2ef006`
remains unpushed. No external message or normative policy has been
promoted.

## External candidate — Grok slot/withdrawal extraction (through lot 35)

`ProtocolSlotExtraction`, `ProtocolWithdrawalExtraction` and
`Eip8282/Tests/ProtocolSlotWithdrawalMutants` are produced on
`grok/eip-slot-withdrawal-extraction-20260911 = 4499b78` by an
independent Grok agent. Through lot 35, the contribution spans 70
commits (35 lots) totalling ~11,900 insertions across the three
files.

Lot 35 contributes 8 new theorems and 5 new mutants demonstrating the
empty-registry Lean `%0` semantic discrepancy: Lean's convention
`Nat.mod _ 0 = id` differs from Python's `ZeroDivisionError`; the
composer short-circuits via `validatorsSweepLimit 0 = 0` so the
divergent `%0` cursor step is never reached inside the composer.
Python behaviour retained in `named_hypotheses_still_open`.

Independent exact review of the delta `ee5cdc4..4499b78` (lot 35, 2
commits, ~230 insertions) is CLEAN with zero blocking and zero
advisory findings. See
[report](../reviews/spark-review-4499b78.md) and
[status receipt](../receipts/direct-grok-slot-withdrawal-delta5-review-status-20260911.json).
Earlier CLEAN reviews on `c39bd18` / `09a15ec` / `8a25e44` /
`15d04df` / `ee5cdc4` remain in effect. Local promotion on
`spark/eip-grok-integration-delta5-20260911`, fast-forwarding from
grok HEAD `4499b78`; grok branch untouched.

`lake build` on the delta modules passes (1221 jobs). PR20 remains
`c3f3c1d`; prepared documentation `7e2ef006` remains unpushed. No
external message or normative policy has been promoted.

## External candidate — Grok slot/withdrawal extraction (through lot 36)

`ProtocolSlotExtraction`, `ProtocolWithdrawalExtraction` and
`Eip8282/Tests/ProtocolSlotWithdrawalMutants` are produced on
`grok/eip-slot-withdrawal-extraction-20260911 = 721be31` by an
independent Grok agent. Through lot 36, the contribution spans 72
commits (36 lots) totalling ~12,200 insertions across the three
files.

Lot 36 introduces a `gweiWrapSub` distinct definition and proves that
`balanceAfterWithdrawals` (which continues to use Lean's `Nat.sub`
saturating semantics) agrees with the Gwei-wrap semantics **only**
under a `BalanceAfterFits` premise; it refutes the equivalence in the
generic case (`gweiWrapSub_ne_sub_of_gt`, `apply_ne_wrap_of_gt`).
`apply_eq_balanceAfter_sat` establishes the unconditional fold
identity independent of the fits premise. No convention is adopted as
protocol semantics.

Independent exact review of the delta `4499b78..721be31` (lot 36, 2
commits, ~320 insertions) is CLEAN with zero blocking and zero
advisory findings. See
[report](../reviews/spark-review-721be31.md) and
[status receipt](../receipts/direct-grok-slot-withdrawal-delta6-review-status-20260911.json).
Earlier CLEAN reviews remain in effect. Local promotion on
`spark/eip-grok-integration-delta6-20260911`, fast-forwarding from
grok HEAD `721be31`; grok branch untouched.

`lake build` on the delta modules passes (1221 jobs). PR20 remains
`c3f3c1d`; prepared documentation `7e2ef006` remains unpushed. No
external message or normative policy has been promoted.

## External candidate — Grok slot/withdrawal extraction (through lot 38)

`ProtocolSlotExtraction`, `ProtocolWithdrawalExtraction` and
`Eip8282/Tests/ProtocolSlotWithdrawalMutants` are produced on
`grok/eip-slot-withdrawal-extraction-20260911 = 4c9dafc` by an
independent Grok agent. Through lot 38, the contribution spans 76
commits (38 lots) totalling ~12,800 insertions across the three
files.

Lots 37-38 add two new definitions (`withdrawalIndexWrap`,
`toValidatorIndexU64`) plus ~24 theorems and 12 mutants demonstrating
the Python-wrap vs Lean-successor / unbounded-`|||` discrepancies
via explicit disagreement lemmas (`toValidatorIndex_two_pow_ne_u64`,
`updateNext_last_u64_ne_wrap`, `indexSeq_last_u64_ne_wrap_list`),
without adopting either convention. `Fits` structures remain the
named gap.

Independent exact review of the delta `721be31..4c9dafc` (lots
37-38, 4 commits, ~560 insertions) is CLEAN with zero blocking and
zero advisory findings. See
[report](../reviews/spark-review-4c9dafc.md) and
[status receipt](../receipts/direct-grok-slot-withdrawal-delta7-review-status-20260911.json).
Earlier CLEAN reviews remain in effect. Local promotion on
`spark/eip-grok-integration-delta7-20260911`, fast-forwarding from
grok HEAD `4c9dafc`; grok branch untouched.
## External candidate — Grok slot/withdrawal extraction (through lot 39)

`ProtocolSlotExtraction`, `ProtocolWithdrawalExtraction` and
`Eip8282/Tests/ProtocolSlotWithdrawalMutants` are produced on
`grok/eip-slot-withdrawal-extraction-20260911 = 7147aec` by an
independent Grok agent. Through lot 39, the contribution spans 78
commits (39 lots) totalling ~13,100 insertions.

Lot 39 introduces `builderFlagNotU64` and `toBuilderIndexU64` as named
companions and proves agreement on flag-clear `Uint64` inputs plus
explicit disagreement at `2^64`. Python semantics are demonstrated,
not adopted as the Lean definition.

Independent exact review of the delta `4c9dafc..7147aec` (lot 39, 2
commits, ~275 insertions) is CLEAN with zero blocking and zero
advisory findings. See
[report](../reviews/spark-review-7147aec.md) and
[status receipt](../receipts/direct-grok-slot-withdrawal-delta8-review-status-20260911.json).
Earlier CLEAN reviews remain in effect. Local promotion on
`spark/eip-grok-integration-delta8-20260911`, fast-forwarding from
grok HEAD `7147aec`; grok branch untouched.

`lake build` on the delta modules passes (1221 jobs). PR20 remains
`c3f3c1d`; prepared documentation `7e2ef006` remains unpushed.
## External candidate — Grok slot/withdrawal extraction (through lot 40)

Grok HEAD `ec15c4b` reaches 40 lots (80 commits, ~13,300 insertions).
Lot 40 proves the XOR-equals-subtract identity on set-bit-40 inputs
inside the `v < 2^64` agreement lemma, while preserving the unbounded
wrap kill-line `toBuilderIndex_two_pow_ne_u64` at `v = 2^64`.

Independent exact review of the delta `7147aec..ec15c4b` (lot 40, 2
commits, ~235 insertions) is CLEAN with zero blocking and zero
advisory findings. See
[report](../reviews/spark-review-ec15c4b.md) and
[status receipt](../receipts/direct-grok-slot-withdrawal-delta9-review-status-20260911.json).
Earlier CLEAN reviews remain in effect. Local promotion on
`spark/eip-grok-integration-delta9-20260911`, fast-forwarding from
grok HEAD `ec15c4b`; grok branch untouched.

`lake build` on the delta modules passes (1221 jobs).
## External candidate — Grok slot/withdrawal extraction (through lot 42)

Grok HEAD `94d4178` reaches 42 lots (84 commits, ~13,800 insertions).
Lots 41-42 are the first delta to touch `ProtocolSlotExtraction.lean`
substantially (211 new lines) rather than the withdrawal file. Two
new semantic discrepancies are demonstrated:

* Lot 41: `compute_time_at_slot` Uint64 wrap outside `2^60` (Nat sum
  ≠ Uint64 wrap at `2^61`, gated in Lean via `TimeFitsU64`).
* Lot 42: `validate_header` independence of `slot_number` (with an
  explicit `validate_header_is_not_slot_nodup` disagreement lemma).

Independent exact review of the delta `ec15c4b..94d4178` (lots 41-42,
4 commits, ~520 insertions) is CLEAN with zero blocking and zero
advisory findings. See
[report](../reviews/spark-review-94d4178.md) and
[status receipt](../receipts/direct-grok-slot-withdrawal-delta10-review-status-20260911.json).
Local promotion on `spark/eip-grok-integration-delta10-20260911`,
fast-forwarding from grok HEAD `94d4178`; grok branch untouched.

`lake build` on the delta modules passes (1221 jobs). PR20 remains
`c3f3c1d`; prepared documentation `7e2ef006` remains unpushed.

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
[bundle](../receipts/direct-system-block-bundle-20260911.json),
[build](../receipts/direct-system-block-build-20260911.json),
[axioms](../receipts/direct-system-block-axioms-20260911.json) and
[rechecked complete source provenance](../receipts/direct-system-block-sources-20260911.json).
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

Independent exact review on the SYSTEM block pair is now CLEAN as part of the
same [combined report](../reviews/spark-review-f2ab5eb.md) noted above (fresh
context, not the author). The earlier
[review-status receipt](../receipts/direct-system-block-review-status-20260911.json)
records the prior quota outage. PR20 remains `c3f3c1d`, and prepared
documentation `7e2ef006` remains unpushed. No unreviewed extension,
external message or normative policy has been promoted.

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
[bundle](../receipts/direct-source-fee-finalization-bundle-20260910.json),
[build](../receipts/direct-source-fee-finalization-build-20260910.json),
[axioms](../receipts/direct-source-fee-finalization-axioms-20260910.json) and
[source excerpts](../receipts/direct-source-fee-finalization-sources-20260910.json).
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

Independent exact review is now CLEAN on both `20783d3` (full gas settlement)
and `eec2142` (source fee finalization): fresh-context reviewer, not the
author; zero blocking findings; one advisory documenting an additive
re-export in `ReferenceOutcomeGas.lean` at the later commit `5cd0fe5` that is
semantically neutral. See [report](../reviews/spark-review-20783d3.md). Earlier
[review-status receipts](../receipts/direct-source-fee-finalization-review-status-20260910.json)
retain the pre-review evidence chain. PR20 remains `c3f3c1d`; prepared
documentation `7e2ef006` remains unpushed. Checked SYSTEM execution,
successful source payment, the ordered SYSTEM block-parent/world composition
and ordinary transaction block incorporation are now composed above.
Next-transaction history remains open. The existing structured task ledger
remains the sole roadmap.

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
[build](../receipts/direct-allocated-total-build-20260910.json) and
[bundle](../receipts/direct-allocated-total-bundle-20260910.json).
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
[bundle](../receipts/direct-dispatch-allocation-bundle-20260910.json).
Source `b8de01363430e093ef3211b162e11cec7d5adb85` passes frozen `make check`,
thirteen production axiom checks and four mutations; see the
[build](../receipts/direct-dispatch-allocation-build-20260910.json).
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
[build](../receipts/direct-initial-access-build-20260910.json) and
[bundle](../receipts/direct-initial-access-bundle-20260910.json).
Independent review remains unavailable; this contribution is not promoted.
The next consumer connection is actual dispatch preparation and allocated gas.

## Source prepayment from the before-transaction journal — candidate

[The prepayment candidate](../receipts/direct-source-prepayment-bundle-20260910.json)
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
[build](../receipts/direct-source-prepayment-build-20260910.json).
Independent review is unavailable; no promotion or PR update is made. The
mutations cover nonce-before-fee ordering and retained nonce effects on fee
underflow, using explicitly injected finite journals rather than canonical
reachability claims. Every new helper is consumed by these complete-call APIs.

## Before-transaction history at the actual checkpoint — candidate

The [checkpoint composition](../receipts/direct-checkpoint-bundle-20260910.json)
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
[build](../receipts/direct-checkpoint-build-20260910.json). Independent exact
review is unavailable and there is no promotion. Source checkpoint representation is
still an input to those APIs; the nonblob prepayment extension above derives it.
The old admission interface does not establish Amsterdam blob tariff equality,
source frame/gas identity or type4 semantics. These boundaries are unchanged.

## Same-receipt source balances candidate — not promoted

The current proof workspace strengthens the source-funding candidate with
[16 balance/composition exports](../receipts/direct-source-balance-bundle-20260910.json).
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
[build](../receipts/direct-source-balance-build-20260910.json).
[Independent exact review is unavailable](../receipts/direct-source-balance-review-status-20260910.json);
this candidate has not entered the reviewed branch or PR.
The publication PR is still #20 at `c3f3c1d644d9e641585dfc5143100123729fd0e4`.
A separate refresh at `7e2ef006c0e3bfafaf98f40eb9768560ad03fe16` contains only the
reviewed snapshot `12806f9` and current publication documents. Its 433 proof/build
inputs match the prior verified source; exact document review is unavailable
because the existing reviewer exhausted quota. It has not been pushed.

## Funded source entry candidate — final review pending

Source `8e92a8bc783862fec9ef602151743fff66eb43a6` on the separate
`codex/source-funding-candidate-20260910` branch adds
[the source funding candidate](../receipts/direct-source-funding-bundle-20260910.json).
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
exports and the source funding mutations; see [build](../receipts/direct-source-funding-build-20260910.json).
Component source review was clean, but the
existing reviewer exhausted its quota before final exact-commit review; see
[review status](../receipts/direct-source-funding-review-status-20260910.json).
This candidate is not promoted to the independently reviewed release. Work on
independent proof obligations continues without new worker jobs or spending.

## Guarded source transfer and pre-transfer rollback

Proof commit `f9c7953771129f05c4b1b4c72f12f5dbc588c425` adds
[the source transfer bundle](../receipts/direct-source-transfer-bundle-20260910.json).
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
[build](../receipts/direct-source-transfer-build-20260910.json) and
[review](../receipts/direct-source-transfer-review-20260910.json).
Source transfer success, actual account payload/world representation,
code-address/current-target/should-transfer construction, source LOG3/context
binding, full Python frame identity and canonical admission are still open.
These additions are outside the unchanged timed release.

## Derived source failure classification

Proof commit `af027e8bdfefe1f0bea92737dd3b0862c35dd3d1` adds the
[derived failure bundle](../receipts/direct-derived-failure-bundle-20260910.json).
The same failed account-aware evaluation now derives its final calldata/PC
conversion bounds and excludes the owner assertion using its nonempty code
fetch. `ReferenceHistoryFailure.settled` obtains the old replay owner from the
initialized history, then proves projected storage rollback, zero parent logs,
empty exceptional output and the ordered meter settlement. No independent
`caught` classification or old `HasOwner` is supplied by this history consumer.

All 14 new exports compile with standard Lean axioms; the exact isolated
`make check` passes, including existing mutation checks. Evidence:
[build](../receipts/direct-derived-failure-build-20260910.json) and
[review](../receipts/direct-derived-failure-review-20260910.json).
Actual source entry construction, code-address/current-target identity,
account/value-transfer state and full saved snapshot binding remain open.
In particular, source `process_call` transfers value before opcodes and may
emit a SYSTEM-address LOG3; `modify_state` may delete a newly empty account.
The opcode projection does not silently discard or justify these source effects.
The frozen timed release under `audit/release/` is unchanged.

## Post-release source account composition

The frozen release remains `58c2a60` (proofs `d46fa07`). Work continues on
`codex/source-account-composition-20260910` toward Ethereum applicability.
The [account bundle](../receipts/direct-account-bundle-20260910.json) adds literal
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
([build](../receipts/direct-account-build-20260910.json),
[review](../receipts/direct-account-source-review-20260910.json)). No released claim or EIP/protocol policy is changed.

