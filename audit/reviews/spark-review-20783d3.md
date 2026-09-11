# Independent review — gas settlement (20783d3) and fee finalization (eec2142)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commits: 20783d3, eec2142
Head: 681d186 (branch codex/source-ordinary-block-candidate-20260911)
Started at: 2026-09-11T10:36:27Z

## Scope items reviewed

Gas settlement (20783d3):
- Verify fresh transaction overlay is preserved through prepayment/probe/value entry, with arbitrary parent chain storage. — OK (`ReferenceFreshStorageEntry.{enter,probe,allocated}` derives `.storage = emptyTx` at the runtime entry from the initial `fresh` overlay; the `parent : ReferenceStorageView.Parent` remains an arbitrary chain).
- Review actual ordered source state/refund charges, telescoping potentials, finite-trace bound and exact U256 conversion. — OK (`ReferenceCheckedRefund.source_balance` telescopes per-event potentials over the actual `ReferenceSourceReplayTrace.Run`; `delta_upper` yields the per-event 21616 cap; `ReferenceRefundCounter.fresh_prefix/terminal` combine with the runtime length bound to prove `refund < UInt256.size` and expose the exact `UInt256.ofNat` round-trip).
- Check REVERT and exceptional restored meters include actual partial-payment metadata and proper source reset. — OK (`ReferenceMeterMetadata.dispatch` preserves baseline/committedSpill through every handler, including partial errors; `ReferenceOutcomeGas.failed` uses this to derive `Valid` after `ReferenceChildMeter.settle .exceptional`; `ReferenceOutcomeGas.terminal` handles the REVERT branch via `restore`).
- Check FullGasTotal derives same actual receipt validity without desired postcondition premise. — OK (see Findings; the only new premise vs. `ReferenceFullLogTotal.verified` is the initial-state `fresh : before.storage = ReferenceRuntimeStateBalance.emptyTx`; no `Valid`, `returned`, `Facts` etc. appears in the hypotheses).
- Gas numbers are not final fee credits, canonical history or complete Ethereum applicability. — OK (`Facts` conclusion is purely gas arithmetic; no block/fee/canonical claim in the theorem).

Fee finalization (eec2142):
- Actual receipt is shared by all3, logs, gas, account rollback and fee journal; no final state premise. — OK (`ReferenceFullFeeTotal.verified` reuses the same `receipt` produced by `ReferenceFullGasTotal.verified`; the fee `Result` is a fresh conclusion driven by that receipt).
- Derivation of prepayment budget and original history total; no source gas/synthetic replay equality. — OK (`ReferenceSourceFeeFinalization.actual` derives the `payout` overflow guard from `TransactionFunding.checkpoint_debit`, `FundingHistory.trace_funds`, `LedgerCreditSafety.genesis_budget`; no synthetic-old-gas equation is asserted).
- Literal source priority subtraction then ordered conversions/credits; zero cleanup and alias/partial errors. — OK (`ReferenceSourceFeeDisbursement.run` matches fork.py:970-1006: refund amount, priority subtraction, refund U256 check, payer credit, tip U256 check, beneficiary credit; the four mutation tests documented in the bundle confirm the ordering).
- Protected nonempty code hash and storage preservation; all balance equations and burn partition. — OK (`ReferenceSourceFeeDisbursement.protected_storage` proves storage identity for accounts with nonempty code hash across all partial-error branches; `ReferenceSourceFeeAmounts.partition/actual` proves the refund+tip+burn = gasLimit*price exact partition).
- No canonical history, full account payload/world correspondence or source block incorporation claimed. — OK (`Result` gives balances up to `.toNat` addition equations and protected-storage equality on the settled journal, not full-account payload equality; no block-incorporation predicate appears).

## Findings

No BLOCKING findings. No ADVISORY findings that alter the verdict.

The following non-blocking observations are recorded for transparency:

1. ADVISORY — `Eip8282/Audit/Integrator/ReferenceOutcomeGas.lean` at HEAD differs from its bundle SHA-256 because a later commit (5cd0fe5, "compose checked SYSTEM execution and local output settlement") added a public re-export `theorem terminal_paid ... := terminal_payment actual` (lines 75-79). The change is purely additive (a delegating alias to the pre-existing private helper `terminal_payment`) and does not alter any theorem promised by the bundle. The bundle SHA `dd85b31...` is exactly reproduced when re-hashing `git show 20783d3:Eip8282/Audit/Integrator/ReferenceOutcomeGas.lean`. Not a defect of commits 20783d3/eec2142 themselves.

## Axiom audit (production modules)

For commits 20783d3 and eec2142 the two `direct-*-axioms-*.json` receipts list every production theorem and, for each, the axioms it depends on. All 26 gas-settlement production entries and 15 fee-finalization production entries (plus their 2+4 mutation tests) are restricted to the standard triple `{propext, Classical.choice, Quot.sound}` (some derive with only `propext`, or `propext + Quot.sound`, i.e. strict subsets). No project-declared `axiom`, `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`, or `native_decide` axiom appears.

Independent grep across all 14 modules confirms no `axiom `/`sorry`/`admit` declarations in source:

- ReferenceCheckedRefund.lean — clean
- ReferenceCheckedStateGas.lean — clean
- ReferenceFreshStorageEntry.lean — clean
- ReferenceFullGasTotal.lean — clean
- ReferenceMeterMetadata.lean — clean
- ReferenceOutcomeGas.lean — clean (the additional `terminal_paid` is a `:=`-defined delegating theorem, not an axiom)
- ReferenceRefundCounter.lean — clean
- ReferenceTransactionSettlement.lean — clean
- ReferenceSourceFeeCredit.lean — clean
- ReferenceSourceFeeDisbursement.lean — clean
- ReferenceSourceFeeAmounts.lean — clean
- ReferenceSettledAccountJournal.lean — clean
- ReferenceSourceFeeFinalization.lean — clean
- ReferenceFullFeeTotal.lean — clean

## Bundle hash verification

Computed via `git show <commit>:<path> | sha256sum`.

Gas settlement bundle (`direct-full-gas-settlement-bundle-20260910.json`) vs. `git show 20783d3:...`:

| module | bundle SHA-256 | computed at 20783d3 | match |
|---|---|---|---|
| ReferenceCheckedStateGas | 96ddbc5e...651aa9 | 96ddbc5e...651aa9 | yes |
| ReferenceFreshStorageEntry | 3bfb3df2...24bcf | 3bfb3df2...24bcf | yes |
| ReferenceCheckedRefund | 36e8de11...a0a9181 | 36e8de11...a0a9181 | yes |
| ReferenceRefundCounter | 0b703026...46d5f291 | 0b703026...46d5f291 | yes |
| ReferenceMeterMetadata | 9d91e217...3a2755a | 9d91e217...3a2755a | yes |
| ReferenceOutcomeGas | dd85b314...2926ca0 | dd85b314...2926ca0 | yes |
| ReferenceTransactionSettlement | 6fdde09c...4880b7ceb14 | 6fdde09c...4880b7ceb14 | yes |
| ReferenceFullGasTotal | b5bc7406...ead6cc279c7 | b5bc7406...ead6cc279c7 | yes |

Fee finalization bundle (`direct-source-fee-finalization-bundle-20260910.json`) vs. `git show eec2142:...`:

| module | bundle SHA-256 | computed at eec2142 | match |
|---|---|---|---|
| ReferenceSourceFeeCredit | a76d9c75...d208f396 | a76d9c75...d208f396 | yes |
| ReferenceSourceFeeDisbursement | 62711c47...ced60bdc53 | 62711c47...ced60bdc53 | yes |
| ReferenceSourceFeeAmounts | 7073273f...543928c71d | 7073273f...543928c71d | yes |
| ReferenceSettledAccountJournal | 45b0efb8...b90bb205bb | 45b0efb8...b90bb205bb | yes |
| ReferenceSourceFeeFinalization | f0df5fd5...a6699a16 | f0df5fd5...a6699a16 | yes |
| ReferenceFullFeeTotal | 652c5863...21de59a37 | 652c5863...21de59a37 | yes |

At the current HEAD (681d186) 13/14 files still hash to the bundle values; ReferenceOutcomeGas.lean was extended by 5cd0fe5 with the additive `terminal_paid` re-export (see advisory finding above). All other files are byte-identical to their frozen bundle SHAs at HEAD.

## Additional structural checks

- Statement of `ReferenceFullGasTotal.verified`: hypotheses are `kind, tx, signature, history, checks, found, recipient, nonblob, costs, emptyHash, accountsParent, before, codeParent, parent, loaded, balances, slots, fresh`. `fresh : before.storage = ReferenceRuntimeStateBalance.emptyTx` is an initial-storage overlay condition; every other hypothesis is identical to `ReferenceFullLogTotal.verified` (transitively existing since 4227772). No `Valid`, `Facts`, or `Result` premise smuggled. Conclusion consists of `Started ∧ ∃ ..., FullLogTotal-conjuncts ∧ ∃ receipt, settle = .returned receipt ∧ ReferenceTransactionSettlement.Facts ...`. `Facts` is a purely arithmetic gas-quantity structure; no fee/balance/block claim.
- Statement of `ReferenceFullFeeTotal.verified`: identical hypothesis set to `ReferenceFullGasTotal.verified`. The conclusion adds a single new conjunct: `ReferenceSourceFeeFinalization.Result ...`. `Result` fields (`success`, `balances`, `protected_storage`, `fee_partition`) are conclusions about the ordered disbursement over the same `finalAccounts`+`receipt`; the `Result.success` field is derived from `funded.1`, not accepted as a hypothesis.
- `ReferenceSourceFeeFinalization.actual` hypotheses: only `kind, tx, history, checks, found, nonblob, emptyHash, accountsParent, before, codeParent, parent, loaded, related, execution, receipt, facts`. The `receipt` is an arbitrary `Receipt`; the `facts : ReferenceTransactionSettlement.Facts ...` and `execution : ReferenceAllocatedExecution.run ... = some ...` are the two composition witnesses supplied by `ReferenceFullGasTotal.verified` at the call site in `ReferenceFullFeeTotal.verified`. No "final balance affords" or "disbursement succeeds" premise.
- Python cross-check (source excerpts vs. Lean projection):
  - `settle_transaction_gas` (fork.py:1174-1239 via gas.py excerpts) is transcribed literally in `ReferenceTransactionGas.settle`: `beforeRefund = txGas - gasLeft - stateLeft`; `gasRefund = min (beforeRefund/5) refund.toNat`; `gasUsed = max (beforeRefund - gasRefund) calldataFloor`; `stateUsed = max(0, netState).toNat`; `executionUsed = max (beforeRefund - stateUsed) calldataFloor`; `gasLeft' = txGas - gasUsed`. Ordering, refund 20% cap, and state clamp match the pinned Python one-for-one.
  - `disburse_gas_fees` (fork.py:970-1006) is transcribed in `ReferenceSourceFeeDisbursement.run`: refund amount = `gasLeft*price`; priority-fee subtraction guarded by `base ≤ price`; tip amount = `gasUsed*(price-base)`; then U256 conversion + payer credit; then U256 conversion + beneficiary credit; zero credits not skipped; equal payer/beneficiary supported. Mutation tests `alias_accumulates`, `second_overflow_retains_refund`, `tip_conversion_after_refund`, `zero_credit_cleans_empty` (bundle-recorded) pin down the ordering, error-retention and empty-account cleanup semantics.
  - `TransactionState` fresh default (state_tracker.py:68-92) has empty storage_writes, storage_reads, created_accounts, code_writes, transient_storage; this exactly matches `ReferenceRuntimeStateBalance.emptyTx` used as the `fresh` premise.
- No 256-iteration ceiling appears; the only numeric bound is `intrinsic ≤ 16777216` (the pinned execution-gas cap consistent with EIP-7825/-analogues), used exclusively to derive `21616*length ≤ 21616*16777216 < UInt256.size` for the refund counter fit.
- No canonical-history / block-incorporation / SYSTEM / deployment / full account-payload equality claim appears in either theorem.
- DIRECT-CLOSURE.md section "Preserved ordinary-call candidate: same-frame guarantees, gas and fee balances" (lines 142-180) accurately mirrors the theorem-body scope: same-frame guarantee + gas arithmetic + ordered fee credits with protected storage; no promotion; canonical history and full-Python correspondence remain explicit external boundaries.

## Conclusion

Both commits are self-contained composition/derivation layers built on the previously reviewed all-three/log certificate (`ReferenceFullLogTotal.verified`). No `sorry`/`admit`, no project-declared axiom, and no non-standard universe axiom is introduced. All bundle SHA-256s reproduce at the source commits; the only later divergence is an additive alias in `ReferenceOutcomeGas.lean` (commit 5cd0fe5) that reuses an existing internal helper without changing the module's public gas-settlement API. The theorem signatures do not smuggle any of the postconditions that the receipts claim to have eliminated (`Valid` outcome-gas, refund/tip conversion success, disbursement `.ok`, final balance affordability, protected-storage identity — all appear only as conclusions or as private lemma call-site facts derived from admission/history/settlement). The Lean transcriptions of `settle_transaction_gas`, `disburse_gas_fees` and `TransactionState` match the pinned Python excerpts at the ordering/cap/clamp level the receipts claim, and the mutation tests pin the fee-ordering, alias-accumulation, and zero-credit-cleanup contracts. No scope drift into canonical history, block incorporation, full-account payload equality, SYSTEM authorization or a 256-iteration ceiling was found.

VERDICT: CLEAN
