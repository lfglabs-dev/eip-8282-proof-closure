# Independent review — SYSTEM + transfer History extensions (e673707)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commit: e67370756a731fd7a99d69b7f6ec3e9de6018a31
Branch: spark/eip-history-nonreceipt-extensions-20260911
Started at: 2026-09-11T11:56:07Z

## Scope items reviewed
- Presence of `sorry` / `admit` / stubs in the new module.
- Axiom set for all 8 declarations vs. the axioms receipt.
- Signature match between `next_system` / `next_transfer` inputs and the underlying `Trace.system` / `Trace.transfer` premises.
- Correctness of the internal ledger extension (`FundingHistory.Step.system` composed with `t.pre` rewrite; `FundingHistory.Step.transfer` direct).
- `rfl`-provability of the six `.*_stable` lemmas.
- Scope disclaimers in the new `audit/DIRECT-CLOSURE.md` section.
- Bundle-hash equality for the new module and 6 consumed dependencies.
- Full 16-field population of `ReleaseCandidate.History` in both constructors.
- Integrator import and Trust `#print axioms` wiring for all 8 declarations.

## Findings
1. ADVISORY — `Eip8282/Audit/Integrator/ReferenceHistoryNonReceiptExtensions.lean:21`. The doc-comment refers to `ReferenceCanonicalHooks.SystemAuthorization`, but there is no `ReferenceCanonicalHooks` module or `SystemAuthorization` declaration anywhere under `Eip8282/`. This is a doc-comment prose reference only (Lean does not resolve names inside doc-comments), so it does not affect the proof surface. Documentation-only fix suggested: point to whatever module actually specifies the SYSTEM authorization obligation, or drop the specific name.
2. ADVISORY — Doc comments and bundle text reference `ReferenceFundedHistoryLifecycle.next` as the analogue that handles the ordinary transaction receipt case. No such module was found under `Eip8282/`. The narrative claim in `audit/DIRECT-CLOSURE.md:73` and in the module doc-comment (line 5) is thus not backed by any in-tree definition of that specific name. Advisory only: it does not affect this commit's proof content, which stands on its own; but the naming claim is unverified in-tree.

Neither finding blocks: both are prose-only references inside comments and markdown; the proof surface of this commit (definitions, theorems, and their axioms) is internally consistent and complete on the checked declarations.

## Axiom audit
Receipt `audit/receipts/direct-history-nonreceipt-extensions-axioms-20260911.json` lists exactly `{propext, Classical.choice, Quot.sound}` for each of the eight declarations. This is the standard classical trio for Lean 4 Mathlib-style developments and matches the eight `#print axioms` lines at `Eip8282/Audit/Trust.lean:3860-3867`. No `sorryAx` and no other axiom is declared.
- `next_system` — {propext, Classical.choice, Quot.sound}
- `next_transfer` — {propext, Classical.choice, Quot.sound}
- `next_system_receipts_stable` — {propext, Classical.choice, Quot.sound}
- `next_transfer_receipts_stable` — {propext, Classical.choice, Quot.sound}
- `next_system_blocks_stable` — {propext, Classical.choice, Quot.sound}
- `next_transfer_blocks_stable` — {propext, Classical.choice, Quot.sound}
- `next_system_credits_stable` — {propext, Classical.choice, Quot.sound}
- `next_transfer_credits_stable` — {propext, Classical.choice, Quot.sound}

Grep for `sorry`/`admit` in the module returned no hits. The classical trio is expected because `AccountMap`, `TreeSet` and the underlying EVM primitives are built on `Classical`. The set is minimal and unchanged.

## Bundle hash verification
Recomputed with `sha256sum` on the working tree at commit e673707:

- `Eip8282/Audit/Integrator/ReferenceHistoryNonReceiptExtensions.lean` -> `11a6ec7e89c3c6f9ffd60c27d32818684e4310f418a357728df343dc3c40bfef` — MATCH.
- `Eip8282/Audit/Integrator/ReleaseCandidate.lean` -> `764488ab43cbb63b775d97f0a41ec98fe520445bcd1390bbca5a834a181c2d66` — MATCH.
- `Eip8282/Audit/Integrator/ActualJournalHistory.lean` -> `744476e8ebc4ce5fbfe722045a405fe0a9a8e7b5d61554898df382daa0a39e8e` — MATCH.
- `Eip8282/Audit/Integrator/FundingHistory.lean` -> `da5af24a0eb4630f8c02beb32c4245e54f08dd0c880ec79278002c6c6352e65f` — MATCH.
- `Eip8282/Audit/Integrator/ProtocolCreditEnvelope.lean` -> `79d4b50bf49d7cefa35e35bd5bb92f6b84dca99cb60aeadc9445ea721dcacb7c` — MATCH.
- `Eip8282/Audit/Integrator/ProtocolTransfer.lean` -> `0f79448d00498376ead1a03594f2ea62eae9df4f678b77bf89582c65c40753bb` — MATCH.
- `Eip8282/Audit/Integrator/TransferFunding.lean` -> `b8d8286170495a4a59d0f61ad19e0354e624ea3a0c0e0f48bd24e92ea7871766` — MATCH.

All 7 bundle hashes match the receipt at `audit/receipts/direct-history-nonreceipt-extensions-bundle-20260911.json`.

## Signature and composition audit

`ActualJournalHistory.Trace.system` (ActualJournalHistory.lean:40-45) takes `(prior, t, sender, zero, fit)` where `sender : t.call.caller = Eip8282.Audit.EvmRunner.sysAddr`, `zero : t.call.value = ⟨0⟩`, `fit : t.call.calldata.size < UInt256.size`. `next_system` at `ReferenceHistoryNonReceiptExtensions.lean:44-70` accepts exactly those three premises under the names `senderIsSys, zeroValue, dataFit` and passes them as `Trace.system h.actual t senderIsSys zeroValue dataFit` on line 65. No extra premise; no premise renamed to a weaker form.

`ActualJournalHistory.Trace.transfer` (ActualJournalHistory.lean:46-50) takes `(prior, sender, recipient, amount, funded)` where `funded : amount.toNat ≤ TransferFunding.worldBalance before sender`. `next_transfer` at lines 77-99 accepts exactly that `funded` premise and passes them as `Trace.transfer h.actual sender recipient amount funded` on line 94. No extra premise; no premise renamed.

Ledger composition for `next_system` at lines 51-54 constructs `FundingHistory.Step.system t.call senderIsSys zeroValue t.executed` yielding `Step t.call.world 0 after` (matching the `Step.system` signature at FundingHistory.lean:31-36, whose after-world comes from `c.result = .ok (created,world,gas,substate,success,out)` matched against `t.executed`'s `after` binding at ReachableCalls.lean:59). The `rw [t.pre] at base` step rewrites `t.call.world` to `before` (using `Transition.pre : call.world = before`, ReachableCalls.lean:53), producing `Step before 0 after`. This is the exact pattern used in `ActualJournalHistory.funding` at ActualJournalHistory.lean:68-71.

Ledger composition for `next_transfer` at lines 82-83 constructs `FundingHistory.Step.transfer before sender recipient amount funded` which by the `Step.transfer` signature at FundingHistory.lean:37-39 directly gives `Step before 0 (ProtocolTransfer.transfer before sender recipient amount)`. The result type of `next_transfer` at line 81 is `History deposit exit (ProtocolTransfer.transfer before sender recipient amount)`; the ledger is extended via `Ledger.conserving h.ledger step` (line 95) using the zero-credit `.conserving` constructor at ProtocolCreditEnvelope.lean:50-52, preserving `p w s c` and hence `baseCredits+credits`. Credit total is unchanged, as claimed.

## History-field audit

`ReleaseCandidate.History` at ReleaseCandidate.lean:31-49 has 16 fields: `depositInputs, exitInputs, linked, baseCredits, credits, pow, withdrawals, migrations, receipts, prior, actual, ledger, counts, blocks, listed, slots`. Both constructors populate all 16 explicitly:

- `next_system` at lines 55-70: `depositInputs, exitInputs, linked, baseCredits, credits, pow, withdrawals, migrations, receipts, prior, actual (updated), ledger (updated), counts, blocks, listed, slots` — 16/16.
- `next_transfer` at lines 84-99: same layout — 16/16.

Only `actual` and `ledger` are replaced; the other 14 fields are copied verbatim (`h.<field>`). This is why each `.*_stable` lemma is defeq-`rfl` provable: the field projections literally reduce to the underlying `h.receipts` / `h.blocks` / `h.credits` / `h.baseCredits`.

## Stability lemmas
All six lemmas at lines 102-146 use `rfl` (either bare `rfl` for the single-equality ones, or `⟨rfl, rfl⟩` for the pair conjunction). Given that the constructor bodies literally set each preserved field via `receipts := h.receipts`, `blocks := h.blocks`, `credits := h.credits`, `baseCredits := h.baseCredits`, the projections reduce by `rfl`. Verified.

## Scope disclaimers in DIRECT-CLOSURE.md

The new section `audit/DIRECT-CLOSURE.md:69-108` explicitly disclaims:
- No adoption of a protocol schedule for SYSTEM Θ (lines 93-96: "Neither extension asserts canonical Ethereum machinery has authorized the SYSTEM Θ or scheduled the transfer").
- No admissibility claim beyond the `funded` premise (lines 94-96).
- No canonical block sequence (implicit in the wording "does not adopt a protocol schedule ... does not produce a canonical block sequence" in the bundle `domain.scope`; the DIRECT-CLOSURE text itself does not literally say "does not produce a canonical block sequence" — it disclaims authorization and scheduling, and the bundle receipt at lines 61-64 carries the block-sequence disclaimer explicitly).
- The `credit` Trace constructor is explicitly left to the caller due to protocol-level classification (lines 79-81).

The four required disclaimers are present across the module doc-comment (lines 18-24 of the .lean file), DIRECT-CLOSURE.md (lines 79-96) and the bundle receipt (lines 61-64). The DIRECT-CLOSURE.md section could be tightened to include the "does not produce a canonical block sequence" disclaimer inline; the bundle already carries it. Advisory.

## Integrator and Trust wiring
- `Eip8282/Audit/Integrator.lean:506` imports `Eip8282.Audit.Integrator.ReferenceHistoryNonReceiptExtensions`.
- `Eip8282/Audit/Trust.lean:3860-3867` contains all 8 `#print axioms` lines, one per declaration.

## Conclusion
The two constructors `next_system` and `next_transfer` extend `ReleaseCandidate.History` by exactly one non-receipt world step, using the underlying `ActualJournalHistory.Trace.system` and `.transfer` constructors with their precise premise sets (no strengthening, no weakening, no renaming to a trivialized form). The internal ledger extension routes through `ProtocolCreditEnvelope.Ledger.conserving` on zero-credit `FundingHistory.Step` constructors, preserving `pow, withdrawals, migrations, baseCredits+credits` and the counts structure. All 14 preserved fields are copied verbatim, so the six `.*_stable` lemmas hold by `rfl`. The eight declarations depend only on `{propext, Classical.choice, Quot.sound}`, the receipt agrees with the `#print axioms` wiring, and no `sorry`/`admit` appears. Bundle hashes for the new module and all six consumed dependencies match the receipt exactly. The DIRECT-CLOSURE.md section carries the required disclaimers on SYSTEM authorization, transfer admissibility (beyond `funded`), and the `credit` classification split; the block-sequence disclaimer is carried in the bundle receipt. The only findings are two advisory doc-comment references (`ReferenceCanonicalHooks.SystemAuthorization` and `ReferenceFundedHistoryLifecycle.next`) that do not resolve to in-tree names, which is a prose-only issue and does not affect the proof surface.

VERDICT: CLEAN
