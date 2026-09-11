# Independent review — History slots/listed alias (6663875)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commit: 666387525a688b2142df22c15a065f065593e768
Branch: spark/eip-history-slots-alias-20260911
Started at: 2026-09-11T13:14:23+00:00

## Scope items reviewed
- Presence of `sorry` / `admit` / stub tactics in the new module and in the three consumed dependencies.
- Axiom drift: each of the three new theorems is claimed to depend only on `{propext, Classical.choice, Quot.sound}`.
- Correctness: each theorem must be a direct projection of `History.slots` / `History.listed` or a direct call to `ActualJournalHistory.work_lt_of_blocks`.
- No premise smuggling: only `h : History deposit exit before` (plus its structure-level type parameters) as input.
- Bundle-hash agreement between the four on-disk `.lean` files and `audit/receipts/direct-history-slots-alias-bundle-20260911.json`.
- Ancillary integration edits: `Integrator.lean` import and `Trust.lean` `#print axioms` lines.

## Findings
1. (Informational, non-blocking) The new module `ReferenceHistorySlotsAlias.lean` contains no `sorry` or `admit` tactic. A grep hit for the substring "admit" was located; it lies in a comment inside `ReleaseCandidate.lean` line 117 ("admitted history edge") and is prose, not a tactic. No blocking issue.
2. `slots_nodup h` is literally `h.slots` (line 28) — direct field projection, exactly the required form.
3. `listed_flatMap h` is literally `h.listed` (line 34) — direct field projection, exactly the required form.
4. `work_lt_from_slots h` is literally `ActualJournalHistory.work_lt_of_blocks h.receipts h.blocks h.listed h.slots` (line 43) — matches the `work_lt_of_blocks` signature in `ActualJournalHistory.lean:132-134` `(receipts : List Receipt) (blocks : List BlockReceipt) (listed : receipts = blocks.flatMap (fun b => b.receipts)) (slots : (blocks.map (fun b => b.slot)).Nodup)`. No hidden reordering, no substituted argument.
5. No premise smuggling: each theorem takes only `{deposit exit : Receipt} {before : AccountMap .EVM}` (implicit) plus the single explicit `h : History deposit exit before`. No auxiliary hypothesis is introduced.
6. The `Integrator.lean` addition is a single import (`Eip8282.Audit.Integrator.ReferenceHistorySlotsAlias`). The `Trust.lean` addition consists of exactly three `#print axioms` lines matching the three declaration names.

## Axiom audit
Per `audit/receipts/direct-history-slots-alias-axioms-20260911.json`:
- `Eip8282.Audit.Integrator.ReferenceHistorySlotsAlias.slots_nodup` — `{propext, Classical.choice, Quot.sound}`.
- `Eip8282.Audit.Integrator.ReferenceHistorySlotsAlias.listed_flatMap` — `{propext, Classical.choice, Quot.sound}`.
- `Eip8282.Audit.Integrator.ReferenceHistorySlotsAlias.work_lt_from_slots` — `{propext, Classical.choice, Quot.sound}`.
- `sorryAx`: NONE. `other_axioms`: NONE.
Consistent with a pure field projection (`slots_nodup`, `listed_flatMap`) and a direct application of a previously-audited theorem (`work_lt_from_slots`). No axiom drift.

## Bundle hash verification
Computed via `sha256sum` on-disk at HEAD 666387525a688b2142df22c15a065f065593e768:
- `Eip8282/Audit/Integrator/ReferenceHistorySlotsAlias.lean` — `8c6fd5df2bcd31c36b2a43f0bebb7eb9593fae7b214a5a183d49b68ec1ceccf3` — MATCHES bundle.
- `Eip8282/Audit/Integrator/ReleaseCandidate.lean` — `764488ab43cbb63b775d97f0a41ec98fe520445bcd1390bbca5a834a181c2d66` — MATCHES bundle.
- `Eip8282/Audit/Integrator/ActualJournalHistory.lean` — `744476e8ebc4ce5fbfe722045a405fe0a9a8e7b5d61554898df382daa0a39e8e` — MATCHES bundle.
- `Eip8282/Audit/Integrator/TransactionAppendBudget.lean` — `aa799503613c3cc88d327f9e011a25dee08ce6bf569359f8d6e512d86cf25518` — MATCHES bundle.
All four hashes agree exactly with `audit/receipts/direct-history-slots-alias-bundle-20260911.json`.

## Conclusion
The commit introduces three consumer-facing named theorems whose proof terms are, respectively, the two structure fields `h.slots` and `h.listed` and one direct application of the already-audited `ActualJournalHistory.work_lt_of_blocks`. No new premise is added, no invariant is claimed beyond what `ReleaseCandidate.History` and `work_lt_of_blocks` already guarantee. The axiom receipt is limited to the standard Lean set, the source module is free of `sorry` / `admit` tactics, and the four bundle hashes reproduce exactly. Ancillary integration edits (one import in `Integrator.lean`, three `#print axioms` lines in `Trust.lean`) are minimal and consistent with the receipts.

VERDICT: CLEAN
