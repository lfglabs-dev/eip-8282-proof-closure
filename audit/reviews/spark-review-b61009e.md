# Independent review — History withdrawal extension (b61009e)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commit: b61009e8fadb1b2a086410d5d000a19edd467fd1
Branch: spark/eip-history-withdrawal-extension-20260911
Started at: 2026-09-11T12:04:42Z

## Scope items reviewed
- `sorry` / `admit` / stub scan of the new module.
- Axiom drift receipt cross-check for all five declarations.
- Correctness of `Ledger.withdrawal` chaining and the `Nat.add_assoc` reassociation used inside the `ledger` field proof.
- Correctness of `Counts` reconstruction (only three fields; `pow_count`, `withdrawal_count`, `migration_conserving`) and re-use of `h.counts.*` where applicable.
- Correctness of `Trace.credit` chaining and matching against the History `actual` field's expected shape.
- Trivialization/renamed-premise scan on the four lemmas.
- DIRECT-CLOSURE.md scope disclaimers (no consensus scheduling, no withdrawal index, no fork identification).
- Bundle SHA256 verification for `ReferenceHistoryWithdrawalExtension`, `ReleaseCandidate`, `ActualJournalHistory`, `ProtocolCreditEnvelope`.
- Field-count verification: all 16 History fields are populated in the `next_withdrawal` structure literal.
- Trust.lean and Integrator.lean import/print-axioms wiring.

## Findings

1. ADVISORY — none escalated to BLOCKING.
   The docstring at line 11 contains the substring "admitted by" which is a natural-language reference to `Ledger.withdrawal`'s admission premise; it is not a `Lean.admit` stub. Grep for `\badmit\b` and `\bsorry\b` in the module body yields zero occurrences outside the comment prose.

2. ADVISORY — The four lemmas (`_receipts_stable`, `_blocks_stable`, `_credits`, `_counters`) are `rfl`-only reductions of the structural definition. They are correct by definitional unfolding of the anonymous constructor and do not smuggle new obligations. In particular, none of them take as input the equation they claim; each takes only the same domain as `next_withdrawal`.

3. ADVISORY — The `nextCount : h.withdrawals + 1 ≤ 16 * 2^64` premise is exactly the shape required by `ProtocolCreditEnvelope.Counts.withdrawal_count` after the counter increments to `h.withdrawals + 1`. It is a genuine domain input, not a proof of the conclusion.

## Axiom audit
Per the receipt `audit/receipts/direct-history-withdrawal-extension-axioms-20260911.json` and the `#print axioms` lines at Trust.lean (appended after line 3852) and inside the module (lines 107-111):

- `next_withdrawal` — `{propext, Classical.choice, Quot.sound}` — CLEAN.
- `next_withdrawal_receipts_stable` — `{propext, Classical.choice, Quot.sound}` — CLEAN.
- `next_withdrawal_blocks_stable` — `{propext, Classical.choice, Quot.sound}` — CLEAN.
- `next_withdrawal_credits` — `{propext, Classical.choice, Quot.sound}` — CLEAN.
- `next_withdrawal_counters` — `{propext, Classical.choice, Quot.sound}` — CLEAN.

No `sorryAx` or other axioms declared. Receipt classification is
`HISTORY_WITHDRAWAL_EXTENSION_AXIOMS_LIMITED_TO_PROPEXT_CLASSICAL_QUOT`.

## Bundle hash verification
Locally computed sha256 vs. `audit/receipts/direct-history-withdrawal-extension-bundle-20260911.json`:

- `Eip8282/Audit/Integrator/ReferenceHistoryWithdrawalExtension.lean` — local `8cd460e3dbc0ab5413e9c58414b1c4bc79fe18f7e3625555511c9a854f976c75` — receipt `8cd460e3dbc0ab5413e9c58414b1c4bc79fe18f7e3625555511c9a854f976c75` — MATCH.
- `Eip8282/Audit/Integrator/ReleaseCandidate.lean` — local `764488ab43cbb63b775d97f0a41ec98fe520445bcd1390bbca5a834a181c2d66` — receipt `764488ab43cbb63b775d97f0a41ec98fe520445bcd1390bbca5a834a181c2d66` — MATCH.
- `Eip8282/Audit/Integrator/ActualJournalHistory.lean` — local `744476e8ebc4ce5fbfe722045a405fe0a9a8e7b5d61554898df382daa0a39e8e` — receipt `744476e8ebc4ce5fbfe722045a405fe0a9a8e7b5d61554898df382daa0a39e8e` — MATCH.
- `Eip8282/Audit/Integrator/ProtocolCreditEnvelope.lean` — local `79d4b50bf49d7cefa35e35bd5bb92f6b84dca99cb60aeadc9445ea721dcacb7c` — receipt `79d4b50bf49d7cefa35e35bd5bb92f6b84dca99cb60aeadc9445ea721dcacb7c` — MATCH.

## Field-shape verification

`ReleaseCandidate.History` (lines 31-49) has exactly 16 fields:
`depositInputs, exitInputs, linked, baseCredits, credits, pow, withdrawals, migrations, receipts, prior, actual, ledger, counts, blocks, listed, slots`.
All 16 are populated in the `next_withdrawal` anonymous constructor (lines 46-68). Preserved verbatim: `depositInputs, exitInputs, linked, baseCredits, pow, migrations, receipts, prior, blocks, listed, slots`. Updated: `credits := h.credits + amount.toNat`, `withdrawals := h.withdrawals + 1`, `actual := Trace.credit ...`, `ledger := by ...`, `counts := ⟨h.counts.pow_count, nextCount, h.counts.migration_conserving⟩`.

### Ledger.withdrawal chain arithmetic
`Ledger.withdrawal h.ledger recipient amount bounded` has type
`Ledger genesis h.pow (h.withdrawals+1) h.migrations ((h.baseCredits + h.credits) + amount.toNat) (before.increaseBalance .EVM recipient amount)`.

The History `ledger` field requires
`Ledger genesis h.pow (h.withdrawals+1) h.migrations (h.baseCredits + (h.credits + amount.toNat)) (before.increaseBalance ...)`.

`Nat.add_assoc a b c : (a+b)+c = a+(b+c)`. `simpa only [Nat.add_assoc]` rewrites the credit index from `(h.baseCredits + h.credits) + amount.toNat` to `h.baseCredits + (h.credits + amount.toNat)`, matching the field. Correct.

### Trace.credit chain arithmetic
`Trace.credit h.actual recipient amount` has type
`Trace exit.world h.receipts (h.credits + amount.toNat) (before.increaseBalance .EVM recipient amount)`.
The History `actual` field expects `Trace exit.world receipts credits before'` where new `receipts = h.receipts`, `credits = h.credits + amount.toNat`, `before' = before.increaseBalance .EVM recipient amount`. Direct match.

### Counts shape
`Counts pow withdrawals migrations` requires: `pow ≤ 2^64`, `withdrawals ≤ 16*2^64`, `migrations = 0`. With new `pow = h.pow`, `withdrawals = h.withdrawals + 1`, `migrations = h.migrations`, the three fields are supplied by `h.counts.pow_count`, `nextCount`, `h.counts.migration_conserving` respectively. Types match.

### DIRECT-CLOSURE.md scope disclaimer
Section "History withdrawal extension candidate" (lines 69-104) explicitly states:
"Neither the extension nor its lemmas assert consensus-level scheduling, a withdrawal index or fork identification; the caller-supplied bounds match exactly what `Ledger.withdrawal` and `Trace.credit` accept."
Also notes independent exact review pending, PR20 unchanged. Scope disclaimer is accurate and complete.

## Conclusion

The `next_withdrawal` definition correctly composes `ActualJournalHistory.Trace.credit` with `ProtocolCreditEnvelope.Ledger.withdrawal` to extend a `ReleaseCandidate.History` by one credit-carrying withdrawal event. All 16 History fields are populated with the correct shapes: eleven are preserved verbatim, two counters/totals are incremented by `1` and `amount.toNat` respectively, the `actual` and `ledger` fields chain through the two constructors, and the `counts` bundle re-uses two existing proofs plus the caller-supplied `nextCount`. The `Nat.add_assoc` reassociation is exactly what is needed to reconcile `Ledger.withdrawal`'s left-associated credit index with the History field's right-associated shape. The four accompanying `rfl`-only lemmas expose the stability and increment shape without pattern matching and do not smuggle in their own conclusions. All five declarations depend only on `{propext, Classical.choice, Quot.sound}`; no `sorry`/`admit` stubs; bundle SHA256s match the receipt; DIRECT-CLOSURE.md scope disclaimer is honest about what the extension does not claim (no consensus scheduling, no withdrawal index, no fork identification).

VERDICT: CLEAN
