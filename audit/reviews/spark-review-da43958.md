# Independent review — History PoW-batch extension (da43958)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commit: da43958d3266ac912131034633cd224f154a9bd9
Branch: spark/eip-history-pow-batch-extension-20260911
Started at: 2026-09-11T12:18:25+00:00

## Scope items reviewed
- No `sorry` / `admit` / stubs in the new module.
- Axiom drift: cross-checked the axioms receipt against declared axiom sets.
- `extend_trace_batch` induction: nil and cons cases, `generalizing credits`.
- Ledger extension via `Ledger.pow` with `Nat.add_assoc` reassociation of `(baseCredits+credits)+amount`.
- Counts update: `pow_count`, `withdrawal_count`, `migration_conserving`.
- Renamed premises / no theorem takes as input the bound it is trying to prove.
- Scope-drift disclaimers in `audit/DIRECT-CLOSURE.md`.
- Bundle hash match for 4 modules against `audit/receipts/direct-history-pow-batch-extension-bundle-20260911.json`.
- All 16 `ReleaseCandidate.History` fields populated by `next_pow_batch`.
- `Trust.lean` `#print axioms` for all five declarations and `Integrator.lean` import.

## Findings

1. ADVISORY — DIRECT-CLOSURE.md scope disclaimer completeness.
   The new "History PoW-batch extension candidate" section correctly
   disclaims consensus-level scheduling, fork identification and canonical
   batch source, but does NOT explicitly state that the migration
   constructor remains uncovered. The bundle receipt (`clause_map`) does
   state this (constrained to `amount = 0` by
   `Counts.migration_conserving = 0`, "left uncovered as a distinct
   decision"), and the commit message repeats it. Non-blocking: the
   substantive scope disclaimers required by the review scope are all
   present in the new DIRECT-CLOSURE.md section; the migration remark is
   present elsewhere in the receipts and commit trail.

2. VERIFIED — `extend_trace_batch` induction is sound.
   - Signature: `generalizing credits` (required so `ih` can be applied
     with the incremented starting count).
   - `nil w` case: batch aggregate = 0, before = after = w; goal
     `Trace initial receipts (credits + 0) w`; `simpa using trace` uses
     `Nat.add_zero` to reduce to `trace`. Correct.
   - `cons recipient amount tail ih` case: aggregate =
     `amount.toNat + total` (per `CreditBatch.cons`); `Trace.credit trace
     recipient amount` yields
     `Trace initial receipts (credits + amount.toNat) (increaseBalance)`;
     `ih next` yields `Trace initial receipts ((credits+amount.toNat)+total) after`;
     `simpa only [Nat.add_assoc]` rewrites to
     `credits + (amount.toNat + total)`, matching the goal. Note the
     inner `amount : UInt256` correctly shadows the outer `amount : Nat`.

3. VERIFIED — Ledger extension.
   `Ledger.pow h.ledger batch bounded` produces
   `Ledger .. (pow+1) w s ((baseCredits+credits)+amount) after`. The
   History field requires `Ledger .. (baseCredits+(credits+amount)) after`.
   `simpa only [Nat.add_assoc]` reassociates correctly.

4. VERIFIED — Counts update.
   `pow_count := nextCount` uses caller-supplied `h.pow + 1 ≤ 2^64`
   (matches `Counts (pow+1) _ _` requirement).
   `withdrawal_count` and `migration_conserving` preserved from `h.counts`
   — correct because `withdrawals` and `migrations` are unchanged.

5. VERIFIED — No trivialized premises.
   `bounded` and `nextCount` are the exact admissions consumed by
   `Ledger.pow` and the `Counts` field; neither is a restatement of the
   theorem conclusions. Field-shape lemmas take no non-trivial witnesses
   they trivialize.

6. VERIFIED — All 16 History fields populated by `next_pow_batch`:
   depositInputs, exitInputs, linked, baseCredits, credits, pow,
   withdrawals, migrations, receipts, prior, actual, ledger, counts,
   blocks, listed, slots (11 preserved via `h.*`; `credits`, `pow`,
   `actual`, `ledger`, `counts` are updated; `listed` and `slots`
   preserved literally since `receipts` and `blocks` are preserved).

7. VERIFIED — Trust.lean adds `#print axioms` for exactly the five
   declarations; Integrator.lean adds the module import. No `sorry` or
   `admit` in the new module (`grep` returned none).

## Axiom audit
Receipt `audit/receipts/direct-history-pow-batch-extension-axioms-20260911.json`
declares for each of the five declarations exactly
`[propext, Classical.choice, Quot.sound]`, `sorryAx: NONE`,
`other_axioms: NONE`.

- `next_pow_batch`: `{propext, Classical.choice, Quot.sound}` — consistent
  with dependence on `Nat.add_assoc`/`simpa` inside proofs that ultimately
  reduce through standard Mathlib/Lean core lemmas.
- `next_pow_batch_receipts_stable`: same — proof is `rfl`.
- `next_pow_batch_blocks_stable`: same — proof is `rfl`.
- `next_pow_batch_credits`: same — proof is `rfl`.
- `next_pow_batch_counters`: same — proof is `⟨rfl,rfl,rfl,rfl⟩`.

Trust.lean lines 3858-3862 emit `#print axioms` for these same five
symbols. Consistent.

## Bundle hash verification
Computed on the source tree at HEAD da43958:

- `Eip8282/Audit/Integrator/ReferenceHistoryPowBatchExtension.lean`
  computed `0149c42a15f14952034f500d823f597cd0751bf002dcc1d10dc6152066f2286e`;
  receipt `0149c42a15f14952034f500d823f597cd0751bf002dcc1d10dc6152066f2286e`. MATCH.
- `Eip8282/Audit/Integrator/ReleaseCandidate.lean`
  computed `764488ab43cbb63b775d97f0a41ec98fe520445bcd1390bbca5a834a181c2d66`;
  receipt `764488ab43cbb63b775d97f0a41ec98fe520445bcd1390bbca5a834a181c2d66`. MATCH.
- `Eip8282/Audit/Integrator/ActualJournalHistory.lean`
  computed `744476e8ebc4ce5fbfe722045a405fe0a9a8e7b5d61554898df382daa0a39e8e`;
  receipt `744476e8ebc4ce5fbfe722045a405fe0a9a8e7b5d61554898df382daa0a39e8e`. MATCH.
- `Eip8282/Audit/Integrator/ProtocolCreditEnvelope.lean`
  computed `79d4b50bf49d7cefa35e35bd5bb92f6b84dca99cb60aeadc9445ea721dcacb7c`;
  receipt `79d4b50bf49d7cefa35e35bd5bb92f6b84dca99cb60aeadc9445ea721dcacb7c`. MATCH.

## Conclusion
The commit adds a single structural History extension (`next_pow_batch`)
chaining `ProtocolCreditEnvelope.Ledger.pow` with a `Trace.credit`
induction over `CreditBatch`, plus four field-shape lemmas. The
`extend_trace_batch` induction correctly handles nil and cons via
`Nat.add_zero` and `Nat.add_assoc`; the ledger reassociation is
`(baseCredits+credits)+amount = baseCredits+(credits+amount)` via
`Nat.add_assoc`; Counts is updated only for `pow_count` from the
caller-supplied admission; all 16 History fields are populated; no
`sorry`/`admit`; the axiom receipt matches the declared classical
core; all four bundle hashes match. The single ADVISORY (migration
uncovered not repeated in the new DIRECT-CLOSURE.md section itself)
does not affect the proof soundness or scope-honesty of the receipts,
since the migration disclaimer appears in the bundle receipt and
commit message. No blocking findings.

VERDICT: CLEAN
