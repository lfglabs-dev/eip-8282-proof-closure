# Independent review — History invariants aliases (f356794)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commit: f356794011b58d6727f08506edb7605e147929c5
Branch: spark/eip-history-invariants-aliases-20260911
Started at: 2026-09-11T13:02:49Z

## Scope items reviewed
- `sorry` / `admit` / stub scan on the new module.
- Axiom drift check against the axioms receipt for all four declarations.
- Correctness of the destructuring projections `.1`, `.2.1`, `.2.2.1`,
  `.2.2.2 kind` against the return type of
  `ReleaseCandidate.invariants` (four-way right-associative conjunction).
- Premise smuggling: only `h : History` (plus `kind` on `invariant_at`).
- DIRECT-CLOSURE.md scope statement (no new premise, no new axiom).
- Bundle sha256 verification for `ReferenceHistoryInvariantsAliases.lean`
  and the three listed dependencies
  (`ReleaseCandidate.lean`, `ActualJournalHistory.lean`,
  `JournalInvariant.lean`).
- Integrator import addition and Trust.lean `#print axioms` additions.

## Findings

1. ADVISORY. The module docstring (line 5) and the DIRECT-CLOSURE.md
   candidate section describe the aliases with phrases such as
   `h.deposit.success = true` and `h.exit.success = true`. In the
   proved definition, `deposit` and `exit` are implicit parameters of
   `History deposit exit before` and NOT structure fields (the actual
   `History` fields are `depositInputs`, `exitInputs`, `linked`,
   `baseCredits`, ...). The theorem statements themselves are correct
   — they reference the implicit `deposit : Receipt` and
   `exit : Receipt` in scope, i.e. `deposit.success = true` and
   `exit.success = true`. The documentation phrasing
   `h.deposit.success` is a harmless shorthand but is not literally the
   theorem statement. Non-blocking.

2. No `sorry`, `admit` or stub in
   `Eip8282/Audit/Integrator/ReferenceHistoryInvariantsAliases.lean`.

3. Destructuring is exact. `ReleaseCandidate.invariants h` returns
   `deposit.success = true ∧ exit.success = true ∧
    ActualJournalHistory.work h.receipts < 2^128 ∧
    ∀ kind, Invariant kind (ActualJournalHistory.work h.receipts) before`.
   Right-associative parsing gives
   `A ∧ (B ∧ (C ∧ D))`, so:
   - `.1 = A` (deposit success)  — used by `deposit_success`
   - `.2.1 = B` (exit success)  — used by `exit_success`
   - `.2.2.1 = C` (work bound)  — used by `work_lt`
   - `.2.2.2 kind = D kind` (per-kind Invariant) — used by
     `invariant_at`.
   Every alias body matches.

4. Premise scope is exactly the History structure. No safe-numerator,
   no per-call invariant, no ledger premise is added beyond what is
   already inside `History`. `invariant_at` additionally takes the
   ordinary `kind : ReachableCalls.Contract`, which matches the
   universal quantifier the alias eliminates.

5. Integrator adds a single import of the new module. Trust.lean
   appends the four `#print axioms` lines. Both additions are inert
   accumulators; they do not change earlier verified content.

6. DIRECT-CLOSURE.md correctly notes: no new premise, no new axiom,
   each alias is a direct projection, PR20 remains `c3f3c1d`, prepared
   `7e2ef006` remains unpushed, independent exact review pending. That
   review pending marker is the invitation this report fulfills.

## Axiom audit

Per `audit/receipts/direct-history-invariants-aliases-axioms-20260911.json`
(`sorryAx: NONE`, `other_axioms: NONE`):

- `Eip8282.Audit.Integrator.ReferenceHistoryInvariantsAliases.deposit_success`
  → `{propext, Classical.choice, Quot.sound}`.
- `Eip8282.Audit.Integrator.ReferenceHistoryInvariantsAliases.exit_success`
  → `{propext, Classical.choice, Quot.sound}`.
- `Eip8282.Audit.Integrator.ReferenceHistoryInvariantsAliases.work_lt`
  → `{propext, Classical.choice, Quot.sound}`.
- `Eip8282.Audit.Integrator.ReferenceHistoryInvariantsAliases.invariant_at`
  → `{propext, Classical.choice, Quot.sound}`.

No axiom drift. Trust.lean now prints these under the section header
for the four new aliases.

## Bundle hash verification

Recomputed sha256 on the working tree at commit f356794:

- `Eip8282/Audit/Integrator/ReferenceHistoryInvariantsAliases.lean`
  → `8ec01061cb5c766afec47980dab0b86d9d91f785ca81509ef20a7a16204c8b35`
  (matches bundle receipt).
- `Eip8282/Audit/Integrator/ReleaseCandidate.lean`
  → `764488ab43cbb63b775d97f0a41ec98fe520445bcd1390bbca5a834a181c2d66`
  (matches).
- `Eip8282/Audit/Integrator/ActualJournalHistory.lean`
  → `744476e8ebc4ce5fbfe722045a405fe0a9a8e7b5d61554898df382daa0a39e8e`
  (matches).
- `Eip8282/Audit/Integrator/JournalInvariant.lean`
  → `c12320d5c137e34211bca2d179579e1ca291e06287cece017d76c64ba016dead`
  (matches).

All four hashes agree exactly with
`audit/receipts/direct-history-invariants-aliases-bundle-20260911.json`.

## Conclusion

The four new theorems are literal named projections of the existing
`ReleaseCandidate.invariants` four-way conjunction, with destructuring
indices exactly matching the right-associative parse of the return
type. No new premise is smuggled in; the only inputs are the `History`
structure itself and (for `invariant_at`) the `kind` from the
universal quantifier being eliminated. The axioms receipt lists only
`{propext, Classical.choice, Quot.sound}` for all four, with `sorryAx`
and `other_axioms` explicitly `NONE`. All four bundle-listed source
hashes match the working tree. Integrator and Trust additions are
inert accumulators. The DIRECT-CLOSURE.md section correctly claims no
new premise, no new axiom and marks the candidate as pending
independent review. The one observation about the docstring/documentation
phrasing (`h.deposit.success` vs. `deposit.success`) is advisory and
does not affect the proved statements.

VERDICT: CLEAN
