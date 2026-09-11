# Independent review — CreditBatch kill-lines (946b3bf)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commit: 946b3bff68d56a54cf810521648fcc7eb5aaef67
Branch: spark/eip-credit-batch-kill-lines-20260911
Started at: 2026-09-11T13:32:43Z

## Scope items reviewed
- Absence of `sorry` / `admit` / stubs in the new module and its consumed dependency.
- Axiom drift: exact axiom sets on all nine declarations vs. the axioms receipt.
- Correctness: each theorem body vs. the definitions in `ProtocolCreditEnvelope`
  (`powMaximum`, `withdrawalMaximum`, `envelope`, `CreditBatch.nil`, `CreditBatch.cons`).
- Bundle hash match: `sha256sum` on both listed modules against the bundle receipt.
- Scope drift: DIRECT-CLOSURE.md section disclaimers (no protocol policy adopted;
  no canonical producer claim; PR20 unchanged; prepared docs unpushed).
- Trust and Integrator wiring: 9 `#print axioms` lines and the single import line.

## Findings

1. ADVISORY: The `nil_credit_zero`, `cons_singleton` and `cons_two_zero_amounts`
   theorems are literal constructor applications of `CreditBatch.nil` and
   `CreditBatch.cons`; the theorem statements exactly match the constructor
   type signatures (indices `world 0 world`, `before (amount.toNat+total) after`).
   No coercion or `simp` hides premise smuggling. The proofs are as tight as
   possible given the inductive.

2. ADVISORY: `powMaximum_value`, `withdrawalMaximum_value` and
   `envelope_expansion` are `rfl` on the `def` right-hand sides in
   `ProtocolCreditEnvelope.lean:21-26`. The literal `14062500000000000000` and
   the expression `(2^64 - 1) * 10^9` match verbatim. `envelope_expansion`
   preserves the exact operand order `totalCredit + powMaximum*pow +
   withdrawalMaximum*withdrawals + migrations`.

3. ADVISORY: `envelope_zero`, `envelope_one_pow`, `envelope_one_withdrawal` are
   `by simp [envelope]`, unfolding to arithmetic identities on 0/1. No
   additional hypothesis is introduced. The stated goal, after `simp [envelope]`,
   reduces to `A + B*0 + C*0 + 0 = A` and analogous forms — provable by
   normalization only.

4. ADVISORY: No `sorry`, `admit`, `axiom`, `unsafe`, or `@[reducible]` shortcut
   appears in the new module. No `import` beyond `ProtocolCreditEnvelope`. The
   `set_option maxRecDepth`/`maxHeartbeats` values match the surrounding
   integrator style.

5. ADVISORY: The DIRECT-CLOSURE.md section explicitly states the kill-lines "do
   not require instantiating a `Ledger` or a `History`" and repeats "No
   unreviewed proof extension, external message or normative policy has been
   promoted. PR20 remains `c3f3c1d`; prepared documentation `7e2ef006` remains
   unpushed." Scope disclaimers are correct.

No BLOCKING findings.

## Axiom audit
Per the receipt `direct-credit-batch-kill-lines-axioms-20260911.json`, and
consistent with the proof shapes:
- `powMaximum_value`: `[]` — pure `rfl` on a `Nat` literal. Consistent.
- `withdrawalMaximum_value`: `[propext]` — `rfl` invokes `propext` via kernel
  normalization on the arithmetic expression. Consistent.
- `envelope_expansion`: `[propext]` — `rfl` on the `def envelope` body.
  Consistent.
- `envelope_zero`, `envelope_one_pow`, `envelope_one_withdrawal`: `[propext]` —
  `simp` uses `propext` only. Consistent.
- `nil_credit_zero`, `cons_singleton`, `cons_two_zero_amounts`:
  `[propext, Classical.choice, Quot.sound]` — the `AccountMap` universe drags
  the full Lean-4 classical trio through the `CreditBatch` constructor
  elaboration. All three axioms lie within the permitted subset. Consistent.

All nine sets are subsets of `{propext, Classical.choice, Quot.sound}`; no
`sorryAx`, no ad-hoc axiom, no `Lean.trustCompiler`. Matches receipt claim.

## Bundle hash verification
- `Eip8282/Audit/Integrator/ReferenceCreditBatchKillLines.lean`:
  computed `66aac14ee2ea3129803144cacf2114cbd2be5773ff03db45369baa3c2e2a2fed`;
  receipt `66aac14ee2ea3129803144cacf2114cbd2be5773ff03db45369baa3c2e2a2fed` — MATCH.
- `Eip8282/Audit/Integrator/ProtocolCreditEnvelope.lean`:
  computed `79d4b50bf49d7cefa35e35bd5bb92f6b84dca99cb60aeadc9445ea721dcacb7c`;
  receipt `79d4b50bf49d7cefa35e35bd5bb92f6b84dca99cb60aeadc9445ea721dcacb7c` — MATCH.

Both hashes match the `direct-credit-batch-kill-lines-bundle-20260911.json`
`components`/`consumed_dependencies` entries exactly.

## Conclusion
The new module `ReferenceCreditBatchKillLines` adds nine standalone kill-line
theorems that exercise the aggregate arithmetic and `CreditBatch` constructors
inside `ProtocolCreditEnvelope`. Each theorem is either a direct `rfl` on a
`def` right-hand side, a `simp [envelope]` reduction to trivial `Nat`
arithmetic, or a literal application of `CreditBatch.nil` / `CreditBatch.cons`.
No premise is smuggled; no new axiom, `sorry`, or `admit` is introduced.
Axiom sets are subsets of the permitted `{propext, Classical.choice,
Quot.sound}`, with `powMaximum_value` axiom-free as advertised. SHA-256 hashes
on both the new module and its sole consumed dependency match the bundle
receipt verbatim. The DIRECT-CLOSURE.md section correctly disclaims that the
kill-lines do not adopt a protocol policy, does not claim a canonical producer,
and confirms PR20 `c3f3c1d` and prepared documentation `7e2ef006` remain in
their previous states. Trust and Integrator wiring add exactly one import and
nine `#print axioms` lines. No scope drift observed.

VERDICT: CLEAN
