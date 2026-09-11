# Independent review — nested CALL uniform pool accounting (4c4dabe)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commit: 4c4dabe7ff059b046d86e9d4007c9742535fa0ad
Branch: spark/eip-nested-call-identity-20260911
Started at: 2026-09-11T11:13:03+00:00

## Scope items reviewed

- Scope 1 — sorry/admit/stubs: OK. `grep -n 'sorry\|admit\|stub'` on
  `Eip8282/Audit/Integrator/ReferenceNestedCallSettlement.lean` returns no
  matches. The module contains only complete proof terms.
- Scope 2 — axiom drift: OK. Receipt
  `audit/receipts/direct-nested-call-settlement-axioms-20260911.json`
  declares:
  - `finish_pools_success` → {propext, Classical.choice, Quot.sound}
  - `finish_pools` → {propext, Classical.choice, Quot.sound}
  - `finish_deterministic` → {propext}
  Trust.lean adds the three `#print axioms` lines
  (Trust.lean:3858-3862). No sorryAx, no additional axioms.
- Scope 3 — renamed premises / trivialized cases: OK.
  `finish_pools_success` takes only `{s, events, child}`, `paid : runFull …`,
  and `hasValue deadRecipient : Bool` — the identical paid-child domain as
  `ReferenceCallChildBoundary.completes`. `finish_pools` similarly takes
  only the paid-child witness plus `outcome : Outcome`; the extended pool
  identity is derived internally, not received as a premise.
  `finish_deterministic` is `Option.some.inj (h₁.symm.trans h₂)`, i.e.
  bona-fide Option injectivity — a real algebraic fact, not
  proof-irrelevance.
- Scope 4 — scope drift in DIRECT-CLOSURE.md: OK. The new section
  (lines 69-111) states explicitly that the module (a) "does not claim
  identity of any foreign interpreter" (no canonical outer-frame
  semantics), (b) "Journal-side rollback preservation and the outer
  `Coupled` trace remain handled by their existing modules", and
  (c) uses the same paid-child domain as `completes` ("it does not
  weaken the domain, does not add a new premise").
- Scope 5 — bundle hash match: OK. All six files' SHA-256 digests match
  the bundle receipt exactly (see Bundle hash verification below).
- Scope 6 — success-case correctness: OK. Each step in the definition
  chain traces faithfully; details in Findings §Analysis.
- Scope 7 — uniform statement correctness: OK. `finish_pools` cases on
  outcome, uses `finish_pools_success` for `.success` and `completes`
  for the two failing outcomes; `if_neg` picks the correct branch and
  the `stateCost` term is threaded through unchanged.
- Scope 8 — determinism theorem: OK. Exactly
  `Option.some.inj (h₁.symm.trans h₂)`, no hidden assumptions, no
  side-preconditions.
- Scope 9 — DIRECT-CLOSURE.md accuracy: OK. Prose statement on line 87
  is
  `pools post = pools s.parent + pools (settle outcome child) + (if outcome = .success then 0 else stateCost hasValue deadRecipient)`,
  which matches the Lean statement (module lines 87-89) character-for-
  character (including the sign of the if-then-else branch).

## Findings

No blocking or advisory findings.

Analysis notes (informational, not findings):

- `finish_pools_success` proof steps traced against the definitions:
  1. `committed : child.committedSpill = 0` — obtained from
     `(accounting paid s.childState).2.2.2`. `accounting` (ReferenceMeter
     Boundary.lean:29-44) returns a 4-tuple whose fourth conjunct is
     `post.committedSpill = pre.committedSpill`. Here `pre = start s =
     init s.childExecution s.childState` (ReferenceCallChildBoundary.lean
     :22) and `init` sets `committedSpill := 0` (ReferenceChildMeter.lean
     :23), so the resulting equality unfolds definitionally to
     `child.committedSpill = 0`. Correct.
  2. `hi : incorporate s.parent child false = some (repay (absorb …))`
     — the `if_pos` guard is
     `⟨committed, fun h => absurd h Bool.false_ne_true⟩`, discharging
     both conjuncts (the second is vacuous because `failed = false`).
     Then `simp only [Bool.false_eq_true, ↓reduceIte]` selects the
     `else` branch of `if failed then absorb … else repay (absorb …)`
     (ReferenceChildMeter.lean:53-57). Correct.
  3. `href : refill hasValue deadRecipient .success (repay …) =
     repay …` — `refill` (ReferenceCallChildBoundary.lean:26-27) is
     `if failed outcome && hasValue && deadRecipient then credit … else _`.
     With `failed .success = false` (ReferenceCallChildBoundary.lean:18-20),
     `Bool.false_and` collapses the guard and the `if` reduces to the
     identity. Correct.
  4. `hf` composes: `settle .success child = child` (definitional,
     ReferenceChildMeter.lean:32-33) and `failed .success = false`
     (definitional) let the two `show` tactics rewrite. `hi` then
     supplies `incorporate = some …` and `Option.map_some ∘ href`
     yields `some (repay (absorb …))`. Correct.
  5. Pool arithmetic: `repay_accounting (absorb s.parent child) 0 .1`
     gives `pools (repay (absorb …)) = pools (absorb …)`
     (ReferenceChildMeter.lean:82-88). Then `simp only [absorb, pools]`
     unfolds to Nat arithmetic on
     `execution + reservoir` and `omega` closes it. Correct.
- `finish_pools` success branch: statement's expected RHS
  `pools s.parent + pools (settle .success child) + 0` collapses to
  `pools s.parent + pools child + 0` via definitional
  `settle .success child = child`, matching the `show` tactic. `ring`
  handles the `+ 0`.
- `finish_pools` reverted/exceptional branches: `completes` supplies
  the shape `outcome ≠ .success → pools post = pools s.parent +
  pools (settle outcome child) + stateCost …`. `Outcome` derives
  `DecidableEq` (ReferenceChildMeter.lean:27-28), so
  `by decide : Outcome.reverted ≠ .success` and the corresponding
  exceptional lemma discharge both the `if_neg` guard and the
  hypothesis of `hb`. Correct.
- `finish_deterministic`: exactly `Option.some.inj (h₁.symm.trans h₂)`.
  Depending only on `propext` is consistent with the standard proof of
  Option constructor injectivity in Lean 4.
- Minor documentation observation (not a finding): the DIRECT-CLOSURE.md
  wording "all three declarations depend only on propext, Classical.
  choice and Quot.sound" is a slight over-approximation for
  `finish_deterministic` (which uses only `propext`). Still logically
  correct (subset), no action required.

## Axiom audit

- Eip8282.Audit.Integrator.ReferenceNestedCallSettlement.finish_pools_success
  → axioms: {propext, Classical.choice, Quot.sound}
- Eip8282.Audit.Integrator.ReferenceNestedCallSettlement.finish_pools
  → axioms: {propext, Classical.choice, Quot.sound}
- Eip8282.Audit.Integrator.ReferenceNestedCallSettlement.finish_deterministic
  → axioms: {propext}

All within the whitelisted trusted kernel set. `#print axioms` lines are
present at the end of the module (lines 120-122) and mirrored in
Trust.lean:3860-3862. Axioms taken from
`audit/receipts/direct-nested-call-settlement-axioms-20260911.json` and
cross-checked against the transitive dependencies (`Option.some.inj`,
`Bool.*` lemmas, `omega`, `simp`, `ring`, `decide`) — none of these
introduces further axioms beyond the standard three.

## Bundle hash verification

Computed with `sha256sum` against files at HEAD 4c4dabe:

| Module | Expected | Computed | Match |
|---|---|---|---|
| ReferenceNestedCallSettlement.lean | 0f84b4bf5729cf01132dc743307500bd3ff23a81199340bd85e04ab578dd584f | 0f84b4bf5729cf01132dc743307500bd3ff23a81199340bd85e04ab578dd584f | OK |
| ReferenceCallChildBoundary.lean | 806047adc162c7a48cb857dfd01a04c3db8c95dec24d19a3719465797f2399ca | 806047adc162c7a48cb857dfd01a04c3db8c95dec24d19a3719465797f2399ca | OK |
| ReferenceChildMeter.lean | 884134ec10ea2ae16edbc2690d95b123eb1dad5d333f5f25bb6be033da29425f | 884134ec10ea2ae16edbc2690d95b123eb1dad5d333f5f25bb6be033da29425f | OK |
| ReferenceCallGrant.lean | 1582e1948d2d06cd15070f5a0211608ee36c8ca7c8b607b9b1b5080a60d3c323 | 1582e1948d2d06cd15070f5a0211608ee36c8ca7c8b607b9b1b5080a60d3c323 | OK |
| ReferenceMeterRollback.lean | 95c68aae475f9a0a5bfd94d23e32a4abbb97f995ec31900f3b402b631c549da1 | 95c68aae475f9a0a5bfd94d23e32a4abbb97f995ec31900f3b402b631c549da1 | OK |
| ReferenceMeterBoundary.lean | 7672cb249fd273e453fa65da26d30801ebb26ce89614b0088634b2168b871328 | 7672cb249fd273e453fa65da26d30801ebb26ce89614b0088634b2168b871328 | OK |

All six digests match exactly. Bundle receipt integrity confirmed.

## Conclusion

The new module `ReferenceNestedCallSettlement` cleanly extends
`ReferenceCallChildBoundary.completes` with a symmetric successful-case
pool accounting equation, packages the three-outcome uniform equation
around it, and exposes `finish` determinism as an ordinary
Option-injectivity fact. All three declarations use the same paid-child
domain as `completes` — no new premise, no new axiom, no proof of a
tautology. All proof steps trace against the frozen dependency
definitions (`init`, `settle`, `refill`, `incorporate`, `repay`,
`absorb`, `accounting`, `repay_accounting`). Axiom, bundle-hash and
scope-drift receipts are internally consistent, and the DIRECT-
CLOSURE.md prose matches the theorem statement.

VERDICT: CLEAN
