# Independent review — grok delta lot 36 (4499b78..721be31)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Delta base: 4499b787a155ff1ec3d1d6d42c7c47d5d80b7490
Delta head: 721be3140dc49a440f90f551d11d623637f86bfc
Branch: origin/grok/eip-slot-withdrawal-extraction-20260911
Started at: 2026-09-11T12:54:56Z

## Scope items reviewed
- Sorry/admit scan of both modified Lean files (in-diff and full file at head)
- Axiom drift sample on 3+ new declarations via `#print axioms` block appended in extraction
- Scope: exactly 3 files touched (2 Lean + 1 receipt); no parallel framework
- Pinned receipt provenance (filename encodes proof commit; base/previous-lot hashes; toolchain)
- New mutants (5) audited for non-trivial kill lines
- Commit message accuracy for `2414eb1` — "bind Gwei wrap vs Lean saturate on excess"
- Docstring / OPEN-list narrative alignment with new theorems

## Findings
1. Zero `sorry`/`admit` tactic uses in either modified file. The two `admit` hits in
   `ProtocolWithdrawalExtraction.lean` at lines 4954 and 5174 are docstring prose
   ("admit only when every conjunct holds", "engine admit"), not tactics — and both
   are outside the delta hunks (pre-existing).
2. Scope respected: `git diff --name-only` returns exactly 3 files, all under
   `Eip8282/Audit/Integrator/`, `Eip8282/Tests/`, and `audit/receipts/`. No wiring,
   Makefile, Trust/YAML, DIRECT-CLOSURE, SYSTEM/block, gas, or history module was
   touched. Receipt explicitly declares `wiring_not_applied`.
3. Commit-message honesty verified for `2414eb1`: `gweiWrapSub` is introduced as a
   *distinct* definition modelling Python `Uint64` two's-complement borrow
   (`(b%M + M - w%M) % M` with `M = 2^64`). It is NOT installed as the semantics of
   `balanceAfterWithdrawals`, which remains `balance - withdrawnAmount` (Lean
   saturate). The pair is bound by:
     - `decreaseBalance_ne_gweiWrap` (excess: sat = 0, wrap > 0)
     - `balanceAfter_eq_wrap_of_fits` (agreement *only* under `BalanceAfterFits`)
     - `gweiWrapSub_ne_sub_of_gt` (refutation without fits)
   The receipt's `not_claimed` explicitly lists "Python Gwei wrap as the Lean
   applyTagged path (Lean saturates)". No adoption. The updated OPEN comment
   (lines 104-113 of the file at head) is consistent: "`BalanceAfterFits` is that
   Python agreement, not a Lean fold identity".
4. `apply_eq_balanceAfter_sat` establishes the fold identity unconditionally
   (Nat.sub associativity), independent of `BalanceAfterFits`, and the accompanying
   docstring is careful to note that `BalanceAfterFits` is not this identity.
5. Mutant kill-lines are all substantive: a concrete `2^64-2` witness bound to the
   pre-existing `decrease_not_u64_wrap` kill-line, a saturate-vs-wrap disequality,
   the unconditional fold identity on excess, refutation of wrap agreement without
   fits, and agreement under fits. None are `by trivial`-shaped rfl-ish placeholders.
6. Receipt provenance: filename `grok-slot-withdrawal-extraction-2414eb1a...json`
   correctly encodes the proof commit `2414eb1a8e9e0d0b331df37f1452c412c7363aba`.
   `previous_lot.receipt = 4499b787...` matches the delta base. Toolchain pinned
   (Lean 4.31.0, commit 68218e876...). Archived body SHA-256s carried forward.
7. Note (informational, not a blocker): `specs/capella/beacon-chain.md` and
   `specs/gloas/beacon-chain.md` cited in the extraction/receipt are not present
   in the working tree — the receipt pins them by SHA-256 rather than checking
   them in, which is the project's established pattern.

## Axiom audit (sample)
Per the receipt's `axioms.new_in_this_lot` and the `#print axioms` block appended
to the extraction file:
- `gweiWrapSub_eq_sub` — `[propext]`
- `gweiWrapSub_of_gt` — `[propext, Quot.sound]`
- `balanceAfter_eq_wrap_of_fits` — `[propext]`
- `apply_eq_balanceAfter_sat` — `[propext]`
- `apply_ne_wrap_of_gt` — `[propext, Quot.sound]`
No `sorryAx`. No project axiom. Only Lean core `propext` / `Quot.sound` (whitelist
consistent with earlier lots and with the pre-check `lake build` axiom sample).

## Bundle/receipt provenance sample
`audit/receipts/grok-slot-withdrawal-extraction-2414eb1a8e9e0d0b331df37f1452c412c7363aba.json`:
- `classification: compiled_additive_extraction_not_adoption_not_guarantee_closure`
- `lot: 36`, `branch: grok/eip-slot-withdrawal-extraction-20260911`
- `commit: 2414eb1a...` (matches filename)
- `previous_lot.receipt: 4499b787...` (matches delta base)
- `commands` include `lake build` (exit 0) on the two touched Lean modules and
  `make check` (exit 0, "Build completed successfully (3608 jobs)")
- `not_claimed` includes protocol-adoption denial and the Python-wrap-as-Lean-path
  denial that the commit message implies

## Conclusion
The delta is a compiled additive extraction. It adds a Python `Uint64` wrap model
(`gweiWrapSub`) purely to *bind* the excess-case discrepancy with the Lean
saturating `Nat.sub` semantics used by `balanceAfterWithdrawals` /
`decreaseBalance`. Nowhere is the wrap installed as Lean's protocol semantics; on
the contrary, agreement is proved conditional on the named `BalanceAfterFits`
hypothesis and refuted without it. No sorry/admit, axioms within whitelist, scope
strictly limited to two Lean files and one receipt, mutants are non-trivial, and
the receipt cleanly pins commit / base / toolchain / archived-body hashes. No
parallel framework introduced. Commit-message claim is accurate.

VERDICT: CLEAN
