# Independent review — grok delta lot 39 (4c9dafc..7147aec)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Delta base: 4c9dafc
Delta head: 7147aec
Branch: origin/grok/eip-slot-withdrawal-extraction-20260911
Started at: 2026-09-11T13:17:39Z

## Scope items reviewed
- Sorry/admit sweep across the two modified `.lean` files (regex `\bsorry\b|\badmit\b|sorryAx`).
- Axiom drift: sample of new declarations (`builderFlagNotU64`, `builderFlagNotU64_lt`, `land_flag_eq_ite`, `toBuilderIndex_eq_u64_of_clear`, `toBuilderIndex_two_pow_ne_u64`); grep for `^axiom `/`native_decide`.
- Scope respected: `git diff --name-only 4c9dafc..7147aec` returns exactly 3 files (2 source + 1 receipt).
- Pinned reference correctness: receipt `grok-slot-withdrawal-extraction-ced710827ad9a42a35a4830259aed155502f6fcd.json` SHAs vs disk at 7147aec.
- Non-trivial mutant kill lines in `ProtocolSlotWithdrawalMutants.lean`.
- Commit message ced7108 accuracy: "bind Uint64 ~FLAG of toBuilderIndex".
- No parallel framework (delta touches only existing `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean` and `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean`).

## Findings
1. `sorry`/`admit` — zero occurrences in production or test at 7147aec. The five surviving `admit` hits in `ProtocolWithdrawalExtraction.lean` and the five in `ProtocolSlotWithdrawalMutants.lean` are all either the semantic word "admit" inside docstrings/comments (engine-admit rule, "not admitted") or field accessors `.admits` on `EngineChecks` — none are the Lean `admit` tactic. No `sorryAx`.
2. Axiom drift — no `axiom` keyword introduced. New theorems recorded in the receipt list only `propext`, `Classical.choice`, `Quot.sound` (some just `propext`, matching `decide`-closed goals). No `native_decide`; no `Trust.lean` edit.
3. Scope respected — exactly 2 source files + 1 new receipt file touched. Makefile, YAML, DIRECT-CLOSURE.md, other Integrator modules and Block/gas/history modules untouched (also explicitly disclaimed under `wiring_not_applied` in the receipt).
4. Bundle-SHA provenance — recomputed SHAs of the three files at 7147aec via `git show 7147aec:<path> | sha256sum`. All three (`30a457c4…`, `3ee4b4be…`, `e4098a51…`) match the receipt exactly. Toolchain `leanprover/lean4:v4.31.0` is consistent with the branch's prior lots.
5. Non-trivial mutants — the four new theorems in `ProtocolSlotWithdrawalMutants.lean` (`flag_u64_not_clears_bit_40`, `two_pow_and_not_ne_u64`, `two_pow_u64_and_not_is_zero`, `small_validator_and_agrees_u64`) each pin distinct observable content: bit-40 clear on the U64 complement, an explicit disagreement at `v = 2^64` between the Lean `Nat` subtract and the Python wrap, the wrap-to-zero at `2^64`, and agreement on both `3` and `FLAG` under U64. None are `True`/tautological.
6. Commit message ced7108 accuracy — the commit message reads "bind Uint64 ~FLAG of toBuilderIndex". The delta introduces `builderFlagNotU64 := (GWEI_MOD - 1) ^^^ BUILDER_INDEX_FLAG` and `toBuilderIndexU64 v := (v % GWEI_MOD) &&& builderFlagNotU64` as *new* Uint64-mirroring names, keeping the original `toBuilderIndex` (Nat subtract) unchanged. The disagreement at `v ≥ 2^64` is explicitly proved (`toBuilderIndex_two_pow_ne_u64`), and the receipt's `not_claimed` list rules out "Python Uint64 & ~FLAG as the Lean unbounded subtract path when v ≥ 2^64". Uint64 semantics are demonstrated as a named alternative, not adopted as `toBuilderIndex`'s meaning. The docstring at lines 703-707 accurately labels the two branches.
7. No parallel framework — the delta reuses existing modules and follows the already-established `_U64` naming used earlier in the file for `toValidatorIndex` (see `toValidatorIndexU64` at prior lots). No new directories, no new frameworks, no re-declared root definitions.
8. Receipt hygiene — `previous_lot` correctly cites `4c9dafc`; `base.sha` `681d186…` matches the current `main`-side head. `named_hypotheses_still_open` list appropriately includes the set-bit identity `v ^^^ FLAG = v - FLAG` (needed to close the remaining ∀), matching the docstring at 703-707. `not_claimed` explicitly disclaims P-SUBMIT-1 / P-DRAIN-1 / P-CONTROL-1 closure, adoption, canonical history, SSZ injectivity.

## Axiom audit (sample)
- `builderFlagNotU64_lt`: receipt lists `{propext, Classical.choice, Quot.sound}`. Proof uses `Nat.xor_lt_two_pow` + `Nat.sub_lt` — standard Mathlib lemmas; classical choice enters via decidability instance packaging. Plausible.
- `builderFlagNotU64_testBit_40`: `{propext}` only. Proof is `unfold … ; decide` — kernel `decide` on concrete `Nat` bit; consistent.
- `land_flag_eq_ite`: `{propext, Quot.sound}`. `Nat.eq_of_testBit_eq` + case split on `testBit v 40`; no unexpected axioms.
- `toBuilderIndex_eq_u64_of_clear`: `{propext, Classical.choice, Quot.sound}`. Uses `Nat.and_two_pow_sub_one_of_lt_two_pow`; consistent with prior `toValidatorIndex_eq_u64_of_lt` axiom footprint.
- `toBuilderIndex_two_pow_ne_u64`: `{propext}`. Two `unfold`+`decide` calls chained by `rw`; matches the decidable path.

## Bundle/receipt provenance sample
- `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean` @ 7147aec → `30a457c4156ae41f700bbac5089176703c9752a96fe381a7a0aec6f3b74cd0ca` (matches receipt `files_sha256`).
- `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean` @ 7147aec → `3ee4b4be0828640da08971692b346c27743399002d8c76196b6d6f7f7a88d89f` (matches).
- `Eip8282/Audit/Integrator/ProtocolSlotExtraction.lean` @ 7147aec → `e4098a51875e742472c5ed0bd8850d1270764c262064b8d990409488d2bc275a` (matches; unchanged in this delta, sensibly still listed in scope because it declares `toValidatorIndex` peers).
- Toolchain SHA `68218e876d2a38b1985b8590fff244a83c321783` and Lean `4.31.0` consistent with prior grok lots.

## Conclusion

The delta from `4c9dafc` to `7147aec` (proof commit `ced7108`, receipt commit `7147aec`) is a clean, additive extraction lot. It introduces a Uint64-mirroring `builderFlagNotU64`/`toBuilderIndexU64` pair, proves agreement with the existing `Nat`-subtract `toBuilderIndex` on the flag-clear `Uint64` domain, and produces an explicit counterexample at `v = 2^64` demonstrating that the Python semantics are *not* adopted as the Lean definition. Four mutant kill-lines in `ProtocolSlotWithdrawalMutants.lean` pin distinct observable content. No `sorry`/`admit`/axiom keyword appears. All three file SHAs recorded in the receipt match the byte content at 7147aec, and axioms are confined to `{propext, Classical.choice, Quot.sound}`. The receipt correctly labels the remaining set-bit identity, SSZ decode, P-SUBMIT-1/P-DRAIN-1/P-CONTROL-1 closure, canonical history and adoption as OPEN. Commit message `ced7108` accurately describes the change: it binds `Uint64(~FLAG)` semantics as a named companion without redefining `toBuilderIndex`. No parallel framework and no scope drift.

VERDICT: CLEAN
