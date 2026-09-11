# Independent review — grok delta lot 40 (7147aec..ec15c4b)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Delta base: 7147aec
Delta head: ec15c4b
Branch: origin/grok/eip-slot-withdrawal-extraction-20260911
Started at: 2026-09-11T13:22:53Z

## Scope items reviewed
- Sorry/admit sweep on both modified `.lean` files (only lot-40 additions region).
- Axiom drift on the 6 new theorems (5 pure, 1 wrapper) + 2 new mutants.
- File-touch discipline: 3 files (2 sources + 1 new receipt).
- Receipt provenance for `audit/receipts/grok-slot-withdrawal-extraction-d5499b21c18f1a6d78f313c3be6ab94763770701.json` — SHA256 pins, base sha, previous-lot chain, commands.
- New mutant kill-lines in `ProtocolSlotWithdrawalMutants.lean`.
- Accuracy of commit `d5499b2` message vs the actual identity: XOR agrees with subtract only within `Uint64` (v < 2^64) domain; wrap kill-line preserved.
- Absence of any parallel proof framework.

## Findings
1. No `sorry` and no `admit` tactic in the newly added regions. The two grep hits on the head files match unrelated pre-existing docstring text and a field/method identifier `admits`, not tactic usage.
2. Diff scope is exactly the three declared files (`git diff --name-only` confirmed). No cross-contamination into gas, nested calls, canonical history, SYSTEM/block modules, Makefile, YAML, Integrator wiring, or DIRECT-CLOSURE.
3. File SHA256 pins in the receipt match the tree at `ec15c4b`: `ProtocolWithdrawalExtraction.lean` → `4fd26df5...`, `ProtocolSlotWithdrawalMutants.lean` → `39ec5fc4...`, both verified byte-for-byte.
4. Receipt base sha `681d1866...` matches `main` HEAD at review time; `previous_lot.receipt` `7147aeca...` matches the delta base commit. Chain is unbroken.
5. Commit message `d5499b2` "bind set-bit XOR vs subtract on toBuilderIndex" accurately describes: (a) `xor_flag_eq_sub_of_flag_bit` proves `v ^^^ FLAG = v - FLAG` under `v.testBit 40 = true`; (b) `toBuilderIndex_eq_u64_of_lt` extends the `Uint64` agreement lemma to include the set-bit branch, closing the previously flag-clear-only theorem. The XOR/subtract identity is *demonstrated* as an equality inside `Uint64` and *bound* to the `Uint64` corridor — it is *not* adopted as a rewrite of `toBuilderIndex` at the unbounded level. The wrap kill-line `toBuilderIndex_two_pow_ne_u64` at `v = 2^64` still stands, matching the receipt's `not_claimed` list and the docstring update that removed the "remains named" clause.
6. The two new mutants exercise the new theorems non-trivially:
   - `flag_xor_flag_is_sub` uses `xor_flag_eq_sub_of_flag_bit (by decide)` — demonstrates the identity applied to `FLAG` itself (both sides degenerate to 0, but the type-level equation names the XOR-vs-subtract bridge at the pinned constant).
   - `flag_plus_three_and_agrees_u64` uses `toBuilderIndex_eq_u64_of_lt` on `FLAG + 3`, exercising the *set-bit* branch of the new agreement lemma (this input has bit 40 set and is well within `2^64`), a kill-line that would fail if XOR/subtract disagreed under `Uint64`.
7. No parallel framework, no new axioms, no new opaques, no imports touched by the diff. Existing `#print axioms` block appended six new declarations; the receipt claims dependence only on `propext`/`Classical.choice`/`Quot.sound`, which is consistent with a standard Lean 4 `Nat`-bitblast proof and with the pre-check `lake build ... 1221 jobs OK`.

## Axiom audit (sample)
Sampled 3 new declarations by inspecting proofs:
- `split_of_flag_bit`: pure `Nat` arithmetic — `Nat.testBit_eq_decide_div_mod_eq`, `Nat.div_div_eq_div_mul`, `Nat.pow_succ`, `Nat.div_add_mod`, `Nat.mul_add`. No axioms beyond Lean core; matches receipt claim `[propext, Quot.sound]`.
- `xor_two_pow_of_flag_bit`: `Nat.eq_of_testBit_eq` + bitwise lemmas (`Nat.testBit_xor`, `Nat.testBit_or`, `Nat.testBit_mul_two_pow`, `Nat.testBit_two_pow`, `Nat.testBit_lt_two_pow`, `Nat.testBit_mod_two_pow`) and the split-plus-lt-implies-or lemma `Nat.two_pow_add_eq_or_of_lt`. Standard Mathlib/stdlib. Matches receipt.
- `toBuilderIndex_eq_u64_of_lt`: reduces via `by_cases hv : v.testBit 40` into (set-bit) rewrite through `toBuilderIndex_of_flag_bit` + `toBuilderIndexU64_of_lt` + `xor_flag_eq_sub_of_flag_bit`, and (clear-bit) delegation to `toBuilderIndex_eq_u64_of_clear`. The extra `Classical.choice` in the receipt is expected from `by_cases`. Consistent.

No project axiom, no `sorryAx`, no `Nat.<something>_ax` fabricated names — dependencies stay in Lean core.

## Bundle/receipt provenance sample
Sample: `audit/receipts/grok-slot-withdrawal-extraction-d5499b21c18f1a6d78f313c3be6ab94763770701.json`.
- `commit: d5499b21...` — matches `HEAD~1` on the branch (`d5499b2 proof: bind set-bit XOR vs subtract on toBuilderIndex`), i.e. the receipt was recorded at ec15c4b for the proof-content commit as required.
- `toolchain.lean_version: 4.31.0` — matches project floor.
- `commands`: two `lake build` invocations, three `lake env lean` per-file checks, plus `make check` with tail `Build completed successfully (3608 jobs).` All exit 0.
- `scope`: 4 entries (three source paths + this receipt). The `ProtocolSlotExtraction.lean` entry is listed under scope but is not in the delta diff (unchanged). SHA lines confirm the two edited files and their hashes; the `ProtocolSlotExtraction.lean` scope inclusion is descriptive of the closure line the lot serves.
- `wiring_not_applied` explicitly disclaims Integrator/Trust/Makefile/DIRECT-CLOSURE edits — consistent with the diff.
- `not_claimed` disclaims Python `Uint64 & ~FLAG` as the unbounded Lean subtract path when `v ≥ 2^64`, which is exactly the semantics preserved by the retained `toBuilderIndex_two_pow_ne_u64` kill-line and the docstring change.

## Conclusion
The delta cleanly extends the `Uint64`-domain agreement lemma with a set-bit branch by proving the bit-40 XOR/subtract identity, adds two matching mutants (a self-XOR degenerate case plus a `FLAG + 3` set-bit case), and updates a docstring/`#print axioms` block. Scope is limited to two source files and one new receipt; the receipt's file-hash pins verify byte-exactly against the tree, base and previous-lot pointers form an unbroken chain from `681d186`, and the axiom claim is consistent with the sampled proofs. The XOR-equals-subtract identity is demonstrated and used only inside `v < 2^64`; the unbounded wrap kill-line at `v = 2^64` remains, so the delta is not adopting the Python semantics at the unbounded level. No sorry/admit, no new axioms, no parallel framework, and the pre-check `lake build ProtocolWithdrawalExtraction ProtocolSlotWithdrawalMutants` succeeded with 1221 jobs.

VERDICT: CLEAN
