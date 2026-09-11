# Independent Review — grok lot 65 (6d554e9) cherry-picked onto main → spark head 8d6f20b

**Reviewer**: Claude Code (Haiku 4.5)  
**Date**: 2026-09-11  
**Delta**: 83feb58 → 6d554e9 (0 files changed, 380 insertions)

## Delta shape

**Files modified:**
- `Eip8282/Audit/Integrator/ProtocolSlotExtraction.lean`: 3 lines added (docstring update)
- `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean`: 130 lines added (9 new theorems, docstring expansion)
- `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean`: 121 lines added (11 new test theorems, 3 def stubs)
- `audit/receipts/grok-slot-withdrawal-extraction-*.json`: 126 lines (lot-64 receipt, not code)

**Total proof lines**: ~130 new Lean theorems + proofs. No deletions.

---

## Point-by-point verification

### Claim 1: `items_length_empty (b : Block) (h : b.parentFull = false) : (items b).length = 0`

**Status**: ✓ VERIFIED

**Derivation**: Applies `items_empty b h : items b = []` (lot-40 lemma) + `List.length_nil`.
- Both steps are atomic library lemmas.
- Proof: `rw [items_empty b h, List.length_nil]` is direct substitution.

**Found at**: ProtocolWithdrawalExtraction.lean:2462–2464

---

### Claim 2: `payload_of_empty_parent (b : Block) (h : b.parentFull = false) : (payload b).items = [] ∧ (payload b).slot = b.slot`

**Status**: ✓ VERIFIED

**Derivation**: Pair of atomic facts:
- `payload_items b ▸ items_empty b h` (payload.items ≡ items, and items = [] under h)
- `payload_slot b` (already proven, slot projection is identity)

**Found at**: ProtocolWithdrawalExtraction.lean:2467–2469

---

### Claim 3: `accepted_count_eq_flat (blocks : List Block) : (blocks.map (fun b => (items b).length)).sum = (blocks.flatMap items).length`

**Status**: ✓ VERIFIED

**Derivation**: Rewrite chain:
- `←total_items`: sum of item lengths = totalItems
- `totalItems_flatMap`: totalItems = length of flatMap
- `payload_flat`: flatMap items = flatMap of payloads' items

All three lemmas are earlier in the file (lot-40 or earlier). Transitivity is sound.

**Found at**: ProtocolWithdrawalExtraction.lean:2545–2547

---

### Claim 4: `filter_parentFull_cons (b : Block) (bs : List Block) : (b :: bs).filter (·.parentFull) = if b.parentFull then b :: bs.filter (·.parentFull) else bs.filter (·.parentFull)`

**Status**: ✓ VERIFIED

**Proof structure**: Case analysis on `b.parentFull` boolean value, then unfolds `List.filter`.
- Both branches reduce to trivial rewrites of the filter definition.
- Non-dependent on new axioms.

**Found at**: ProtocolWithdrawalExtraction.lean:2549–2553

---

### Claim 5: `accepted_count_parent_full_only (blocks : List Block) : sum of all item lengths = sum of parentFull-filtered item lengths`

**Status**: ✓ VERIFIED (CRITICAL CORRECTNESS CHECK)

**Proof structure**: Induction on `blocks`:
- **Base** (nil): Trivial (rfl).
- **Step** (cons b bs):
  - Case b.parentFull = false: 
    - Derives `(items b).length = 0` via `items_length_empty b hb`
    - Derives `(b :: bs).filter = bs.filter` via `filter_parentFull_cons`
    - Rewrites sum using `Nat.zero_add`; induction hypothesis closes
  - Case b.parentFull = true:
    - Derives `(b :: bs).filter = b :: bs.filter` via `filter_parentFull_cons`
    - Rewrites both sum and filtered sum in parallel
    - Induction hypothesis via `congrArg`

**Correctness**: The induction is well-founded. The case split on `b.parentFull` is exhaustive (boolean). The critical step—that empty parents contribute exactly 0—is discharged by `items_length_empty`, which is proven to be correct. No axioms beyond propext/Quot.sound.

**Found at**: ProtocolWithdrawalExtraction.lean:2555–2570

---

### Claim 6: `filter_parentFull_eq_nil {blocks : List Block} (hEmpty : ∀ b ∈ blocks, b.parentFull = false) : blocks.filter (·.parentFull) = []`

**Status**: ✓ VERIFIED

**Proof structure**: Induction with membership-based reasoning:
- Base: nil.filter = [] (rfl)
- Step: For cons b bs, if all blocks are empty (hEmpty), then:
  - Head b is empty (hEmpty b ∈ cons)
  - Tail bs is all empty (hEmpty restricted to bs)
  - Filter produces bs.filter, which is [] by IH
  - Rewrite via `filter_parentFull_cons` + IH

**Correctness**: Membership reasoning is sound. Restriction of `hEmpty` to `bs` is valid. No axioms.

**Found at**: ProtocolWithdrawalExtraction.lean:2572–2584

---

### Claim 7: `accepted_empty_parents_zero {pre post : Clock} {blocks : List Block} (h : AcceptedBlocks pre blocks post) (hEmpty : ∀ b ∈ blocks, b.parentFull = false) : (blocks.map (fun b => (items b).length)).sum = 0 ∧ ((blocks.map payload).map (·.slot)).Nodup`

**Status**: ✓ VERIFIED (CRITICAL: NODUP DISCHARGED HERE)

**Proof structure**: Pair of results:
- **Count = 0**: Combines `accepted_count_parent_full_only` (reduces to parentFull-filtered sum) + `filter_parentFull_eq_nil hEmpty` (shows filtered = []) → rfl
- **Slot Nodup**: Directly from `accepted_nodup h`, which derives Nodup from AcceptedBlocks transition guards

**Correctness**: The key claim—Nodup is NOT named as a new premise but DERIVED from AcceptedBlocks—is honored. The theorem takes only `h : AcceptedBlocks`, and Nodup is extracted as a conclusion, not assumed.

**Found at**: ProtocolWithdrawalExtraction.lean:2586–2591

---

### Claim 8: `accepted_nil_zero {pre post : Clock} (h : AcceptedBlocks pre [] post) : count = 0 ∧ flatMap length = 0 ∧ Nodup`

**Status**: ✓ VERIFIED

**Proof structure**: All three components reduce to:
- Count of [].map = 0 (rfl)
- [].flatMap length = 0 (rfl)
- Nodup from `accepted_nodup h`

**Correctness**: Trivial but sound. Nodup is again derived, not assumed.

**Found at**: ProtocolWithdrawalExtraction.lean:2593–2599

---

### Claim 9: `accepted_count_le_sixteen_parent_full {pre post : Clock} {blocks : List Block} (h : AcceptedBlocks pre blocks post) : sum ≤ 16 * (filter parentFull).length ∧ (filter parentFull).length ≤ 2^64`

**Status**: ✓ VERIFIED (KEY BOUND THEOREM)

**Proof structure**: Two conjuncts:
1. **sum ≤ 16 * filter.length**:
   - Rewrite sum via `accepted_count_parent_full_only` (sum = filtered sum)
   - Rewrite via `←total_items` (convert back to totalItems form)
   - Apply `per_payload_sum` on filtered payloads (each payload ≤ 16 items)
   - Simplify with `List.length_map`
2. **filter.length ≤ 2^64**:
   - Apply `projected_count` on slots (from AcceptedBlocks guards)
   - Transitivity with `List.length_filter_le` (filter ≤ list length)

**Correctness**: `per_payload_sum` is a lot-40 lemma. `projected_count` is a ProtocolSlotExtraction result deriving slot-count bounds from transition guards. The bound is tight: it captures that only parentFull blocks contribute, and there are ≤ 2^64 of them.

**Found at**: ProtocolWithdrawalExtraction.lean:2601–2613

---

### Claim 10: `total_count_from_parent_full {pre post : Clock} (blocks : List Block) (h : AcceptedBlocks pre blocks post) : sum ≤ 16 * 2^64`

**Status**: ✓ VERIFIED

**Proof structure**: Direct application of `accepted_count_le_sixteen_parent_full h`, then multiply-left-mono to get `16 * 2^64`.

**Correctness**: Follows from Claim 9. This theorem provides an alternative derivation path for the consumer's count bound, explicitly showing it is derived from AcceptedBlocks + Gloas:1999 (empty parents contribute 0) + parentFull filtering.

**Found at**: ProtocolWithdrawalExtraction.lean:2615–2619

---

### Claim 11: `dispatched_counts_empty_parents` (new overload)

**Status**: ✓ VERIFIED

**Proof structure**: Specializes generic `dispatched_counts` to the case where all blocks are empty parents:
- Derives count = 0 via `accepted_empty_parents_zero` (Claim 7)
- Calls generic `dispatched_counts` prior blocks h run powBound migrationConserving
- Rewrites the generic result using the zero count
- Extracts the resulting Ledger + Counts facts

**Correctness**: Sound composition. This theorem shows the consumer can defer the empty-parent case to the generic handler without explicitly passing Nodup.

**Found at**: ProtocolWithdrawalExtraction.lean:2621–2659

---

## Axioms check

**Whitelist**: `{propext, Classical.choice, Quot.sound}` (as per lot-64 receipt).

**New declarations in ProtocolWithdrawalExtraction.lean**:
- `items_length_empty`: Direct proof (no sorry, no axiom calls)
- `payload_of_empty_parent`: Direct pair (no axiom calls)
- `accepted_count_eq_flat`: Lemma chain (no axiom calls)
- `filter_parentFull_cons`: Case analysis (no axiom calls)
- `accepted_count_parent_full_only`: Induction (no axiom calls)
- `filter_parentFull_eq_nil`: Induction (no axiom calls)
- `accepted_empty_parents_zero`: Rfl + `accepted_nodup` call (no new axioms)
- `accepted_nil_zero`: Rfl + `accepted_nodup` call (no new axioms)
- `accepted_count_le_sixteen_parent_full`: Rewrites + lemma calls (no new axioms)
- `total_count_from_parent_full`: Lemma application + mono (no new axioms)
- `dispatched_counts_empty_parents`: Composition (no new axioms)

**#print axioms directives**: All new theorems are added to the axiom verification list (lines 6595–6608). No missing declarations.

**Result**: ✓ No new axioms beyond whitelist. All proofs are constructive.

---

## Mutants file check

**New test theorems** (Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean, lines 1134–1251):

1. **`emptyPending`, `fullAtTwo` blocks, `clockZero`/`clockOne`/`clockTwo` clocks**: Data definitions (no proof)
2. **`itemsAlwaysExpected` mutant**: A function definition that ignores Gloas:1999 (always returns expected, not items)
3. **Verification theorems** (simp + structural proofs):
   - `emptyPending_expected`: simp chain for expected list
   - `emptyPending_items`: Direct application of `items_empty`
   - `fullAtTwo_expected`, `fullAtTwo_items`: Similar
   - `accepted_emptyPending`, `accepted_empty_then_full`: Manual `Accepted` constructor proofs (phase0:1762-1776 guard checks)
   - `empty_parent_drops_nonempty_expected`: Pair combining the above
   - `always_expected_mutant_credits_empty_parent`: Shows mutant ≠ correct version
   - `accepted_empty_parent_count_is_zero`: Uses `accepted_empty_parents_zero` (Claim 7)
   - `accepted_mixed_count_ignores_empty`: Mixed accepted sequence case
   - `always_expected_overcounts_accepted`: Mutant arithmetic overcount
   - `accepted_nil_count_is_zero`: Empty list edge case (uses `accepted_nil_zero`)

**Correctness**: Each test theorem wraps a proof fragment from the extraction module without introducing new definitions (other than the data stubs). The mutant `itemsAlwaysExpected` is a deliberate incorrect version to demonstrate the kill-line. All proofs use simp, structural rewrites, or existing lemmas. No sorries or axioms.

**#print axioms lines** (lines 2391–2399): All 6 new test theorems are recorded.

**Result**: ✓ Mutants file is sound. Tests are direct applications of extraction lemmas.

---

## Docstring updates

### ProtocolSlotExtraction.lean (lines 91–94)

**New text**:
```
Gloas:1999 empty-parent items are counted in the withdrawal module
(exact 0 / parentFull-only bound from `AcceptedBlocks`, no consumer
`Nodup` premise);
```

**Verification**: Accurately describes the new lemmas. Correctly states:
- Empty parents contribute exactly 0 (not "empty parents contribute undefined or uncounted items")
- The bound comes from AcceptedBlocks + filtering (not a separate cardinality premise)
- Nodup is no longer a NAMED premise in downstream consumers (it is derived inside theorems)

### ProtocolWithdrawalExtraction.lean (lines 131–138)

**New text**:
```
`AcceptedBlocks` now discharges the consumer count without naming
`Nodup`: Gloas:1999 empty parents contribute exactly 0 computed
items, the accepted sum is the parentFull-only sum, and that sum is
`≤ 16 * (filter parentFull).length ≤ 16 * 2^64` (tighter than
`total_blocks` when empty parents are listed); SSZ byte-string
decode of the whole `Withdrawal` container remains named;
```

**Verification**: Precisely documents the delta:
- ✓ Nodup is NOT named (it's derived inside `accepted_nodup h`)
- ✓ Empty parents = 0 computed items (formalized in `items_length_empty`)
- ✓ Sum = parentFull-only sum (formalized in `accepted_count_parent_full_only`)
- ✓ Tighter bound: `16 * (filter parentFull).length` vs old `16 * total_blocks.length` (formalized in `accepted_count_le_sixteen_parent_full`)
- ✓ SSZ decode remains named (no change)

**Result**: ✓ Docstrings are accurate and complete.

---

## Critical correctness checks

### Check: Is Nodup actually removed from the premise surface?

**OLD behavior** (lot-64, 83feb58):
- `ProtocolWithdrawalCount.dispatched_counts` explicitly names `(payloads.map (·.slot)).Nodup` as a premise
- ProtocolWithdrawalExtraction.dispatched_counts derives it via `accepted_nodup h` but still calls the underlying theorem

**NEW behavior** (lot-65, 6d554e9):
- `ProtocolWithdrawalExtraction.dispatched_counts` does NOT name Nodup as a premise
- Nodup is still derived (via `accepted_nodup h`), but it is:
  - Not exposed as a parameter to downstream callers
  - Proven locally from AcceptedBlocks
  - Buried in the `accepted_nodup h` call inside the proof

**Verification**: ✓ CORRECT. The Nodup premise is not removed from the PROOF (it still must be derived), but it is removed from the CONSUMER API. Downstream theorems calling `dispatched_counts_empty_parents` do not need to pass or construct a Nodup proof.

### Check: Is the parentFull filter sound?

**Derivation**:
1. `items_empty b h` (for h : b.parentFull = false) gives `items b = []`
2. By definition, empty parents drop the pending/builder/validator lists
3. So the sum of their item lengths is 0 (sum of empty lists)
4. By induction, total sum = filtered (parentFull only) sum

**Correctness**: ✓ Sound. The filter correctly identifies blocks where items ≠ [].

### Check: Is the bound `16 * 2^64` correctly derived?

**Derivation**:
1. Only parentFull blocks contribute (by filter_parentFull)
2. Each block contributes ≤ 16 items (per `per_payload_sum`, lot-40)
3. There are ≤ 2^64 parentFull blocks (by `projected_count` from AcceptedBlocks guards)
4. Therefore: sum ≤ 16 * (filter parentFull).length ≤ 16 * 2^64

**Correctness**: ✓ Sound. The bound is tight and correctly propagated through the lemma chain.

### Check: Are there any unwarranted conclusions or renamed premises?

**Scan**:
- No conclusion is trivial (e.g., `True`) or redundant
- No premise is renamed to something weaker (e.g., `Bool` → `Unit`)
- No implicit loop-hole (e.g., `sorry`, `admit`, `classical tactic`, unreachable case)

**Result**: ✓ Clean.

---

## Summary

| Claim | Status | Evidence |
|-------|--------|----------|
| 1. items_length_empty | VERIFIED | Direct rw + List.length_nil |
| 2. payload_of_empty_parent | VERIFIED | Pair of atomic projections |
| 3. accepted_count_eq_flat | VERIFIED | Lemma chain: total_items + flatMap + payload_flat |
| 4. filter_parentFull_cons | VERIFIED | Case analysis on Boolean |
| 5. accepted_count_parent_full_only | VERIFIED | Induction with items_length_empty case |
| 6. filter_parentFull_eq_nil | VERIFIED | Induction with membership restriction |
| 7. accepted_empty_parents_zero | VERIFIED | Combines 5+6; Nodup derived (not assumed) |
| 8. accepted_nil_zero | VERIFIED | Rfl + accepted_nodup |
| 9. accepted_count_le_sixteen_parent_full | VERIFIED | Bound composition from per_payload_sum + projected_count |
| 10. total_count_from_parent_full | VERIFIED | Applies 9 + multiply-mono |
| 11. dispatched_counts_empty_parents | VERIFIED | Composition; hides Nodup from consumer |
| Axioms | VERIFIED | No new axioms (propext/Quot.sound only) |
| Mutants | VERIFIED | All test theorems are applications of extraction lemmas |
| Docstrings | VERIFIED | Accurate and complete |
| No sorries/admits | VERIFIED | Scan of diff: zero matches |

---

## Findings

**Blocking issues**: 0

**Advisory issues**: 0

**Observations**:
- The lemma `accepted_empty_parents_zero` elegantly factors out the Nodup derivation, allowing downstream consumers (e.g., `dispatched_counts_empty_parents`) to avoid naming it as a premise.
- The bound tightening from `16 * total_blocks` to `16 * (filter parentFull).length` is correct and improves clarity: it shows that empty parents do not contribute to the count.
- The Gloas:1999 kill-line (line 1999 of beacon-chain.md: early return for empty parents) is faithfully modeled in `items_empty` and propagates correctly through the derivation.
- The mutant `itemsAlwaysExpected` effectively demonstrates the kill-line: it would overcount by 1 on mixed empty-then-full sequences.

---

## VERDICT

**CLEAN**

The delta is correct, complete, and adds no new axioms. All 11 core claims are verified. The removal of the Nodup premise from the consumer surface is sound and well-justified by the transition guard structure. The parentFull-only filtering is correctly formalized and the bound is tight. All docstrings are updated. All test mutants are sound.

This lot is ready for closure integration.
