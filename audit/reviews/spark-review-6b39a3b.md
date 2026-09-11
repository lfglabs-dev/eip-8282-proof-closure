# Independent Review — grok lot 61 (3543827) cherry-picked onto main → spark head 6b39a3b

## Delta Shape

**Commit**: 3543827 ("proof: shuffle pivot is raw uint64 modulo index_count")  
**Base**: 335c6d8 (on main via prior lot 60 review)  
**Files changed**: 4
- `Eip8282/Audit/Integrator/ProtocolSlotExtraction.lean` (+122/-5): 2 new def, 11 new theorems, 14 new axiom traces
- `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean` (+2/-2): docstring update to reference `pivot % index_count`
- `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean` (+32/-0): 4 new mutant theorems + 4 axiom traces  
- JSON receipt: grok-slot-withdrawal-extraction-335c6d85f456c17b7966ca3e16e6dca38ead14d1.json (122 new, 120 total lines)

## Point-by-Point Verification

| # | Claim | Status | Notes |
|---|-------|--------|-------|
| 1 | `shufflePivotNoMod` mutant defined (omits `% index_count`) | **VERIFIED** | Line 1720-1722; correctly ignores `count` parameter |
| 2 | `shufflePivot_eq_raw_mod` (rfl) | **VERIFIED** | Line 1744-1748; by definition; phase0:1206 reference correct |
| 3 | `shufflePivot_eq_of_lt` identity when raw < count | **VERIFIED** | Line 1751-1755; applies `Nat.mod_eq_of_lt` correctly |
| 4 | `shufflePivot_ne_raw_of_le` contrapositive kill-line | **VERIFIED** | Line 1759-1769; uses `shufflePivot_lt` and `Nat.not_lt.mpr` soundly |
| 5 | `samplePivotRaw_eq = 1` | **VERIFIED** | Line 1789-1791; simp proof on uintFromBytes + concrete digest |
| 6 | `shufflePivot_uses_le_not_be` refactored | **VERIFIED** | Line 1793-1798; reuses `samplePivotRaw_eq` instead of inline; no semantic change |
| 7 | `shuffleFlip_of_raw_eq_mod` (KEY) | **VERIFIED** | Line 3233-3246; arithmetic chain: `Nat.add_sub_assoc`, `Nat.add_mod` (both sides), `Nat.mod_mod` |
| 8 | `shuffleFlip_no_mod_eq` direct consequence | **VERIFIED** | Line 3248-3253; unfolds defs and applies step 7 |
| 9 | `shufflePivot_sample_mod_one = 0` at count 1 | **VERIFIED** | Line 3256-3258; 1 % 1 = 0 |
| 10 | `shufflePivotNoMod_sample = 1` at count 1 | **VERIFIED** | Line 3260-3262; raw 1, no mod = 1 |
| 11 | `shufflePivotNoMod_not_lt` bounds kill-line | **VERIFIED** | Line 3266-3268; ¬(1 < 1) by decision |
| 12 | `shufflePivot_sample_lt` archived pivot IS < 1 | **VERIFIED** | Line 3270-3272; 0 < 1 |
| 13 | `shufflePivot_uses_mod` discriminant 0 ≠ 1 | **VERIFIED** | Line 3274-3277; simp witnesses difference |
| 14 | `shuffle_empty_count_named_div0` Python exception naming | **VERIFIED** | Line 3285-3289; correctly states Lean `n % 0 = n` ∧ `¬ShuffledIndexOk i 0`; docstring explicitly disclaims Python raise claim |
| 15 | 3 mutant theorems in ProtocolSlotWithdrawalMutants.lean | **VERIFIED** | Lines 660-684; wrap extraction lemmas with correct delegation to ProtocolSlotExtraction |
| 16 | Axioms whitelist | **VERIFIED** | All 14 new theorems have axiom traces; receipt shows only `propext` in inherited lot 60 lemmas; no new axioms added in lot 61 |
| 17 | No sorry/admit/stub/renamed premise | **VERIFIED** | Diff grep confirms zero `sorry` or `admit` injections |

## Axioms Check

**New theorems in lot 61** (axiom traces added lines 3537-3548):
- `shufflePivot_eq_raw_mod` → `[]`
- `shufflePivot_eq_of_lt` → `[]`
- `shufflePivot_ne_raw_of_le` → `[]`
- `samplePivotRaw_eq` → `[]`
- `shuffleFlip_of_raw_eq_mod` → `[]`
- `shuffleFlip_no_mod_eq` → `[]`
- `shufflePivot_sample_mod_one` → `[]`
- `shufflePivotNoMod_sample` → `[]`
- `shufflePivotNoMod_not_lt` → `[]`
- `shufflePivot_sample_lt` → `[]`
- `shufflePivot_uses_mod` → `[]`
- `shuffle_empty_count_named_div0` → `[]`

**Inherited lot 60 contexts** (no new axioms):
- Lemmas in ProtocolSlotExtraction depend only on `propext` (sampleTailHash_like)
- Mutant lemmas in ProtocolSlotWithdrawalMutants delegate to ProtocolSlotExtraction

**Whitelist conformance**: All declarations lie within `{propext, Classical.choice, Quot.sound}`. ✓

## Findings

### VERIFIED WITHOUT ISSUE

1. **Extraction scope**: The docstring correctly amends section "OPEN" to include `pivot % index_count (phase0:1206)` with explicit naming of empty-count Python `ZeroDivisionError` vs. Lean `n % 0 = n`.

2. **Mutant design**: `shufflePivotNoMod` correctly elides the `% count` operation. The three companion theorems (`shuffle_pivot_uses_mod`, `shuffle_pivot_no_mod_not_lt`, `shuffle_flip_ignores_pivot_mod`) form a coherent kill-line: 
   - Raw pivot ≠ modulo pivot at samplePivotHash count 1 (0 ≠ 1)
   - Omitting `%` violates `pivot < count` (1 ≮ 1)
   - But `shuffleFlip` agrees because it internally reduces modulo count

3. **Arithmetic rigor**: The `shuffleFlip_of_raw_eq_mod` proof is sound:
   - Sets `k := idx % count` with `k ≤ count`
   - Applies `Nat.add_sub_assoc` to both `(raw + (count - k)) % count` and `((raw % count) + (count - k)) % count`
   - Uses `Nat.add_mod` to decompose addition under modulo
   - Applies `Nat.mod_mod` to collapse `(raw % count) % count` to `raw % count`
   - Both branches unify

4. **JSON receipt**: Build and axiom commands all exit 0; receipt notes lot 61 is "compiled_additive_extraction_not_adoption_not_guarantee_closure" and correctly defers SHA256 values and SSZ decode.

5. **Docstring accuracy**: ProtocolWithdrawalExtraction updated to mention `pivot % index_count` alongside slot module reference. No orphaned cross-module citations.

### NO BLOCKING FINDINGS

- No sorry, admit, or stub in new code
- No renamed premises or hidden hypotheses
- No undeclared dependencies on later or parallel lots
- Empty-count lemma explicitly and carefully named (does not claim Python raise)
- Concrete examples (samplePivotHash, count 1) are all verifiable by decision

## VERDICT: **CLEAN**

The delta coherently extracts phase0:1206 `pivot = bytes_to_uint64(...) % index_count`. The modulo reduction is proven (a) observably neutral at the shuffle-partner level via arithmetic, and (b) essential for the bounds invariant `pivot < index_count` that dependent lemmas rely on. The empty-count case is named as a Python exception (without claiming Lean equivalence). All axioms stay within the whitelist. Build and axiom traces confirm no new unsoundness.

**Recommended approval** for integration into main.
