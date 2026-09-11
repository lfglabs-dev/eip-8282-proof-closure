# Independent Review — grok lot 49 (3257937) cherry-picked onto main → spark head b13d04e

**Reviewer**: Independent exact reader
**Reviewed commit**: 3257937f3f9d56ffdfbf2638e16d556ffd133e62
**Base commit (prior lot 48)**: c4253ed (origin/main)
**Target branch**: spark/eip-grok-lot49-to-main-20260911 at b13d04e590992038e052e92e62f897014a25994d
**Scope**: Phase0 `compute_shuffled_index` extraction (assert, identity init, 90-round bookkeeping, flip involution)
**Extraction hypothesis**: Pivot and swap-bit digests remain uninterpreted; SHA256 values uninterpreted

---

## Delta Shape

Three files modified, 201 net additions:
- `Eip8282/Audit/Integrator/ProtocolSlotExtraction.lean`: +159 lines (extraction module)
- `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean`: +15 lines (docstring updates)
- `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean`: +36 lines (6 mutant test wrappers)
- JSON receipt: +119 lines (metadata)

**Build status**: Successful (lake build 3675 jobs)

---

## Point-by-Point Verification

1. **Round count constant** (phase0:588) `SHUFFLE_ROUND_COUNT = 90` ✓
   - Definition at 1508: `def SHUFFLE_ROUND_COUNT : Nat := 90`
   - Identity proof 1510-1511: `shuffleRoundCount_eq : SHUFFLE_ROUND_COUNT = 90 := rfl`
   - Mutant 1513-1515: `shuffleRoundCount_ne_hash32 : SHUFFLE_ROUND_COUNT ≠ HASH32_BYTES := by decide`
   - Axioms: none (rfl, decide)

2. **Assert** (phase0:1230) `ShuffledIndexOk index count := index < count` ✓
   - Definition 1530-1531: standard Prop wrapper
   - Rejection at equality 1533-1535: via `Nat.lt_irrefl`
   - Rejection at zero 1537-1539: via `Nat.not_lt_zero`
   - Axioms: none

3. **Identity init** (phase0:1203) `identityPerm n = List.range n` ✓
   - Definition 1518-1519: direct alias
   - Length 1521-1523: via `List.length_range`
   - Get 1525-1527: `simp [identityPerm, h]` with bound hypothesis
   - Axioms: propext (via simp)

4. **0-round mutant reduces to identity** (phase0:1231) ✓
   - Definition 1543-1544: `shuffledIndexOf perm index := perm[index]?`
   - Identity proof 1546-1548: `shuffledIndexOf_identity {n i} (h : i < n) : shuffledIndexOf (identityPerm n) i = some i := identityPerm_get h`
   - Axioms: propext (via identityPerm_get)

5. **Round tag width** (phase0:1205) Uint8 not Uint64 ✓
   - Proof `uintToBytes1_five` 1551-1552: `uintToBytes 1 5 = [5]` via simp
   - Proof `uintToBytes8_five` 1554-1556: `uintToBytes 8 5 = [5,0,0,0,0,0,0,0]` via simp
   - Inequality 1558-1561: `round_bytes_is_not_u64` via rewrite and decide
   - Axioms: propext (via simp)

6. **Bucket tag width** (phase0:1214) Uint32 not Uint64 ✓
   - Proof `uintToBytes4_one` 1564-1566: `uintToBytes 4 1 = [1,0,0,0]` via simp
   - Inequality 1568-1573: `bucket_bytes_is_not_u64` via rewrite of `uintToBytes8_one` and decide
   - Axioms: propext (via simp)

7. **Preimage separation** (phase0:1211-1214) via list-length disagreement ✓
   - Pivot preimage 1578-1579: `seed ++ shuffleRoundBytes round` (length: seed+1)
   - Bucket preimage 1585-1586: `seed ++ shuffleRoundBytes round ++ uintToBytes 4 bucket` (length: seed+5)
   - Separation 1588-1593: `shufflePivotPreimage_ne_bucket` via `congrArg List.length` and simp
   - Axioms: propext

8. **Flip function** (phase0:1209) `(pivot + count - idx % count) % count < count` ✓
   - Definition 1596-1597: standard form
   - Bound 1599-1601: `shuffleFlip_lt (0 < count)` via `Nat.mod_lt`
   - Axioms: none

9. **Flip normalized on `idx < count`** ✓
   - Theorem 1603-1607: `shuffleFlip_of_lt` unfolds definition and applies `Nat.mod_eq_of_lt`
   - Axioms: propext (via unfold and rw)

10. **Flip involution** (shuffleFlip twice = identity on `{0,...,count-1}`) ✓
    - Theorem 1610-1639: `shuffleFlip_involutive (hcount : 0 < count) (hidx : idx < count)`
    - Proof structure (30 lines, no sorry):
      * Line 1613: Invokes `shuffleFlip_of_lt` on original index
      * Line 1614: Establishes first flip result < count
      * Line 1615: Rewrites outer flip using the bound
      * Line 1616: Sets r := (pivot + count - idx) % count
      * Line 1618-1619: Establishes idx ≤ pivot + count via transitivity
      * Line 1620-1621: Applies `Nat.div_add_mod`: count * (pivot + count - idx) / count + r = pivot + count - idx
      * Line 1622-1624: Computes sum as pivot + count via `Nat.sub_add_cancel`
      * Line 1625-1638: Establishes pivot + count - r = count * ((pivot + count - idx) / count) + idx via associativity and arithmetic
      * Line 1639: Final step: `Nat.add_comm`, `Nat.add_mul_mod_self_left`, `Nat.mod_eq_of_lt hidx`
    - Axioms: propext, Quot.sound (via ac_rfl reassociation)
    - Assessment: Complete arithmetic proof, no gaps

11. **Concrete sample** `shuffleFlip 3 8 1 = 2 ∧ shuffleFlip 3 8 2 = 1` ✓
    - Theorem 1642-1644: `shuffleFlip_sample := by decide`
    - Manual verification: (3+8-1)%8 = 10%8 = 2; (3+8-2)%8 = 9%8 = 1
    - Axioms: none (decide)

12. **Mutants file** (6 new theorems in ProtocolSlotWithdrawalMutants.lean, lines 422-450) ✓
    - `shuffled_index_rejects_equal_count` (422-425): wraps `shuffled_index_rejects_eq 7`
    - `shuffle_rounds_are_not_hash32` (427-430): wraps `shuffleRoundCount_ne_hash32`
    - `shuffle_round_bytes_are_uint8` (432-435): wraps `round_bytes_is_not_u64`
    - `shuffle_bucket_bytes_are_uint32` (437-440): wraps `bucket_bytes_is_not_u64`
    - `shuffled_index_identity_before_rounds` (442-445): wraps `shuffledIndexOf_identity` with concrete bound
    - `shuffle_flip_is_involution` (447-450): wraps `shuffleFlip_sample`
    - Assessment: All are thin wrappers with correct instantiations and references

13. **Docstring updates** (open/scope notes) ✓
    - ProtocolSlotExtraction line 70: "pivot and swap-bit digests stay uninterpreted"
    - ProtocolWithdrawalExtraction line 161: "hash digests and the swap bit stay uninterpreted"
    - Both correctly state SHA256 values and pivot/swap-bit digests remain **uninterpreted**
    - Assessment: Docstrings accurately reflect extraction scope

14. **Axioms whitelist** (14 + 6 = 20 new `#print axioms` statements) ✓
    - Slot extraction module (lines 1730-1743): 14 declarations
      * `shuffleRoundCount_eq`: no axioms
      * `shuffleRoundCount_ne_hash32`: no axioms
      * `identityPerm_length`: propext
      * `identityPerm_get`: propext
      * `shuffled_index_rejects_eq`: no axioms
      * `shuffled_index_rejects_empty`: no axioms
      * `shuffledIndexOf_identity`: propext
      * `round_bytes_is_not_u64`: propext
      * `bucket_bytes_is_not_u64`: propext
      * `shufflePivotPreimage_ne_bucket`: propext
      * `shuffleFlip_lt`: no axioms
      * `shuffleFlip_of_lt`: propext
      * `shuffleFlip_involutive`: propext, Quot.sound
      * `shuffleFlip_sample`: no axioms
    - Mutant module (lines 1768-1773): 6 declarations
      * `shuffled_index_rejects_equal_count`: no axioms
      * `shuffle_rounds_are_not_hash32`: no axioms
      * `shuffle_round_bytes_are_uint8`: propext
      * `shuffle_bucket_bytes_are_uint32`: propext
      * `shuffled_index_identity_before_rounds`: propext
      * `shuffle_flip_is_involution`: no axioms
    - All axioms within whitelist {propext, Classical.choice, Quot.sound}
    - Assessment: CLEAN

15. **No sorry / admit / stub** ✓
    - Checked lines 1507-1644 (all new extraction code): no sorry
    - Checked shuffleFlip_involutive proof (lines 1610-1639): complete proof, no gaps
    - Checked mutants file (lines 422-450): all wrappers, no sorry
    - Build exits with code 0: compilation succeeds

---

## Axioms Check

**Declared allowed axioms**: `{propext, Classical.choice, Quot.sound}` (standard)

**Observed axiom dependencies** (from `#print axioms` output):
- No custom axioms introduced
- No `sorryAx` present
- propext: used for simp-based type arguments and equality definitions
- Quot.sound: used in `shuffleFlip_involutive` via `ac_rfl` reassociation
- Classical.choice: not used in new code

**Assessment**: Axioms whitelist satisfied. No suspicious or out-of-scope dependencies.

---

## Findings

**Blocking issues**: 0

**Advisory issues**: 0

**Build verification**: Passed (3675 jobs)

**Proof integrity**: All 15 claims verified to specification.
- Round count and assertion proofs are direct/decide.
- Identity preimage and flip involution proofs are complete arithmetic with justified tactics.
- Mutant wrappers correctly instantiate base theorems.
- Docstrings accurately state extraction scope (SHA256 and swap-bit digests uninterpreted).
- No sorry, no missing axioms, no out-of-spec proofs.

**Code quality**: Clean, readable, well-documented with inline docstrings. Arithmetic proof in `shuffleFlip_involutive` uses appropriate lemmas (`Nat.div_add_mod`, `Nat.sub_add_cancel`, `Nat.add_mul_mod_self_left`) and reasoning chain is transparent.

---

## VERDICT: CLEAN

All extraction claims verified. No blockers or advisories. Ready for integration.
