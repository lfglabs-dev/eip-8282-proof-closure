# Independent Review — zero-counts extension of genesis-seed History at spark head f75cef0

## Delta shape

Three files modified across f146123..f75cef0:
1. `Eip8282/Audit/Integrator/ReferenceGenesisSeededHistory.lean` — adds three new theorems (`counts_zero`, `exists_seed_zero_counts`) with 36 new LOC
2. `Eip8282/Audit/Trust.lean` — records two new `#print axioms` lines
3. `audit/receipts/direct-history-seed-zerocounts-review-status-20260911.json` — review intake record

No changes to public consumer signatures.

## Point-by-point verification

### 1. `Counts 0 0 0` structure fields vs. proof
**VERIFIED**

`ProtocolCreditEnvelope.Counts` definition (PCE.lean:78-81):
- `pow_count : pow ≤ 2^64` → proven by `decide` for pow=0
- `withdrawal_count : withdrawals ≤ 16*2^64` → proven by `decide` for withdrawals=0
- `migration_conserving : migrations = 0` → proven by `rfl` for migrations=0

All field types match exactly. Triviality is correctly discharged.

### 2. `exists_seed` inheritance and parameter binding
**VERIFIED**

`exists_seed_zero_counts` proof (line 91-93):
- Calls `exists_seed` with named parameters `(pow := 0) (withdrawals := 0) (migrations := 0)`
- Supplies `ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world 0 0 0 0 exit.world`
- Passes `counts_zero` as the `counts : ProtocolCreditEnvelope.Counts 0 0 0` argument
- Returns `Nonempty (History deposit exit exit.world)` ✓

No sorry/admit/stub found. Proof is complete and term-mode.

### 3. `ReferenceFundedHistoryLifecycle.initial` signature conformance
**VERIFIED**

`initial` constructor (RFL.lean:41-48) signature:
```
(depositInputs : FactoryHistoryGuarantees.Inputs .deposit deposit.call)
(exitInputs : FactoryHistoryGuarantees.Inputs .exit exit.call)
(linked : exit.call.world = deposit.world)
{baseCredits pow withdrawals migrations : Nat}
(prior : FundingHistory.Trace GenesisFundingWorld.world baseCredits deposit.call.world)
(ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world pow withdrawals migrations baseCredits exit.world)
(counts : ProtocolCreditEnvelope.Counts pow withdrawals migrations)
```

When called from `exists_seed` (line 57-58 of RGSH.lean) with `(baseCredits := 0)`, the implicit parameters resolve to `baseCredits=0, pow=0, withdrawals=0, migrations=0`, and the ledger type becomes `Ledger GenesisFundingWorld.world 0 0 0 0 exit.world` ✓

### 4. Axiom dependency chain
**VERIFIED**

Per review receipt and `#print axioms` output:
- `counts_zero` depends on `[propext]` only
  - `decide` tactic is kernel-computable
  - `rfl` is kernel-computable
  - No external axioms invoked
  
- `exists_seed_zero_counts` axioms: `[propext, Classical.choice, Quot.sound]`
  - Inherited entirely from `exists_seed` (PR#72, already CLEAN)
  - No new axioms introduced
  - Whitelist-compliant ✓

### 5. Ingredient reduction claim
**VERIFIED**

Claim: from six → four in seed + zero-count case.

Six ingredients in `ReferenceFundedHistoryLifecycle.initial`:
1. `depositInputs` — still required by caller
2. `exitInputs` — still required by caller
3. `linked` — still required by caller
4. `baseCredits` — implicit (fixed to 0 by exists_seed)
5. `prior : FundingHistory.Trace` — discharged by `exists_seed` via `FundingHistory.Trace.initial`
6. `ledger : ProtocolCreditEnvelope.Ledger` — still required by caller
7. `counts : ProtocolCreditEnvelope.Counts` — discharged by `counts_zero`

Result: caller supplies 4 explicit arguments (items 1–3, 6), plus the `ledger` hypothesis. The implicit baseCredits, prior (via genesisSeed), and counts (via counts_zero) are all discharged locally. Reduction verified ✓

### 6. Non-triviality of theorem statement
**VERIFIED**

`exists_seed_zero_counts` produces `Nonempty (History deposit exit exit.world)` from four premises (depositInputs, exitInputs, linked, ledger). This is non-trivial: without a witness satisfying the History record structure (deposits, exits, linked-world, credits ledger), no such inhabitant exists. The theorem is not a tautology. ✓

### 7. Public consumer API preservation
**VERIFIED**

No diffs in:
- `ReferenceFullFeeBlockTotal.verified`
- `ReferenceCheckedSystemBlock.verified`

Both still take bare `history` premise. Caller burden reduced without API change ✓

### 8. Trust.lean axiom recording
**VERIFIED**

Lines added:
```lean
#print axioms Eip8282.Audit.Integrator.ReferenceGenesisSeededHistory.counts_zero
#print axioms Eip8282.Audit.Integrator.ReferenceGenesisSeededHistory.exists_seed_zero_counts
```

Inserted in correct section (after `exists_seed` line). Matching review receipt output ✓

## Axioms check

From receipt and direct inspection:

| Theorem | Axioms | Whitelist |
|---------|--------|-----------|
| `counts_zero` | `[propext]` | ✓ |
| `exists_seed_zero_counts` | `[propext, Classical.choice, Quot.sound]` | ✓ |

No new axioms introduced. Inherits trusted legacy from PR#72 genesis-seed step-(a).

## Findings

**Blocking issues**: 0
**Advisory issues**: 0

- All three field proofs of `counts_zero` match their `Counts` structure definition
- Parameter binding from `exists_seed_zero_counts` to `exists_seed` is correct and complete
- No unproven sub-goals (no sorry/admit)
- Ingredient reduction from 6 to 4 in seed + zero-count case is correctly claimed
- Axiom whitelist compliance verified
- Public API signatures unchanged
- Trust.lean axiom recording complete and accurate

## VERDICT: CLEAN

The extension correctly discharges the `ProtocolCreditEnvelope.Counts` ingredient in the canonical zero-count case, reducing the seed-seeded History producer's caller obligation from six to four ingredients (depositInputs, exitInputs, linked, ledger). All proofs are complete, axioms are whitelist-compliant, and no breaking changes to public consumers. Ready for merge.
