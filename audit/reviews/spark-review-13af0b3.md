# Independent Review — genesis-seed History existence lemma at spark head 13af0b3

## Delta shape

The delta introduces a single new theorem `exists_seed` in a new module `Eip8282/Audit/Integrator/ReferenceGenesisSeededHistory.lean` (lines 35–60). Two supporting changes:
- `Integrator.lean`: new import line at line 507
- `Trust.lean`: new axiom-check line appended after FundedHistoryLifecycle section

The two public consumers (`ReferenceFullFeeBlockTotal.verified`, `ReferenceCheckedSystemBlock.verified`) remain unmodified—`history` premise is still bare on both.

## Point-by-point verification

### 1. New module compiles cleanly
**VERIFIED**
File `/home/th0rgal/work/eip-8282/direct-closure-implementation/Eip8282/Audit/Integrator/ReferenceGenesisSeededHistory.lean` is syntactically complete and structurally sound. Lake build at spark head succeeded (3608 jobs). Module namespace, imports, and set_option declarations are correct.

### 2. `exists_seed` axioms lie in trust boundary
**VERIFIED**
Axiom check at spark head (via `lake env lean --run Eip8282/Audit/Trust.lean`) confirms:
```
'Eip8282.Audit.Integrator.ReferenceGenesisSeededHistory.exists_seed' depends on axioms: [propext, Classical.choice, Quot.sound]
```
All three are in the acceptable trust set {propext, Classical.choice, Quot.sound}. No escape into Oracle or unsafe axioms.

### 3. Proof body soundness
**VERIFIED**
The proof (lines 57–60) is:
```lean
refine ⟨ReferenceFundedHistoryLifecycle.initial depositInputs exitInputs linked (baseCredits := 0) ?_ ledger counts⟩
rw [genesisSeed]
exact FundingHistory.Trace.initial
```

(a) `initial` signature accepts these arguments: depositInputs, exitInputs, linked (explicit); baseCredits := 0 (explicit); ? (implicit prior); ledger, counts (explicit). Types match exactly to the function definition.

(b) Residual goal after `refine` is `FundingHistory.Trace GenesisFundingWorld.world 0 deposit.call.world` (the implicit prior parameter).

(c) `rw [genesisSeed]` where `genesisSeed : deposit.call.world = GenesisFundingWorld.world` transforms goal to `FundingHistory.Trace GenesisFundingWorld.world 0 GenesisFundingWorld.world`.

(d) `FundingHistory.Trace.initial : Trace initial 0 initial` exactly matches the transformed goal where `initial := GenesisFundingWorld.world`.

All steps type-check correctly.

### 4. No sorry, admit, stub, or trivial conclusion
**VERIFIED**
The theorem statement claims existence of a canonical `History deposit exit exit.world` given five explicit premises (depositInputs, exitInputs, linked, genesisSeed, ledger, counts) plus implicit pow/withdrawals/migrations. The claim is non-trivial: without these six ingredients plus the `Nonempty` wrapper construction, no History can be produced. The proof is complete (no sorry/admit present).

### 5. Public consumer signatures unchanged
**VERIFIED**
Byte-for-byte comparison of `ReferenceFullFeeBlockTotal.verified` signature at base (0a19797) and head (13af0b3): identical. The `history : ReleaseCandidate.History deposit exit tx.world` premise remains a bare hypothesis on both consumers. This is correctly labeled as "step-(a)"—removes the FundingHistory.Trace sub-obligation, not the history premise itself.

### 6. `ProtocolCreditEnvelope.Ledger` type signature match
**VERIFIED**
Theorem expects `ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world pow withdrawals migrations 0 exit.world`.
The `initial` constructor definition expects `ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world pow withdrawals migrations baseCredits exit.world`.
When `baseCredits := 0` is passed, the constructor body performs `ledger := by simpa only [Nat.add_zero] using ledger`, which simplifies `baseCredits + 0 = 0 + 0 = 0`. This simplification is transparent; types align exactly.

### 7. Returns `Nonempty` rather than direct History
**VERIFIED**
Return type is `Nonempty (History deposit exit exit.world)`. This is intentional per docstring (line 42–45): "packaged as Nonempty (Prop) so downstream lemmas can destruct it without depending on specific structural fields." Structural axioms do not escape this wrapper; callers requiring the exact History use `ReferenceFundedHistoryLifecycle.initial` directly.

### 8. `Trust.lean` axiom-check line appended
**VERIFIED**
File shows `#print axioms Eip8282.Audit.Integrator.ReferenceGenesisSeededHistory.exists_seed` appended at line immediately preceding the "Non-receipt-adding extensions" comment block. This is the correct position in the audit trail.

### 9. `Integrator.lean` import order correct
**VERIFIED**
New import line `import Eip8282.Audit.Integrator.ReferenceGenesisSeededHistory` is inserted at line 507, immediately after `ReferenceFundedHistoryLifecycle` and before `ReferenceHistoryNonReceiptExtensions`. This places the new module in the logical dependency order (depends on FundedHistoryLifecycle, depended upon by extensions).

## Axioms check

Confirmed via `lake env lean --run Eip8282/Audit/Trust.lean`:
- `exists_seed` depends on: **propext, Classical.choice, Quot.sound** (all in trust boundary)
- No undefined axioms, no oracle axioms, no sorries in the proof

## Findings

- **Blocking issues**: 0
- **Advisory issues**: 0
- **Code quality**: Excellent. Documentation is complete and accurate. Proof strategy is minimal and transparent. No unnecessary generalizations or unstated assumptions.

## VERDICT: CLEAN

The genesis-seed History existence lemma is sound, axiomatically clean, and correctly positioned as a step-(a) helper to discharge the FundingHistory.Trace ingredient of the history premise for downstream consumers. No blocking or advisory issues detected.
