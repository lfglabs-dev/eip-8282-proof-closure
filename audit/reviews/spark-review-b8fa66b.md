# Independent review — canonical-producer hook interfaces (b8fa66b)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commit: b8fa66b114298d31dbdd95c0a6add6fd578c9d37
Branch: spark/eip-canonical-hooks-20260911
Started at: 2026-09-11T11:35:06Z

## Scope items reviewed
- Absence of `sorry` / `admit` / stubs in the new module.
- Axiom drift for the four declared theorems against the axioms receipt.
- No fabricated policy: no witness of a producer, no adopted Ethereum
  admission machinery, no SYSTEM schedule, no deployed address is
  asserted.
- Field consistency of `CompleteAdmission` against
  `ReferenceFullFeeBlockTotal.verified` (`checks`, `found`, `recipient`,
  `nonblob`, plus admission-side).
- Field consistency of `Deployment` against
  `FactoryHistoryGuarantees.two_seeds` (`deposit`, `exit`, `linked`).
- Field consistency of `SystemAuthorization` against
  `ActualJournalHistory.Trace.system` (`sender`, `zero`, `fit`).
- Scope wording in `audit/DIRECT-CLOSURE.md` new section.
- Bundle hash match for the module and its 5 declared consumed
  dependencies against
  `audit/receipts/direct-canonical-hooks-bundle-20260911.json`.
- Type-valued-ness of `Deployment` (justified by data fields carried by
  `FactoryHistoryGuarantees.Inputs`).

## Findings

1. ADVISORY — `Eip8282/Audit/Integrator/ReferenceCanonicalHooks.lean:71`.
   `CompleteAdmission` carries a `funding : TransactionFunding.Admission
   tx sender` field that is not required as a separate argument by
   `ReferenceFullFeeBlockTotal.verified`
   (`Eip8282/Audit/Integrator/ReferenceFullFeeBlockTotal.lean:21`). In
   the current pipeline `TransactionFunding.Admission` is constructed
   from `SourceChecks` plus `OldConsumerCompatibility` inside
   `ReferenceAdmissionExtraction.admission`
   (`Eip8282/Audit/Integrator/ReferenceAdmissionExtraction.lean:278`).
   Bundling `funding` alongside `checks` is strictly redundant (a
   canonical producer of `SourceChecks` and `OldConsumerCompatibility`
   already yields it) and slightly widens the interface beyond what the
   downstream conditional theorem accepts. This is not a soundness
   issue — the structure only records extra hypotheses — but the doc
   claim that the fields match the exact tuple the downstream fee-block
   theorems accept is imprecise: they take `checks, found, recipient,
   nonblob` (plus a separate `history` and `costs`), not `funding`. The
   `.project` theorem is honest (it just returns the fields as a
   conjunction, with no soundness claim about downstream signatures).
   ADVISORY only.

2. OK — No `sorry`, `admit`, or stub anywhere in the module (grep
   returned none).

3. OK — `Deployment` is a plain (Type-valued) `structure`, correct
   given that `FactoryHistoryGuarantees.Inputs`
   (`Eip8282/Audit/Integrator/FactoryHistoryGuarantees.lean:24`)
   contains data fields (`steps : Nat`, `sender : Account .EVM`,
   `factory : Account .EVM`) — Prop-valued would have been ill-typed.
   The three fields `depositInputs`, `exitInputs`, `linked` map exactly
   onto the leading three arguments of `two_seeds`
   (`Eip8282/Audit/Integrator/FactoryHistoryGuarantees.lean:100`).

4. OK — `SystemAuthorization`
   (`Eip8282/Audit/Integrator/ReferenceCanonicalHooks.lean:118`)
   fields — `caller`, `zeroValue`, `dataFit` — match the three input
   propositions of the `Trace.system` constructor
   (`Eip8282/Audit/Integrator/ActualJournalHistory.lean:43-44`):
   `t.call.caller = sysAddr`, `t.call.value = ⟨0⟩`,
   `t.call.calldata.size < UInt256.size`. `MessageCall.Context` at
   `Eip8282/Audit/Integrator/MessageCall.lean:26,32,34` supplies the
   `caller : AccountAddress`, `value : UInt256`, `calldata : ByteArray`
   fields the equalities reference; types check.

5. OK — `AllHooks` is a Type-valued structure combining the three hooks;
   `.propHooks` returns the conjunction of the two Prop-valued halves,
   and the docstring correctly notes the Type-valued `Deployment` is
   accessible directly.

6. OK — DIRECT-CLOSURE.md scope disclaims correctly at
   `audit/DIRECT-CLOSURE.md:79-83`: "Complete Ethereum admission
   (signature recovery, full blob validation, capacity, type-4
   authorization) remains OPEN and must widen this structure."
   `SystemAuthorization` prose (`:91-95`) correctly disclaims that no
   schedule is adopted, no authorization source is identified and no
   automatic SYSTEM invocation is asserted. `Deployment` prose (`:85-89`)
   correctly describes it as Type-valued because `Inputs` carries data
   fields. The concluding paragraph (`:101-105`) states the module adds
   no axiom, adopts no protocol policy, and does not claim any canonical
   producer exists.

7. OK — The four declared theorems assert only what field-access
   tuples deliver: `CompleteAdmission.project` unpacks the five fields;
   `Deployment.linked_hypothesis` returns `h.linked`;
   `SystemAuthorization.project` unpacks the three fields;
   `AllHooks.propHooks` conjoins the two Prop halves. No producer
   existence claim, no bytecode identification, no address production,
   no schedule adoption is present in either the structures or the
   theorems.

8. OK — Trust.lean at `Eip8282/Audit/Trust.lean:3854-3863` adds the
   four `#print axioms` lines for the four projection theorems.
   Integrator.lean at `Eip8282/Audit/Integrator.lean:506` adds the
   single import line for the new module.

## Axiom audit

Cross-referenced
`audit/receipts/direct-canonical-hooks-axioms-20260911.json`:
- `CompleteAdmission.project`: axioms
  `{propext, Classical.choice, Quot.sound}`. OK.
- `Deployment.linked_hypothesis`: axioms
  `{propext, Classical.choice, Quot.sound}`. OK.
- `SystemAuthorization.project`: axioms
  `{propext, Classical.choice, Quot.sound}`. OK.
- `AllHooks.propHooks`: axioms
  `{propext, Classical.choice, Quot.sound}`. OK.
- Receipt records `sorryAx: NONE`, `other_axioms: NONE`. Reviewer did
  not re-run `lake build` or `make check` (per scope). Axiom-drift claim
  is consistent with the trivial field-access nature of the four
  theorems.

## Bundle hash verification

Computed `sha256sum` on the frozen checkout and compared to
`audit/receipts/direct-canonical-hooks-bundle-20260911.json`:

- `Eip8282/Audit/Integrator/ReferenceCanonicalHooks.lean`
  computed `e8336993fc1a4dd10164e4bfeda0a5623a711ff565fc0ca73f4e999ea40d6f86`
  vs receipt `e8336993fc1a4dd10164e4bfeda0a5623a711ff565fc0ca73f4e999ea40d6f86`. MATCH.
- `Eip8282/Audit/Integrator/ReferenceAdmissionExtraction.lean`
  computed `25ad6d2e4398a7d7049fa44d9d202e772daa8e95125da9cdbe2d5ab976a3d618`
  vs receipt `25ad6d2e4398a7d7049fa44d9d202e772daa8e95125da9cdbe2d5ab976a3d618`. MATCH.
- `Eip8282/Audit/Integrator/TransactionFunding.lean`
  computed `dff074ffa97b3c17862496c3cd92bfb50611c7f19796c79ad95a469778508f2f`
  vs receipt `dff074ffa97b3c17862496c3cd92bfb50611c7f19796c79ad95a469778508f2f`. MATCH.
- `Eip8282/Audit/Integrator/FactoryHistoryGuarantees.lean`
  computed `641937241f6f4cff741c1d05f888a6c4868441dd6d4a6599d666e0f0eadc9cb2`
  vs receipt `641937241f6f4cff741c1d05f888a6c4868441dd6d4a6599d666e0f0eadc9cb2`. MATCH.
- `Eip8282/Audit/Integrator/ActualJournalHistory.lean`
  computed `744476e8ebc4ce5fbfe722045a405fe0a9a8e7b5d61554898df382daa0a39e8e`
  vs receipt `744476e8ebc4ce5fbfe722045a405fe0a9a8e7b5d61554898df382daa0a39e8e`. MATCH.
- `Eip8282/Audit/Integrator/ReferenceSourcePrepaidCheckpoint.lean`
  computed `9803817d40c22c03996dc36f9ff8e296e5309f8c135c2e6a700999aae425f795`
  vs receipt `9803817d40c22c03996dc36f9ff8e296e5309f8c135c2e6a700999aae425f795`. MATCH.

All six hashes match.

## Conclusion

The commit adds four `structure` declarations plus four trivial
projection theorems for canonical-producer hook interfaces at admission,
deployment and SYSTEM authorization boundaries. The theorems are pure
field-access packaging; no protocol policy, producer existence, admission
machinery, invocation schedule, or deployed address is asserted. Axiom
audit is consistent with the trivial nature of the theorems (only
`propext`, `Classical.choice`, `Quot.sound`), matching the axioms
receipt. All six bundle hashes match. The `Deployment` structure is
correctly Type-valued. The DIRECT-CLOSURE.md new section correctly
disclaims that complete Ethereum admission remains OPEN and must widen
`CompleteAdmission`. The only advisory is that `CompleteAdmission`
bundles a `funding : TransactionFunding.Admission` field that is not
strictly required as a separate argument by
`ReferenceFullFeeBlockTotal.verified` (it is derivable via the existing
`ReferenceAdmissionExtraction.admission` helper); this is a widening of
the interface, not a soundness concern. No BLOCKING findings.

VERDICT: CLEAN
