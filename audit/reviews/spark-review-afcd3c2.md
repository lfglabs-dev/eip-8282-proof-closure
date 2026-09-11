# Independent review — History funds bridge (afcd3c2)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commit: afcd3c257aa0b907192cc336bc3fc7e5e1073c1b
Branch: spark/eip-history-funds-bridge-20260911
Started at: 2026-09-11T12:34:16+00:00

## Scope items reviewed
- No `sorry` / `admit` / stubs in the new module.
- Axiom drift limited to `{propext, Classical.choice, Quot.sound}`.
- Correctness of `funding_trace_from_genesis` (unfolds `funding_budget h.ledger initial_funds_le h.counts).1`).
- Correctness of `worldFunds_lt_ceiling` (composes `.2` of `funding_budget` with `FundingHistory.trace_funds`, via `lt_of_le_of_lt`).
- Correctness of `worldBalance_lt_ceiling` (composes `TransferFunding.balance_le_funds` with `worldFunds_lt_ceiling`).
- DIRECT-CLOSURE.md new "History→funds ceiling bridge candidate" section disclaimer.
- Bundle hash match against `audit/receipts/direct-history-funds-bridge-bundle-20260911.json` (7 entries).
- No premise smuggling: only `h : History deposit exit before` (plus `address` for the balance variant); no additional premises hidden in implicit arguments.
- Integrator.lean import and Trust.lean `#print axioms` lines (3 declarations).

## Findings
- None. No BLOCKING or ADVISORY items.

## Axiom audit
- `funding_trace_from_genesis` → per `audit/receipts/direct-history-funds-bridge-axioms-20260911.json`: `[propext, Classical.choice, Quot.sound]`. `#print axioms` invocation present at `Eip8282/Audit/Trust.lean:3858`. Underlying `funding_budget` and `initial_funds_le` share the same base (verified via existing `#print axioms` lines in `ProtocolCreditEnvelope` and `GenesisFundingWorld`). `sorryAx`: NONE. Other axioms: NONE.
- `worldFunds_lt_ceiling` → same axiom set `[propext, Classical.choice, Quot.sound]`. `#print axioms` at `Eip8282/Audit/Trust.lean:3859`. Composition uses `FundingHistory.trace_funds` (kernel-only, no additional axioms per its inductive-recursor proof) and `lt_of_le_of_lt` (Mathlib order lemma, inherits the same base).
- `worldBalance_lt_ceiling` → same axiom set. `#print axioms` at `Eip8282/Audit/Trust.lean:3860`. Composition uses `TransferFunding.balance_le_funds` (already audited with the same base) and `Nat.le.trans_lt`.

## Bundle hash verification
Computed `sha256sum` matches the recorded bundle values for all 7 modules:
- `Eip8282/Audit/Integrator/ReferenceHistoryFundsBridge.lean` → `d222cc2ecebffc95da500f6760410988419c17cb2cb4564b6991f00af649f45c` ✓
- `Eip8282/Audit/Integrator/ReleaseCandidate.lean` → `764488ab43cbb63b775d97f0a41ec98fe520445bcd1390bbca5a834a181c2d66` ✓
- `Eip8282/Audit/Integrator/ProtocolCreditEnvelope.lean` → `79d4b50bf49d7cefa35e35bd5bb92f6b84dca99cb60aeadc9445ea721dcacb7c` ✓
- `Eip8282/Audit/Integrator/GenesisFundingWorld.lean` → `fa696efa6f52872f4e42105ed25c635ff8d0515c8cc0636b96d21e4c76ef570c` ✓
- `Eip8282/Audit/Integrator/FundingHistory.lean` → `da5af24a0eb4630f8c02beb32c4245e54f08dd0c880ec79278002c6c6352e65f` ✓
- `Eip8282/Audit/Integrator/TransferFunding.lean` → `b8d8286170495a4a59d0f61ad19e0354e624ea3a0c0e0f48bd24e92ea7871766` ✓
- `Eip8282/Audit/Integrator/FundedDomain.lean` → `957cb3c9fa8951df7daf57bf0cb0fae883c4b01e7b514c0dee551edf773cd1d7` ✓

## Correctness notes
- `History` structure (`ReleaseCandidate.lean:31–48`) exposes fields `baseCredits`, `credits`, `ledger : Ledger GenesisFundingWorld.world pow withdrawals migrations (baseCredits+credits) before`, `counts`. The bridge instantiates `funding_budget`'s implicit `initial = GenesisFundingWorld.world`, `world = before`, `c = baseCredits+credits`. The genesis premise slot is filled by `GenesisFundingWorld.initial_funds_le : worldFunds world ≤ GenesisFundingInput.totalCredit` — exact match for `funding_budget`'s `TransferFunding.worldFunds initial ≤ GenesisFundingInput.totalCredit`.
- `funding_budget` (`ProtocolCreditEnvelope.lean:96–106`) returns `FundingHistory.Trace initial c world ∧ TransferFunding.worldFunds initial + c < FundedDomain.fundingCeiling`. The `.1` projection yields exactly the type asserted by `funding_trace_from_genesis`.
- `FundingHistory.trace_funds` (`FundingHistory.lean:64–68`) yields `worldFunds world ≤ worldFunds initial + credits`. With the trace built by `funding_trace_from_genesis h`, this gives `worldFunds before ≤ worldFunds GenesisFundingWorld.world + (baseCredits+credits)`, which chains with the `.2` bound via `lt_of_le_of_lt` to `worldFunds before < fundingCeiling`.
- `TransferFunding.balance_le_funds` (`TransferFunding.lean:99–103`) yields `worldBalance world key ≤ worldFunds world`; `.trans_lt` with `worldFunds_lt_ceiling h` yields the per-address bound.
- All three theorems are `theorem` (not `def`); no `unsafe`, no `native_decide`, no `decide +kernel` in this module.

## Scope / drift
- The DIRECT-CLOSURE.md section (`audit/DIRECT-CLOSURE.md:69–104`) states: "Neither lemma adopts a new premise: they specialize existing conditional theorems to the concrete History fields." It disclaims new protocol policy and correctly attributes the axiom trio. It also declares "Independent exact review pending. No unreviewed proof extension, external message or normative policy has been promoted. PR20 remains c3f3c1d; prepared documentation 7e2ef006 remains unpushed." No scope drift.
- Bundle receipt's `domain.scope` and `verification.mutations` fields honestly disclose that no dedicated mutation testing was added (existing downstream mutants on the parent theorems remain in effect); this matches the bridge's role as a conditional-lemma specialization.
- No premise smuggling: signatures are `{deposit exit : Receipt} {before : AccountMap .EVM} (h : History deposit exit before)` for the trace/world variants and additionally `(address : AccountAddress)` for the balance variant. No `[Instance]` arguments, no additional propositional premises.

## Conclusion
The frozen commit adds three consumer-facing bridge theorems that faithfully compose `ProtocolCreditEnvelope.funding_budget`, `GenesisFundingWorld.initial_funds_le`, `FundingHistory.trace_funds` and `TransferFunding.balance_le_funds` into a single History-keyed form. Signatures, projections and axiom bases are consistent with the parents; no new premise is introduced, no `sorry`/`admit` appears, all 7 bundle hashes match, and the DIRECT-CLOSURE.md section correctly disclaims scope. The Integrator.lean import and three Trust.lean `#print axioms` lines are in place.

VERDICT: CLEAN
