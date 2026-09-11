# Independent review — funded History lifecycle constructors (8f76438)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commit: 8f76438e88021cac5acf9a5089eb7ce5e93ef9f5
Branch: spark/eip-funded-history-lifecycle-20260911
Started at: 2026-09-11T10:57:27Z

## Scope items reviewed

- **1. `sorry` / `admit` / stubs** — OK. `grep -nE "\bsorry\b|\badmit\b|\bsorryAx\b|^axiom "` on the new module returned no matches.
- **2. Axiom drift** — OK. The receipt `direct-funded-history-lifecycle-axioms-20260911.json` lists exactly the eight declarations with `{propext, Classical.choice, Quot.sound}` each, and matches the eight `#print axioms` lines added at `Eip8282/Audit/Trust.lean:3860-3867`.
- **3. Renamed premises** — OK. `initial` does not take a `History deposit exit exit.world` (only the four independent ingredients: factory inputs, prior funding Trace to `deposit.call.world`, credit Ledger to `exit.world`, Counts). `next` does not take a `History deposit exit r.world`; only `h : History deposit exit before` and one further Υ receipt with its independent resources. `freshSlot` is `slot ∉ h.blocks.map (fun b => b.slot)` (strictly weaker than Nodup on the extended list); `slots.Nodup` on the extended list is *derived*, not an input (see lines 113-120 of the new module).
- **4. Trivial or vacuous conclusion** — OK. `initial` and `next` return a proper `History` populating all 16 structure fields (History has 16 fields; the bundle receipt's "15 fields" comment is a minor documentation slip, see finding A1). `receipts_extend` states `(next ...).receipts = h.receipts ++ [r]` by `rfl` (line 132); `blocks_extend` proves `((next ...).blocks).length = h.blocks.length + 1` by `simp [next]` (line 145).
- **5. Scope drift** — OK. `audit/DIRECT-CLOSURE.md` lines 69-110 correctly disclaim: "Neither constructor asserts canonical Ethereum production of its ingredient records… The lifecycle module does not compose the ordinary block incorporation with the History extension." No sequencer is adopted, no canonical ancestry claim is made.
- **6. Bundle hash match** — OK. Computed SHA-256 of `Eip8282/Audit/Integrator/ReferenceFundedHistoryLifecycle.lean` equals `6731ff704c6339624191b3d3ffa499cb291297811f0ef15e09085b37852bedc5` (bundle value). All six consumed-dependency SHA-256s in the bundle match the current files (see Bundle hash verification section).
- **7. Ledger extension soundness** — OK. `next` builds `step : FundingHistory.Step before 0 r.world` using `Step.transaction r.call account admission r.executed` (which yields `Step r.call.world 0 r.world`, then `linked ▸` rewrites `r.call.world = before`). It feeds this into `ProtocolCreditEnvelope.Ledger.conserving h.ledger step`, whose signature (line 50-52 of ProtocolCreditEnvelope.lean) accepts `Ledger init p w s c before` and `Step before 0 after`, returning `Ledger init p w s c after`. Credit total (`baseCredits + h.credits`) is preserved: `credits` is copied unchanged from `h.credits`, and `Step.transaction`'s credit contribution is `0`. The `linked` rewrite goes from `r.call.world` to `before`, correct direction.
- **8. Trace extension soundness** — OK. `next` builds `actual := ActualJournalHistory.Trace.transaction h.actual r linked account admission fit resources`. The `Trace.transaction` constructor (ActualJournalHistory.lean:33-39) requires `prior : Trace initial receipts credits before`, `r`, `linked : r.call.world = before`, and the three resource witnesses, returning `Trace initial (receipts++[r]) credits r.world`. `h.actual : Trace exit.world h.receipts h.credits before`, so the result has type `Trace exit.world (h.receipts++[r]) h.credits r.world`, exactly matching the History field type at the new `before := r.world`.
- **9. Block-slot uniqueness soundness** — OK. The `slots` proof (lines 113-120) applies `List.Nodup.append` to `h.slots` (Nodup of pre-existing slots) and `List.nodup_singleton _` (Nodup of `[slot]`) with the disjointness `∀ a ∈ h.blocks.map slot, a ∉ [slot]`. After `simp only [List.mem_singleton]` and `rintro rfl`, the residual goal is `slot ∈ h.blocks.map (fun b => b.slot) → False`, discharged by `freshSlot ha`. A mutation replacing `freshSlot` with `True` would leave the residual goal unprovable, breaking `Nodup`.
- **10. Consistency with existing `ReleaseCandidate.History`** — OK. History has 16 fields (ReleaseCandidate.lean:31-48). Both `initial` and `next` populate all 16 with types matching:
  - depositInputs / exitInputs : `FactoryHistoryGuarantees.Inputs .{deposit,exit} {deposit,exit}.call` — supplied or copied.
  - linked : `exit.call.world = deposit.world` — supplied or copied.
  - baseCredits, credits, pow, withdrawals, migrations : `Nat` — supplied or copied; `initial` uses `credits := 0`.
  - receipts : `List Receipt` — `[]` in initial, `h.receipts ++ [r]` in next.
  - prior : `FundingHistory.Trace GenesisFundingWorld.world baseCredits deposit.call.world` — supplied or copied.
  - actual : `ActualJournalHistory.Trace exit.world receipts credits before` — `Trace.initial` gives `Trace exit.world [] 0 exit.world` (matching `before = exit.world`); `Trace.transaction ...` gives the extended shape.
  - ledger : `Ledger ... (baseCredits+credits) before` — in `initial` `credits=0`, so `simpa only [Nat.add_zero] using ledger` converts `Ledger ... baseCredits exit.world`; in `next`, `Ledger.conserving` preserves `(baseCredits+h.credits)` and moves target from `before` to `r.world`.
  - counts : `Counts pow withdrawals migrations` — supplied or copied.
  - blocks : `List BlockReceipt` — `[]` or `h.blocks ++ [newBlock]`.
  - listed : `receipts = blocks.flatMap (fun b => b.receipts)` — `by simp` in initial (both sides `[]`); a `simp only [flatMap_append, flatMap_cons, flatMap_nil, append_nil, newBlock, hl]` chain in next.
  - slots : `(blocks.map slot).Nodup` — `by simp` in initial; `List.Nodup.append` chain in next with `freshSlot`.

## Findings

- **A1 [ADVISORY] `audit/receipts/direct-funded-history-lifecycle-bundle-20260911.json:31`** — bundle documents the ReleaseCandidate dependency as `"used_for": "History structure and its 15 fields"`, but the History structure in `Eip8282/Audit/Integrator/ReleaseCandidate.lean:31-48` declares 16 fields (depositInputs, exitInputs, linked, baseCredits, credits, pow, withdrawals, migrations, receipts, prior, actual, ledger, counts, blocks, listed, slots). Cosmetic receipt inaccuracy; no impact on soundness or the constructors themselves — both `initial` and `next` populate all 16 fields.

No other findings. No BLOCKING findings.

## Axiom audit

Per `audit/receipts/direct-funded-history-lifecycle-axioms-20260911.json` and the eight `#print axioms` lines at `Eip8282/Audit/Trust.lean:3860-3867`:

- `ReferenceFundedHistoryLifecycle.initial` — `{propext, Classical.choice, Quot.sound}`
- `ReferenceFundedHistoryLifecycle.next` — `{propext, Classical.choice, Quot.sound}`
- `ReferenceFundedHistoryLifecycle.receipts_extend` — `{propext, Classical.choice, Quot.sound}`
- `ReferenceFundedHistoryLifecycle.blocks_extend` — `{propext, Classical.choice, Quot.sound}`
- `ReferenceFundedHistoryLifecycle.depositInputs_stable` — `{propext, Classical.choice, Quot.sound}`
- `ReferenceFundedHistoryLifecycle.exitInputs_stable` — `{propext, Classical.choice, Quot.sound}`
- `ReferenceFundedHistoryLifecycle.initial_receipts_empty` — `{propext, Classical.choice, Quot.sound}`
- `ReferenceFundedHistoryLifecycle.initial_blocks_empty` — `{propext, Classical.choice, Quot.sound}`

`sorryAx`: NONE. Other axioms: NONE. Non-standard axioms: NONE.

## Bundle hash verification

Bundle receipt lists the following SHA-256 values; computed values on the frozen source (from `sha256sum`) match exactly:

| Module path | Expected SHA-256 | Computed SHA-256 | Match |
|---|---|---|---|
| `Eip8282/Audit/Integrator/ReferenceFundedHistoryLifecycle.lean` | `6731ff704c6339624191b3d3ffa499cb291297811f0ef15e09085b37852bedc5` | `6731ff704c6339624191b3d3ffa499cb291297811f0ef15e09085b37852bedc5` | yes |
| `Eip8282/Audit/Integrator/ReleaseCandidate.lean` | `764488ab43cbb63b775d97f0a41ec98fe520445bcd1390bbca5a834a181c2d66` | `764488ab43cbb63b775d97f0a41ec98fe520445bcd1390bbca5a834a181c2d66` | yes |
| `Eip8282/Audit/Integrator/ActualJournalHistory.lean` | `744476e8ebc4ce5fbfe722045a405fe0a9a8e7b5d61554898df382daa0a39e8e` | `744476e8ebc4ce5fbfe722045a405fe0a9a8e7b5d61554898df382daa0a39e8e` | yes |
| `Eip8282/Audit/Integrator/FundingHistory.lean` | `da5af24a0eb4630f8c02beb32c4245e54f08dd0c880ec79278002c6c6352e65f` | `da5af24a0eb4630f8c02beb32c4245e54f08dd0c880ec79278002c6c6352e65f` | yes |
| `Eip8282/Audit/Integrator/ProtocolCreditEnvelope.lean` | `79d4b50bf49d7cefa35e35bd5bb92f6b84dca99cb60aeadc9445ea721dcacb7c` | `79d4b50bf49d7cefa35e35bd5bb92f6b84dca99cb60aeadc9445ea721dcacb7c` | yes |
| `Eip8282/Audit/Integrator/FactoryHistoryGuarantees.lean` | `641937241f6f4cff741c1d05f888a6c4868441dd6d4a6599d666e0f0eadc9cb2` | `641937241f6f4cff741c1d05f888a6c4868441dd6d4a6599d666e0f0eadc9cb2` | yes |
| `Eip8282/Audit/Integrator/TransactionAppendBudget.lean` | `aa799503613c3cc88d327f9e011a25dee08ce6bf569359f8d6e512d86cf25518` | `aa799503613c3cc88d327f9e011a25dee08ce6bf569359f8d6e512d86cf25518` | yes |

## Conclusion

The two new constructors and six auxiliary lemmas in `Eip8282/Audit/Integrator/ReferenceFundedHistoryLifecycle.lean` compose the existing `ReleaseCandidate.History` structure from four independent ingredient obligations (factory deployment inputs, prior funding trace from genesis, credit ledger to exit-world, count admission) at construction time, and extend it by one further actual Υ receipt with independently admitted admission/data-size/fuel/slot/gas resources. No premise restates the conclusion; slot Nodup on the extended list is derived, not required. Ledger extension routes through `Ledger.conserving` with `Step.transaction` (credit contribution 0), so the extended ledger's credit total is preserved. The DIRECT-CLOSURE.md section correctly disclaims canonical Ethereum production of the ingredients and explicitly notes that the module does not compose block incorporation with History extension. All eight declarations depend only on `{propext, Classical.choice, Quot.sound}`; no sorry, admit, or non-standard axiom exists in the new module. All seven bundle SHA-256s match the frozen sources. One advisory finding (cosmetic field-count phrasing in the bundle receipt) does not affect soundness.

VERDICT: CLEAN
