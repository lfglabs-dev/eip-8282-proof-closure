# Independent review — Two-step composition lemmas for `ReferenceFundedHistoryLifecycle.next` (261cbbe)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commit: 261cbbe on branch spark/eip-next-composition-20260912
Base: origin/main = 9497bbe
Started at: 2026-09-11

## Bundle summary

`git diff --stat 9497bbe..261cbbe`:
- `Eip8282/Audit/Integrator.lean` — +1 line (single new import)
- `Eip8282/Audit/Integrator/ReferenceHistoryNextComposition.lean` — new module, 76 lines
- `Eip8282/Audit/Trust.lean` — +5 lines (2 `#print axioms` for the new theorems plus a 3-line explanatory comment)

Total: +82/-0. Matches the announced scope of 1 new module + 1 Integrator import + 2 Trust lines (plus a header comment on the Trust side).

## 1. `sorry` / `admit`

`grep -in "sorry\|admit"` on the new module returns 10 hits, all substring matches inside `admitted*` / `admission*` parameter names (`admittedGas1`, `admittedGas2`, `admission1`, `admission2`). No tactic occurrence of `sorry` or `admit`. Clean.

## 2. Axioms

Both theorems are proved by `simp [receipts_extend]` / `simp [blocks_extend]`, chained to lemmas in `ReferenceFundedHistoryLifecycle` which themselves close by `rfl` (line 132) and `simp [next]` (line 145). No `native_decide`, no `Classical.choice`-triggering combinators, no imports beyond `ReferenceFundedHistoryLifecycle` (which the audit chain already accepts). Expected axiom set: `{propext, Classical.choice, Quot.sound}`. Two `#print axioms` statements are included at the module bottom (lines 73–74) and mirrored in `Trust.lean`.

## 3. Correctness

`next` (Reference…Lifecycle.lean line 74) returns a `History deposit exit r.world` with `receipts := h.receipts ++ [r]` (line 103) and `blocks := h.blocks ++ [newBlock]` (line 108).

- `next_next_receipts`: goal reduces via `receipts_extend` (rfl) to `(h.receipts ++ [r1]) ++ [r2] = h.receipts ++ [r1, r2]`. This is definitionally true (`List.append_assoc` collapses; `[r1] ++ [r2] = [r1, r2]` by `rfl`). `simp [receipts_extend]` closes it.
- `next_next_blocks_length`: goal reduces via `blocks_extend` (twice) to `(h.blocks.length + 1) + 1 = h.blocks.length + 2`. `simp` normalizes the arithmetic. Standard.

Both proofs are direct equational consequences as advertised.

## 4. Premise smuggling

Cross-checked the composed premises against what two consecutive `next` applications require:
- First `next`: `linked1`, `account1`, `admission1`, `fit1`, `resources1`, `slot1`, `gas1`, `freshSlot1 : slot1 ∉ h.blocks.map …`, `admittedGas1` — matches lines 27–34.
- Second `next` (on `next h r1 …`, whose type is `History deposit exit r1.world`): needs `r2.call.world = r1.world` — line 35 has `linked2 : r2.call.world = r1.world`; then `account2`, `admission2`, `fit2`, `resources2`, `slot2`, `gas2`, `freshSlot2 : slot2 ∉ (next h r1 …).blocks.map …` (line 41), `admittedGas2`.

No extra hypotheses beyond what iterated `next` already demands. The `freshSlot2` premise correctly references the intermediate history's blocks (not some independent list), preserving slot-uniqueness through the composition.

## 5. Bundle / scope

- 1 new module (`ReferenceHistoryNextComposition.lean`).
- 1 new import in `Eip8282/Audit/Integrator.lean` (line 517, alphabetically-adjacent to peer references).
- 2 new `#print axioms` lines in `Trust.lean` (lines 3951, 3952) plus a 3-line explanatory comment (lines 3949–3950). Within announced scope; the Trust comment is documentation, not new content.

No changes to any other file. No touched proofs elsewhere.

## Findings

- Zero `sorry`/`admit`.
- Proofs are direct consequences of pre-existing `receipts_extend` / `blocks_extend`.
- Premise list exactly matches what two composed `next` calls demand.
- Axiom footprint should be the standard `{propext, Classical.choice, Quot.sound}`.
- Bundle exactly matches announced scope (1 module + 1 import + Trust hooks).

Nothing blocking.

VERDICT: CLEAN
