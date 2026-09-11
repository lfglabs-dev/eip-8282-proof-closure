# Independent review — block-level gas capacity envelope (5c99d47)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commit: 5c99d47820ca28f39613ea768ded24381a334db7
Branch: spark/eip-block-capacity-20260911
Started at: 2026-09-11T11:22:02Z

## Scope items reviewed
- No `sorry` / `admit` / stubs in the new module — OK.
- Axiom drift bounded to `{propext, Classical.choice, Quot.sound}` — OK.
- Renamed premises / trivialized cases — OK (no theorem takes its own bound as an input).
- Scope drift in `audit/DIRECT-CLOSURE.md` — OK (input list disclaimer preserved).
- Bundle hash match (three files) — OK (all three sha256 sums match receipt).
- Proof correctness of `totalGas_le`, `totalGas_lt`, `totalAppends_le_totalGas` — OK.
- Consistency of `uniform_envelope` with declared shape — OK (exact `⟨total_lt ..., totalGas_lt ...⟩`).

## Findings
No BLOCKING findings. No ADVISORY findings.

Detailed observations:

1. `Eip8282/Audit/Integrator/ReferenceBlockGasCapacity.lean:27` — `totalGas`
   is defined as `(blocks.map (fun b => b.gas.val)).sum`, mirroring
   `ResourceBounds.totalAppends` on the gas dimension. Clean definition.
2. `Eip8282/Audit/Integrator/ReferenceBlockGasCapacity.lean:31-40`
   (`totalGas_le`) — induction on list. `nil` closes by `simp`. `cons`
   uses `b.gas.isLt : b.gas.val < 2^64`, rewrites the goal into
   `b.gas.val + totalGas bs ≤ (bs.length+1)*(2^64-1)`, then `Nat.add_mul`
   + `omega` closes using `ih` and `hb`. Structure and dependencies are
   identical to `ResourceBounds.total_le` (the sibling on
   `b.appends`/`b.charged`).
3. `Eip8282/Audit/Integrator/ReferenceBlockGasCapacity.lean:44-51`
   (`totalGas_lt`) — same shape as `ResourceBounds.total_lt`: uses
   `hs.length_le_card` + `Fintype.card_fin` to derive
   `blocks.length ≤ 2^64`, multiplies by `2^64-1`, then transitivity
   with `2^64*(2^64-1) < 2^128` (`decide`). Correct.
4. `Eip8282/Audit/Integrator/ReferenceBlockGasCapacity.lean:55-63`
   (`totalAppends_le_totalGas`) — induction on the list. `cons` case
   rewrites the goal to `b.appends + totalAppends bs ≤ b.gas.val + totalGas bs`
   and closes with `omega` using `ih` and `b.charged : appends ≤ gas.val`.
   Correct pointwise-from-charged use.
5. `Eip8282/Audit/Integrator/ReferenceBlockGasCapacity.lean:67-70`
   (`uniform_envelope`) — definitionally equal to
   `⟨total_lt blocks hs, totalGas_lt blocks hs⟩`. No additional claim.
6. The four `#print axioms` lines in
   `Eip8282/Audit/Integrator/ReferenceBlockGasCapacity.lean:72-75` and the
   mirroring four lines in `Eip8282/Audit/Trust.lean:3860-3863` are
   syntactically well-formed and target the exact declaration names
   listed in the axioms receipt.
7. `Eip8282/Audit/Integrator.lean:506` correctly exposes
   `ReferenceBlockGasCapacity` via a single import.
8. `audit/DIRECT-CLOSURE.md:69-104` — the new "Block-level gas envelope —
   capacity candidate" section explicitly disclaims that "arbitrary Θ
   histories" are covered, requires the input `BlockUsage` list to come
   from "actual transaction gas accounting, including nested calls and
   refunds", and confirms that "canonical Ethereum production of the
   input list, block-slot admission and per-block gas admission remain
   distinct obligations". No claim of canonical production, sequencer
   adoption, or per-transaction gas accounting. Scope discipline holds.

## Axiom audit
Cross-check against `audit/receipts/direct-block-gas-capacity-axioms-20260911.json`:
- `Eip8282.Audit.Integrator.ReferenceBlockGasCapacity.totalGas_le` →
  `{propext, Quot.sound}` per receipt. Consistent with the pure
  Nat/List induction; no `Classical.choice` invoked (no `Fintype.card`
  path).
- `Eip8282.Audit.Integrator.ReferenceBlockGasCapacity.totalGas_lt` →
  `{propext, Classical.choice, Quot.sound}` per receipt. Consistent
  with the `Fintype.card_fin` path picking up `Classical.choice` (same
  as `ResourceBounds.total_lt`).
- `Eip8282.Audit.Integrator.ReferenceBlockGasCapacity.totalAppends_le_totalGas` →
  `{propext, Quot.sound}` per receipt. Consistent with the pure
  Nat/List induction; no `Fintype` path.
- `Eip8282.Audit.Integrator.ReferenceBlockGasCapacity.uniform_envelope` →
  `{propext, Classical.choice, Quot.sound}` per receipt. Consistent
  because it consumes `totalGas_lt` (and `total_lt`) which already
  carry `Classical.choice`.

All four declarations remain within the declared trust base. No
`sorryAx`, no `other_axioms`. Consistent with `Trust.lean`
scope.

## Bundle hash verification
Computed via `sha256sum` on the three module paths:
- `Eip8282/Audit/Integrator/ReferenceBlockGasCapacity.lean`
  measured `e2b728e206c4f82c1ccbdd1d9d62c003bbf032a3b3d54cdb486aa98edac642d6`
  vs receipt `e2b728e206c4f82c1ccbdd1d9d62c003bbf032a3b3d54cdb486aa98edac642d6`
  — MATCH.
- `Eip8282/Audit/Integrator/ResourceBounds.lean`
  measured `099a06b7178531f58fb8c889ecd583bbe7fd890d1490ae0261d971f5640d87b6`
  vs receipt `099a06b7178531f58fb8c889ecd583bbe7fd890d1490ae0261d971f5640d87b6`
  — MATCH.
- `Eip8282/Audit/Integrator/AppendStorage.lean`
  measured `06e1f4e9e0c0f447c52eff02f853b9f15b511f58b944e8ecb21745e4e54c23eb`
  vs receipt `06e1f4e9e0c0f447c52eff02f853b9f15b511f58b944e8ecb21745e4e54c23eb`
  — MATCH.

All three bundle hashes match the receipt exactly.

## Conclusion
The commit adds a small, honest arithmetic corollary layered on top of
the audited `ResourceBounds.BlockUsage` typing and the same
`Fintype.card_fin` slot-uniqueness trick used by `ResourceBounds.total_lt`.
`totalGas_le` and `totalAppends_le_totalGas` are pure list inductions
using `Fin.isLt` and the pre-existing `BlockUsage.charged` field
respectively; `totalGas_lt` is a direct structural clone of
`total_lt` on the gas dimension; `uniform_envelope` is a bare `⟨_, _⟩`
pair with no additional claim. No `sorry`/`admit`, no trivialized
premises (no theorem takes its own bound as an input), axiom set matches
the receipt, bundle hashes match exactly, and the DIRECT-CLOSURE
disclaimer preserves the same trust boundary as `ResourceBounds`: the
input `BlockUsage` list still must be produced by upstream Ethereum
admission machinery, no sequencer is adopted, and no per-transaction
gas accounting is claimed.

VERDICT: CLEAN
