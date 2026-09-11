# Independent review — grok delta lots 41-42 (ec15c4b..94d4178)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Delta base: ec15c4b
Delta head: 94d4178
Branch: origin/grok/eip-slot-withdrawal-extraction-20260911
Started at: 2026-09-11T13:35:46Z

## Scope items reviewed
- Sorry/admit scan on modified regions.
- New declaration axiom-drift audit (spot sample).
- Scope respected: only 5 files touched (2 Lean src + 1 test + 2 receipts).
- Consistency of the small `ProtocolWithdrawalExtraction.lean` (+7) edit — docstring only, no code drift.
- Both new receipts (189e92e5, 80a93a24) fetched from the grok branch and cross-checked against the delta they attest.
- Non-trivial kill lines in new mutants.
- Commit-message accuracy for 189e92e / 80a93a2 (Python `Uint64` wrap and `validate_header` slot independence): demonstration, not adoption.
- No parallel framework / no new `axiom` or `constant` declarations.

## Findings
1. Sorry/admit: grep of `+` lines in the three edited Lean files matches only prose uses ("admits this pair", "duplicate `slot_number`s are admitted", `validate_header_admits_duplicate_slots`). No `sorry`/`admit` tactic, no `sorryAx`. Zero.
2. Axiom drift: no `axiom` / `constant` keywords introduced in the delta. New `#print axioms` blocks report only `propext` and `Quot.sound` — consistent with `by decide` / propositional equality reasoning about `Nat` and finite lists. The receipt schedules each new lemma's axiom set explicitly.
3. Scope: 5 files, 517+/7- across exactly the advertised subset. No edits to `Block`, `Integrator`, `Makefile`, `Trust`, `YAML`, `DIRECT-CLOSURE`, or SYSTEM/gas/history — matches the receipt `wiring_not_applied` field.
4. `ProtocolWithdrawalExtraction.lean` (+7): entirely inside a `/-- ... -/` docstring block enumerating open hypotheses. Adds two named hypotheses: `TimeFitsU64` wrap is `timeAtSlotWrap` (identity under Fits) and `validate_header` does not bind `header.slot_number`. Both are the exact hypotheses proved in the ProtocolSlotExtraction additions. Not scope drift.
5. Receipts:
   - `189e92e5…json` (lot 41): pinned base sha `681d1866…` matches this project's `main`/current head; toolchain `leanprover/lean4:v4.31.0`; `files_sha256` supplied for the three edited Lean files; commands include per-module `lake env lean` and `make check` with tail "check ok"; axiom map lists only `propext`/`Quot.sound` per lemma. `previous_lot` chains back to `d5499b2 / ec15c4b`, matching the delta base.
   - `80a93a24…json` (lot 42): `previous_lot` cites `189e92e5` and `8ce9d80` — consistent chain. Files sha256 updated. Cited fork.py line numbers 323/431-486/472 match the docstring citations in the code.
6. Mutants (`ProtocolSlotWithdrawalMutants.lean`): six time-wrap mutants + three `validate_header` slot-number mutants. Non-trivial:
   - `time_nat_ne_wrap_two_pow_61` — witnesses `timeAtSlotNat ≠ timeAtSlotWrap` at slot 2^61; this shows Lean's `Nat` sum is not adopted as the Python `Uint64` result outside the `TimeFitsU64` domain.
   - `bounded_time_is_not_necessary` — `slot < 2^60` bound is sufficient not necessary (2^60 still Fits).
   - `validate_header_is_not_slot_nodup` — refutes a `Nodup` mutant on `slot_number`.
   - `validate_header_admits_duplicate_slots` — direct witness `[1/7, 2/7]`.
   - `validate_header_ignores_slot_relabel` — relabel invariance under `number`-only walk.
   All discharge into named lemmas in `ProtocolSlotExtraction.lean`.
7. Commit messages `189e92e` and `80a93a2` describe demonstrations of Python semantics (archived `Uint64` wrap; `fork.py:323/472`), not adoption. The `TimeFitsU64` gate keeps Lean's `timeAtSlot.val` equal to the wrap only inside its domain (`timeAtSlot_eq_wrap` requires `h : TimeFitsU64 …`). The refutation lemma `timeAtSlotNat_ne_wrap_two_pow_61` demonstrates disagreement outside the domain. Consistent with the receipt's `not_claimed`: "Python Uint64 constructor as a kernel object; the wrap is the archived % 2^64 model".
8. No parallel framework — additions live inside the existing `Eip8282.Audit.Integrator.ProtocolSlotExtraction` namespace, extending `ElAppended` / `timeAtSlotNat` / `TimeFitsU64`. `ElHeader` is a new record but immediately linked back to the existing `ElAppended` walk via `ElHeadersAppended` and `el_headers_number_nodup := el_nodup`.

## Axiom audit (sample)
Per receipt `axioms.new_in_this_lot`:
- `timeAtSlotWrap_lt`, `timeAtSlotWrap_eq_of_fits`, `TIME_MOD_pos`, `TIME_MOD_eq`, `timeAtSlot_eq_wrap`: `[propext]` only.
- `timeFits_min_genesis_two_pow_60`, `timeFits_of_bounded_not_necessary`, `timeFits_rejects_min_genesis_two_pow_61`, `timeAtSlotNat_min_genesis_two_pow_61`, `timeAtSlotWrap_min_genesis_two_pow_61`, `timeAtSlotNat_ne_wrap_two_pow_61`: `[propext, Quot.sound]`.
- `el_headers_appended_iff`: `[]`; `el_headers_number_nodup`: `[propext]`; `el_headers_relabel_slot`: `[]`; `sampleEl_*` witnesses: `[]` / `[propext]`; `el_headers_slots_need_not_nodup`, `validate_header_slots_not_nodup`: `[]`.
No `sorryAx`, no project axiom.

## Bundle/receipt provenance sample
- `audit/receipts/grok-slot-withdrawal-extraction-189e92e5fd9a88861be5485fea0976bd02c5f90a.json`: base sha `681d1866…` matches project state; toolchain `lean 4.31.0`; commands include `lake build EvmYul.FFI.ffi:dynlib`, per-module `lake env lean`, and `make check` returning "check ok" with 3608 jobs; `cited_functions` maps to `specs/phase0/beacon-chain.md` (rehashed sha256 `95bbeca1…`).
- `audit/receipts/grok-slot-withdrawal-extraction-80a93a24ee0cc64aa37fbe900d997a12ce001ac7.json`: `previous_lot.proof = 189e92e5…` / `previous_lot.receipt = 8ce9d80…` — chain is well-formed; `archived_bodies_rehashed` cites `src/ethereum/forks/amsterdam/fork.py`; `not_claimed` explicitly disavows `validate_header` binding `slot_number`.

## Conclusion
The delta is a compiled additive extraction on the slot/withdrawal lane. It (a) models Python `Uint64(genesis + slot*12)` as `timeAtSlotWrap` and proves the Lean `timeAtSlot.val` equals the wrap only under `TimeFitsU64`, exhibiting an explicit disagreement at slot 2^61; and (b) extracts `ElHeader.slotNumber` from fork.py:323 and refutes the mutant that would require `slot_number` uniqueness in `validate_header`. Both new lots respect scope, contain no `sorry`/`admit`/`axiom`/`constant`, chain their receipts correctly to the previous lot, and provide non-trivial kill lines. The 7-line edit to `ProtocolWithdrawalExtraction.lean` is a docstring-only synchronization of the named open hypotheses. Python semantics are demonstrated, not adopted.

VERDICT: CLEAN
