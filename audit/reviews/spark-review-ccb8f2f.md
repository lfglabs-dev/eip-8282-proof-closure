# Independent review — grok delta lot 43 (94d4178..ccb8f2f)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Delta base: 94d4178
Delta head: ccb8f2f
Branch: origin/grok/eip-slot-withdrawal-extraction-20260911
Started at: 2026-09-11T13:39:58Z

## Scope items reviewed
- Sorry/admit scan across the two modified `.lean` files
- Axiom whitelist for a sample of the 24 new `#print axioms` entries
- File-scope: only 3 files touched, matching commit stat and receipt scope list
- Receipt provenance / cited-function pinning
- Non-trivial mutant kill lines in `ProtocolSlotWithdrawalMutants.lean`
- Commit-message accuracy for a5da641 ("bind withdrawal-credential first-byte prefixes")
- No parallel framework introduced (no new `axiom`, no adopter machinery)

## Findings
1. No `sorry` or Lean `admit` tactic in either modified file. The occurrences of `admit` in `ProtocolWithdrawalExtraction.lean` at 5547/5570/5575/5767/5783 are Python-spec terminology (structure field `admits : engineAdmits c = true`) and pre-exist the delta; not introduced by this lot.
2. No `axiom` declarations added; no `constant`. Receipt records new declarations with only `propext` (for `iff`-shaped) and empty axiom sets (for `rfl` bytes/`rfl` cons/nil). Consistent with the shapes reviewed: `bls/eth1/compounding_prefix_byte` are `rfl`; `hasEth1Bytes_nil`, `hasEth1Bytes_cons`, `hasEth1Bytes_bls`, `hasCompoundingBytes_cons`, `hasCompoundingBytes_eth1`, `hasExecutionBytes_*` are direct `rfl` on the `match` on `[]` vs `b :: _`; iff and swap lemmas use `split`/`simp` on decidable equalities.
3. Scope respected. `git diff --name-only` yields exactly `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean`, `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean`, `audit/receipts/grok-slot-withdrawal-extraction-a5da641e77ace641adf6907752f53ffa9802a7fb.json`. Receipt `scope` array lists the same 3 paths. Wiring-not-applied section explicitly disclaims sibling modules (StageExtraction, Makefile, Integrator, Trust, YAML, DIRECT-CLOSURE, SYSTEM/block/gas/history) — matches diff.
4. Pinned reference correctness. Doc-strings cite phase0:553 (BLS 0x00), phase0:554 (ETH1 0x01), Electra:285 (COMPOUNDING 0x02), Capella:317 ([:1] test), Electra:634-635 / 641-645 / 651-658 (has_compounding / has_execution), Electra:733-740 (get_max_effective_balance). Receipt `cited_functions` mirrors these, and `archived_bodies_rehashed` names phase0/capella/electra beacon-chain.md with SHA-256 digests.
5. New mutants are non-trivial: `prefix_swap_flips_max` refutes the 0x01↔0x02 swap by delegating to `prefix_swap_changes_max` (which unfolds `maxEffectiveBalance` to `MIN_ACTIVATION_BALANCE ≠ MAX_EFFECTIVE_BALANCE_ELECTRA` via `decide`); `bls_prefix_is_not_execution` blocks accepting `0x00`; `first_byte_selects_tag` binds the `WithdrawalPrefix` tag to the singleton first-byte list across all three prefix values; `empty_cred_is_not_eth1` blocks empty-slice acceptance. Each corresponds to a distinct one-byte mutant of the archived predicates.
6. Commit message a5da641 accuracy. The proof binds the archived first-byte constants (BLS/ETH1/COMPOUNDING) to Bytes1 `[:1]` tests via `credOfByte` / `hasExecutionBytes`, ties them to the existing `WithdrawalPrefix` inductive, and preserves the 31-byte tail as named input (see docstring at line 411 and OPEN section at 106-110). No protocol adoption: `hasExecutionCredential_of_byte` is proved as a *bridge* between the byte view and the tag view, `viewWithByte` constructs a `ValidatorView` from a byte without asserting the SSZ decode obligation, and the receipt `not_claimed` explicitly disclaims protocol adoption, canonical history, SSZ injectivity, and interpretation of bytes 1-31. This matches the message.
7. No parallel framework. All new declarations live in the existing `ProtocolWithdrawalExtraction` namespace; they reuse `WithdrawalPrefix`, `ValidatorView`, `hasExecutionCredential`, `isFullyWithdrawable`, `maxEffectiveBalance`, `MIN_ACTIVATION_BALANCE`, `MAX_EFFECTIVE_BALANCE_ELECTRA`, and `isFullyWithdrawable_rejects_other_prefix` from the pre-existing file rather than shadowing them.

## Axiom audit (sample)
- `bls_prefix_byte : BLS_WITHDRAWAL_PREFIX = 0` — `rfl`. Receipt claims `[]`. Consistent.
- `credOfByte_eq_eth1_iff` — `split`/`simp` on decidable ifs. Receipt claims `[propext]`. Consistent with iff-elimination through `simp`.
- `prefix_swap_changes_max` — rewrites via `maxEffective_of_eth1_byte` / `maxEffective_of_compounding_byte`, closes by `decide` on `MIN_ACTIVATION_BALANCE ≠ MAX_EFFECTIVE_BALANCE_ELECTRA`. Receipt claims `[propext]`. Consistent (the rewrite lemmas each carry `propext`).
- `isFullyWithdrawable_rejects_bls` — reuses pre-existing `isFullyWithdrawable_rejects_other_prefix` after mapping `.cred = credOfByte 0x00` to `.cred = .other` via `credOfByte_bls`. Receipt claims `[propext]`. Consistent (inherits from the reused lemma).

## Bundle/receipt provenance sample
- `audit/receipts/grok-slot-withdrawal-extraction-a5da641e77ace641adf6907752f53ffa9802a7fb.json` records commit `a5da641`, base `681d1866` on `codex/source-ordinary-block-candidate-20260911`, previous lot proof `80a93a24` / receipt `94d41788`, toolchain Lean `v4.31.0` / commit `68218e876`. Commands include `make check` with tail `Build completed successfully (3608 jobs). ... check ok`. `files_sha256` lists the two Lean files plus the sibling `ProtocolSlotExtraction.lean` (unchanged) — the unchanged-sibling hash is a defensible pin. `wiring_not_applied` correctly notes the Makefile test list still omits `ProtocolSlotWithdrawalMutants`, so the local gate is `lake build` of the test module (not `make check` traversal). `not_claimed` lists closure of P-SUBMIT-1 / P-DRAIN-1 / P-CONTROL-1, protocol adoption, canonical history, SSZ injectivity, and interpretation of bytes 1-31 — matches the classification `compiled_additive_extraction_not_adoption_not_guarantee_closure`.

## Conclusion
The delta is a self-contained, additive extraction of the archived first-byte withdrawal-credential prefixes (0x00 / 0x01 / 0x02) into named `Nat` constants plus decidable Bytes1-slice predicates, wired to the pre-existing `WithdrawalPrefix` inductive via `credOfByte` and `viewWithByte`. It carries only `propext` on iff/rewrite lemmas and no axioms on `rfl` byte facts. The mutant tests kill non-trivial one-byte swaps and an empty-slice acceptance. The 31-byte credential tail and SSZ container decode remain explicitly named open hypotheses; no protocol adoption or guarantee closure is claimed. Scope respects the 3-file boundary, no sibling module (SlotExtraction, StageExtraction, Trust, YAML, SYSTEM/block/gas/history) is touched, and no parallel framework is introduced. Commit message accurately reflects the change.

VERDICT: CLEAN
