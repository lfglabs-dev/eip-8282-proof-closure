# Independent review — grok slot/withdrawal extraction lot-45 (93c39e0)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commits: 4126919 (proof), 93c39e0 (receipt)
Head: 93c39e0 on `origin/grok/eip-slot-withdrawal-extraction-20260911`
Previous CLEAN: 078ab58 (already merged into main via PR#37)
Started at: 2026-09-11

## Scope of the delta

`git diff 078ab58..93c39e0 --name-only` yields exactly three files:

- `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean` (+153 net)
- `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean` (+24)
- `audit/receipts/grok-slot-withdrawal-extraction-41269190460b821340cc62430a49382d63451699.json` (new, +122)

This exactly matches the `scope` field in the new receipt. No other file
(Integrator, Guarantees, Trust, Makefile, DIRECT-CLOSURE.md, YAML manifests,
SYSTEM/block/gas/history modules) is touched. No parallel framework is
introduced — the delta adds definitions inside the pre-existing
`ProtocolWithdrawalExtraction` module and consumes them from the pre-existing
`ProtocolSlotWithdrawalMutants` test module.

## Check 1 — Zero `sorry` / `admit` tactic uses

`git show 93c39e0:Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean |
grep -nE 'sorry|admit\b|axiom '` returns two hits at lines 5816 and 6036;
inspection of the surrounding text shows both are English uses of the word
"admit" inside `/-- … -/` docstrings (`engineAdmits` and a payload-facts
comment describing consensus admission). A precise regex for tactic use
(`:=\s+sorry|by sorry|by admit\b|:= admit\b`) returns 0 hits in either the
Integrator file or the mutants file. No `sorryAx` reference is added. No
`axiom` declaration is added.

## Check 2 — Axioms in whitelist

The receipt records the axioms of every new export. Every entry is either
`[]` (`executionAddress_bits`, `accountAddress_size_ne_u256`,
`bytesLeToNat_nil`, `execution_width_ne_credential`) or `['propext']`. No
`Classical.choice`, no `Quot.sound`, no project axiom, no `native_decide`.
The seventeen new production exports and the four new mutation exports all
fall inside the standard {`propext`} subset of the allowed
{`propext`, `Classical.choice`, `Quot.sound`} whitelist. Confirmed by
comparing to the previous review (`spark-review-f2ab5eb.md`) which
established the whitelist across the merged trunk.

## Check 3 — Scope exact

Confirmed above: three files match the receipt's `scope` array
bit-for-bit; SHA-256 of the two Lean files at commit 93c39e0 equals the
values recorded under `files_sha256`:

- ProtocolWithdrawalExtraction.lean = `e4c125d4db7e4b6d7229b97c26d2b310b40c1996de6e694b3be95488dae9094b`  MATCH
- ProtocolSlotWithdrawalMutants.lean = `6c5e74fad9462d84d19000ee179fed552244241304e6ded6dcf4a12ce337f1cf`  MATCH
- ProtocolSlotExtraction.lean is listed under `files_sha256` for context; the
  file is unchanged in the delta, so the recorded hash is that of the trunk
  version (checked: the diff touches only the two files above).

## Check 4 — Receipt pinned correctly

Receipt filename encodes the proof commit
`41269190460b821340cc62430a49382d63451699` — matches
`git log`'s `4126919…` short hash of the parent of 93c39e0. The receipt's
`commit` field matches the filename hash. The `previous_lot.receipt`
`078ab588…` matches the previous CLEAN receipt (merged in PR#37), and
`previous_lot.proof` `7d8fc7b1…` matches the previous proof commit. The
`base` block pins `sha` `681d186…` which is the local trunk head at
`main`/`codex/source-ordinary-block-candidate-20260911`.

## Check 5 — Non-trivial mutants

Four new theorems in `ProtocolSlotWithdrawalMutants` (lines 202-220):

- `execution_address_is_not_uint256`: separates the 160-bit `AccountAddress`
  from a 256-bit UInt256 mistake — rules out the "credit as UInt256" mutation.
- `execution_address_is_big_endian`: on the concrete sample `[1,0,…,0]`,
  BE = `256^19` while LE = `1`; a byte-order swap is disequal.
- `execution_width_is_not_credential`: `20 ≠ 32` rules out reading the whole
  credential slot rather than `credentials[12:]`.
- `account_address_wraps_two_pow_160`: exposes the `Fin 2^160` wrap, showing
  an unbounded-Nat interpretation would credit address 0.

Each mutant references the extracted invariants (not vacuous `True` or
self-implication) and cites the archived Capella section as its intent.
The consequent inequality/equality has a computable witness (`sampleBeAddr`
or `decide`).

## Check 6 — Commit 4126919 accuracy

Commit message: "proof: bind ExecutionAddress 20-byte big-endian decode".
Body: "Extract Capella:454 ExecutionAddress as AccountAddress.ofNat of the
BE 20-byte integer. Width is 2^160, not UInt256. A little-endian mutant of
[1,0,…,0] is 1, not 256^19. Wrap of 2^160 is 0."

Verified inside `ProtocolWithdrawalExtraction.lean` (lines 736-871): the
delta adds `bytesBeToNat`, `bytesLeToNat`, `executionAddressNat`,
`executionAddress`, plus width/wrap/BE-vs-LE theorems. `executionAddress`
returns `AccountAddress.ofNat (bytesBeToNat (bytes.take 20))`, and
`executionAddress_val_eq` grounds the projection.

Importantly, protocol semantics are NOT adopted: the module's OPEN block
(lines 105-108) is rewritten to list "SSZ byte-string decode of the whole
`Withdrawal` container (field order, `credentials[12:]`, and 20-byte BE
`executionAddress` are extracted)" as OPEN, and lines 158-160 list "SSZ
`Withdrawal` root injectivity" (with the BE decode explicitly folded into
the extracted-not-proved set) as OPEN. `WithdrawalsRootMatch` remains
described, not applied. No SSZ container decode adapter is introduced; no
Trust.lean, DIRECT-CLOSURE.md or YAML manifest is edited. The receipt's
`wiring_not_applied` and `named_hypotheses_still_open` sections match this
boundary.

## Check 7 — No parallel framework

The delta is exclusively additive: new definitions
(`bytesBeToNat`, `bytesLeToNat`, `executionAddressNat`, `executionAddress`,
`sampleBeAddr`) plus theorems added to the existing
`ProtocolWithdrawalExtraction` module, plus four theorems restated in the
existing `ProtocolSlotWithdrawalMutants` module. No new module file. No
duplicate `AccountAddress` / `ExecutionAddress` / `Withdrawal` type is
introduced (the delta uses EvmYul `AccountAddress.ofNat` and
`AccountAddress.size` directly). `executionAddress` returns EvmYul's
`AccountAddress`, not a shadow.

## Findings

None (no BLOCKING or ADVISORY findings).

## Conclusion

The lot-45 delta (`4126919` + `93c39e0`, +299 lines, 3 files) is purely
additive over `078ab58` and passes all seven blocking checks. It extracts
the `Capella:156/454` 20-byte big-endian `ExecutionAddress` → EvmYul
`AccountAddress` (Fin `2^160`) decode as an isolated lemma set, together
with four mutation witnesses (UInt256 miswidth, little-endian mutant,
credential-length mutant, `2^160` wrap). Protocol semantics are NOT
adopted: the whole-container SSZ byte-string decode, `SszWithdrawal` root
injectivity and `WithdrawalsRootMatch` remain named OPEN in the module
docstring and the receipt. All new theorems trace their axioms to at most
`propext`; no `sorry`/`admit` tactics; no project axiom introduced. The
new receipt is correctly pinned to the proof commit, prior receipt/proof
commits, and local trunk base; the recorded SHA-256 of the two Lean files
matches the on-disk contents at commit 93c39e0.

VERDICT: CLEAN
