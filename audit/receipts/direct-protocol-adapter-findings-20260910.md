# Verified adapter findings and remaining decisions

This is an internal integration record. No author message, normative change,
publication or fork adoption is authorized by this record.

## Old blob tariff is not Amsterdam's tariff

Original helper `1015d44e`, source SHA256 `d210786cb742d0bc3c9e6f6052163c6c56aa6b602c53be2c494eed7b3865845a`,
labelled the old `BlockHeader.getBlobGasprice` coverage test as a source
validation clause. The literal formulas use different update fractions:
old pinned EVMYulLean `3338477`, Amsterdam `11684671`. At excess blob gas
`3338477`, the archived integer recurrence returns respectively `2` and `1`.
A cap of `1` therefore passes this source price test but fails the old one.
This is an arithmetic example, not a canonical block or exploit reproduction.
The complete source and independent review are archived in
`direct-hermes-context-contributions-20260910.json` and
`direct-reference-admission-original-review-faraday-20260910.json`.

Refuted: an unconditional implication from source blob-price admission to the
old coverage test under identical header fields. The original conditional Lean
arithmetic theorem remains valid. Functional impact: using it unconditionally
would omit admitted source transactions or misstate their entry funding.
Economic impact: in the example, old blob prepayment is twice the source amount.
Security impact: this is a gap in the funding/reachability justification; no
EIP-8282 bytecode vulnerability is established by it. Author intent would not
repair that implication.

Local correction: `SourceChecks` is an explicitly incomplete set of checks on
represented fields. `OldConsumerCompatibility` separately requires the pinned
sender's presence and coverage of the old blob tariff. The history consumers
require both. Actual source blob validation, default-account representation,
nontruncating Uint conversions and type-4 transactions remain open. These
transactions have not been excluded from the proposed protocol domain.

## Withdrawal computations and credited payload lists differ

The original C helper counts lists newly computed by `process_withdrawals`.
At the pinned Gloas source, an empty parent returns before updating
`payload_expected_withdrawals`; it does not clear that cache. Consequently,
identifying the per-block newly computed lists with the payload lists needs a
proof. The C helper explicitly left this transport open.

`ProtocolWithdrawalExpectationState` now starts from the exact empty cache in
`upgrade_to_gloas`, applies the update/retain recurrence, and counts every
resulting payload list. It derives the per-payload and lifetime count through
the accepted-slot guards, including repeated list contents. It does not assume
that each computed list is credited at most once. Both previously supplied
stage bounds are derived by `ProtocolWithdrawalStageExtraction`.

Functional/economic implication: a funding ledger must count the actual credited
items, not just invocations which recompute the cache. Security implication:
confusing those counts could understate the envelope used for queue bounds.
No repeated canonical mint or protocol exploit is established here. Actual
candidate extraction, accepted chronology, payload verification and EL credit
updates must still supply the same history and dispatch.

## Exact CL-to-EL check and proposed cryptographic boundary

Newly archived complete bodies at CL
`ad0058fd0d34c5dcf504fa51ea2f4f11077b9996` are Git-tree verified in
`direct-cl-inheritance-sources-20260910.json`. Gloas fork-choice lines 659–701
check the payload slot against the beacon state, the parent hash, timestamp,
committed gas limit and block hash, then compare the SSZ roots of the complete
withdrawal lists and ask the execution engine to validate the payload.
The checked equality is of SSZ roots, not an unconditional equality of lists.
Gloas uses ProgressiveList here; its type alone supplies no cap of sixteen.

Proposed boundary for Thomas's decision: treat absence of a collision between
the two particular complete SSZ withdrawal lists checked by an accepted
envelope as a cryptographic assumption, with exact SSZ encoding/decoding and
SHA-256 implementation identified. This is not global injectivity of a
256-bit hash, which would be false, and is not an assumption about the projected
recipient/amount lists alone. Before accepting that boundary, keep the
list-transport theorem explicitly conditional. An alternative is to keep the
payload-list correspondence as an external engine-validation boundary, also
explicit and pending acceptance. Neither alternative closes engine admission,
canonical selection, one-time execution, or EL/SYSTEM scheduling by itself.

BLS and consensus processing outside the three guarantees remain distinct from
these necessary EL/SYSTEM and funding bindings. Fork/inhibition/upgrades still
await the earlier scope decisions; no variant has been adopted here.
