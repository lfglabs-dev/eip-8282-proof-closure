# Independent final registration review

Verdict: CLEAN for registration of the three conditional direct parents. No documentation/type mismatch or registration blocker found in the reviewed changes. This is not a full-build receipt or a conclusion that protocol applicability is closed.

Worktree: `/Users/thomas/work/eip-8282/direct-closure-implementation`.
Read-only review; no source changes or Lean builds by reviewer. Executed the read-only metadata/pin check `python3 scripts/audit_metadata.py`: `audit-check ok`.

## Registered statements and facade

The YAML retains exactly the canonical IDs in their required order: P-SUBMIT-1, P-DRAIN-1, P-CONTROL-1. Parent and evm.theorem point to DirectGuarantees.psubmit1_direct, pdrain1_direct and pcontrol1_direct respectively. These are the reviewed parameter-code predicates at the pinned runtime for both kinds. PControl retains RuntimeControl, actual Lambda Initializes and SystemProgress; no part of that conjunction was dropped.

AllGuarantees now imports DirectGuarantees and contains explicit Lean examples of these same three predicate instances for arbitrary kind, while retaining the historical imports. Registry changes only its evm description; it adds no public ID or artificial closure status. DirectGuarantees has only a registration-comment change in this delta: the theorem types and proofs are unchanged. No finite receipt/native theorem is conjoined into the direct correctness parents.

The checker adds precisely THETA_CONDITIONAL_FORALL to accepted scope labels and keeps existing canonical-ID, pin, literal and theorem-name checks intact. This label accurately distinguishes actual complete-call conditional quantification from CFG/finite trace scopes. The checker's preexisting short-name existence scan is still only a metadata check; the facade examples and frozen full compilation are the typed validation. The docs do not portray the Python checker as a proof checker.

## Scope and assumptions

Every row separates CHECKED theorem scope from PARTIAL overall classification and OPEN protocol_closure. The common domain matches the current structures: pre-target owner, real/apparent value equality, calldata.size<2^256, independent budget<2^128, ordered HEAD/TAIL, tail/count within budget, enabled excess+count within budget, and either inhibition or natural fee numerator<=2892. Drain additionally discloses the physical queue representation and exit source width. No original-code pin, path witness, assumed fee completion or desired poststate is hidden inside those domains.

The prose correctly states admission necessity and actual-result properties, not unconditional paid-user liveness. Deposit amount minimum is the actual 10^9 gwei, with fee plus amount*1gwei payment. Exit authenticity is caller20||pubkey48. Getter claims concern account lookups, created accounts and logs; access bookkeeping is expressly allowed to differ. Failed completed calls restore the pre-transfer journal, with evaluator OutOfFuel outside the .ok tuple. No transaction gas-fee refund claim is introduced.

Control's initializer domain discloses preimage, absent target/no collision, fuel and branch-specific constructor resources and actual creation success. It makes no low-gas creation-liveness or canonical genesis-address assertion. SYSTEM progress discloses owner, permission, 2.5M gas and Context.fuel>=8503, without an enabled-state premise.

assumptions.yaml preserves historical A-ABSTRACT-TX as OPEN/superseded and distinguishes it from the new parent dependencies rather than claiming it proved. Historical packed reachability and synthetic-world limitations remain explicitly scoped to their old evidence. The new local-domain, pinned-semantics and protocol-closure records correctly identify the remaining environmental/application obligations. A-NATIVE-DECIDE is limited to historical evidence and the five transported finite mutation receipts, not the universal parents or funded LOG0 certificate. Deployment/fork binding remains OPEN; live codehash observation is not offered as a full closure shortcut.

README and the new DIRECT-CLOSURE section say the conditional theorems are proved while protocol applicability remains open. They disclose the untruncated tariff/safe domain and 2893 arithmetic counterexample, finite mutation scope, standard parent axioms, remaining recursive funding/event/history composition and pending frozen full-build validation. Older DIRECT-CLOSURE entries that said registration was pending are explicitly identified as prior snapshots, not silently promoted to closed protocol results.

## Mutation metadata and trust

Checked the selected mutation definitions and pinned bytes:

- LOG0 length: deposit byte274, PUSH1 operand184 -> 0; not byte269's calldata-copy length.
- Gate: deposit byte22, EQ0x14 -> LT0x10.
- TARGET: deposit byte571, 8 -> 9.
- Deposit cap: byte304, 64 -> 32.
- Exit cap: byte244, 16 -> 8.
- Deposit partial HEAD slot: byte483, slot2 -> slot9.

DirectThetaKills supplies exactly the 1/3/2 same-PSubmit/PDrain/PControl negations selected in YAML. The funded LOG0 has the actual Θ transfer and 158 kernel-checked steps. The other five retain their individually disclosed old native receipt axioms. Those proofs and wrapper were independently reviewed in `/tmp/eip-DirectThetaSubmit-review.md`; their theorem types are unchanged here.

The new metadata/docs explicitly reject a universal sibling-survival claim and preserve the real stale-slot overlap with PSubmit's SYSTEM record frame. The overlap is described as a consequence of the predicates, not an additional compiled seventh refutation. Historical Boolean sibling checks are labeled finite. No clause was weakened to force artificial isolation.

Trust imports the test-only collector and prints its three dependency sets separately; existing direct-parent #print axioms remain present. Makefile adds DirectThetaKills to the test build, thereby including the funded certificate/wrapper via imports. It does not make tests conjuncts of correctness theorems. The normal lake build already reaches the facade/Integrator/Trust; final make check remains root's pending frozen-candidate validation.

## Historical evidence and change boundaries

Verified byte-for-byte against HEAD that these archives contain the complete previous files:

- audit/history/pre-direct-guarantees-20260909.json = prior audit/guarantees.yaml, SHA256 a2b33fe9c37c59ffc130f7acb6f1507df9f332e5525351192dcf7af98d41b97e.
- audit/history/pre-direct-assumptions-20260909.json = prior audit/assumptions.yaml, SHA256 7a08d31e70fe8ffbe10a132c14a64c53522eb8b776751ded0f898858e676f158.
- audit/history/pre-direct-README-20260909.md = prior README.md, SHA256 63c4b18f5073faa23f7853d080802602f93e49457fdab3186f6e15e3504c9a77.

Historical Lean parent files have no working diff. The preexisting untracked CreationFunding.lean is outside this registration review; this report does not certify that separate proof lane. No normative pin change, merge, deployment or external publication is part of the reviewed action.

Acceptance remains source-bound: commit the reviewed candidate, run frozen full make check and retain its actual result. The current prose already says this receipt is pending. After it passes, registration can be delivered as the stronger conditional evidence surface, with full protocol closure still OPEN.

## Exact reviewed source hashes

- `audit/guarantees.yaml`: `c31d4005b76e1c06a9d0ba8b60f3c859783ab73f0ffdd0a07c73b1bed9d205bb`
- `audit/assumptions.yaml`: `cca5dcccb9e1db16f9e7f2b93c65c6532be6f88d5db117fa00cc45a0bf587ccd`
- `scripts/audit_metadata.py`: `c6a83965eff36f30777ade81f8d640c336ade7318c685228b2fd71bc9456026e`
- `Eip8282/Audit/AllGuarantees.lean`: `1068eaf320b104c6a4fb7c7f5484b240facca847c648702e1ebc98b9381cea4c`
- `Eip8282/Audit/Guarantees/Registry.lean`: `1e5babdfa598503553ad78bc62d90c23eb6998ef692dba485e247512d37d6fe7`
- `Eip8282/Audit/Integrator/DirectGuarantees.lean`: `5ff993fdd230deb47917074ab3416db8b5dc4bab5d9b92bb3a396e98e2b0034f`
- `README.md`: `f3c1eddc1481dd429bef21fb57c211a6cce619ed6dc9b85e3a5e164e006cb4c9`
- `audit/DIRECT-CLOSURE.md`: `70076933f9e1b970e5b56bc5e484f19c2135b664c81b8ae3d35d383a7e7b108d`
- `Makefile`: `d02bee103d041b1c3fa991d92f7288c651c93e1e9ebe0415c16f0e6d42e8f215`
- `Eip8282/Audit/Trust.lean`: `9979cd7f371b0626ba172cc0ecb2f0547b4e0b5f6bc54ff7f02567540608e7a8`
- `Eip8282/Tests/DirectThetaKills.lean`: `df9633ea5ba2fe5892a14f5689ce474cdede276f12317e4e777094d1c965459a`
