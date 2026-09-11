# Independent reviews: conditional direct parents

# Independent integrator review: AuditedChildGas

Source SHA-256: `476d03b05433139f778807104864ce4cd14ac3020d8aea4dcb609d7c2651904a`.

CLEAN within the stated single-edge scope. The child Context reproduces all literal Θ inputs including accessed substate, actual code selection, apparent/real value equality, memory slice, sender/source, depth and gas allowance. Context.fuel=fuel-1 is justified by actual child completion and its result supplies Θ(fuel); no fuel completion assumption is fabricated. AppendGasPath derives 919/1847 from that same actual successful child, then accepted Z supplies forwarded-word fit. The gas returned by the step-extracted child equals the witnessed child gas by deterministic result equality, which discharges returned≤allowance before the natural settlement equation is used. This counts that child's charge once at this CALL edge. It does not sum trees, prove histories valid, or assume that a parent finally commits. Actual child success, code selection, non-SYSTEM source and exact input size remain explicit. Standard axiom reports inspected in /tmp/eip-AuditedChildGas-1.log.


---

# Independent review: TransferFunding

Verdict: **CLEAN for natural-total nonincrease across the actual funded Θ entry transfer.** This is not a conservation theorem for subsequent execution or the complete transaction.

Frozen reviewed source: `Eip8282/Audit/Integrator/TransferFunding.lean`
SHA-256: `b8d8286170495a4a59d0f61ad19e0354e624ea3a0c0e0f48bd24e92ea7871766` (matches assignment).

Read entire candidate, actual `MessageCall.Context.entryWorld`, the corresponding Θ credit/debit code in the pinned EVMYul semantics, UInt256 arithmetic bridge, and the relevant Std.TreeMap list/lookup lemmas. No proof edits or builds. Compiler log inspected: `/tmp/eip-TransferFunding-local-compile.log`, containing expected reports with only propext, Classical.choice, Quot.sound and no warnings/errors.

## Actual transfer binding

The private `credited` helper exactly repeats the first half of Context.entryWorld: absent recipient is inserted only for nonzero value; existing recipient is updated by word addition. The second half explicitly matches the credited map's sender lookup and debits that account. The proofs reduce the **existing actual** `c.entryWorld` to this expression; they do not prove a fact about an unrelated transition or assume its result equals an expected map.

This is also exactly Θ's two-step transfer in `.lake/packages/evmyul/EvmYul/EVM/Semantics.lean` lines726ff: recipient credit first, sender lookup in σ'₁ second, sender debit third. The comment in Θ says sufficient funds was checked earlier; the candidate does not treat that comment as proof. Its exported hypothesis explicitly requires actual pre-transfer `c.value.toNat ≤ worldBalance c.world c.caller`.

Actual value is used throughout, not apparent CALLVALUE. No ordinary-value equality is needed for this transfer-only theorem. No execution result, opcode path, permission, code pin, supply bound or desired post-state is smuggled into the premise.

## Finite map sum

`worldFunds` sums natural balances of every entry in `AccountMap.toList`; `worldBalance` reads the same actual account and defaults absence to zero. Neither is a chosen ghost supply or a sum over only touched accounts.

`funds_insert` proves the replacement identity

```
funds(insert world key account) + oldBalance = funds(world) + newBalance.
```

The proof uses the library's actual `toList_insert_perm`, maps to balances, and preserves the sum under permutation. The filtered remainder removes the key. Existing-entry case obtains membership from actual get? and derives key uniqueness from TreeMap.keys.Nodup; `filter_sum` therefore removes exactly the one old balance. Absent-entry case proves no filtered key can occur from the contradictory get? result. This avoids unsound natural subtraction when replacing balances.

Library law requirements concern the AccountAddress key comparison/BEq. AccountAddress is `Fin(2^160)` with its standard order/equality. The argument requires no LawfulBEq instance for Account values or AccountMap equality. The key filter's Boolean negation is explicitly identified with the library predicate. `balance_le_funds` follows by inserting a zero-balance default and using nonnegative natural remaining funds, including the absent-account case.

## Distinct and alias cases

For distinct sender/target, credit_lookup_other proves that credit cannot change the sender lookup. `credit_funds_le` allows recipient addition to wrap: `(a+b).toNat ≤ a.toNat+b.toNat`, so credit can increase the natural total by at most the sent value. The funded pre-balance is thus the balance actually debited. `toNat_sub_of_le` derives the debit's natural value without underflow; the replacement identity subtracts exactly value from the credited total. Combining these yields total_after≤total_before.

An absent distinct sender has pre-balance zero. The explicit funded premise forces value.toNat=0; credit_funds_le then suffices, with no invented positive sender balance or account-existence hypothesis. An absent recipient with positive value is inserted exactly as the actual code does. Existing recipient with zero value is also handled, despite an actual map insertion occurring.

For caller=target, the proof does **not** incorrectly reuse the original balance for the second lookup. It expands the real transfer, performs the lookup in the credited map, and uses word cancellation `(a+b)-b=a`. Consequently the same-account final natural total equals the original total even if the intermediate credit wraps. This branch does not claim the intermediate debit is naturally underflow-free; modular cancellation of the exact two operations is the correct reasoning. If the aliased account is absent, fundedness forces zero value, and the transfer leaves the world unchanged.

No recipient-addition fit is assumed, so exact total equality is intentionally not exported for distinct accounts. A recipient overflow can reduce natural total. The theorem's `≤` result is correct and sufficient for an upper-supply budget. The alias branch proves equality only where cancellation justifies it.

## Exported scope and remaining obligations

`entry_funds_le` establishes actual entry-world natural-total nonincrease under sufficient pre-sender funds. `entry_funds_budget` propagates any supplied initial total bound through precisely that transfer. `balance_le_funds` now supplies the individual-account-to-real-total part of a funding argument.

These results do not yet establish sufficient funds from actual transaction or nested-call admission, preserve total through executed code, count external issuance, prove a supply ceiling, or account for transaction fees/refunds. Θ alone permits contexts lacking the sufficient-funds check; this file properly restricts its theorem rather than claiming all such contexts conserve funds. Recipient overflow is permitted mathematically, so do not describe the general exported theorem as unconditional exact conservation. Missing and self accounts are covered without assuming owner presence or distinctness.

Dependency hashes:
- MessageCall.lean: `3f16088bd13b6f6fdf13de417e4843f08e9dcd61fa6dfdddfc6342c250ccf342`
- pinned EvmYul/EVM/Semantics.lean: `8b49f1aee609ce888041ba9e7253bbe55d06fda136252bc46d4e006755110f4b`
- EntryReach/Words.lean: `81794ed621d68d8226ad69baba2b1a2672324d1175c7cfe8d6d39f40da95a083`

No findings requiring changes.


---

# Independent review: DirectAppend and DirectControl

Verdict: CLEAN for the stated conditional, actual-completed-call scope. No source changes or builds performed.

## Exact source binding

- `Eip8282/Audit/Integrator/DirectAppend.lean`: SHA-256 `647eaa41fe5a8637e0df70834bb501d4ebbcf555cf5414fcb0c79eb0221ad600`.
- `Eip8282/Audit/Integrator/DirectControl.lean`: SHA-256 `a7fde1c5324713a55594f56c9d863553019636194eff5594da8661dde08580ec`.
- Worktree HEAD observed during review: `1c517955c0d246d300abc262ae90f974b30def85`; the hashes above, not an assumption that the files are already committed, identify the reviewed content.
- Pinned EVMYulLean: `b62586650b4f96cc6da25f36574aaa8f329a6420`.
- Existing receipts read: `/tmp/eip-DirectAppend-1.log` and `/tmp/eip-DirectControl.log`. Exported theorem closures list only `propext`, `Classical.choice`, `Quot.sound`. Compilation was not repeated in this read-only review.

## Same execution and tuple

`DirectAppend.observed_of_receipt` joins the receipt equality and the caller-supplied actual Θ equality with `Except.ok.inj`. Its projections select precisely world, substate and output from `(created, world, gas, substate, true, out)`. Thus the all-slot overlay, natural storage statement, single anonymous log and empty bytes belong to the same returned result. It does not merely export effects from another sufficient-resource run.

`user_append` passes the same `h` to admission and SuccessfulAppend. The actual accepted input supplies exact 184/48-byte shape. Pre-call Bounded is transported across the real transfer and `append_fits` is proved before the append receipt is invoked. No post-state agreement, sufficient gas, evaluator budget, permission, or completed-loop premise replaces execution inversion.

The reviewed dependencies preserve actual Θ semantics: recipient credit precedes sender debit; CALLVALUE is apparent value and is bound to actual value by `hactual`; successful Ξ world/substate settlement retains the real empty-world fallback. Append and SYSTEM commitment exclude that fallback from derived surviving-owner evidence, not from an assumed nonempty post-world. Other-account preservation in DirectAppend is correctly relative to `c.entryWorld`, so the caller's real balance transfer is not incorrectly claimed unchanged.

## Independent observations and fee/payment

The observation definitions contain no execution equality, XiCall, code pin, path witness, or legacy model transition. Context supplies data fields; none of these predicates inspects its code or executes its result. AppendDataSpec gives a pure storage overlay and receipt encoding, including the original calldata for deposits and the actual caller's 20-byte source followed by pubkey for exits. The log equation is exactly the previous log series with one empty-topic event appended.

DirectAdmission's same existential price is used for both completed natural tariff and PaidInput. Its numerator is pre-call excess + natural max(0, count - TARGET), with TARGET 8/2. Actual success gives operational completion and uninhibited state; EnabledSafe then yields numerator <= 2892, prevents numerator wrapping, and FeeSafeDomain identifies that actual operational price with MathQuoteCompletes. MathQuoteCompletes existentially witnesses a completed natural recurrence; its meaning contains no 256-step or other fixed cutoff. The finite upper trajectory used to certify the safe domain does not change that definition or restrict actual interpreter fuel.

Payment refers to `c.value.toNat`. Deposit amount is the eight big-endian calldata bytes at offset 80; the uint64 bound derives the stake multiplication fit, and the already-checked fee comparison permits natural subtraction. PaidInput requires exact 184 bytes, amount >= 1,000,000,000 gwei, and price + 1,000,000,000 * amount <= actual wei value. Exit requires exact 48 bytes and price <= actual value. No signature-validation claim is made.

## Control branches

`DirectControl.completed` handles every actual completed Bool result. The false branch exports the full original journal (world, substate, created accounts). The inhibition implication applies only to non-SYSTEM callers and derives false status plus that rollback. Interpreter OutOfFuel is a separate error and cannot satisfy the completed-result premise.

For true status, only the actual caller selects SYSTEM versus user. SYSTEM requires no uninhibited premise and projects its actual all-slot result to count = 0 and the exact natural latch/unlock/fold precedence. Nonempty input latches INH; otherwise old INH unlocks to zero; otherwise the new excess is saturated excess + count - TARGET. The coupled pre-budget bounds the intermediate sum before word addition. The calldata fit premise makes natural nonempty equivalent to the executed word test.

A successful empty-input user call produces Getter: all account lookups and created accounts are preserved, logs are preserved, actual value is zero, and actual returned bytes encode the same natural completed price. ReadOnly does not assert full substate equality: access bookkeeping may change. Both actual settlement branches are accounted for.

A successful nonempty user call uses DirectAppend's StoragePost to conclude unchanged excess and natural count + 1. The projection selects those exact fields. DirectControl intentionally does not republish the stronger append pointer/log properties, which remain in DirectAppend.

## Remaining boundaries

These theorems retain pre-owner, runtime-code pin, ordinary apparent/actual value equality, calldata size fit, Bounded budget with budget < 2^128, and EnabledSafe as explicit assumptions. They do not establish that all protocol histories satisfy those assumptions, that the code is installed at the canonical authorized address, or that every paid well-formed call succeeds. SYSTEM may fail through actual execution; inhibition is not claimed to prevent such unrelated failure. Initialization is outside these two modules. No aggregate gas/funding theorem or full transaction validity is established here.

The complete DirectControl theorem uses some assumptions uniformly that individual failure/getter/SYSTEM branches need less of. This is interface strength, not circularity. Its natural fee claim is deliberately restricted to the safe pre-domain. Within these boundaries, the documentation and proof statements agree.


---

# Independent integrator review: DirectDrain

Source SHA-256: `915a08868399a8fe39baea245b7bacb9fea5912a4b6cdafd86c9a07ea4c2dab3`.

CLEAN within the explicit local input domain. Domain includes only independently observed storage/queue/source-width, owner, value equality, size fit and safe/budget bounds; no original-code constraint. The actual completed tuple determines failure vs success, then actual caller selects SYSTEM vs user. SYSTEM output is exact encoded take and represented drop, joined to natural pointer/stale observations of the same world. UserQueue is a pure input-record list extension and is proved equal to the prior q-based representation; getters retain the same queue, appends extend by exactly one, HEAD remains fixed. Failure restores the actual world and represented queue. The standard safe domain is stronger than strictly needed for draining but explicit, not inferred from a desired output. This is not protocol-history extraction or a same-parent Θ mutation refutation. Standard axioms inspected in /tmp/eip-DirectDrain-3.log.


---

# DirectInitialization / DirectSubmit — independent integration review

**Outcome: CLEAN for these exact sources and their explicit conditional scope.**

- DirectInitialization.lean SHA-256: `c195ad44ccc597fa534d8337b5b60d4e16976b0b1273f56b615a67019a465458`
- DirectSubmit.lean SHA-256: `ab6ee97c55c9d9d4356b484632e6e2a62489e11f00411f33098b9ebd41968fee`

Both complete files and the relevant complete DirectAppend, DirectAdmission, UniversalGate and InitializedInvariant dependencies were read. Hashes were checked twice. Supplied `/tmp/eip-DirectInitialization.log` and `/tmp/eip-DirectSubmit-final.log` contain respectively one and two reports with only propext, Classical.choice and Quot.sound. No source edit or rebuild of these reviewed modules was performed. A separate owned SystemFrame implementation was compiled during the same task and is outside this independent review.

## DirectInitialization

The parameter `init` occurs in an equality to the tested call's initializer, while Domain does not contain the original initializer pin. Observed requests the intended runtime code and initial controls. Thus testing another initializer does not falsify a hidden original-code premise before its behavior can be examined. The expected runtime is appropriately in the output specification.

Domain keeps actual preimage construction, exact fuel relation, no-collision/absence and constructor resource assumptions explicit. These are input conditions, not desired initial storage of the published world. The deposit and exit branches retain the differing permission/sender-existence requirements of the existing proofs.

The theorem starts with actual successful Lambda, including its collision selection, code-deposit decision and resulting world; it does not infer successful installation from a sufficient init-code bound alone. The returned account, installed code, initial excess, empty queue representation, Bounded0, EnabledSafe and unchanged logs all refer to that same returned world/substate. Deposit starts at zero; exit starts at INHIBITOR. The extra empty SourceWidth fact from InitializedInvariant.exit_creation is safely omitted because Observed does not demand it.

This proves conditional successful creation at the exact Lambda-computed address. It does not establish existence of a successful creation, canonical predeploy address, actual activation scheduling, valid CREATE/creation transaction, or a universal claim about arbitrary occupied targets. Those boundaries are stated in the module header. The expected-empty representation is an initialization property, not an induction across future calls.

## DirectSubmit

Observed is code-independent and takes the actual complete-call results. On false status it demands rollback of world, substate and created-account journal. It also demands this failed journal for inhibited user calls. On true status with nonempty calldata it demands enabled admission, a single authentic physical append/log, and payment at a completed mathematical quote. It contains no sufficient-resource assumption or pre-supplied quote-completion witness.

The actual completed theorem requires the user branch and v'=v, calldata-size fit, pre-owner existence, the independently supplied pre-state budget below2^128 and the explicit EnabledSafe fee domain. Failure rollback is taken from the real Θ settlement. Inhibition rejection uses actual-success inversion; an inhibited input cannot slip through by running out of ordinary EVM gas. Proof-evaluator OutOfFuel is excluded because the theorem quantifies completed .ok results, not all evaluator errors.

The append branch delegates to DirectAppend.user_append, which first derives the paid input and obtains AppendFits from the pre-state budget, then uses the actual append receipt. Its existential receipt world/substate/output is identified with the given real result before exporting storage/log observations. The record encoding and other-account frame are independent predicates; the latter is correctly measured against entryWorld after actual value transfer.

DirectAdmission obtains the exact completed word quote used by the successful call and proves it equals the natural tariff on the explicit safe domain. The fee witness attached to PaidInput is that same price. Deposit checks include 184 bytes, amount>=10^9 gwei and fee+amount*10^9 wei<=value; exit checks 48 bytes and fee<=value. No signature verification is claimed.

invalid_nonempty is valid logical inversion of this behavior: false status uses the rollback clause; true status contradicts absence of the mathematical paid-input witness. It makes no false liveness promise for a valid paid call with insufficient gas.

## Limits to preserve in the final façade

- At this reviewed hash, completed is explicitly a **user-call theorem**. The predicate does not yet establish SYSTEM non-append or getter no-log/no-write behavior. Those clauses must be composed from their own theorems; this review must not be reused automatically for a later expanded predicate.
- Empty successful calldata makes the append implication vacuous; it does not claim the getter's fee/output/control behavior here.
- The local pre-budget and EnabledSafe premises remain supplied invariants. Neither whole Ethereum reachability nor the economic funding ceiling is proved by this file.
- Runtime equality and a pre-owner witness are not by themselves canonical installed-predeploy identity or message-call admission. v'=v excludes delegated apparent-value cases and is explicit.
- Journal rollback is not a claim that spent gas is restored, or that enclosing transaction fees/balances are unchanged.

No blocking mismatch, circular poststate assumption, extra axiom, finite cutoff substitution, or theorem-scope overclaim found in these exact sources.


---

# Independent integrator review: SystemFrame

Source SHA-256: `74b04b8a3a98ba7226479d0b53d955b98bf48e6ea16742888e5bdb1b69b9efa9`.

CLEAN. The exact SystemInversion published state is used to transport log preservation and the other-account frame through both pointer cases and the two final control SSTORE operations. Touches preserve logs/maps as specified. The actual Theta result supplies the real Xi result and settlement branch. In the empty-world fallback, any existing other account in entryWorld would contradict the Boolean empty test; entry_keeps_existing similarly forces the pre-world other account absent. Thus the other-account frame is relative to the real transferred entry world even in that branch. No owner/resource or predicted post-state premise is added. This proves no SYSTEM log append at arbitrary successful-call resources, independently of local arithmetic domain assumptions. Standard axiom reports inspected in /tmp/eip-SystemFrame-local-compile.log.


---

# DirectGuarantees and SystemProgress — independent final source review

**Outcome: CLEAN for the exact conditional local guarantees below. This is not approval to reclassify the registered protocol guarantees as closed.**

- DirectGuarantees.lean: `9b39dc88aac5acb38b4ef7bac387739e9e0e1ab52f5c0e6994b9e1d0a792850d`
- SystemProgress.lean: `543378c2b97f1eb7668c68f15742bc23d784c8c0ba9b22c89a6983f7f34d77b7`

Complete latest sources reviewed. `/tmp/eip-DirectGuarantees-progress.log` contains three standard-axiom reports and `/tmp/eip-SystemProgress.log` contains one; parent reports compilation exit0. No edit or rebuild of these modules performed. The new SYSTEM progress conjunct is included in this review; earlier façade hashes are superseded.

Relevant complete specifications and composition dependencies read: DirectSubmit, DirectAppend, DirectAdmission, DirectControl, DirectDrain, DirectInitialization, AppendDataSpec, UniversalGate, SystemDataSpec, CommittedSystem; relevant QueueInvariant record/representation and GetterInversion.ReadOnly definitions. The existing SystemFrame is my implementation and was consumed as a dependency, not independently re-reviewed here.

## Parameter-code domains and mutation usefulness

PSubmit, PDrain and RuntimeControl quantify actual completed Θ results for a parameter code. Their code equality refers to this parameter, not a hard-coded original runtime hidden in Domain. Domain supplies independent pre-state owner/value/calldata/budget/safe-fee conditions. PDrain additionally supplies a represented pre-queue and exit source width. These conditions do not assert a desired poststate, quote completion, successful path, or operational helper output.

PControl combines RuntimeControl, a separately parameterized initializer property, and SystemProgress for the same runtime parameter. The initializer domain has no original init-code pin; the expected installed runtime occurs in its conclusion. Runtime and creation contexts are independently quantified, preventing irrelevant constraints on one call from making the other clause vacuous.

A mutation can therefore be tested under the same preconditions and refute the same behavior predicate. The theorem does not itself supply such counterexamples. Existing finite Ξ/runSummary observations cannot be relabeled as completed Θ counterexamples to this façade without their actual-result and domain bindings. The module explicitly keeps same-predicate Θ mutants as an acceptance gate.

## P-SUBMIT coverage

The caller alone selects the SYSTEM/user observation. SYSTEM failures restore the journal; SYSTEM successes preserve all record slots >=4 and add no logs. Ordinary successful empty calls must satisfy GetterInversion.ReadOnly: this includes created-account preservation, every account lookup unchanged, identical logs, **and c.value=0**. Thus getters cannot append, emit a receipt, or succeed with payment under this property.

Ordinary successful nonempty calls must be enabled and satisfy the independent authentic append/storage/log predicates, together with a paid input at the same completed natural fee. The observations specify one tail/count successor, unchanged head/excess, authentic record words, preserved outside slots, and exactly one pushed anonymous log from the target. Deposits preserve all184 calldata bytes and do not assert signature verification. Exits use the actual caller's address and the supplied48-byte pubkey. Deposit payment includes the amount floor and quoted fee plus amount×10^9 wei.

Failures and inhibition are actual journal observations, not assumed reverted poststates. The append branch is success necessity; it does not promise every paid user call succeeds with arbitrary gas/fuel. That matches the declared safety scope.

## P-DRAIN coverage

The independent represented list is tied to physical words, ordered HEAD/TAIL, a bounded physical window and exact length TAIL−HEAD. For successful SYSTEM calls, the result contains natural min(length, cap) pointer updates, unchanged old record slots, representation of queue.drop n, and an actual returned byte buffer equal to the flattened queue.take n encoding. Caps are64 deposits/16 exits; deposit encoding includes the proven amount byte reversal, and exit encoding preserves source/pubkey order under SourceWidth.

For successful users, HEAD is unchanged and the old list remains a prefix of the post-queue, with precisely the input-derived physical record appended for nonempty input and the original queue for getters. False status restores the pre-world and represented queue. Therefore only SYSTEM removes old records. The pre-representation and bounds are supplied domain facts; their establishment over protocol histories is not smuggled into this predicate.

## P-CONTROL coverage and progress

RuntimeControl exposes failure rollback, inhibited-user failure, caller-selected SYSTEM updates, read-only natural-price getters, and successful user excess preservation/count increment. SystemDataSpec.ControlSlots gives nonempty latch, inhibited empty unlock, and otherwise the natural saturating excess+count−target fold. Its intermediate addition fit follows from the pre-state budget. DirectAdmission's quote uses the separate effective numerator excess+max(0,count−target); there is no substitution of the SYSTEM-stored excess for the quoted numerator. FeeSafeDomain justifies equality on the explicit input domain; the certificate budget is not a256-step fee definition.

The initializer component supplies actual successful Lambda installation of the intended runtime, deposit zero/enabled versus exit INHIBITOR, and empty initial invariants. It retains actual-success, resources, absence and collision conditions; it does not manufacture deployment success or canonical address identity.

The added SystemProgress removes the important runtime availability loophole of pure success-conditional safety. For **every storage image**, owner existence, SYSTEM identity, write permission, gas>=2,500,000 and fuel>=8,503 yield an existential actual successful Θ result. There is no EnabledSafe, non-inhibited, bounded-storage or desired-result premise. The common bounds are conservative for exit. The proof derives steps=fuel−1, transports actual owner existence, then extracts the real successful committed result from CommittedSystem. It does not erase the empty-world settlement branch by assumption.

Consequently an always-reverting runtime cannot satisfy PControl: it fails the progress conjunct on adequately resourced SYSTEM inputs, including inhibited storage. The original arbitrary-resource safety statements remain unchanged. These are explicit evaluator resources, not a proof that Ethereum supplies that gas/fuel or schedules the call.

## Remaining boundaries, not defects of these conditional statements

- Protocol justification of owner/installation, ordinary value provenance, queue representation, source width, budget and safe-fee invariant is still separate.
- Positive sufficient SYSTEM progress is now exported; successful-user/quote liveness at sufficient resources is not part of these three safety predicates. If an availability SLA for user calls is desired, state it separately.
- The initializer clause remains conditional on actual successful creation. It can be satisfied vacuously by an initializer that always fails; proving deployment existence/provisioning is a separate activation obligation. Do not call it unconditional deployment progress.
- PSubmit/PDrain individually are safety properties and do not themselves reject an always-failing runtime. Their conjunction with PControl now includes runtime SYSTEM progress. This distinction is intentional and should remain visible when presenting each predicate alone.
- No proof-evaluator OutOfFuel behavior is covered by the completed-result quantifiers. Ordinary EVM failures are covered by false status and rollback; spent gas is not restored by those journal equalities.
- Runtime equality is not by itself proof of canonical predeploy installation or valid upstream call admission. Fork, genesis, resource scheduling and inter-transaction/ancestor accounting remain explicit acceptance gates.
- Same-predicate completed-Θ mutation receipts remain to be constructed/checked before public guarantee promotion. No Registry/YAML status was changed by this review.

No blocking source defect, circular postcondition, original-code mutation-vacuity premise, or missing agreed safety clause found in this final scoped façade. The documentation correctly calls it conditional local evidence rather than the registered public parents.
