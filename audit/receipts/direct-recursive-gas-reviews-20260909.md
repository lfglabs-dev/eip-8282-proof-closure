# Independent reviews for universal gas and ordinary funding


---

# Independent review: CreationGas

Verdict: CLEAN for the stated local accounting scope. No correctness blocker found.

Reviewed source: `Eip8282/Audit/Integrator/CreationGas.lean`
SHA256: `13aff91fba701884c09b25065ac1f8e7afaa849ce2b4c3b9e75abebed975feeb`
Worktree: `/Users/thomas/work/eip-8282/direct-closure-implementation`.
Read-only review; no proof changes or compilation performed by reviewer. Inspected the supplied final `/tmp/eip-CreationGas-4.log`: all seven printed theorem dependencies are only `propext`, `Classical.choice`, and `Quot.sound`; no diagnostics appear.

## Semantic binding

Read the complete candidate and the relevant executable CREATE/CREATE2, Lambda, X/Z, Step/StepOk/stepPre definitions and CreationSettlement's complete context, settlement equation and success inversion. The two variants have the actual three/four stack arguments and absent/present 32-byte salt. `child` is the literal Lambda invocation with the original child fuel, after the actual instruction counter increment, opcode gas debit and sender nonce insertion. Code, init memory slice, sender/origin, depth, original world, accrued substate and permission all match the dispatcher. No alternative execution or post-world agreement is supplied.

The nonce gate uses the actual default account and threshold `2^64 - 1`. Funds use the actual owner balance with zero for a missing owner; depth and init-code size tests match the executable conjunction. Denied dispatch preserves the pre-dispatch world and does not publish the tentative nonce insertion. The actual Z also checks creation size and static permission: `accepted_*` explicitly requires this real acceptance, so it does not assert that an oversized CREATE can complete in a full evaluator run.

The exception disjunction retains every actual Lambda error, including zero child fuel and propagated init OutOfFuel. In this pinned evaluator CREATE catches that error, assigns zero returned child gas, an empty account map, stack zero, and empty return data. The theorem does not replace this unusual upstream behavior with a rollback world. Ordinary child failures returned as `.ok (..., false, ...)` remain on the completed-tuple branch, as they should.

## Gas arithmetic and limits

CREATE forwards `L` of gas after the opcode debit; this differs correctly from CALL. `forwarded_fit` follows from `L n = n - n/64` and the bounded gas word. `settlement_nat` requires both opcode-cost sufficiency and returned child gas at most that actual allowance. These premises justify subtraction and the final natural-number addition without modular wrap. `accepted_gas` supplies the genuine Z memory debit and opcode-cost bound; both accepted-dispatch results account for memory, opcode cost and the actual child debit exactly once.

The completed-child branch intentionally leaves its returned-gas inequality as an implication premise. It has not proved universal child gas monotonicity by assuming the desired conclusion. The exception branch needs no such hypothesis and debits the whole allowance. The denied branch credits back the same representable allowance and therefore pays only opcode and memory cost.

The pinned CREATE/CREATE2 final guard checks `(chargedGas + returnedGas).toNat < L chargedGas`, with a word addition before the comparison. This can matter even when the later natural settlement expression fits. `step_child` and `step_denied` retain actual `StepOk` and peel this guard only from an actual successful step; they do not assert liveness or manufacture a step after proving the natural identity. Thus the guard's unusual word behavior is not silently removed.

`lambda_code_debit` is tied by actual Lambda success inversion to its exact init execution. Successful creation implies all deposit rejection guards were false, in particular `Gcodedeposit * code.size <= initGas`. The resulting subtraction is therefore natural and the theorem proves exact code-deposit debit. Optional address-preimage encoding success remains explicit. It does not assume code installation from init success alone, nor claim failed-deposit, collision, or preimage-failure success.

## Remaining scope

These are local real-step/real-Lambda accounting lemmas suitable for a later fuel induction. They do not by themselves establish the child returned-gas bound, a full-call aggregate bound, transaction/block accounting, protocol gas-limit validity, or any Ethereum supply conclusion. Fuel remains evaluator recursion fuel, not gas. The proof correctly permits fuel zero at the Lambda boundary and records how the actual dispatcher catches that exception.

Reviewed dependency hashes:

- CreationSettlement.lean: `d95b28f2a46daf588a2aaf15e8a8f77fc28b075116e5f2395360e73152383820`
- ActualAppendGas.lean: `79a04a7b1a092026b24e3dfc3b0adc9bffaaa17a473e76a3f8a5447e75a7ea0d`
- OrdinaryGas.lean: `d41661f413814579343e04a37da8cb87624881f63ac132440077beb8dc0adfd4`
- EvmYul/EVM/Semantics.lean: `8b49f1aee609ce888041ba9e7253bbe55d06fda136252bc46d4e006755110f4b`
- EvmYul/EVM/Gas.lean: `9f06caccf5cc8f27f7822392cd1963c8353eb816052f4596321a12c2da707436`

---

# Independent review: ReturnedGas

Verdict: CLEAN for universal remaining-gas monotonicity of the pinned evaluator.
Reviewer: root integrator, not the module author. Read-only review.
Source: Eip8282/Audit/Integrator/ReturnedGas.lean
SHA256: b39d7af6e35834bb6ecd3364fd1055768ae8e11712dc92d811312e4ffce9dde9

Read the complete module, its actual X/Ξ/Θ/Lambda dispatch and settlement in
EvmYul/EVM/Semantics.lean, and the previously reviewed ordinary/CALL/family/CREATE
accounting interfaces. The terminal targeted compilation is recorded separately
in /tmp/eip-ReturnedGas-final.log. Universal exports depend only on propext,
Classical.choice and Quot.sound.

All five predicates quantify the actual evaluator at arbitrary fuel and inputs.
No bound on a child's gas, code pin, execution path, sufficient balance, or
predicted post-state appears in the final predicates. StepBound requires actual
Z acceptance and actual StepOk; these are supplied by the inversion of X.
The X predicate covers both success and REVERT. A genuine evaluator error has
no fabricated final state. Xi starts the actual fresh state. Theta covers both
code and all ten pinned precompiles, and the literal default dispatch branch.
The cryptographic routines are not evaluated or trusted as gas inequalities:
the proofs inspect the enclosing guard and gas debit, retaining all possible
crypto results. Theta's empty-world fallback does not affect its gas projection.

The strong induction is well founded on actual evaluator fuel. X at successor
uses the predecessor Step and X bounds; Xi, Theta and Lambda use their actual
predecessor evaluator. CALL-family Step needs two units of fuel to reach the
child Theta; CREATE needs one to reach Lambda. Zero-fuel CALL helper failures
are explicitly inverted, while CREATE's caught exceptions use the existing
whole-allowance debit and never invent a successful child result. The stack
operands come from Z's actual delta guard. The six recursive opcodes exhaust
the complement of OrdinaryGas.Ordinary, including distinct CALLCODE,
DELEGATECALL and STATICCALL value/permission conventions.

Natural gas arithmetic uses actual Z to rule out memory/opcode underflow and
forwarding overflow. The local child bounds required by earlier accounting
lemmas are now discharged by smaller-fuel induction, and the word allowance
is converted only after its fit proof. Lambda code-deposit settlement handles
success, deposit rejection, REVERT and actual exceptions; successful subtraction
is bounded by the init gas even before stronger exact-debit facts are needed.
No gas resource or liveness theorem is claimed: a computation may still exhaust
interpreter fuel, gas or encounter an exception.

This closes the previously explicit local returned-gas premises for completed
child calls. It does not count successful audited child events, prove their
nonduplicated aggregate debit, extract transaction/block histories, relate the
pinned evaluator to every Ethereum fork, or prove a protocol supply bound.

---

# Independent review: StorageFunding and SelfdestructFunding

Verdict: CLEAN at the exact final hashes below. No semantic correctness blocker found.

- `Eip8282/Audit/Integrator/StorageFunding.lean`: `0340e3ac715e17f415d2708e3916b417f138e9fba445efee4af88c3cf5b3a044`
- `Eip8282/Audit/Integrator/SelfdestructFunding.lean`: `a231fbc4c38c1424e7ce63f0ad1c327d9b9fc4352b37c6d60dfb8543e5e4db35`

Worktree: `/Users/thomas/work/eip-8282/direct-closure-implementation`.
Read-only review; no proof edits or compilation by reviewer. The complete final sources were read, including the restored match reductions in `updated_le`. Inspected `/tmp/eip-StorageFunding-2.log` and `/tmp/eip-SelfdestructFunding-6.log`: their printed theorem dependencies contain only propext, Classical.choice and Quot.sound, with no diagnostics. The earlier SelfdestructFunding -5 log was a failed cosmetic-cleanup attempt and is not validation of this final source.

## Storage writes

`replace_preserves` is an exact finite account-map sum identity specialized to an existing account whose balance is unchanged. It does not assume a desired resulting total. `sstore_preserves` uses the actual sstore operation: owner absence selects the original state, even though the implementation also destructures get! for refund calculations; owner presence replaces precisely that account with updateStorage. Both erase-on-zero and insert-on-nonzero branches preserve its balance. Refund and access-bookkeeping changes do not enter the account-balance total.

`tstore_preserves` similarly follows the actual owner lookup and updateAccount insertion. Missing owners are unchanged; both transient erase/insert branches preserve balance. Neither theorem needs account existence, funding, arithmetic fit or a supply bound. These are proofs about the concrete State operations; the thin raw-opcode/charged-Step wrappers remain to be composed.

## SELFDESTRUCT

`updated` matches the actual EVM raw opcode's account-map expression in both created-account branches. `raw_nonincrease` obtains the actual successful state by destructuring the real stack and createdAccounts.contains branch; it does not posit agreement with `updated`. Stack underflow cannot satisfy its actual-success premise. The destination is the actual AccountAddress.ofUInt256 stack operand.

All cases are covered:

- Missing source: unchanged map in both branches.
- Existing source, missing target, zero balance: unchanged map.
- Existing source, missing target, nonzero balance: insert the default recipient with the full source balance, then clear the existing source. Distinctness is derived from the contradictory lookups rather than assumed for the whole theorem.
- Existing distinct source/target: the real target word balance is incremented, then the source is cleared. `Nat.mod_le` correctly bounds modular credit by the natural sum. Overflow may destroy natural funds, so nonincrease is the correct unrestricted conclusion.
- Same source/target, created this transaction: both actual zero-balance insertions are retained. Applying `zero_le` twice handles repeated-key insertion safely without counting the account twice.
- Same source/target, not created this transaction: the actual map remains unchanged.

The helper `credit_clear_le` explicitly requires an existing source and distinct addresses and derives the total from two exact funds_insert identities, preserving the source lookup across the recipient insertion. Its credit bound is proved from actual balances in every caller. `zero_le` works even for an initially absent key: insertion of a zero-balance account cannot add to the finite total.

The result is solely about balances after this real opcode. It does not claim the selfDestructSet bookkeeping deletes an account immediately or prove later transaction-finalization behavior. Other account fields and accrued substate may change.

## Finite sum foundation and trust

Re-read TransferFunding's full finite-sum implementation. worldFunds sums balance.toNat over actual AccountMap.toList. funds_insert follows TreeMap's insertion permutation, unique keys and actual lookup membership. It requires lawful comparison/equality only for the AccountAddress key, not LawfulBEq for Account records. No post-state total, ghost supply or assumed model agreement is used. No native evaluation, sorry or new axiom was introduced by these modules.

Dependency hashes inspected:

- TransferFunding.lean: `b8d8286170495a4a59d0f61ad19e0354e624ea3a0c0e0f48bd24e92ea7871766`
- SystemSpec.lean: `291b21d9803b148276bf05a111940fb4bc37af676a89466a0ba808c1a2d80b26`
- EvmYul/Semantics.lean: `e6bd5acd768d93f50a93f789a301d2f9218b210bdcd3739f95088fd4e5279d7b`
- EvmYul/StateOps.lean: `ed24f52c490c1f9a56f4df5a3883533dad884ca2276f58d05cbf9ed3cd386e21`
- EvmYul/State/AccountOps.lean: `4ae05f7e6cf0e296060c2e94c19758a67f03f680831c1878303e475afc166c47`

## Minimal next composition (proposal only)

Reuse OrdinaryGas.Ordinary, not a new opcode taxonomy. Prove a single raw ordinary nonincrease theorem from actual raw opcode success, with valid-opcode hypothesis if needed: SSTORE/TSTORE use these storage lemmas, SELFDESTRUCT uses raw_nonincrease, and every other nonrecursive opcode preserves accountMap exactly. Small DUP/SWAP helpers and the same finite opcode/stack case split as OrdinaryGas.raw_gas should suffice.

Then derive `StepOk fuel cost (op,arg) pre post -> worldFunds post.accountMap <= worldFunds pre.accountMap` through OrdinaryGas.dispatch and the fact stepPre changes only gas/execLength. A zero-fuel successful Step is impossible. Finally use actual Z acceptance to derive validity and Z_ok_state to carry accountMap unchanged from pre to mid, giving an accepted-step theorem on the actual original world. This is the smallest useful API for the later recursive evaluator funding proof; no gas-cost inequality is needed for this balance projection.

An XRuns prefix corollary may be added by ordinary trace induction only if a consumer needs it. Neither these modules nor that corollary alone closes CALL/CREATE child funding, Lambda alias/collision behavior, Θ rollback/empty-world settlement, transaction fees/refunds or protocol issuance bounds.

---

# Independent review: OrdinaryFunding

Verdict: CLEAN for the stated actual ordinary-step funding scope.

Source: `Eip8282/Audit/Integrator/OrdinaryFunding.lean`
SHA256: `dc8c4eddd8af0b05396e4882d77fac97ead4e512e5996ed784c465f4ae5c53a6`.
Worktree: `/Users/thomas/work/eip-8282/direct-closure-implementation`.

Read the complete source, the relevant actual raw opcode operations and their dispatchers, and OrdinaryGas's complete dispatch/validity interfaces. No proof edits or compilation by reviewer. Inspected `/tmp/eip-OrdinaryFunding-4.log`: raw_nonincrease and accepted_step_nonincrease report only propext, Classical.choice and Quot.sound, with no diagnostics.

The finite measure is the actual AccountMap balance sum from TransferFunding, not a ghost budget or abstract supply. OrdinaryGas.Ordinary excludes exactly CALL, CALLCODE, DELEGATECALL, STATICCALL, CREATE and CREATE2. The raw theorem additionally excludes INVALID; the accepted-step parent derives that exclusion from the real Z guard. Thus it does not rely on the raw semantics' default/fallback behavior for INVALID or recursive opcodes.

The raw proof splits the finite opcode constructors, then actual stack/argument forms. It is not a sampling of concrete states. Successful DUP/SWAP alter only stack/PC; their failing branches cannot satisfy actual success. SSTORE/TSTORE use the actual top-two-operand binaryStateOp and preserve the concrete shared-state balances by the independently reviewed StorageFunding lemmas, including missing owners and storage zero erasure. SELFDESTRUCT uses the reviewed actual raw nonincrease theorem, covering source/target alias, absent accounts, created-account behavior and modular recipient credit.

EXTCODEHASH's dedicated helper correctly separates the dead-account branch and hash lookup while observing that both only add an accessed-account entry to substate. No evaluated hash equality or external hashing axiom is needed for account-map preservation. Other branches close by actual account-map identity after the successful raw result; stack arguments remain arbitrary and insufficient-stack executions are eliminated by the success equation.

step_nonincrease uses the exact OrdinaryGas.dispatch equation on the same pre-state and actual successful StepOk. Fuel zero is impossible. stepPre changes only instruction count and gas, so its accountMap is definitionally the input map. No gas-sufficiency or word-arithmetic claim is needed for this funds projection, even though low-level gasCost is arbitrary.

accepted_step_nonincrease then uses actual accepted Z to derive valid opcode and Z_ok_state to transport the pre-state map across memory gas charging. zMid changes only gas. The conclusion is on the same actual post-world produced by StepOk and the original pre-world, with no assumed post-state property, code pin, owner-existence, funded-transfer or supply-bound premise.

Scope remains intentionally local to actual successful nonrecursive steps. This does not yet prove complete recursive X/Ξ/Θ/Lambda funding conservation or transaction/block accounting. In particular, CALL/CREATE entry effects, nested execution, reverted journals, empty-world settlement and external fee/reward/withdrawal rules require their own composition. No protocol closure is implied by this module.

Dependency bindings:

- OrdinaryGas.lean: `d41661f413814579343e04a37da8cb87624881f63ac132440077beb8dc0adfd4`
- StorageFunding.lean: `0340e3ac715e17f415d2708e3916b417f138e9fba445efee4af88c3cf5b3a044`
- SelfdestructFunding.lean: `a231fbc4c38c1424e7ce63f0ad1c327d9b9fc4352b37c6d60dfb8543e5e4db35`
- TransferFunding.lean: `b8d8286170495a4a59d0f61ad19e0354e624ea3a0c0e0f48bd24e92ea7871766`

The storage/SELFDESTRUCT dependency review is recorded separately in `/tmp/eip-Storage-Selfdestruct-Funding-review.md`.

---

# Independent review: TransactionGas

Verdict: CLEAN for actual transaction gas projection and the conditional count wrapper.

Source: `Eip8282/Audit/Integrator/TransactionGas.lean`
SHA256: `c9d1714110c73b74a29bc2eb2900b2264fd4136275a8d4cd3e5788647044476e`.
Worktree: `/Users/thomas/work/eip-8282/direct-closure-implementation`.

Read the complete candidate, complete RefundAccounting dependency, actual pinned Υ implementation, and ReturnedGas's exact ThetaBound/LambdaBound definitions and exported theorem/induction interface. This review does not claim a second complete audit of ReturnedGas's 660-line mutual proof; root has separately reviewed that module. No edits or builds. `/tmp/eip-TransactionGas-1.log` reports only propext, Classical.choice and Quot.sound for all three exported theorems, without diagnostics.

`provisional_remaining` splits the actual provisional creation/message-call selection. The creation branch uses Lambda at exactly Context.fuel; the message branch uses Θ at that same fuel, with actual toExecute selection (including precompiles), checkpoint/original world, entry substate and transaction value/apparent value. The error branches cannot satisfy the supplied `.ok` provisional tuple. It applies the universal remaining-gas theorem to that actual selected execution and then identifies the tuple; no predicted child result, alternate fuel or remaining-gas premise is supplied. Bool false is covered as well as true.

RefundAccounting.Context.provisional and its result_observation unfold Υ literally. The checkpoint, intrinsic-gas subtraction, access-list initialization and creation/message selection match. Υ returns exactly the provisional substate and status while its final world performs refunds, beneficiary credit, selfdestruct/dead-account erasure and transient-storage cleanup. The projection does not assume provisionalWorld equals final world or omit that finalization from the real result.

`result_debit` inverts the same actual transaction result to its provisional tuple and obtains the remaining bound above. entryGas is a natural saturating subtraction cast to a word; it is always representable and no larger than the word gas limit, even without transaction validation. Therefore the remaining value is at most the limit. RefundAccounting.net_toNat then justifies both no-wrap additions/subtractions in the actual word expression: refund is min(gross/5, refundBalance), returned gas is remaining+refund <= limit, and used is gross-refund. The candidate proves exactly this natural formula and used<=limit. It does not assert validation of intrinsic gas, sender funding, gas prices, nonce or any protocol transaction precondition.

`count_le_used` retains the independent hypothesis `919*count <= gasLimit.toNat - remaining.toNat`. The called inversion theorem joins the supplied provisional tuple to the very provisional tuple selected by the actual final result through deterministic tuple equality, so the refund balance and remaining gas belong to the same execution. The 1/5 cap then yields count<=used. This is sound conditional arithmetic; `count` is an arbitrary natural number satisfying that aggregate charge hypothesis, not a derived number of actual append events. The theorem neither assigns local append charges to distinct steps nor handles nested/rolled-back events by itself.

No global transaction-funding, block gas-envelope, history-extraction or protocol supply closure is established here. What is newly discharged is the previously explicit remaining<=entry premise at the actual Υ provisional execution boundary.

Dependency hashes:

- ReturnedGas.lean: `b39d7af6e35834bb6ecd3364fd1055768ae8e11712dc92d811312e4ffce9dde9`
- RefundAccounting.lean: `4c67ebc4ccb77819248e0c6030cc5f63a0274ce0752d8ad17784a136096750fb`
- EvmYul/EVM/Semantics.lean: `8b49f1aee609ce888041ba9e7253bbe55d06fda136252bc46d4e006755110f4b`
