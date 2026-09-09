# Actual recursive execution and transaction funding reviews

These are modular supporting results. Protocol admission, external credits,
intermediate budgets and event extraction remain separate obligations.

## Frozen source bindings

- `Eip8282/Audit/Integrator/CallWorld.lean`: `d91c68bcce947482acaabbd79c9779ac60bf49f6c908acf7185830f5059bbc18`
- `Eip8282/Audit/Integrator/CreationFunding.lean`: `56aea62e253201415efc28eab267a99f9d6adc671885521d4eaec10b7c59816a`
- `Eip8282/Audit/Integrator/CreationWorld.lean`: `5b096b395cb74f05511c6a288522630cbf436cac205881ffe9f7760597b358ed`
- `Eip8282/Audit/Integrator/ExecutionFunding.lean`: `faa5fd66ac0daa24770a2dd4608cf8729721166a7636ccd8ac27ed88fc8b7d5b`
- `Eip8282/Audit/Integrator/FinalizationFunding.lean`: `e63683924b7f7ba1fdacd84c8c9cf76d3d770b3fc64e5e468ce9aa594a56bcb0`
- `Eip8282/Audit/Integrator/TransactionFunding.lean`: `dff074ffa97b3c17862496c3cd92bfb50611c7f19796c79ad95a469778508f2f`

---

# Independent review: CallWorld

CLEAN. Root integrator review, not the author.
Source: Eip8282/Audit/Integrator/CallWorld.lean
SHA256: d91c68bcce947482acaabbd79c9779ac60bf49f6c908acf7185830f5059bbc18
Targeted /tmp/eip-CallWorld-1.log reports only standard Lean axioms.

Read complete source, literal EVM.call and its final state replacement, and
frozen CallDispatchGas/CallFamilyGas helpers. Generic helper gate checks the
real code owner's funds/depth, which must not be mistaken for funding arbitrary
source parameters; the module correctly makes no funding assertion. Actual
child tuple inversion includes both success statuses and preserves its exact
world, independent of CALL's success-stack calculation. Errors cannot yield an
invented child tuple. Denied dispatch publishes the actual original world and
stack zero; no child code or funding hypothesis is smuggled in.

CALL and all three family wrappers compose through the exact helper invocation,
including execLength increment and final stack/PC replacement, whose accountMap
projection is unchanged. Their source/recipient/code target, actual/apparent
value, permission and fuel are exactly the existing reviewed helper parameters.
The resulting post-world equality is derived from the actual StepOk, not
assumed. No gas-bound or recursive funding inequality appears in a premise.
No axiom or native evaluation is added. These are local dispatch projections,
not yet the mutual execution funding induction or protocol balance conservation.

---

# Independent review: CreationFunding

CLEAN for its stated local entry/nonce/settlement scope.
Reviewer: root integrator, not module author.
Source Eip8282/Audit/Integrator/CreationFunding.lean
SHA256 56aea62e253201415efc28eab267a99f9d6adc671885521d4eaec10b7c59816a

Read complete candidate and actual Lambda entry/collision/settlement in pinned
EvmYul/EVM/Semantics.lean, CreationSettlement, TransferFunding and StorageFunding.
The previous author's targeted /tmp/eip-CreationFunding-2.log has standard axiom
reports only; root independently reruns targeted compilation separately.

Installation changes only code and preserves the finite balance sum even when
its getD default account was absent. NonceWorld is the literal CREATE insertion
of the owner's incremented nonce; absence inserts an account of zero balance,
so funds and the owner's balance are preserved. The real nonceAllowed upper
bound prevents increment wrap and proves the inserted nonce is nonzero.

For distinct sender/derived target, Lambda's actual debit-then-credit order
cannot increase natural funds if the real sender can afford value. The credited
account is built from the OLD target, unlike Theta. Distinctness establishes
that target's balance was not affected by the earlier sender debit. Modular
recipient credit may lose value; no false equality or no-wrap hypothesis is
introduced. Missing sender leaves the actual world unchanged.

The alias case must not be passed to the distinct transfer theorem. With a
nonzero sender nonce, the actual collision check selects one-byte INVALID as
init code, and every actual completed settlement restores the input world.
The proof supplies no hash injectivity, absence of address fixed points, or
predicted execution result. The selected-invalid theorem also prevents an
incorrect inference that arbitrary user init code runs against the potentially
inflated alias entry world. Final gas or creation liveness is not claimed.

These helpers do not yet compose into universal recursive funding conservation,
transaction admission or an initial protocol supply bound. A raw arbitrary
Lambda boundary needs the funding and alias/collision conditions stated here;
internal CREATE derives the nonce condition from its real admitted increment.
No project axiom or native evaluation receipt is added.

---

# Independent review: CreationWorld

Verdict: CLEAN.

Source: `Eip8282/Audit/Integrator/CreationWorld.lean`
SHA256: `5b096b395cb74f05511c6a288522630cbf436cac205881ffe9f7760597b358ed`.
Worktree: `/Users/thomas/work/eip-8282/direct-closure-implementation`.
No edits or builds by reviewer. Read the complete candidate; `/tmp/eip-CreationWorld-2.log` contains only the standard propext, Classical.choice and Quot.sound dependencies and no diagnostics.

The theorem projects the accountMap of actual CREATE/CREATE2 StepOk at fuel+1. Stack shapes, caller nonce and funds/depth/size gates are the exact CreationGas definitions previously reviewed against executable dispatch. The child uses precisely Lambda fuel after the charged state and actual nonce insertion, with correct absent/present salt. The proof splits that actual child result, unfolds the real dispatcher and identifies the actual successful step state; it does not assume a predicted child world or apply a funding theorem.

For a completed Lambda tuple, either Bool status is allowed and post.accountMap is exactly its returned world. For any Lambda error, including OutOfFuel and address encoding errors, CREATE's actual catch-all publishes the literal empty map. The proof preserves this unusual upstream behavior rather than substituting the original journal. In each branch it removes the final word gas guard only from actual StepOk, so no success/liveness claim is derived by ignoring an overflow guard.

The pre-nonce and helper admission gates remain explicit and necessary for this two-branch statement. Denied creation is intentionally outside this theorem and remains covered by CreationGas.step_denied. It proves no fundedness, balance conservation, account existence, gas sufficiency or protocol condition. It is the exact world bridge needed before separately applying a Lambda funding induction.

Dependency review: `/tmp/eip-CreationGas-review.md` covers CreationGas SHA `13aff91fba701884c09b25065ac1f8e7afaa849ce2b4c3b9e75abebed975feeb` and its literal CREATE/CREATE2/Lambda semantics.

---

# Independent review: ExecutionFunding

Verdict: CLEAN for the stated actual-evaluator balance-sum bounds.

Reviewed complete frozen 580-line module `Eip8282/Audit/Integrator/ExecutionFunding.lean`, SHA256 `faa5fd66ac0daa24770a2dd4608cf8729721166a7636ccd8ac27ed88fc8b7d5b`. Read-only review; no proof edits or builds. Inspected `/tmp/eip-ExecutionFunding-5.log`: all_bounds and all five exported projections report only propext, Classical.choice, Quot.sound. No sorry, new axioms, native evaluation, supply ceiling or assumed desired poststate occurs in the candidate.

## Statement and induction

`worldFunds` is the finite natural sum of balances in the actual AccountMap.toList, not a ghost supply variable. XBound and XiBound concern actual success payloads only; REVERT has no returned world at those boundaries. ThetaBound and LambdaBound cover either Boolean status of actual completed results. StepBound requires actual Z acceptance and actual StepOk, so it is an accepted instruction theorem, not a claim about arbitrary unchecked raw transformers.

Strong induction uses actual evaluator fuel: X(n+1) invokes Step(n) and, on continuation, X(n); Xi(n+1) invokes X(n); Theta(n+1) and Lambda(n+1) invoke Xi(n). CALL-family Step(n+2) invokes helper(n+1), then Theta(n). CREATE-family Step(n+1) invokes Lambda(n). The low-fuel CALL cases are eliminated by actual helper OutOfFuel, and zero-fuel X/Xi/Theta/Lambda results cannot satisfy completed-result premises. Step's child induction hypotheses use strictly smaller fuel, and all_bounds obtains Step(n) independently from those smaller child bounds before constructing the other components. No circular postcondition premise or replacement execution at larger resources is used.

## Actual world transport

X inversion binds the actual decoded instruction, accepted Z, actual step, and same final world. Halt and continuation cases compose nonincrease correctly. Xi reconstructs the evaluator's exact fresh initial machine with input world and projects its actual successful final account map.

Code Theta first uses actual credit-then-debit entry_funds_le under real value <= real sender balance. A successful Xi world is bounded by that actual entry world. The upstream `world == empty` fallback is split literally: either original world is selected, or the actual child world. This needs no LawfulBEq for Account and does not turn lookup equality into structural map equality. REVERT and completed exceptional failure restore the original world; interpreter OutOfFuel cannot be a completed Theta result.

All ten precompiles were checked against complete PrecompiledContracts.lean and Theta's actual dispatch table, including unknown-target default. Their world projection is input world or literal empty world; cryptographic outputs need no correctness/FFI assumptions for this projection. The adapter binds precompile input to actual transferred entryWorld and the real environment (empty code), then applies Theta's same empty-world fallback. No precompile is omitted, and no gas-bound premise is needed.

Lambda handles failed preimage by contradiction with actual completion. For distinct sender/derived target, actual debit-then-fresh-credit entry is nonincreasing with funded sender; recipient modular addition may reduce the total. Init errors and REVERT restore input world. Actual init success composes Xi nonincrease with entry_nonincrease, then either deposit failure restores input world or code installation preserves funds.

The alias branch is correctly separate: a real existing sender with nonzero nonce forces occupied-target deposit failure, and every completed settlement returns the input world. No Xi induction hypothesis is applied to the potentially inflated alias entry. This is important: raw Lambda is NOT proved conservative without its explicit NonzeroNonce condition. Internal CREATE/CREATE2 derive that condition from their actual admitted nonce increment, with the 64-bit gate excluding wrap to zero; they do not assume it externally.

## Internal instruction coverage

Actual Z preserves the world and stack apart from gas charging. Accepted_stack derives the needed 7/6/3/4 operands. Ordinary covers precisely the complement of CALL/CALLCODE/DELEGATECALL/STATICCALL/CREATE/CREATE2; its already reviewed instruction proof includes SSTORE/TSTORE and all SELFDESTRUCT balance cases.

For CALL and CALLCODE, the real gate checks codeOwner's balance, and the source address passed to Theta is proved to round-trip to that same owner. DELEGATECALL and STATICCALL have zero real transfer, regardless of apparent value. The .empty code used to obtain family_funded is irrelevant to its funding projection and is not an original-code pin or replacement child premise. Actual child invocation/result is independently obtained by CallWorld, including arbitrary selected code/precompile and either Boolean status. Denied calls retain the actual prior world.

For CREATE/CREATE2, actual funds/depth/size and nonce gates are split. Funded value is transported to the actual nonceWorld, whose total and owner balance are preserved. CreationWorld supplies the same actual Lambda returned world, or literal empty world for a caught child exception (including OutOfFuel). The latter is safely bounded by zero; denied branches keep the old map. No child failure is silently treated as a successful Lambda result.

## Scope limits

This is a universal theorem for every finite evaluator fuel and arbitrary code/state satisfying its local input conditions, not a finite test or 256-iteration cutoff. It establishes nonincrease at the named actual execution boundaries. It does not prove equality (modular credits, burns and upstream caught-error empty maps can reduce funds), execution termination, a global Ethereum supply ceiling, transaction admission, transaction fee/refund settlement, protocol issuance/withdrawals, cumulative event counting, or a bound on every nested/intermediate entry world. In particular, applying LambdaBound at a top-level creation transaction still requires deriving its funded-value and nonzero-nonce inputs from actual transaction processing. These are honest remaining composition obligations, not hidden conclusions of this module.

CallWorld was authored by this reviewer and independently reviewed CLEAN by root; this review rechecks its use and binding, not claims independent authorship review of that dependency. Prior independent reviews cover TransferFunding, CallFunding, OrdinaryFunding, CreationWorld and CreationFunding; complete relevant actual semantic clauses were reread here. ReturnedGas is used only for exact precompile dispatch and accepted stack extraction, not as an assumed funding theorem.

## Source bindings

- `Eip8282/Audit/Integrator/ExecutionFunding.lean`: `faa5fd66ac0daa24770a2dd4608cf8729721166a7636ccd8ac27ed88fc8b7d5b`
- `Eip8282/Audit/Integrator/CreationFunding.lean`: `56aea62e253201415efc28eab267a99f9d6adc671885521d4eaec10b7c59816a`
- `Eip8282/Audit/Integrator/CreationWorld.lean`: `5b096b395cb74f05511c6a288522630cbf436cac205881ffe9f7760597b358ed`
- `Eip8282/Audit/Integrator/CallWorld.lean`: `d91c68bcce947482acaabbd79c9779ac60bf49f6c908acf7185830f5059bbc18`
- `Eip8282/Audit/Integrator/OrdinaryFunding.lean`: `dc8c4eddd8af0b05396e4882d77fac97ead4e512e5996ed784c465f4ae5c53a6`
- `Eip8282/Audit/Integrator/CallFunding.lean`: `d5429791c3baf878e2fa0ea041d8bb00604b39f97bb5e23cfd25ad75c5aed9f2`
- `Eip8282/Audit/Integrator/TransferFunding.lean`: `b8d8286170495a4a59d0f61ad19e0354e624ea3a0c0e0f48bd24e92ea7871766`
- `Eip8282/Audit/Integrator/ReturnedGas.lean`: `b39d7af6e35834bb6ecd3364fd1055768ae8e11712dc92d811312e4ffce9dde9`
- `Eip8282/Audit/Integrator/SuccessInversion.lean`: `16296f56350ba53322d29e8cce6c8799ae95c175489d92689ed170d2875297c7`
- `Eip8282/Audit/Integrator/MessageCall.lean`: `3f16088bd13b6f6fdf13de417e4843f08e9dcd61fa6dfdddfc6342c250ccf342`
- `Eip8282/Audit/Integrator/CreationSettlement.lean`: `d95b28f2a46daf588a2aaf15e8a8f77fc28b075116e5f2395360e73152383820`
- `.lake/packages/evmyul/EvmYul/EVM/Semantics.lean`: `8b49f1aee609ce888041ba9e7253bbe55d06fda136252bc46d4e006755110f4b`
- `.lake/packages/evmyul/EvmYul/EVM/PrecompiledContracts.lean`: `cb69358e1f534c46e7054e4ef60eb8f78f7c78502b9d6e7e3ecf375c60206012`

---

# Independent review: FinalizationFunding

Verdict: CLEAN.

Reviewed complete frozen `Eip8282/Audit/Integrator/FinalizationFunding.lean`, SHA256 `e63683924b7f7ba1fdacd84c8c9cf76d3d770b3fc64e5e468ce9aa594a56bcb0`. Read-only; no proof changes or builds. `/tmp/eip-FinalizationFunding-3.log` contains successful axiom reports for credit_le, erase_le, clearTransient_le and cleanup_le, each only propext, Classical.choice, Quot.sound.

- `credit_le` unfolds actual AccountMap.increaseBalance. Missing-account insertion has exactly the supplied amount (including zero); existing-account modular addition is bounded by the natural sum. The actual finite-map insertion identity cancels the prior balance. No overflow exclusion, account-presence premise, or equality overclaim is introduced.
- `erase_le` derives actual erased-map toList inclusion from getElem?_erase and mem_toList_iff_getElem?_eq_some. Key uniqueness implies pair uniqueness in the erased list; Nodup.subperm converts inclusion to a sublist up to permutation. Mapping balances and summing nonnegative naturals gives the desired total bound. This is about actual map contents, not an assumed balance-preservation predicate, and requires no LawfulBEq instance for Account.
- `erase_list_le` composes each actual erase for arbitrary address lists, including repeats and missing accounts. `erase_set_le` rewrites the literal TreeSet.foldl to its toList fold and applies that result. There is no condition on membership or correctness of a selected deletion set.
- `rebuild_le` is a valid deliberately weak bound for arbitrary entries and starting world: insertion total is at most old total plus the inserted balance, even with duplicate keys. The transient reset changes only tstorage. Starting from empty and folding the actual original world.toList proves clearTransient_le. It does not assume an extensional or structural equality between the rebuilt map and the original map, and does not require a map order assumption.
- `cleanup` exactly matches the three actual Υ operations: erase selfDestructSet from the input world; compute touched-and-dead addresses using State.dead on that SAME original cleanup input world (the actual post-credit σStar', not the map after destruct erasure); erase that set from the destruct result; rebuild the surviving map with empty transient storage. `cleanup_le` composes those three actual bounds in this order.

The theorem concerns the natural sum of actual account balances. It correctly allows decreases from modular credit overflow or erasures and does not assert that all selected accounts should be deleted under an external protocol specification. It imposes no assumption on deletion sets, created accounts, account existence or desired poststate. The finalization operations are literal and their order matches Υ, but this module does not yet bind a completed Υ result to cleanup or prove fee escrow/refund conservation. Those belong to the separately active TransactionFunding composition and were not reviewed here. No supply ceiling, issuance, transaction-validity or aggregate event-count claim is made.

Read dependencies: TransferFunding.funds_insert and worldFunds/worldBalance, actual AccountMap.increaseBalance, actual State.dead, actual Υ finalization clauses, and List.Nodup.subperm / nonnegative sublist sum semantics. Previously reviewed TransferFunding remains unchanged.

## Source bindings

- `Eip8282/Audit/Integrator/FinalizationFunding.lean`: `e63683924b7f7ba1fdacd84c8c9cf76d3d770b3fc64e5e468ce9aa594a56bcb0`
- `Eip8282/Audit/Integrator/TransferFunding.lean`: `b8d8286170495a4a59d0f61ad19e0354e624ea3a0c0e0f48bd24e92ea7871766`
- `.lake/packages/evmyul/EvmYul/Maps/AccountMap.lean`: `8ce51e59b0d2be13b7bb749225a28bb532c8cc07574f798617c03a7392b08b54`
- `.lake/packages/evmyul/EvmYul/StateOps.lean`: `ed24f52c490c1f9a56f4df5a3883533dad884ca2276f58d05cbf9ed3cd386e21`
- `.lake/packages/evmyul/EvmYul/EVM/Semantics.lean`: `8b49f1aee609ce888041ba9e7253bbe55d06fda136252bc46d4e006755110f4b`

---

# Independent review: TransactionFunding

Verdict: CLEAN for the stated conditional whole-transaction funding theorem.

Reviewed complete frozen `Eip8282/Audit/Integrator/TransactionFunding.lean`, SHA256 `dff074ffa97b3c17862496c3cd92bfb50611c7f19796c79ad95a469778508f2f`. Read-only; no edits or builds. Inspected `/tmp/eip-TransactionFunding-6.log`: all six printed theorems use only propext, Classical.choice, Quot.sound. Its only reported warning concerns unfolding autogenerated `Υ.match_1`; this is a refactor-maintenance issue, not a soundness or scope defect. No sorry, native evaluation, new axiom or opaque assumed transition occurs.

## Independent admission and exact debit

Admission requires a real pre-world sender account, natural sufficient balance for gasLimitNat * actual effectivePriceNat + natural calcBlobFee + transaction valueNat, sender nonce < 2^64-1, and actual priorityFeeNat <= effectivePriceNat. These refer only to actual inputs and pre-state; none is a child/final-world property. Both prices are the literal word formulas from Υ via RefundAccounting.Context. This is a sufficient local admission predicate, not a claimed extraction from consensus validation or a maximum-fee transaction validation theorem.

checkpoint_eq matches Υ's actual sender insertion, including gas-price product, separate blob-fee debit and nonce increment. debited_balance derives product and blob-fee casts fit in UInt256 from natural fundedness and the original balance's inherent word bound. It then proves each subtraction cannot underflow; it does not equate modular arithmetic with naturals by assumption. Consequently checkpoint_debit is an exact finite-world identity: funds(checkpoint) + upfront = funds(preworld).

checkpoint_funded derives sufficient actual transfer balance after fee escrow. checkpoint_nonce binds the actual inserted debited account and uses the admitted nonce bound to prove the increment is nonzero without wrap. Thus the nonzero-nonce premise of raw Lambda funding is discharged for real transaction creation, rather than assumed about a created poststate.

## Actual provisional execution

Context.provisional exactly selects Lambda for recipient none, Theta for recipient some, with the actual checkpoint used as both current and original world, actual entry gas and access substate, actual selected code/precompile, and the same sender/origin, input value/data, header and permissions as pinned Υ. Its interpreter fuel is literally c.fuel, with no off-by-one substituted execution.

provisional_funds applies the already reviewed universal ExecutionFunding bounds to the actual child equation recovered by splitting that expression. It derives the funded value and, for Lambda, nonzero nonce from Admission. It retains arbitrary Boolean status. Child errors cannot satisfy a completed provisional result and are eliminated; neither error nor false status is silently treated as successful execution. The resulting world bound is against the actual checkpoint.

## Settlement and whole-world result

payout_le derives refunded gas <= original limit from the real capped refund formula and remaining <= limit, then proves netGasNat = limitNat - returnedGasNat. Refund plus used gas exactly partition the original gas limit. Each word payment product is bounded above by its natural multiplication, and priority <= effective price bounds the beneficiary part. Thus the two actual credit amounts together cannot exceed gasLimitNat * effectivePriceNat. No assumed equality of modular products, refund bound supplied by a consumer, distinct-address condition, or recipient-presence premise is used.

settledWorld matches Υ: sender refund first, optional beneficiary payment second, then exact self-destruct erasure, dead-account erasure (tested against the same post-credit world), and transient-store rebuild. Credit and cleanup lemmas apply to the actual worlds in sequence, including sender/beneficiary alias or absent accounts. settled_funds_le is a bound relative to the actual provisional world, not a supplied final state.

result_equation is equality of the FULL actual Υ result expression, including world, substate, status, net gas, and error propagation. Its proof unfolds the literal evaluator and helpers; it is not the earlier gas-only projection. Compared with the complete actual Υ source, the checkpoint, both provisional dispatch cases, fee calculations, credit order and cleanup all agree.

result_funds rewrites the actual result with that equality, recovers its actual provisional tuple, derives its funds bound, and derives remaining <= entryGas <= gasLimit through TransactionGas and ReturnedGas. It then combines the actual settlement bound with the exact escrow identity. The natural blob fee is a nonnegative additional debit and is not refunded. The final world in the conclusion is forced by the actual completed result equality; there is no assumed final-world agreement or desired funding postcondition. Both success=true and success=false are covered because status remains arbitrary throughout.

## Scope and remaining obligations

This proves funds(final actual Υ world) <= funds(input world) for every finite evaluator fuel and every actual completed transaction result satisfying independent Admission. It is a whole-world transaction theorem, not merely transfer-entry or gas observation. There is no supply-ceiling or aggregate charge hypothesis. It does not prove equality, exact base/blob burn amounts, successful completion, signature/sender recovery, nonce equality to transaction nonce, intrinsic-gas validation, fee-cap/base-fee validity, consensus admission implying Admission, block/protocol issuance or withdrawals, or a global supply bound over a protocol history. The supplied sender is the one passed to the pinned Υ function. Those remaining environment and consensus bridges are accurately excluded by the source comment.

The UInt256 fee formulas may have behaviors outside protocol-valid inputs; the theorem intentionally uses those literal values and explicit priority/funding conditions. It does not claim they equal unbounded protocol pricing formulas without an additional validity bridge. Interpreter OutOfFuel remains an error, outside the completed-result premise; the theorem is arbitrary-finite-fuel safety, not termination or a fixed iteration cutoff.

ExecutionFunding and FinalizationFunding hashes remain unchanged from their independent CLEAN reviews. TransactionGas and RefundAccounting are also unchanged; their relevant complete sources and the literal pinned Υ implementation were reread for this composition. No semantic finding blocks integration.

## Source bindings

- `Eip8282/Audit/Integrator/TransactionFunding.lean`: `dff074ffa97b3c17862496c3cd92bfb50611c7f19796c79ad95a469778508f2f`
- `Eip8282/Audit/Integrator/ExecutionFunding.lean`: `faa5fd66ac0daa24770a2dd4608cf8729721166a7636ccd8ac27ed88fc8b7d5b`
- `Eip8282/Audit/Integrator/FinalizationFunding.lean`: `e63683924b7f7ba1fdacd84c8c9cf76d3d770b3fc64e5e468ce9aa594a56bcb0`
- `Eip8282/Audit/Integrator/TransactionGas.lean`: `c9d1714110c73b74a29bc2eb2900b2264fd4136275a8d4cd3e5788647044476e`
- `Eip8282/Audit/Integrator/RefundAccounting.lean`: `4c67ebc4ccb77819248e0c6030cc5f63a0274ce0752d8ad17784a136096750fb`
- `.lake/packages/evmyul/EvmYul/EVM/Semantics.lean`: `8b49f1aee609ce888041ba9e7253bbe55d06fda136252bc46d4e006755110f4b`
- `.lake/packages/evmyul/EvmYul/State/TransactionOps.lean`: `edfb3e96f719dd31081c5836fa310c1c2996afb10ff0baa0436faa348cbccbdc`

---

# Independent second review: CreationFunding

Verdict: CLEAN for the stated local creation-funding and alias-settlement lemmas.

Source: `Eip8282/Audit/Integrator/CreationFunding.lean`
SHA256: `56aea62e253201415efc28eab267a99f9d6adc671885521d4eaec10b7c59816a`.
Worktree: `/Users/thomas/work/eip-8282/direct-closure-implementation`.
This report is separate from root's existing `/tmp/eip-CreationFunding-review.md`. No edits or builds by reviewer. Read the complete candidate and matched its operations against the previously reviewed complete CreationSettlement context and actual Lambda implementation. The supplied `/tmp/eip-CreationFunding-root-validation.log` is clean and reports only standard Lean axioms for its six printed theorem dependencies.

The total is TransferFunding.worldFunds, the finite natural sum of actual map balances. getD_balance handles absence using the real default account's zero balance. install_preserves changes only code and therefore preserves this total even if installing an absent account with zero balance. nonceWorld is exactly CREATE's owner insertion with incremented nonce. nonce_preserves and nonce_balance cover existing and missing owners; they do not assume an account exists. nonce_positive obtains actual presence from insert and proves the increment cannot wrap using the admitted nonce threshold (<2^64-1), rather than assuming the output nonce is nonzero.

entry_distinct follows Lambda's real debit-before-insert order. The fresh target account is built from the OLD target account and receives value+oldBalance. Distinctness proves that debiting sender leaves the target lookup unchanged. Actual sender funding supplies no-underflow for subtraction; modular recipient credit is bounded by the natural sum using Nat.mod_le, so only nonincrease is claimed. Missing sender follows Lambda's actual unchanged-world branch. No target balance-fit, account existence or address-hash injectivity is assumed.

The alias case is correctly separated. Lambda's target insertion can overwrite the sender debit with an account built from the old sender and thus increase an intermediate entry-world balance. This module does NOT assert entry conservation for that case. It proves that an existing sender with nonzero nonce makes both the literal collision selector choose one-byte INVALID and the later occupied-target depositFailure guard true.

alias_settle_world then proves every completed settlement at target=sender returns the input world, for an arbitrary init RunResult. Error OutOfFuel cannot satisfy its .ok premise; other errors and REVERT restore the input world directly. Even an arbitrary successful init result cannot escape restoration, because the occupied-target guard is derived from the actual original-world sender nonce. Thus the theorem need not assume init failure or invoke execution induction on a potentially inflated intermediate world. Its input settle equality is the graph of a concrete semantic operation, not desired poststate agreement; the consumer must still bind it to actual Lambda with the existing result_eq_settle theorem.

The public statements do not prove full Lambda or recursive evaluator conservation by themselves. They provide the distinct funded-entry case, code-installation frame, nonce bridge and alias rollback case needed for that subsequent induction. They make no transaction nonce/admission, canonical address, hash collision resistance, supply or protocol-history claim. The later consumer must ensure the nonzero nonce premise for actual top-level creation as well as for admitted CREATE/CREATE2, and must not call the entry-distinct result when sender and target alias.

Reviewed finite-map foundation: TransferFunding SHA `b8d8286170495a4a59d0f61ad19e0354e624ea3a0c0e0f48bd24e92ea7871766`. Its funds_insert identity uses lawful AccountAddress ordering and finite-list permutation, not LawfulBEq on accounts. No new native evaluation, sorry or custom axiom is present in CreationFunding.
