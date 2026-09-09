# Independent reviews: append necessity and invariant preservation

# AccountedState — independent source review

**Outcome: CLEAN for the observed-storage arithmetic and preservation scope.**

Source: `Eip8282/Audit/Integrator/AccountedState.lean`.
SHA-256 checked twice: `382a0419905acd948e36c7290e2b81f6d3641f712e4077bb471386340b7b54e7`.

Read all declarations and the complete relevant `QueueArithmetic` pointer proofs, plus `ResourceBounds`, `AppendStorage` control/no-alias lemmas, and `ControlSpec`/`SystemSpec` control formulas. Inspected `/tmp/eip-AccountedState-2.log`: all six printed declarations have only standard axioms. Parent reports compilation exit 0. No build or source edit performed in this review.

## Checked facts

- `Bounded` reads slots 0–3 from an arbitrary observation function. It correctly stores `HEAD≤TAIL≤budget`, `count≤budget`, and the coupled `excess+count≤budget` only when the excess word is not INHIBITOR. Thus it does not attempt to bound the inhibitor sentinel numerically or lose the joint bound needed at SYSTEM.
- `initial` requires only the actual initial control observations: head, tail and count zero, excess zero or INHIBITOR. It derives `Bounded 0`; it does not manufacture an initialized account map. Binding these premises to constructor installation remains a separate step.
- `mono` is ordinary weakening of the budget on the same read map. This is the correct algebra for a rollback to a previously bounded journal with a now larger cumulative execution budget. It is not itself an execution/rollback theorem, and does not claim to extract a prior journal.
- `append_fits` uses only entry `Bounded` and `budget<2^128`, before any post-state assumption. The maximum stride is six; the independent numerical margin bounds the entire record window and both count/tail successors below 2^256. No record/control alias or count increment is assumed in order to derive that margin.
- `append` first derives that fit, then uses the independent `expected_head`, `expected_excess`, `expected_count_nat`, and `expected_tail_nat` lemmas. Queue order is preserved, tail/count increase by one, and the unchanged excess plus incremented count fits `budget+1`. The uninhibited entry gate is an explicit input fact intended to come from actual successful-call classification. The output active-bound proof does not assume the bound it is proving.
- `system_control` retains latch-before-unlock-before-fold ordering. Nonempty calldata is incompatible with a non-inhibited output. Empty calldata from INHIBITOR produces zero. In the enabled branch the coupled entry bound and `budget<2^256` imply the intermediate addition fits, then natural saturated subtraction cannot increase the total. The target is unrestricted here; no unjustified target-smallness premise is needed.
- `system` derives pointer behavior through `QueueArithmetic.pointers`. Its required `drained≤length`, together with queue order, proves the head addition does not wrap. Full drain resets both pointers; partial drain advances head no further than tail and preserves tail. Count resets to zero, and the derived control bound therefore suffices for the post-state's coupled bound. Cases include empty queue/zero drain and zero budget.

## Limits to retain when integrating

1. These are preservation lemmas for the independently specified read maps, not yet an induction over actual Θ executions or protocol histories. The earlier direct endpoint theorems must identify the actual resulting read map, with their own conditions; arbitrary-success classification remains a separate task.
2. `budget` is an independent Nat parameter here. Its interpretation as the cumulative number of locally successful appends, including later-reverted children, still needs the concrete trace and nonduplicated gas-accounting bridge. No such interpretation is silently proved by the structure name or `mono`.
3. The output of `append` has budget+1 but does not prove `budget+1<2^128` from `budget<2^128` alone. This is correct. A history proof must supply a bound on every prefix from a larger independently accounted total, or reserve room for the next event.
4. The actual caps 64/16 are not assumptions hidden in `system`. Instantiate its drain premise using `QueueArithmetic.deposit_count`/`exit_count` and `min≤length`; these already derive the capped word count under queue order.
5. The resource envelope protects slot arithmetic and control sums. It does not establish the much stronger fee-recurrence product bounds or the external funding ceiling of `FundedDomain`.

No blocking defect, circular postcondition, dropped wrap condition, or overclaim found within this scope.

Relevant dependency hashes:

- `QueueArithmetic.lean`: `95dd375417bcf6ddd2fa2bf3326807f1db7080e9ddfb0f75c4f2d1f7aa925da9`
- `ResourceBounds.lean`: `099a06b7178531f58fb8c889ecd583bbe7fd890d1490ae0261d971f5640d87b6`
- `AppendStorage.lean`: `06e1f4e9e0c0f447c52eff02f853b9f15b511f58b944e8ecb21745e4e54c23eb`
- `ControlSpec.lean`: `a8d1c48459d1779fabba1031f9b8e2474ae429638615826c9a4b0b63fdb39ebf`
- `SystemSpec.lean`: `291b21d9803b148276bf05a111940fb4bc37af676a89466a0ba808c1a2d80b26`

---

# FundedDomain — independent source review

**Outcome: CLEAN for the conditional preservation statements actually exported.**

Reviewed source: `Eip8282/Audit/Integrator/FundedDomain.lean`.
SHA-256, checked before and after review:
`957cb3c9fa8951df7daf57bf0cb0fae883c4b01e7b514c0dee551edf773cd1d7`.

Read the complete module, the relevant complete arithmetic/payment modules, and the actual settlement/storage transports on which its specializations depend. Inspected `/tmp/eip-FundedDomain-3.log`: the eight printed principal results list only `propext`, `Quot.sound`, and where needed `Classical.choice`. The parent reports compilation exit 0; this read-only review did not rerun Lean or alter sources.

## Findings

1. **The funding argument is a boundary-crossing proof, not an assumed safe post-state.** `paid_append_safe` assumes only the prior natural numerator is at most 2892. Since a count increment raises that numerator by at most one, the only way to leave the interval is to append at prior numerator 2892. At precisely that numerator, `boundary_price` identifies the completed operational quote with `fundingCeiling`. Actual payment of that quote contradicts `value < fundingCeiling`. This proves prior numerator <2892 and hence the desired successor bound. It does not assume monotonicity of the wrapped tariff outside the interval, nor the postcondition being established. The strict inequality on funding is material.

2. **The boundary price is independently certified, with no hidden semantic cutoff.** `fundingCeiling = FeeSafeDomain.certificateOutput / 17`; `boundary_math` obtains the mathematical quote from `upper_stops`. `boundary_price` uses `any_quote_agrees` and uniqueness of the natural quote to cover every finite operational completion witness `n`, not just the certificate's 462-step witness. `FeeSafeDomain` proves the whole interval by monotonicity of trajectory fit/completion from a kernel-checked upper trajectory. `MathFee.PrefixFits` checks output addition, numerator-times-accumulator, denominator product, and counter increment before division. Both fee evaluators return `none` on an unfinished prefix; neither returns a truncated partial fee. Natural existence/uniqueness and budget stability include zero-budget edge cases. No legacy Model-256 theorem is used by this argument.

3. **SYSTEM sum bounds are derived from the entry invariant.** In the enabled branch, `excess + max(count-target,0) ≤2892` and `target≤8` imply `excess+count≤2900<2^256`. That justifies `foldWord_eq_nat_of_sum_lt` on the intermediate addition, before the comparison and subtraction. The resulting natural fold is at most the old safe numerator. `expected_system_safe` additionally uses the independent count-reset theorem, so the new numerator is the new excess. Nonempty calldata latches first; empty calldata while inhibited unlocks. Neither of these branches relies on a bound for the inhibited word, arbitrary prior count, or funding. The proof does not accidentally identify the quote numerator with the SYSTEM fold below target.

4. **Append control effects retain the necessary independent storage conditions.** `expected_append_safe` uses `AppendStorage.expected_excess` and `expected_count_nat`. Those establish unchanged excess and a natural count successor under `AppendFits`, including non-aliasing of the record window with control slots. The funding invariant is not used to manufacture an unproved tail/window bound. `AppendFits` remains a genuine separate premise; even a very small fee numerator does not bound the queue tail over a long history.

5. **The successful-call specializations use the same quote and the actual transferred value.** Both submission theorems first obtain an actual `AppendResult` via `SubmissionCall`. `SubmissionCall` extracts the fee-loop output and quotient from the supplied `hq`, and passes that exact output/price into the actual bytecode path. The funding proof rewrites the same `hq`, rather than introducing an unrelated cheaper quote. `hactual : apparentValue = value` binds bytecode CALLVALUE to the transferred value. The deposit checks retain both the minimum amount and `fee + 10^9 * amount ≤ value`; the uint64 amount proves this product fits before any payment equivalence. Exit retains `fee ≤ value`.

6. **The pre-call natural numerator is not an already-wrapped surrogate.** `SuccessfulUser.numerator` reads the original Θ target's slots before transfer. `TransferFrame.codeCall_storage` relates those exact reads to bytecode entry for all values, equal caller/target, and missing-account cases. `deposit_numerator` / `exit_numerator` use the explicit natural bound to discharge the modulo and identify `effExcess`. `hnat` and `he` therefore connect the operational quote to precisely the natural precondition used in `paid_append_safe`.

7. **Safety is attached to the actual published Θ result.** The generic `append_result_safe` and `system_result_safe` are explicitly transport lemmas: they take already-proved independent receipt/storage interfaces, not raw execution alone. Their concrete specializations discharge those interfaces through `SubmissionCall` and `CommittedSystem`; thus no safe post-world is assumed. `SafeResult` contains the actual Θ result equality and reads that same returned world. The underlying commit chain derives owner survival and rules out Θ's empty-world fallback by map size, without a `LawfulBEq Account` assumption or a desired-world identity premise. The constructor and earlier source modules are dependencies, not newly re-certified independent modules in this review.

## Scope that must remain explicit

- This establishes preservation under the stated prior safe-domain condition, strict call-value ceiling, code pin, successful-path acceptance/completion conditions, owner/fit conditions, and sufficient gas/fuel. It is not yet an inversion theorem for every successful append, a constructor-to-history induction, or a theorem of protocol reachability.
- Assuming the **entry** invariant for a preservation step is not circular. Supplying it for all reachable entries still needs a proved initialization and induction; placing the desired **post** invariant inside an environment policy would not discharge that work.
- `fundingCeiling` is an external ceiling on each call's value, not a proved Ethereum supply bound, sender-balance bound, cumulative spend bound, or chain rule. Θ itself does not establish ordinary funding admission. Nested calls, available balance and any economic bound must be bound separately.
- The code equality specifies Θ's explicit code branch. Installed-code identity at the canonical predeploy address and authorized caller/SYSTEM scheduling are not proved by these theorem signatures; `PinnedCall`/protocol consumers must supply those links.
- Inhibition is deliberately an alternative in `EnabledSafe`, not a claim that the inhibited numeric word satisfies the tariff interval.
- The module does not claim arbitrary global storage safety, FIFO correctness, or absence of the verified tariff divergence above 2892. The unrestricted economic/protocol version of the original guarantees remains open until the external domain and state induction are justified.

No blocking defect or overclaim found within these exported, explicitly conditional statements.

## Dependency source bindings

- `FeeSafeDomain.lean`: `3f23254c5bcced81f37ca5e510e6575e940ff3dc2455d798c2313348c46d6bbd`
- `MathFee.lean`: `5db596d01d2d93ea604c3fab7aa7e924248be8301187fa5ac82cc1813aecdf73`
- `SuccessfulUser.lean`: `fb5651794e94dac56439daaeb3ca83aa4c012d6916998cb638b1fdee5e80afff`
- `SubmissionCall.lean`: `face1db4310075322e020321797e520da7068221633495912bdd192b0ff1e7b8`
- `CommittedAppend.lean`: `1bae1c578fb56ca68e7a1cd3cb6c2c6e7ac9719e55748e5d1fd2900c86dc7b5b`
- `CommittedSystem.lean`: `e28f6cdb5c11c3ce7613333cdd4ddda04f76df2e7b6a3537b7d8be4453d11d92`
- `TransferFrame.lean`: `d7344861f8706ed4ef57954f8d0a5464212f45f12a5940976a6ebdd5bd945a1b`
- `ControlSpec.lean`: `a8d1c48459d1779fabba1031f9b8e2474ae429638615826c9a4b0b63fdb39ebf`
- `AppendStorage.lean`: `06e1f4e9e0c0f447c52eff02f853b9f15b511f58b944e8ecb21745e4e54c23eb`
- `SystemSpec.lean`: `291b21d9803b148276bf05a111940fb4bc37af676a89466a0ba808c1a2d80b26`

---

# Independent root review: UniversalRejection.lean

CLEAN. Frozen SHA256 5a513a8c25d266069c4e79c3899503cb691f4c9ee520ac9ac0dc90e41d5fac8f.

Read the complete module and the already reviewed SuccessfulUser admission, TransferFrame and UniversalGate journal dependencies. Input predicates independently enumerate wrong calldata sizes, nonzero getter value, deposit amount below the actual 1e9-gwei floor and natural fee/stake underpayment. The operational fee input is read from pre-transfer storage. KnownPrice witnesses any completed quote at that input; quoteWithin_unique correctly identifies it with the price of the same actual successful call, independently of execution budget. No arbitrary-resource execution is replaced with a sufficiently funded execution.

The two proofs split the actual completed Θ status. False uses whole pre-call journal rollback; true contradicts actual admission with concrete invalid inputs. The explicit ordinary-value binding and calldata-size fit are needed for natural payment and size comparisons. Gas, fee-domain bounds and execution-loop completion are not assumptions. A completed quote is an explicit input only for the known-price underpayment branch. OutOfFuel is outside a completed result; output and remaining gas are intentionally unconstrained.

Inspected /tmp/eip-UniversalRejection-1.log: all reported axioms standard. Reviewer did not author or edit the proof. Exact-commit integration check follows separately.

---

# AppendInversion independent source review — CLEAN

Reviewed frozen source SHA256 `11b57eb1e9446067a798c51c7ad97f34767630c8be796d481f109b180031a4ce`, confirmed locally. Read the complete module, actual success/effect inversion and fee-exit/guard dependencies, relevant bytecode-checked suffix shapes, EndpointState publication, AppendStorage independent maps/frame, AppendSpec anonymous logs/other-account frame, ExitRecord encoding, and upstream SSTORE/updateStorage/LOG semantics. Parent standalone compile log `/tmp/eip-AppendInversion-final.log` is clean and all printed exports use only propext, Classical.choice, Quot.sound. No edits/build performed.

## Actual execution and both suffixes

Every effect helper starts from actual `X ... = success final out`; success_effect retains the same final/out after the actual accepted exceptional/gas checks and concrete instruction effect. The proof does not replay a generously funded surrogate run. Z state changes are handled through the existing withGE/Z state lemmas; storage refund/access and logging effects remain in the concrete shared state.

The exit suffix covers count SSTORE, all three record SSTOREs (caller then calldata words), caller<<96 MSTORE at0, calldata copy48 bytes at20, LOG0 of68 bytes, tail SSTORE and STOP224. Deposit covers count, all six calldata-word SSTOREs, copy184 at0, LOG0 of184, tail SSTORE and STOP283. The checked block shapes match those memory lengths/offsets, and no write/log is skipped. STOP derives full shared-state equality and empty output from the actual halting branch, retaining arbitrary remaining gas.

## Same continuation and publication

The user results recover the actual full X execution from Ξ, then actual user-to-fee-head execution. AdmissionInversion fee_exit returns both its completed recurrence witness and continuation with that same output/counter, same state/memory and same final/out. This continuation flows through the actual exact-length dispatch and every payment/floor/stake guard into the write suffix. The completed-loop equation may be unused in this storage theorem because the actual continuation itself suffices; there is no independent price substitution. Payment/fee identification remains available from the separately proved admission theorem.

`resultAt_of_X` publishes the derived full state through the exact Ξ wrapper, using the actual final gas. Although ResultAt introduces an existential gas instead of directly equating the supplied published tuple, both hypotheses/conclusions equate the same deterministic c.result, so they necessarily refer to the same published tuple and bytes. No observation-only result or assumed post-state equality is used.

## Independent receipt and preservation

XiAppendResult joins actual Ξ success, owner existence, every-slot equality to an independently defined entry-read overlay, natural control-slot postconditions, authentic single appended LOG0 and other-account preservation in one actual world/substate. AppendStorage.expected/recordWord are specified from entry tail/count, calldata words and actual caller, not from an assumed final execution state. HasOwner supports real SSTORE account updates (including zero-value storage erasure); AppendFits separates physical record keys from controls and each other and prevents natural count/tail overflow. Logs are exactly prior logSeries.push(owner,emptyTopics,record), not mere membership:184 original calldata bytes for deposit; independent20-byte source||48-byte pubkey for exit. StoragePost preserves every slot outside count/tail/new record window; OtherAccountsUnchanged is relative to Ξ entry world.

Scope remains honest: these are Ξ success-necessity theorems, not Θ transfer/settlement theorems. No gas/quote-completion/permission premise is supplied; actual success supplies accepted effects. Exact calldata sizes and non-SYSTEM source are explicit; independent storage interpretation additionally assumes HasOwner and AppendFits. Prior logical FIFO preservation still requires the separate queue representation/window invariant; these theorems alone state physical slots. No protocol-history bounds, funding, installed-code authorization or mathematical-fee agreement is inferred.

No concrete correctness or overclaim findings.

---

# Independent root review: SuccessfulAppend.lean

CLEAN. Frozen SHA256 7dd2fab6f9f754bbd4c75043ef2a87b4df3cce25555d1d7ec004346836313e07.

Read the complete module and reviewed AppendInversion, CallSuccess, TransferFrame, WorldNonempty, CallBridge and SuccessfulUser dependencies. Actual Θ success supplies positive fuel and the exact successful Ξ payload. The receipt is derived from that actual execution, not from a second high-gas run. Its surviving owner excludes the actual empty-world settlement fallback; commits_endpoint preserves the same actual world, logs and returned empty buffer. All independent AppendResult observations belong to this deterministic result. Other-account preservation is correctly relative to the value-transferred world.

Both paid_append variants derive inhibition exclusion, completed quote and natural payment for that same call; apparentValue=value is explicitly required there. The lower-level append receipt itself does not need that payment binding. Owner existence is an input-world lookup transported through the actual transfer; local AppendFits remains explicit and is not called a protocol fact. Exact calldata size is an input here and derives its word-size fit in the admission composition. No permission, gas, evaluator-fuel or completed-quote premise remains.

Inspected /tmp/eip-SuccessfulAppend-1.log: five standard axiom reports. No source changes by reviewer. Final exact-commit validation follows separately.

---
