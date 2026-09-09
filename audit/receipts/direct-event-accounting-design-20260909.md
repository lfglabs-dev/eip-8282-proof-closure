# Minimal actual-execution event accounting

Design recommendation, not a completed proof. Read-only inspection of the pinned mutual evaluator, its precompile/settlement branches, and the existing gas/path APIs. No edits or builds.

## Recommended first target

Count a conservative superset: every ACTUALLY EXECUTED LOG0 whose actual stack length word is at least 68 bytes, in every nested frame, regardless of later rollback. Each such instruction costs at least 375 + 8*68 = 919 gas. Then inject distinct locally successful audited append calls into these actual LOG occurrences, using their existing 68/184-byte LOG path proofs. Counting only canonical predeploy events can be a later filtered subset; neither a code pin nor a queue invariant is needed for the generic gas theorem.

This is smaller and safer than summing the existing whole-append lower bounds at every call-tree node: parent gas debit already includes child debit. It also deliberately counts a LOG executed before that SAME frame later fails, which is harmless overcounting for the desired successful-append bound.

## Concrete certificate representation

Use a small tree of actual instruction occurrences:

```lean
inductive EventTrace where
  | done
  | step (marked : Bool) (child : Option EventTrace) (next : EventTrace)
```

`count` sums marked + child.count + next.count. The certificate, not the naked tree, gives it meaning. Define mutually inductive relations `XCert`, `XiCert`, `ThetaCert`, `LambdaCert`, and `AcceptedStepCert`, indexed by the ORIGINAL fuel, complete original inputs, actual `Except` outcome and EventTrace. Use the existing input Context records where applicable; raw Theta needs ToExecute as an index so all ten precompiles remain covered. No new execution state or transition function is needed.

An X node obtains its actual decode, Z equation, and a step certificate. Its next subtree is the unique actual X continuation, or done on halt/error. AcceptedStepCert has exactly one child subtree for the actually admitted CALL-family/CREATE-family invocation, and none for ordinary instructions or denied branches. The ordinary LOG0 marker is the EXACT Boolean test `op = LOG0 && 68 <= (pre.stack.getD 1 0).toNat`, enabled only when the actual instruction step completed; it is false on a failed instruction. Marker is computed, not freely supplied. Xi/Theta/Lambda wrapper certificates pass through the same tree and add no event themselves. Precompiles contribute done. Error-before-execution and fuel-zero cases contribute done; a generic `actualResult = error -> done` constructor is forbidden because it would erase already executed descendants.

Proof fields bind every child to the literal child arguments and actual returned outcome; they must not allow an arbitrary list of children. There is exactly one child invocation per recursive instruction and exactly one sequential continuation. The existing semantics' equality is an index/erasure condition, not an assumed cost or postcondition.

For distinctness, use structural positions: root event has []; child events receive a child prefix and next events a next prefix. Prove the flattened occurrence paths Nodup by construction. Do NOT identify occurrences by (code address, PC), fuel alone, log bytes or account-map content: loops, repeated calls and fuel reuse across frames make those collide. Xi/Theta/Lambda wrappers do not create duplicate occurrences.

Deliver both soundness (certificate erases to the exact evaluator equation) and completeness/extraction for EVERY actual outcome, including errors, by mutual strong induction on actual fuel. Prove trace determinism, or at least deterministic flattened marked occurrences, using deterministic Z/step/child results. Existing XRuns prefixes can then be embedded into the unique X certificate. This is a conservative instrumentation of the existing evaluator, with an erasure theorem; it is not a replacement abstract EVM.

## Main invariant; no assumed aggregate charge

Define an accounting residual of an actual result: the actual returned gas for completed outcomes (including REVERT and Boolean false), and 0 for `.error`. Zero on error is ONLY an accounting convention, not a claim that raw OutOfFuel returns a gas field.

Prove mutually, for certified X/Xi/Theta/Lambda evaluation and accepted steps:

```
residual(actualResult) + 919 * trace.count <= inputGas.toNat
```

For an accepted step, include actual Z memory charging in inputGas. This single invariant supplies both ReturnedGas's inequality and the missing event debit; no `919*count <= gross` premise occurs. The actual fuel recursion is already mapped by ReturnedGas: X(n+1)->Step(n),X(n); Xi(n+1)->X(n); Theta/Lambda(n+1)->Xi(n); CALL-family Step(n+2)->Theta(n); CREATE-family Step(n+1)->Lambda(n).

Ordinary successful steps use OrdinaryGas.accepted_step_debit; qualifying LOG0 additionally uses ActualAppendGas.accepted_log_cost. Failed ordinary steps have no new event. X continuation combines child/local-step count with the disjoint next count and telescopes gas. Halting RETURN/STOP/SELFDESTRUCT and REVERT terminate the same sequence; Z rejection has no executed instruction or child.

CALL success/failure-status children use the exact identity
`parentPost + (allowance - childReturned) + netOverhead + memory = parentPre`.
Child IH gives `childReturned + 919*childCount <= allowance`. Hence adding childCount is paid from allowance minus returned gas. Do not also add CALL's full opcode charge to nested charges. Stipend is included in allowance, and overhead is Cextra minus stipend, already proved nonnegative. Denied calls have childCount=0.

Theta successful/REVERT gas is unchanged from Xi; caught non-OutOfFuel error selects zero gas, retaining the trace. OutOfFuel propagates with accounting residual zero. The empty-world fallback has no effect on trace count or gas. Precompile traces have zero events and existing returned-gas bounds suffice.

Lambda REVERT and caught error retain the init trace despite rollback. Successful installation subtracts code-deposit cost (additional debit); deposit failure selects zero gas, so init-event debit remains bounded. Preimage failure has no init subtree. Address alias/collision needs no special funding argument here: any actually attempted init is traced, and the existing gas outcome is used.

## Exact missing edge/extraction lemmas

1. Generalize success_step to an all-outcome X unfolding/decomposition: zero fuel, Z error, Step error, continuation, success halt and REVERT halt. A Step error must retain the child trace if a recursive instruction already invoked it. Existing success-only inversion is insufficient.
2. Extend CALL-family actual helper/dispatch extraction to error outcomes. Preserve admitted child.error before propagation, handle helper fuel zero and denied branches explicitly. `CallWorld.step_*` and `step_child_gas` currently start from StepOk and cannot extract this branch.
3. Extend CREATE/CREATE2 extraction beyond StepOk: distinguish child completion, caught child error, denied gate/nonce, and the AFTER-child word-guard rejection. Even when the final guard rejects, retain the child's complete event subtree. The current CreationGas.step_child/accepted_child_debit only describe the accepted final step.
4. Prove error-side allowance budgets directly from accepted Z: CALL-family `allowance <= cost <= midGas <= preGas`; CREATE `allowance <= chargedGas <= midGas <= preGas`. Existing forwarded_fit proves the relevant fits, but expose these inequalities without requiring a completed step. This pays all descendant events when the parent itself errors and has accounting residual zero.
5. Supply raw Theta/Lambda all-outcome wrapper extraction using their real settlement, including unknown precompile default and failed creation preimage. The existing exact Context settlement lemmas cover code Theta and successful preimage Lambda; raw adapters must preserve the remaining branches.
6. Prove generic qualifying-LOG0 step debit from accepted Z + actual StepOk, without an assumed successful future continuation. `accepted_log_cost` already gives cost=375+8*len; `success_log_debit` alone is too narrow.
7. Prove XRuns-prefix embedding into all-outcome XCert, using XStepAt.deterministic and actual fuel. AppendGasPath.exit_log_path/deposit_log_path then locate a marked occurrence in the SAME actual subtree, not in a separately chosen larger-fuel trace.
8. Prove distinct successful audited call nodes map injectively to those occurrences. The chosen log belongs to the call's own local instruction sequence, so distinct call-frame paths give distinct log paths; outer wrapper nodes must not be counted again. Pinned audited runtimes have no recursive call instructions; an explicit no-recursive-child lemma from their supported path is a useful additional simplifier. Do not count inherited entry-substate logs or final receipts, which may have been rolled back.

Useful current APIs (arguments elided only here):

- `XStepAt vj fuel cost pre post := exists mid, Z ... = ok(mid,cost) and StepOk fuel ... mid post and H ... = none`.
- `XRuns vj fuel pre trace rest post`; `XRuns.X_eq`; `XStepAt.deterministic`. XRuns omits terminal/error steps and keeps a recursive Step opaque, so plain opcodeCharges cannot solve this task.
- `AppendGasPath.exit_log_path q huser hsize hsuccess : LogPath q 68`, and deposit variant 184. `ThroughLog` retains actual atLog stack, actual XStepAt and supported prefixes/suffixes. Theta debit endpoints are 919/1847, without supplied path/resource premises.
- `CallDispatchGas.accepted_step_call_debit`, `CallFamilyGas.accepted_step_debit`, and denied variants: exact child result plus natural settlement identity conditional on returned<=allowance; discharge that condition by the new child IH.
- `CreationGas.accepted_child_debit`: completed Lambda branch plus conditional natural identity, OR actual Lambda.error with exact `postGas + allowance + opcodeCost + memory = preGas`. `lambda_code_debit` gives successful code-deposit subtraction.
- `TransactionGas.provisional_remaining` and `result_debit` bind real provisional/final gas; `count_le_used` still has explicit aggregate charge and is the eventual consumer, not a source of that charge.

## CREATE obstruction check and proof order

CREATE catches ALL Lambda errors, including evaluator OutOfFuel, and resumes with empty account map, zero child returned gas and full allowance debit. This odd world behavior does not invalidate gas aggregation: error-side IH bounds events by the entire allowance that the parent actually consumes. Dropping that subtree WOULD be an unsound event-count interpretation. CALL propagates its child error instead; retain that subtree as well.

The CREATE final guard tests WORD `(chargedGas + childReturned).toNat < L chargedGas`. That addition can wrap, so a mathematically affordable creation may still error under the pinned evaluator. Do not replace it by a natural guard or infer successful execution from available gas. On accepted outcomes, existing settlement_nat derives a nonwrapping actual final gas from returned<=allowance. On rejected outcomes, residual=0 and child allowance<=input suffice for the event bound. No universal-aggregation counterexample is apparent from this guard, but its rejected branch is currently a missing extraction lemma and must be covered.

Suggested implementation order: (1) trace/certificate and all-outcome extraction with uniqueness; (2) generic marked LOG invariant for ordinary X including errors; (3) recursive CALL and CREATE edge adapters, then mutual aggregate theorem; (4) audited append occurrence injection; (5) actual Υ provisional extraction gives `919*appendCount <= limit - remaining`, including reverted ancestors, then the existing capped-refund arithmetic gives appendCount<=reported net gas. Count only actual execution attempts; committed-queue-event filtering is a separate subset/history mapping. Block association, distinct transaction slots and protocol limits remain later obligations.

This proposal does not assert those extraction, distinctness or aggregate theorems already exist.

## Inspected source hashes

- `Eip8282/Audit/Integrator/ReturnedGas.lean`: `b39d7af6e35834bb6ecd3364fd1055768ae8e11712dc92d811312e4ffce9dde9`
- `Eip8282/Audit/Integrator/CallGasAccounting.lean`: `35fc0df6019b4de427b3a1fced13564fa41b9c3a7e16ac40b9a929f8391f78b1`
- `Eip8282/Audit/Integrator/CallFamilyGas.lean`: `cae233fa8cbc8d8bd84c8ba00e48970c97a1abba03fe6987682d897e12a0e4b0`
- `Eip8282/Audit/Integrator/CallDispatchGas.lean`: `e1c5f79113ed283b4193bf6548adf7b91190a5b37183b00caf19a644460c6d4b`
- `Eip8282/Audit/Integrator/CreationGas.lean`: `13aff91fba701884c09b25065ac1f8e7afaa849ce2b4c3b9e75abebed975feeb`
- `Eip8282/Audit/Integrator/AppendGasPath.lean`: `4ae4dfb5b97ede8a12f108dc79ba45c4e041936b554772cbefb8c5539074c366`
- `Eip8282/Audit/Integrator/ActualAppendGas.lean`: `79a04a7b1a092026b24e3dfc3b0adc9bffaaa17a473e76a3f8a5447e75a7ea0d`
- `Eip8282/Audit/Integrator/OrdinaryGas.lean`: `d41661f413814579343e04a37da8cb87624881f63ac132440077beb8dc0adfd4`
- `Eip8282/Audit/Integrator/SuccessInversion.lean`: `16296f56350ba53322d29e8cce6c8799ae95c175489d92689ed170d2875297c7`
- `Eip8282/Audit/Integrator/TransactionGas.lean`: `c9d1714110c73b74a29bc2eb2900b2264fd4136275a8d4cd3e5788647044476e`
- `.lake/packages/evmyul/EvmYul/EVM/Semantics.lean`: `8b49f1aee609ce888041ba9e7253bbe55d06fda136252bc46d4e006755110f4b`
- `.lake/packages/evmyul/EvmYul/EVM/Proof/Execution.lean`: `8c70c77f09ec1b867788afbf1ddb8b6927b4fc5fd1cf8fee40e965a67eff8af5`
