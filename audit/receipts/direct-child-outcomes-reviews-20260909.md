# All-outcome recursive adapters and child-charge edge reviews

The child charge bound is an explicit induction hypothesis. These adapters
do not establish a universal nested-event count or protocol closure.

## Frozen source bindings

- `Eip8282/Audit/Integrator/CallOutcome.lean`: `4db2f3e3c92cdc8f958a9f8d69efd9b5d9c627d8ad421c847e11d4af1886a956`
- `Eip8282/Audit/Integrator/CreationOutcome.lean`: `2f3acec9be4d3c26f425ff9e94d8bbbb4709ffee9b93527313e31ff22a541ed3`
- `Eip8282/Audit/Integrator/RecursiveEventDebit.lean`: `5f2e5192fa26543e30eb470773417ebba0c57ed3a5947ec5a90a454ffd39a9b3`

---

# Independent review: CallOutcome

CLEAN. Root integrator review, independent of the author.
Source SHA256: 4db2f3e3c92cdc8f958a9f8d69efd9b5d9c627d8ad421c847e11d4af1886a956.
Read the complete module and literal pinned EVM.call / CALL-family dispatcher,
plus the reused helper definitions and accepted cost/forwarding identities.
Target /tmp/eip-CallOutcome-2.log completed with exit 0; all fifteen printed
public theorems have only standard Lean axioms and no warnings.

Full step equations preserve both helper success and error, exact actual stack
operands, execLength update, permissions, source/recipient/code target and real
versus apparent value. The helper error iff retains exactly the admitted child
Theta error; pure output memory and stack/PC construction add no error branch.
The gate is the actual owner's balance/depth test, not an assertion that an
arbitrary helper source is funded. CALLCODE, DELEGATECALL and STATICCALL keep
their actual six/seven operand layouts and distinct real/apparent value rules.

Denied helpers are constructed from the actual branch and return zero stack
status with unchanged accountMap, regardless of any hypothetical child result.
Fuel zero and dispatcher fuel one are explicit OutOfFuel endpoints; the latter
reaches helper fuel zero after the assumed actual stack shape. They do not
misclassify a zero-fuel helper as a completed denied call.

Allowance inequalities derive from actual Z and literal Ccallgas<=Ccall,
including the stipend, independently of StepOk, returned gas or a child count.
No error is assigned a returned world or gas field. No event aggregation or
protocol admission is claimed. The new adapter exposes the error child edge
needed by a later full nested-event certificate; it does not yet count that
child's events or compose their charge with the parent's continuation.

---

# Independent review: CreationOutcome

Verdict: CLEAN.

Complete frozen source reviewed at SHA256 `2f3acec9be4d3c26f425ff9e94d8bbbb4709ffee9b93527313e31ff22a541ed3`. `/tmp/eip-CreationOutcome-3.log` reports only propext, Classical.choice, Quot.sound for all four theorems. No edits or builds were performed.

select is the literal CREATE/CREATE2 child-result selection. Completed Lambda contributes the actual address, created set, world, gas, substate, Boolean status and output, replacing only those fields in the post-opcode-charge/incremented-counter state. EVERY Lambda error, including OutOfFuel and address-preimage errors, is caught identically: address0, literal empty account map, zero child gas, false status and empty output; other fields remain those of the charged parent state. It does not misdescribe this as restoring the parent world.

finish preserves the exact actual fields and order: result stack word tests child false status, depth equal1024, insufficient owner balance and init byte size >49152; returnData is empty on success and child output otherwise; the post-child guard uses UInt256 ADD before conversion to Nat. Active memory words use the charged parent's activeWords/off/len, final gas is UInt256.ofNat(chargedGasNat - L(chargedGasNat) + returnedGasNat), and the actual chosen child's state then receives those machine fields plus parent stack/PC replacement. No natural reinterpretation of the word guard or invented no-wrap premise occurs.

admitted_equation binds the FULL EVM.step(fuel+1) outcome, under real 3/4 stack layout and nonce/funds/depth/init-size gates, to settle of the SAME actual CreationGas.child at fuel. That child contains the actual owner nonce increment and Lambda environment, gas after opcode charge, original world, init memory and CREATE/CREATE2 salt distinction. Both child outcomes are split and definitionally matched to the literal source. No final StepOk or successful final guard is assumed. In particular fuel0 child remains visible and is caught, unlike CALL propagation.

denied_equation handles either nonce denial or funds/depth/size denial, retaining the same final guard. Its selected state is the charged parent, its returned gas is the actual allowance cast, and statusfalse forces stack0. No uncalled Lambda equation is a premise. The nonce-denied source's default address is definitionally0. The equation correctly does not assert that a denied raw step always succeeds: the literal word-add guard can still reject when its addition wraps.

finish_error_iff exactly states that finish errors iff its literal guard rejects and the error is OutOfGass. A caught child's error does not propagate as that error; it first becomes select's false result. The theorem applies to arbitrary Selected data as an algebraic helper, but admitted_equation binds actual use to the real child selection, so no arbitrary child poststate is introduced into an execution theorem. No claim is made that all child errors cause parent failure; typically zero returned gas lets settlement continue.

accepted_allowance_le derives allowance<=original pre-step gas from actual Z memory and opcode sufficiency. After opcode debit cannot underflow under those checks; L is bounded by that charged gas. No stack/child/parent result, returned-gas bound, funding ceiling or event-count assumption is required. This is the needed error-side budget inequality for a future child-event induction.

Scope is accurately limited to positive dispatcher fuel with explicit actual operand layout and admitted/denied gate split; dispatcher fuel0 and stack-underflow branches are not packaged here. The module is an exact outcome adapter, not an execution completion or gas-aggregation theorem. It preserves the pinned semantics' unusual CREATE catchall empty-world behavior and potential after-child word-guard rejection. Descendant trace retention and aggregate event charging still require composition; neither is silently claimed here. No blocking finding.

Read against both complete actual CREATE/CREATE2 dispatch branches, Step.stepPre, CreationGas.child/allowance/gates/stack/salt definitions and ActualAppendGas.accepted_gas. These dependencies remain unchanged from earlier clean reviews.

## Source bindings

- `Eip8282/Audit/Integrator/CreationOutcome.lean`: `2f3acec9be4d3c26f425ff9e94d8bbbb4709ffee9b93527313e31ff22a541ed3`
- `Eip8282/Audit/Integrator/CreationGas.lean`: `13aff91fba701884c09b25065ac1f8e7afaa849ce2b4c3b9e75abebed975feeb`
- `Eip8282/Audit/Integrator/ActualAppendGas.lean`: `79a04a7b1a092026b24e3dfc3b0adc9bffaaa17a473e76a3f8a5447e75a7ea0d`
- `.lake/packages/evmyul/EvmYul/EVM/Semantics.lean`: `8b49f1aee609ce888041ba9e7253bbe55d06fda136252bc46d4e006755110f4b`
- `.lake/packages/evmyul/EvmYul/EVM/Proof/Execution.lean`: `8c70c77f09ec1b867788afbf1ddb8b6927b4fc5fd1cf8fee40e965a67eff8af5`

---

# Independent review: RecursiveEventDebit

Verdict: CLEAN as explicit conditional induction-edge lemmas, NOT a universal event-count theorem.

Complete frozen source reviewed at SHA256 `5f2e5192fa26543e30eb470773417ebba0c57ed3a5947ec5a90a454ffd39a9b3`. `/tmp/eip-RecursiveEventDebit-1.log` reports only propext, Classical.choice, Quot.sound for all four theorems. Read-only; no edits or builds.

stepResidual, thetaResidual and lambdaResidual select the actual returned gas on completed results and accounting zero on errors. The tuple projections are correct, including the extra creation address. Neither Boolean false nor REVERT-derived completed tuples are replaced with zero: their actual gas is retained. The error-zero convention does not assert that raw OutOfFuel returns a gas field or always consumes all EVM gas.

call_charge's premise is attached to the SAME literal Theta child invoked by CALL at its actual smaller fuel, on entered(mid), with actual owner source, recipient/code target, actual/apparent value, calldata memory, permission and gas allowance. Actual Z starts at pre and returns mid. In the completed-parent branch, accepted_step_call_debit recovers the exact child tuple and rewrites that same expression in the IH. Child residual+charge<=allowance supplies returned<=allowance. The actual natural settlement then pays charge from allowance-returned, leaving net overhead and memory debit nonnegative. It does not add the full CALL opcode cost to descendant charges a second time.

family_charge repeats that argument using the existing literal variant childResult and allowance: CALLCODE has owner source/recipient and actual value; DELEGATECALL has caller source, owner recipient, zero actual value and inherited apparent value; STATICCALL has zero values and false permission. The exact child tuple from actual dispatch rewrites the IH, so there is no alternate-code or predicted-result substitution. Both parent and child completed status remain arbitrary.

For either CALL theorem, a parent error has residual0, and the IH implies charge<=allowance; actual Z independently proves allowance<=pre gas. This branch need not identify the particular error to prove the inequality. The separately reviewed all-outcome adapters are still required when a future trace extractor needs to retain and identify that error's actual child subtree. No parent StepOk is assumed by the theorem itself.

creation_charge binds the actual CreationGas.child at fuel with nonce-updated world and gas after opcode charge, retaining actual nonce/funds/depth/size admission. A completed parent with completed child uses its exact returned gas and allowance-returned debit. A completed parent that caught a child error (including OutOfFuel) uses the exact full-allowance debit; rewriting the SAME actual child expression turns the IH residual into0, so its charge is paid. A parent error, including the literal post-child word-guard rejection, is covered by residual0 and Z's independent allowance bound. There is no natural-guard replacement or successful-parent/child requirement. This theorem is deliberately weaker on errors and does not claim their result contains an actual remaining-gas endpoint.

uncharged_step is valid for EVERY accepted opcode and actual step outcome, using residual0 on errors and ReturnedGas on completed states. Its comment describes an intended no-child use, but the theorem does not establish that no child/event exists. Consumers must justify an uncharged branch from actual trace structure/denial/low fuel; using it to omit an executed child subtree would make a future event-count interpretation incomplete. This is a scope note, not a defect in the stated inequality.

The scalar charge is an arbitrary Nat with an explicit child residual+charge<=allowance hypothesis. The module neither binds it to a counted occurrence list nor derives that IH globally. It adds no hidden poststate, resource bound, supplied aggregate charge or funding requirement beyond that prominently stated induction hypothesis and actual local Z/stack/gates. A mutual all-outcome extraction/accounting proof still must instantiate charge with the child's real event count and combine distinct child/local/continuation events. This matches the source's explicit induction-edge status and avoids claiming universal event closure prematurely.

Reviewed complete current source and checked relevant exact child-debit API formulas and unchanged dependencies. CallOutcome was authored by this reviewer and independently reviewed CLEAN by root; its use is checked here without claiming independent authorship review of that dependency. No blocking finding.

## Source bindings

- `Eip8282/Audit/Integrator/RecursiveEventDebit.lean`: `5f2e5192fa26543e30eb470773417ebba0c57ed3a5947ec5a90a454ffd39a9b3`
- `Eip8282/Audit/Integrator/CallOutcome.lean`: `4db2f3e3c92cdc8f958a9f8d69efd9b5d9c627d8ad421c847e11d4af1886a956`
- `Eip8282/Audit/Integrator/CreationOutcome.lean`: `2f3acec9be4d3c26f425ff9e94d8bbbb4709ffee9b93527313e31ff22a541ed3`
- `Eip8282/Audit/Integrator/CallDispatchGas.lean`: `e1c5f79113ed283b4193bf6548adf7b91190a5b37183b00caf19a644460c6d4b`
- `Eip8282/Audit/Integrator/CallFamilyGas.lean`: `cae233fa8cbc8d8bd84c8ba00e48970c97a1abba03fe6987682d897e12a0e4b0`
- `Eip8282/Audit/Integrator/CallGasAccounting.lean`: `35fc0df6019b4de427b3a1fced13564fa41b9c3a7e16ac40b9a929f8391f78b1`
- `Eip8282/Audit/Integrator/CreationGas.lean`: `13aff91fba701884c09b25065ac1f8e7afaa849ce2b4c3b9e75abebed975feeb`
- `Eip8282/Audit/Integrator/ReturnedGas.lean`: `b39d7af6e35834bb6ecd3364fd1055768ae8e11712dc92d811312e4ffce9dde9`
