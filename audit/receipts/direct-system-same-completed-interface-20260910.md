# Same-Completed reference SYSTEM composition

Source-only API recommendation, 2026-09-10. No compilation or new equivalence claim.

Use a generic consumer **taking one `h : SystemExecutionResources.Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes c.fuel c.entry`**. Preserve that Type-valued `h` in the result, rather than independently extracting two Completed witnesses and trying to equate their traces.

## Inputs and derivation

Inputs beyond `h`: initial `parent : ReferenceStorageView.Parent`, `tx : ReferenceStorageView.Tx`, `slots : ReferenceStorageView.Related parent tx c.entry.toState`, `owner : SystemSpec.HasOwner c.entry.toState`, `permission : c.env.perm = true`, `cdfit : c.env.calldata.size < UInt256.size`, `outputFit : outputBytes <= 32*cap`, and `host : 32*cap < 2^System.Platform.numBits`. Runtime initial At is derived from `c.code_pinned` and the image entry-site lemma by cases on kind.

1. `ReferenceRuntimeView.initial_related c parent tx slots owner` supplies `Related parent (initial c tx) c.entry` (empty stack and coherent empty memory are derived).
2. `ReferenceSystemTrace.from_runs h.run hat (initial c tx) related ha permission cdfit h.exit_capacity host` supplies a finish view and `Viewed` on **h.trace**, **h.rem+2**, **h.exitState**; `ha` is the restriction of `h.allowed` to the prefix operations. There is no per-edge capacity certificate input.
3. `SystemMemoryResources.attach h hat outputFit` supplies actual terminal `h.finalState.activeWords <= cap` as well as full memory cost, using h.output_operands and h.terminal. This is needed because h.exit_capacity alone is pre-RETURN capacity.
4. `ReferenceReturnView.halted h.halt.charge h.terminal finishRelated finalCapacity host h.returned` supplies exact terminal Result and `h.output = output finish off len`. Use `ReferenceReturnSlice.output_eq_extract finishRelated off len` to publish the literal eager-memory unpadded output slice. No terminal PC equality. If useful retain h.halt.decode plus actual decoder matching at h.at_exit; decode_matches itself requires nonhalting, so do not apply it to RETURN. Instead use actual site membership (RETURN rules EOF out) and the finite decoder equality directly.
5. `SystemMeterResources.pay_completed inputs h hat outputFit initialMeter executionBound reservoirBound` supplies PricedTrace on that very same h.trace plus literal terminal event, and sequential payment. Or accept `Paid inputs h systemMeter` already produced by a wrapper. Inputs is universal reading data; payment does not prove those readings equal the corresponding source storage view or actual source warmth/original state.

Suggested result package: same `h`, `Paid inputs h meter`, initial/finish view and exact Viewed trace, terminal Result, output slice equality, and h.success retained verbatim. Trace event/read-state alignment is indexed by actual states; a further coupling predicate between `Inputs pre` and the evolving source view is still needed before calling this a reference execution.

## Concrete wrappers without duplicate executions

`SystemMeterResources.deposit inputs c system permission gas fuel` returns `exists h : Completed RuntimeExecutionScope.deposit 8500 400 11776 c.fuel c.entry, Paid inputs h systemMeter`, assuming `Deposit.callerWord c = sysW`, permission, gas exactly UInt256.ofNat 30000000, fuel >=8502. Exit gives steps800/cap40/output1088/fuel>=802 with `Exit.callerWord`. Destructure once, run the generic view consumer on that h, retain Paid. Discharge outputFit and host by kernel arithmetic (both supported host widths). Initial current-slot correspondence, owner existence and cdfit remain explicit; default empty calldata discharges cdfit definitionally. These constructors require no queue invariant and work through inhibition, but this is still pinned execution plus source-shaped actions/payment.

## Same endpoint to existing guarantees

`EndpointState.result_of_X_success c hX` publishes the **full** Xi result `(h.finalState.createdAccounts, h.finalState.accountMap, h.finalState.gasAvailable, h.finalState.substate)` and h.output. Rewrite h.success jumpdest table by the existing Deposit/Exit table identity; do not use XiCall.observe_result, which forgets world/log fields. XiCall.result wraps X with fuel c.fuel+1.

For an actual message context C, choose c=`CallBridge.codeCall C codeEq steps`, with C.fuel=steps+1. `CallBridge.execution_eq_codeCall` binds the actual transfer-entry world. `CallBridge.commits_endpoint` consumes that exact Xi endpoint and the nonempty-world boolean. Derive nonempty from the terminal Result owner (and its environment relation) using `WorldNonempty.beq_empty_false_of_get_some`, rather than assume it. This produces the same actual Theta receipt; initial code-installed/funding/transfer/context binding remains outside the view theorem.

Construct `ReachableCalls.Transition` for that same receipt and use `JournalGuarantees.completed t initialInvariant budgetBound calldataFit`: it derives a physical queue and all three Submit/Drain/Control observations on the same receipt. `SystemJournal.preserves` additionally needs SYSTEM caller, zero actual value, calldata fit, budget<2^128 and initial invariant. Existing `ProtocolSystemCalls.guarantees` packages these from a separately constructed progress receipt; do not substitute it for same-h composition unless actual receipt equalities are explicitly identified. Its call uses canonical pinned target/code, 30M, default substate, zero value, originalWorld=world and fuel>=8503; reference scheduling and context extraction remain open.

No canonical deployment, history invariant, reference dispatcher execution, checked state representation, source readings, BLS/admission or fork adoption is discharged by this composition.
