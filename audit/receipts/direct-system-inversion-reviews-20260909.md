# Independent reviews: initialization, SYSTEM and gas traces

# InitializedInvariant — independent source review

**Outcome: CLEAN for the conditional actual-creation initialization scope.**

Reviewed the complete `Eip8282/Audit/Integrator/InitializedInvariant.lean`, SHA-256
`2aac90df903d5f12e14c55821441940cfe25c15cbdd9d9bf503550c66f039382`, checked twice. Inspected the supplied `/tmp/eip-InitializedInvariant-final.log`; all four principal reports contain only standard axioms. Parent reports compilation exit 0. No rebuild or source edit in this review.

The source correctly uses an independently absent target in the **pre-deployment** world, not desired zero storage in the final world. `zero_of_absent` unfolds the actual defaulted account/storage observation. The deposit specialization obtains installed code, address and storage observations from the real successful Lambda result via `CreationSettlement.deposit_creation`, then derives every target slot is zero. Exit obtains the actual slot-zero latch and preservation of other slots from the corresponding Lambda theorem, then uses absence only for those unchanged slots.

`initial_invariant` combines the actual control observations with the separately proved initialization of `AccountedState.Bounded`, the explicit enabled-or-safe numerator predicate, and `QueueInvariant.represents_empty`. The zero-budget active sum is zero for deposit; INHIBITOR is handled by the allowed alternative for exit. The empty FIFO proof includes ordered zero pointers and the physical-window condition `4≤2^256`; its contents clause is appropriately vacuous because there are no records. `SourceWidth []` establishes only the width condition for that empty list, not authentication of a nonexistent record.

The installed account/code witness, storage facts, invariant and unchanged log series all concern the same world returned by the actual Lambda equality `hr`. There is no unrelated final state, assumed post-world agreement, replacement CREATE model, or use of a sufficient-constructor bound to silently assert successful code deposit. `hr` retains actual success, so the underlying settlement has already passed collision-selected execution and code-deposit checks. The explicit constructor code, permission where needed, resource and no-collision hypotheses remain visible.

Scope to preserve:

- Address identity is the exact symbolic Lambda-computed address. No canonical predeploy address, deployment transaction validity, CREATE/CREATE2 admission or success existence is established here.
- Pre-world target absence is stronger than mere zero control slots and is an explicit domain assumption. This does not cover every upgrade or reactivation scenario; those require their own initial-state argument.
- Deposit's theorem reports slot0=0 and the initialized predicates; exit reports slot0=INHIBITOR. The result does not assume or derive a global supply/funding ceiling.
- These are initial invariants. Induction over ordinary calls, ancestor rollback, inter-transaction processing, and protocol accounting remains separate.
- Existing source `CreationSettlement` is used as a reviewed dependency; this review does not claim an independent re-review of my own implementation of that module.

No blocking defect or scope overclaim found.

Relevant dependency hashes:

- `CreationSettlement.lean`: `d95b28f2a46daf588a2aaf15e8a8f77fc28b075116e5f2395360e73152383820`
- `AccountedState.lean`: `382a0419905acd948e36c7290e2b81f6d3641f712e4077bb471386340b7b54e7`
- `FundedDomain.lean`: `957cb3c9fa8951df7daf57bf0cb0fae883c4b01e7b514c0dee551edf773cd1d7`
- `QueueInvariant.lean`: `5e15726133885b59340a5ffc4d8650fe33d4cda27639039ad1fe92fe49de5219`

---

# Independent source review: ActualAppendGas

Verdict: CLEAN for actual supported-step/trace accounting and conditional whole-call LOG0 debit. Unconditional extraction of LogPath from successful append remains OPEN, explicitly documented in the source.

Reviewed source SHA256: 79a04a7b1a092026b24e3dfc3b0adc9bffaaa17a473e76a3f8a5447e75a7ea0d
File: Eip8282/Audit/Integrator/ActualAppendGas.lean
Compiler receipt examined: /tmp/eip-ActualAppendGas-local-compile.log; all printed closures use only propext, Classical.choice, Quot.sound. No proof edits or builds in this review.

Read the complete new module and relevant pinned EVMYulLean Gas.C', memoryExpansionCost, EVM.step, X, Proof.Execution.Z, XStepAt, XRuns, and the actual supported-opcode/SymExec.step_withGE definitions. Cross-checked the existing success inversion and codeCall/Theta result bridge, including fuel offsets and final published gas.

Findings:

- accepted_gas extracts both actual no-underflow guards: memory expansion first, then opcode cost computed on the memory-charged intermediate state. It does not substitute an upper estimate for the actual cost.
- step_gas restricts raw opcode execution to allOps. The enumerated blockOps plus individual effects exclude CALL, CALLCODE, STATICCALL, DELEGATECALL, CREATE, CREATE2 and SELFDESTRUCT. These restrictions prevent child-frame returned gas from invalidating monotonic debit. The raw supported operation preserves gas, while EVM.step performs the real subtraction.
- accepted_step_debit uses the guards to translate word subtraction into exact natural subtraction, including both memory and opcode charges. No wraparound or saturating-subtraction inference is silently assumed.
- LOG0 costs are read from the actual second stack operand, whose equality survives Z. The bounds 919=375+8*68 and 1847=375+8*184 are correct; memory expansion is additional and only strengthens the inequalities.
- Supported trace labels are not arbitrary annotations: XRuns.cons records decodeAt of its actual pre-state and actual gasCost from XStepAt. xruns_debit therefore telescopes real accepted steps. It deliberately omits memory charges from opcodeCharges, yielding a sound lower bound.
- trace_log_debit joins one real LOG0 step between real supported prefix/suffix traces with matching states and fuel indices. It assumes neither predicted gas consumption nor desired final gas.
- The trace suffix stops before its halting instruction. success_final_step_debit separately inverts and charges that actual instruction. Halting membership eliminates a nonhalting continuation, and the returned final state is the executed post-state. Thus STOP/RETURN charging is not dropped at the boundary; REVERT cannot become a successful result.
- LogPath contains actual XRuns/XStepAt witnesses plus explicit support and a final supported halt. It does not by itself assert successful evaluation, and xi_log_debit correctly supplies and transports actual success through those traces before invoking the halt lemma. Its remaining witness premise is material and is correctly acknowledged.
- xi_log_debit identifies final gas from the actual Xi published tuple, not from a desired endpoint state. theta_log_debit gets exactly the same gas from CallSuccess.codeCall_of_success, including the real empty-world settlement branch. Positive fuel is derived from success. There is no sufficient-gas, completion or gas-output premise.

Remaining scope boundaries: LogPath extraction, aggregate transaction/nested-frame accounting, refunds, funding/balance/supply justification and protocol-history budget bounds. A local opcode lower bound is not by itself a transaction-wide append-count bound.

## Concrete next decomposition for LogPath extraction

Use a NEW module and preserve the frozen inversion foundations. Reuse existing generated code/shape lemmas and actual success; do not prove resource sufficiency or infer traces from final-state equality.

1. Add a supported-segment wrapper containing actual XRuns plus Supported and the same successful continuation. Prove empty/one-step/concatenation constructors using XRuns.refl/cons/trans and support under list append. This is packaging of existing semantics, not a new execution relation.
2. Add trace-preserving adapters for a checked symBlock, taken/untaken JUMPI and supported effect. The current success_symBlock proof discards XStepAt after establishing the continuation, so it cannot alone supply a trace. Replay its short induction with success_continue; retain the Z, StepOk and H=none witnesses before rewriting the actual post-state to withGE shaped. Each block operation gets support from guardOk -> blockOps -> allOps. Effect support is a concrete membership proof. Keeping the segment abstraction opaque will avoid giant appended-state elaboration costs.
3. Establish the trace-preserving 24-instruction nonzero fee cycle, then fee-head-to-exit by strong induction on actual successful fuel, exactly as AdmissionInversion.fee_exit. Retain the concatenated supported segment at each induction step. The zero-accumulator branch executes the checked head block and taken exit JUMPI. No completed recurrence or iteration cap is assumed.
4. Replay user-entry-to-fee-head with supported segments, using the already proved nonINH/admission facts to discharge failing branches. Compose with the fee-exit segment and the size/payment checks. Exit reaches PC165; deposit reaches PC205. Require only actual successful nonSYSTEM Xi and exact48/184 input (or derive exact size from admission for nonempty calldata under calldata-fit).
5. Trace the successful append suffix to the LOG0 pre-state using the current AppendInversion instruction sequence. Exit: blocks165/174/187/194/202/208/214 and effects SSTORE173/186/193/201, MSTORE207, COPY213, arriving at PC217 with length68. Deposit: blocks205/214/228/236/244/252/260/268/273 and SSTORE213/227/235/243/251/259/267, COPY272, arriving at PC276 with length184. Derive the actual LOG0 XStepAt using success_continue, retaining its cost; no gas lower bound is needed.
6. Trace from afterLog to the final STOP pre-state. Exit block218, SSTORE223, STOP224. Deposit block277, SSTORE282, STOP283. These give afterTrace support and the actual final decode/Halting facts. Keep STOP outside XRuns, as required by LogPath and success_final_step_debit.
7. Concatenate entry, fee-loop, admission and pre-LOG segments; package the middle LOG0 and post-LOG suffix as LogPath. Then existing xi_log_debit/theta_log_debit immediately discharge unconditional local append debit. Owner, storage capacity, receipt post-state and mathematical fee safety are unnecessary premises for this gas-path extraction.

A broad theorem asserting all arbitrary byte offsets decode to supported opcodes would be wrong: PUSH data are not instruction boundaries. Following checked sites and actual jumps avoids that trap.

---

# Independent root review: SystemInversion.lean

CLEAN. Frozen SHA256 79a7f947800d665fcae8aec7cfac978e54f500233e1c84436bb6af2e3f49bba5.

Read the complete module in two passes (including both concrete loop bodies) and the previously reviewed actual-success step/block/effect/RETURN adapters and SystemSpec storage interpretation. Each prefix follows the real caller branch and cap selection, preserving the SAME final/out in its continuation. No system_returns or better-resourced execution is substituted.

The loop induction counts remaining records. Its actual cap bounds (16/64) prove index representation and inequality before each iteration; the terminal equality follows ofNat_toNat, independently of evaluator fuel. All input storage touches are represented by Touched; this preserves storage, code/environment and the values used by writeItem/drainMem. Exit's three MSTOREs and deposit's six MSTOREs plus eight descending MSTORE8 instructions use actual step effects, including memory expansion. The bodies return the same actual successful continuation at the next loop head.

Full versus partial head stores are inverted from the actual comparison. The control path checks nonempty calldata before inhibited/unlock and the wrapped count+excess fold. It retains exact word semantics; no natural sum bound is silently used. Both final SSTOREs and RETURN are followed, deriving the shared state and real selected return bytes. Actual Ξ publication fixes the exact world, created accounts, substate, gas and output witnesses.

The operational state-result parents need only actual Ξ success and SYSTEM caller. The independent all-slot parents additionally require an input owner because upstream SSTORE on a missing owner is not a genuine update. SystemSpec.system_storage uses the real touched/head/control witnesses to derive the independent map universally, including every stale record slot. No post-world equality is supplied as an input. Natural FIFO interpretation/order/source width, Θ settlement and protocol histories remain separate.

Inspected /tmp/eip-SystemInversion-7.log: warning-free reported compile exit0, all printed theorems standard Lean axioms. No proof changes by reviewer. Exact-commit integration check follows separately.

---
