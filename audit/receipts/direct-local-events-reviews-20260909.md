# Linked funding histories and local event certificate reviews

These are frame-local and linked-history results; nested aggregation and
protocol extraction remain open.

## Frozen source bindings

- `Eip8282/Audit/Integrator/FundingHistory.lean`: `67008d4534dcc5893ed9a30213c3ad54cbb5e09aef1dc0e81b5ffb4c047703b1`
- `Eip8282/Audit/Integrator/FrameEvents.lean`: `d5f2ff9126b3a054f5f63b71d4dbaf9a2d79070ec6a7ac80ddd2a54963c32f66`
- `Eip8282/Audit/Integrator/AppendEvents.lean`: `227ac63c9d323bac1a1b3e9e396738d982a6bc71e5e2a7ea2742fbe011ed9d83`

---

# Independent review: FundingHistory

Verdict: CLEAN.

Reviewed complete frozen `Eip8282/Audit/Integrator/FundingHistory.lean`, SHA256 `67008d4534dcc5893ed9a30213c3ad54cbb5e09aef1dc0e81b5ffb4c047703b1`. `/tmp/eip-FundingHistory-2.log` reports only propext, Classical.choice, Quot.sound for all seven printed projections. No edits or builds were performed.

The Step constructors bind literal operations and input conditions: an actual Υ result with TransactionFunding.Admission, an actual code-Θ result with SYSTEM caller and zero actual value, or a literal AccountMap.increaseBalance credit. They do not carry a desired post-balance, post-budget, conservation proposition or supplied execution summary. Both Boolean statuses are admitted. The system constructor restricts caller even though the underlying zero-value funding theorem is stronger and does not need that identity; this is harmless scope restriction. It permits arbitrary code/apparent value, correctly because conservation depends on real transfer value and actual execution. No audited-code pin or canonical predeploy provenance is claimed by it.

step_funds applies actual transaction conservation, derives the zero-value Theta fundedness premise, or bounds the actual credit by amount.toNat. Trace links each next operation's exact input and output world to the prior one. Its index sums actual explicit credit amounts as naturals, rather than stipulating a supply bound. The induction correctly yields funds(world) <= funds(initial) + credits; credits need not equal net funds minted when word additions overflow. This upper-bound treatment is safe.

balance_budget uses the actual finite-map individual-balance bound. message_value_lt additionally requires actual transferred value to be funded by the real pre-call sender; the total ceiling is imposed on initial funds plus accumulated credits, not on a desired final world. transaction_value_lt derives the value comparison from the actual pre-admission fee-and-value condition and actual sender lookup. message_entry_budget composes actual credit-then-debit Theta entry conservation with the history bound; missing/alias account cases are covered by the already reviewed TransferFunding result.

xruns_funds is about an actual existing XRuns prefix. Every cons contains the actual Z equation and actual StepOk, and ExecutionFunding.step_funds includes all recursive opcodes and either completed child status. The transitivity direction is correct. Neither eventual enclosing success nor an eventual result is needed. prefix_owner_budget then bounds the encountered owner by the actual frame's initial world funds. These statements include prefixes before later rollback/errors; they do NOT assert an unreturned state after an error, and do NOT claim arbitrary raw nested entry worlds are already linked to the top-level history.

Scope is accurately documented: this is an inductive collection of linked actual receipts and explicit credit operations, not a new operational EVM or an extraction theorem for the complete protocol. No provenance or consensus rules for the credit constructor are assumed/proved. Actual genesis bounds, issuance/withdrawal mapping, transaction validation implying Admission, and the initial-plus-credit ceiling must still be supplied independently. The module imports FundingBounds but does not pretend its conditional arithmetic establishes that provenance. Likewise, deriving every encountered nested message context and its real funding gate from a whole evaluator trace remains separate. Actual vs apparent value must be connected where a later CALLVALUE consumer needs that equality.

Dependencies TransactionFunding, ExecutionFunding and FinalizationFunding are unchanged from the independent CLEAN reviews. XRuns/XStepAt definitions and actual accepted-step interpretation were checked alongside this review; the no-later-outcome claim matches their nonhalting-prefix relation. There is no fixed iteration cutoff, native decision proof, extra axiom, or circular postcondition premise.

## Source bindings

- `Eip8282/Audit/Integrator/FundingHistory.lean`: `67008d4534dcc5893ed9a30213c3ad54cbb5e09aef1dc0e81b5ffb4c047703b1`
- `Eip8282/Audit/Integrator/TransactionFunding.lean`: `dff074ffa97b3c17862496c3cd92bfb50611c7f19796c79ad95a469778508f2f`
- `Eip8282/Audit/Integrator/ExecutionFunding.lean`: `faa5fd66ac0daa24770a2dd4608cf8729721166a7636ccd8ac27ed88fc8b7d5b`
- `Eip8282/Audit/Integrator/FinalizationFunding.lean`: `e63683924b7f7ba1fdacd84c8c9cf76d3d770b3fc64e5e468ce9aa594a56bcb0`
- `Eip8282/Audit/Integrator/TransferFunding.lean`: `b8d8286170495a4a59d0f61ad19e0354e624ea3a0c0e0f48bd24e92ea7871766`
- `Eip8282/Audit/Integrator/FundingBounds.lean`: `32f80b6277840cd0ac76bf355423eb2fb2d539a879bd8f4cd4508add3b4703f9`
- `Eip8282/Audit/Integrator/FundedDomain.lean`: `957cb3c9fa8951df7daf57bf0cb0fae883c4b01e7b514c0dee551edf773cd1d7`
- `.lake/packages/evmyul/EvmYul/EVM/Proof/Execution.lean`: `8c70c77f09ec1b867788afbf1ddb8b6927b4fc5fd1cf8fee40e965a67eff8af5`

---

# Independent review: FrameEvents

Verdict: CLEAN for explicitly SINGLE-FRAME event accounting.

Complete source reviewed at SHA256 `d5f2ff9126b3a054f5f63b71d4dbaf9a2d79070ec6a7ac80ddd2a54963c32f66`. `/tmp/eip-FrameEvents-7.log` reports only propext, Classical.choice, Quot.sound for all nine printed projections. No edits/builds or new proof assumptions were made.

Trace is indexed by the exact original X inputs, fuel, actual Except result and local event list. Its six cases match literal X: zero fuel, actual Z rejection, actual step error, nonhalting continuation, normal halt, REVERT. Every executable step is tied to actual Z and Step equations. sound uses the matching actual evaluator unfold lemmas. extract exhausts precisely those branches at the actual fuel; it neither assumes eventual success nor restarts at a larger budget. Step/StepOk are the literal graph of EVM.step, not an alternate instruction relation.

Marked reads actual decoded LOG0 and the second stack operand >=68. emit is computed from that predicate and occurs only after actual StepOk. Thus no rejected LOG is counted. Actual LOG0 dispatch returns its logged state atomically after successful pop2; it has no subsequent error branch that would hide an executed local log. On recursive step error, descendants may already have executed logs, but stepError's empty list is correct ONLY because this module explicitly counts the current frame, not descendants. Earlier current-frame events are retained by preceding next constructors, even when the tail ends in OutOfFuel, exceptional halt or REVERT. Inherited entry log contents and final journal contents are not counted.

step_debit derives stack availability from actual Z, cost =375+8*len from accepted_log_cost, and the natural opcode-plus-memory debit from OrdinaryGas.accepted_step_debit. The >=919 bound is derived from len>=68, not supplied. For all unmarked instructions, including recursive ones and their false-status outcomes, the already reviewed ReturnedGas.step_remaining proves actual post gas nonincrease. Halting/revert emit cases are harmless generality (their true halting opcode is not LOG0). gas_bound telescopes those real local debits and includes actual returned gas for completed success/REVERT. For errors, residual=0 is expressly only an accounting definition: it invents neither a returned endpoint nor a claim that raw OutOfFuel spends all EVM gas. Error base cases contain no local event at the failing step, and preceding events still satisfy the bound.

Occurrences are labelled by remaining fuel at that local instruction, so occurrence_lt and distinct correctly derive strict descent and Nodup. These IDs are frame-local: siblings/nested frames may reuse them. deterministic compares certificates even across different result indices; deterministic Z, Step and H force compatible constructor cases and identical next states, then the induction fixes the entire event list. There is no free event-selection field or constructor that can skip a qualifying successful local instruction.

prepend replays each actual XRuns prefix step with Trace.next and composes the computed event prefixes. contains_site extracts the actual continuation after the supplied real XStepAt, prepends the actual prefix, and uses deterministic to identify that reconstructed list with the GIVEN certificate's list. It does not assume the site's continuation succeeds, nor swap executions/fuel. Although the intermediate certificate has its own syntactic result index, sound/determinism tie it to the same actual X run. The same-certificate occurrence claim is therefore sound.

extracted_bound gives an actual all-outcome certificate, local Nodup and derived local gas bound with no supplied trace, gas bound or poststate. The count is a conservative superset of qualifying local LOG0 sites, not yet a count of authentic successful append calls. Child event extraction/retention, global call-path distinctness, nested gas aggregation and transaction/block event accounting remain OPEN and are explicitly excluded. In particular, current stepError must not be reused unchanged as the terminal constructor of a future descendant-counting trace.

Read alongside: literal X, actual graph Step/StepOk, all six X unfold helpers, XRuns/XStepAt, actual LOG0 dispatch, accepted_log_cost, OrdinaryGas's exact debit, and ReturnedGas's completed-step bound. Dependencies retain prior reviewed hashes. No blocking finding.

## Source bindings

- `Eip8282/Audit/Integrator/FrameEvents.lean`: `d5f2ff9126b3a054f5f63b71d4dbaf9a2d79070ec6a7ac80ddd2a54963c32f66`
- `Eip8282/Audit/Integrator/ReturnedGas.lean`: `b39d7af6e35834bb6ecd3364fd1055768ae8e11712dc92d811312e4ffce9dde9`
- `Eip8282/Audit/Integrator/OrdinaryGas.lean`: `d41661f413814579343e04a37da8cb87624881f63ac132440077beb8dc0adfd4`
- `Eip8282/Audit/Integrator/ActualAppendGas.lean`: `79a04a7b1a092026b24e3dfc3b0adc9bffaaa17a473e76a3f8a5447e75a7ea0d`
- `.lake/packages/evmyul/EvmYul/EVM/Semantics.lean`: `8b49f1aee609ce888041ba9e7253bbe55d06fda136252bc46d4e006755110f4b`
- `.lake/packages/evmyul/EvmYul/EVM/Proof/Execution.lean`: `8c70c77f09ec1b867788afbf1ddb8b6927b4fc5fd1cf8fee40e965a67eff8af5`

---

# Independent review: AppendEvents

Verdict: CLEAN for local audited-site membership in the same actual frame certificate.

Complete source reviewed at SHA256 `227ac63c9d323bac1a1b3e9e396738d982a6bc71e5e2a7ea2742fbe011ed9d83`. `/tmp/eip-AppendEvents-1.log` reports only propext, Classical.choice, Quot.sound for all four printed theorems. Read-only; no edits/builds.

path_occurrence unpacks the actual LogPath prefix from q.entry at q.fuel and the actual LOG0 XStepAt at fLog. Its Marked proof uses the very same decode and stack-length operand plus len>=68. FrameEvents.contains_site places fLog in EVERY certificate of that same q.entry/q.fuel/jump table, even when the certificate has an independently written result index. FrameEvents.deterministic ties these indices' traces to the same execution. It cannot satisfy membership with an unrelated larger-fuel run or an arbitrary event list.

exit_occurrence and deposit_occurrence derive LogPath from the existing arbitrary-success bytecode path theorems, with non-SYSTEM source and exact natural calldata size48/184. XiCall's only intrinsic constraint is its actual executed code pin; its result is Xi(q.fuel+1), whose actual X starts at q.fuel and q.entry. Thus the wrapper's fuel/table binding is correct. The LOG lengths are the correct68/184, and no fee completion, gas sufficiency, storage invariant, predicted state or assumed path is a premise of these wrappers.

successful_events obtains the event list/certificate/Nodup/gas bound by universal extraction, then adds a witness of membership using the actual successful Xi receipt. Its conclusion remains about the actual X residual and q.entry gas, and is appropriately weaker than an explicitly rewritten Xi-gas result. It asserts at least one matching occurrence exists; it does not claim that the entire generic list contains exactly one event or that distinct call frames already have globally distinct IDs.

The source's description as a local injection edge is acceptable: it establishes a concrete actual-site-to-list membership, not yet a global injection on call nodes. That final injection, descendant event extraction/aggregation and a transaction count bound remain separate. No Θ settlement, world/log authentication or protocol-reachability result is newly claimed by this file; those existing proofs are not silently substituted by this wrapper. No blocking finding.

## Source bindings

- `Eip8282/Audit/Integrator/AppendEvents.lean`: `227ac63c9d323bac1a1b3e9e396738d982a6bc71e5e2a7ea2742fbe011ed9d83`
- `Eip8282/Audit/Integrator/FrameEvents.lean`: `d5f2ff9126b3a054f5f63b71d4dbaf9a2d79070ec6a7ac80ddd2a54963c32f66`
- `Eip8282/Audit/Integrator/AppendGasPath.lean`: `4ae4dfb5b97ede8a12f108dc79ba45c4e041936b554772cbefb8c5539074c366`
- `Eip8282/Audit/Integrator/ActualAppendGas.lean`: `79a04a7b1a092026b24e3dfc3b0adc9bffaaa17a473e76a3f8a5447e75a7ea0d`
- `Eip8282/Audit/XiTransport.lean`: `0bfa4d4fbf34dfc6ee0e85725d113c3954a4dc9ecaa3ad7b653ad1a74eb66b8b`
