# Reviews: actual call-family funding/gas and same-predicate Theta drain mutants

# Independent review: CallFamilyGas

Verdict: **CLEAN within the stated local gas-settlement scope.** No incorrect dispatcher layout, stipend input, recipient/target conflation, or assumed child result found.

Exact frozen source SHA-256: `cae233fa8cbc8d8bd84c8ba00e48970c97a1abba03fe6987682d897e12a0e4b0` (`Eip8282/Audit/Integrator/CallFamilyGas.lean`), matching assignment.

Entire candidate and its CallDispatchGas/CallGasAccounting dependency sources read, alongside actual EVM.step/EVM.call/Θ layouts, C'/Ccallgas/Ccall/Cextra and CALL-family memoryExpansionCost branches. No edits or builds. `/tmp/eip-CallFamilyGas-final.log` inspected: all eight expected axiom reports, standard propext/Classical.choice/Quot.sound only (address_word only propext), no errors/warnings.

## Dispatcher and actual child

Variant is only a finite selection of literal pinned argument layouts. Its definitions match EVM.step:

| Variant | Stack operands | Child source | Storage recipient | Code target | Actual / apparent value | Permission |
|---|---|---|---|---|---|---|
| CALLCODE | gas,target,value,inOff,inLen,outOff,outLen | current codeOwner | current codeOwner | stack target | operand / operand | inherited |
| DELEGATECALL | gas,target,inOff,inLen,outOff,outLen | previous executionEnv.source | current codeOwner | stack target | zero / inherited weiValue | inherited |
| STATICCALL | gas,target,inOff,inLen,outOff,outLen | current codeOwner | stack target | stack target | zero / zero | false |

The shared `value` argument is deliberately unused for both six-operand variants, in stack construction, transfer, apparent value, gas cost and gate. DELEGATECALL does not invent a value operand from its input offset, and its inherited apparent value does not produce a stipend or funding gate.

`step_helper` unfolds the actual StepOk and EVM.step, derives pop7/pop6 from the given actual stack, and identifies both the helper result and final stack/PC update. `entered pre` is exactly the execLength increment made by the real dispatcher. The fuel offsets are correct: step(fuel+2) dispatches call(fuel+1), which invokes Θ(fuel). The instruction-count change affects none of the gas, environment, account, memory or substate fields used by the child helper.

`childResult` is the literal child Θ call via CallGasAccounting.child, not a predicted result relation. It keeps original world, created accounts, block context and origin; converts source/recipient/code target to actual addresses; warms the code target in the child's input substate; selects code/precompile from toExecute at the code target; passes the actual input-memory slice and depth+1. The input slice is unchanged by the helper's gas subtraction. `address_word` correctly round-trips inherent160-bit addresses, so C' using codeOwner and dispatch using ofNat(codeOwner) refer to the same account.

`step_child_gas` derives the existential child tuple by case analysis of the actual helper/Θ result. Both child true and false statuses are retained. An Except error cannot inhabit the supplied successful StepOk branch; no invented completed child result is inserted in that case. Replacing the final stack and PC leaves the actual settled gas unchanged.

## Accepted charge, memory and stipend

The actual C' branches charge Ccall with exactly the same converted code target, recipient, requested gas and actual value as the dispatcher. For CALLCODE and DELEGATECALL the recipient is codeOwner, not the code target; STATICCALL uses the target for both. `accepted_cost` obtains cost=C' mid from real Z and uses Z's preserved stack; it is not an independent cost premise.

The helper computes Ccallgas from its input state **before** subtracting gasCost, matching allowance on mid. Access cost is likewise computed before adding the target to the child-access substate. The initial Z memory debit is separately included as `memoryExpansionCost pre (opcode kind)`. Actual Gas.lean uses stack3/4 and5/6 for CALLCODE memory ranges, and2/3 and4/5 for DELEGATECALL/STATICCALL, matching their stack constructors. The proof keeps that actual expression rather than supplying a hand-computed memory-cost bound.

Ccallgas is Cgascap plus stipend; Ccall is Cgascap plus Cextra. The reused proof establishes stipend≤Cextra from actual transferred value and Gcallstipend2300≤Gcallvalue9000. Therefore allowance≤accepted opcode cost≤mid gas<2^256. `accepted_forwarded_fit` derives the complete stipend-inclusive word fit before assuming anything about the child. It does not substitute the requested gas for the capped allowance.

For an actual completed child and the explicitly supplied local condition returnedGas≤allowance, settlement_nat proves both subtraction and addition cannot wrap. The exported natural identity is exactly:

```
post gas + (allowance - child returned gas)
         + (Cextra - stipend) + pre-op memory cost = pre-op gas.
```

Subtracting stipend from overhead is necessary: the stipend is already included in child allowance. It is not charged a second time. The condition is expressed against the exact recovered child tuple. No aggregate child-debit bound or global gas monotonicity is hidden in this statement.

## Denied branch

The gate matches the actual helper: actual transferred value≤current codeOwner balance (zero for absent owner) and depth<1024. For DELEGATECALL/STATICCALL the value comparison is automatically satisfied, including absent accounts; denial can only arise from depth. For CALLCODE it checks the current executing account, not the external code target.

When this gate is false, the actual helper invokes no child, chooses false status, and credits back Ccallgas. `step_denied_gas` proves the real final zero stack result and exact word-gas equation. `accepted_denied_debit` supplies the returned-allowance bound by reflexivity after the derived word-fit lemma, so it assumes no child result or child monotonicity. Its natural debit is memory cost plus Cextra minus stipend. That is the pinned helper's behavior, including the value-carrying stipend in the refund; it is not an independently asserted protocol rule.

The return-data memory write and active-word update do not create an additional gas debit after Z in this pinned implementation. The helper gas projection is obtained by unfolding those actual updates, and the dispatch's stack/PC replacement does not change it.

## Scope

These are local accepted-Z/StepOk projections for three CALL-family variants, complementing the separate CALL module. They do not prove that an arbitrary enclosing bytecode reaches these instructions, that every child completes, or that every child returns no more than its allowance. That last condition remains explicit only on the entered-child natural debit theorem; denied dispatch requires no such condition. Recursive child accounting, CREATE/CREATE2, precompile monotonicity, ancestor failures/rollbacks and total transaction/block event accounting remain separate obligations. No native evaluation, new axiom, post-state agreement or alternate execution model is introduced.

Dependency SHA-256 bindings:
- CallDispatchGas: `e1c5f79113ed283b4193bf6548adf7b91190a5b37183b00caf19a644460c6d4b`
- CallGasAccounting: `35fc0df6019b4de427b3a1fced13564fa41b9c3a7e16ac40b9a929f8391f78b1`
- ActualAppendGas: `79a04a7b1a092026b24e3dfc3b0adc9bffaaa17a473e76a3f8a5447e75a7ea0d`
- pinned EVM/Gas.lean: `9f06caccf5cc8f27f7822392cd1963c8353eb816052f4596321a12c2da707436`
- pinned EVM/Semantics.lean: `8b49f1aee609ce888041ba9e7253bbe55d06fda136252bc46d4e006755110f4b`

No changes requested.

---

# Independent review: CallFunding

Verdict: **CLEAN for funding and natural-total nonincrease at the actual child entry transfer.** No circular funds premise or overclaim about the child's published post-world found.

Exact frozen source SHA-256: `d5429791c3baf878e2fa0ea041d8bb00604b39f97bb5e23cfd25ad75c5aed9f2`, matching assignment (`Eip8282/Audit/Integrator/CallFunding.lean`). Entire source read; actual context/helper binding checked against AuditedChildGas and the previously reviewed CallFamilyGas, CallDispatchGas and TransferFunding implementations. No edits or builds. `/tmp/eip-CallFunding-local-compile.log` contains all ten expected axiom reports, only propext/Classical.choice/Quot.sound, no errors/warnings.

## Funding inequality

`gate_to_nat` reads exactly the account tested by the word-order gate. Both absent and present cases convert the same word balance into worldBalance's natural observation; absence is zero on both sides. UInt256's unsigned order makes the comparison its toNat comparison without an overflow conversion.

For ordinary CALL, AuditedChildGas.source is the dispatcher's ofNat(codeOwner) converted back to AccountAddress. `call_source` uses the inherent160-bit address round-trip proof, so the child caller is exactly the account whose balance was checked. The context's actual value is the stack value, and its world is the pre-helper account map. Consequently `call_funded` supplies TransferFunding's exact **pre-transfer sender-balance** hypothesis; it does not use a recipient balance, inherited CALLVALUE or a post-transfer balance.

For CALLCODE, the same codeOwner/source round-trip binds the checked account to the child caller; recipient is also codeOwner, independently of the external code target. TransferFunding covers the resulting self-transfer through its exact credit-then-debit alias reasoning.

DELEGATECALL and STATICCALL transfer actual zero. Their sender-balance requirement therefore follows from Nat.zero_le even if the child caller is absent or different from the account inspected by the raw helper gate. DELEGATECALL preserves the prior executionEnv.source as child caller and the inherited weiValue as **apparent** value; that apparent value never becomes transferred value or a funding amount. STATICCALL uses current codeOwner as source and zero for both values.

In particular, these funding results do not prove ordinary-value equality for DELEGATECALL. A consumer needing apparentValue=value must still distinguish that variant. The ignored extra `value` parameter on six-operand variants does not affect transfer, allowance or context fields through CallFamilyGas definitions.

## Context and actual result binding

`familyContext` uses the actual pre-helper account map and original transaction map, actual created accounts/block environment, target-warmed substate, correct source and origin, separate recipient/code-target selection, actual Ccallgas allowance, actual input memory slice, depth+1 and variant permission. STATICCALL forces permission false; the other variants inherit it.

`family_context_result` unfolds the same literal child Θ from CallGasAccounting. The only transformed machine state is `entered pre`, whose execLength increment changes none of those Θ inputs. Positive child fuel is required exactly to justify `(fuel-1)+1=fuel` when converting to MessageCall.Context.result. The explicit `toExecute ... = .Code code` premise binds the parameter bytecode to actual selection at the code target; it is not an impossible original-runtime pin or an arbitrary replacement code. Precompile cases are intentionally excluded from this context equality.

The isolated `family_entry_funds_le`/budget statements do not need positive fuel or code-selection premises because they concern only the syntactically selected context's transfer, independent of whether it is invoked. The actual-step wrappers close that invocation boundary: they recover the real child tuple from StepOk and the admitted gate, derive positive child fuel from the impossibility of Θ0 completing, then transport that same tuple through context_result. No predicted child result or gas-sufficiency premise is inserted.

`call_step_entry` correctly performs the same composition for CALL through AuditedChildGas.context_result/child_positive. `family_step_entry` covers the other variants. Both retain the actual child Bool success without requiring it true, so child-level ordinary failures are not silently discarded. The full funds/depth gate excludes the helper's no-child denial branch. These are projections of actual helper dispatch; they do not independently establish reachability of an opcode in an enclosing bytecode run.

## Exact scope of totals

TransferFunding establishes natural-total **nonincrease** over the actual entryWorld under fundedness, including missing accounts, self-transfer and potential recipient addition wrap. It does not assert exact equality for every distinct-account transfer. CallFunding composes that result with the real dispatcher funds gate and propagates any supplied pre-map budget.

Crucially, even in `call_step_entry`/`family_step_entry`, the inequality is about `context.entryWorld`. The separately recovered published `world` after child code execution is **not** claimed to satisfy the bound. The file does not prove conservation through arbitrary child code, subsequent parent execution, transaction fees/refunds, supply issuance, reentrancy or recursive rollback histories. No supply ceiling, budget after execution, or canonical predeploy provenance is assumed derived. These boundaries are stated accurately in the header and theorem conclusions.

## Dependency bindings

- AuditedChildGas: `476d03b05433139f778807104864ce4cd14ac3020d8aea4dcb609d7c2651904a`
- CallFamilyGas: `cae233fa8cbc8d8bd84c8ba00e48970c97a1abba03fe6987682d897e12a0e4b0`
- CallDispatchGas: `e1c5f79113ed283b4193bf6548adf7b91190a5b37183b00caf19a644460c6d4b`
- TransferFunding: `b8d8286170495a4a59d0f61ad19e0354e624ea3a0c0e0f48bd24e92ea7871766`

These match the relevant previously reviewed frozen sources. No changes requested.

---

# Independent review: DirectThetaDrainMutations

Outcome: CLEAN for the stated finite actual-Theta drain-mutation scope.

Source: Eip8282/Tests/DirectThetaDrainMutations.lean
SHA-256: cf371254f95e1d3e309d0deab724ccd7088e76a81dbc58f4e85dd20e4205f99b
HEAD observed during review: e76ad07d38279b581d3ba5955e43c9593d0ac723
Read-only review; no build and no source edits. Supplied compilation output inspected: /tmp/eip-DirectThetaDrainMutations-5.log, with no error or warning and the five expected axiom reports.

Dependencies inspected include the complete new file, old PDrain1Mutant receipts and their physical fixtures, EvmRunner, the previously reviewed DirectThetaMutations adapter, QueueInvariant.Represents/SourceWidth, DirectDrain.Domain/Observed, SystemDataSpec.DrainSlots, and DirectGuarantees.PDrain.

Dependency hashes:
- DirectThetaMutations: c324c198700f99d1255ee86ff485b0eb2693de67498302e614048ee1f4583801
- DirectDrain: 915a08868399a8fe39baea245b7bacb9fea5912a4b6cdafd86c9a07ea4c2dab3
- QueueInvariant: 5e15726133885b59340a5ffc4d8650fe33d4cda27639039ad1fe92fe49de5219
- DirectGuarantees: 9b39dc88aac5acb38b4ef7bac387739e9e0e1ab52f5c0e6994b9e1d0a792850d
- PDrain1Mutant: 02d2f5a0602c7a58f9d8c07fb47d842197c89e86f810aa46dffbf22e1f0865a9

## Checked findings

1. queueOfRead is a physical list of the input storage's record words, with six words per deposit and three per exit. It takes no bytecode or execution result. represents_queueOfRead proves the actual representation obligations: HEAD zero, TAIL n, ordered pointers, physical window within UInt256.size, list length equal to TAIL-HEAD, and equality of every stored word to the corresponding list word. This does not fabricate a post-queue or assume a desired execution invariant. It is a legitimate pre-queue chosen from the actual input storage, not an authenticity/protocol-history certificate.

2. deposit_domain and exit_domain hold for every parameter bytecode. Each parameter is actually installed in the fixture target account and is the code supplied to Theta. The control slots are 100/5/0/65 for deposit and 100/5/0/17 for exit. Budget 105 bounds tail, count and enabled excess+count, and is below 2^128. Quote numerators are respectively 100 and 103, both within EnabledSafe's 2892 boundary. Ordinary value is zero, calldata is empty, and owner existence is supplied by the actual pre-world lookup. No original-code pin, poststate, execution path, or protocol-reachability assumption occurs in either domain proof.

3. The exit source-width proof checks all Fin 17 indices, namely 0 through 16. Thus it covers the undrained seventeenth record as well as the first sixteen. Each source is the actual first word at key 4+3*i and is below 2^160. List membership in queueOfRead is transported through List.mem_ofFn to this check. The source words in the fixture are 0xA100+i. The use of kernel decide here evaluates fixed storage/arithmetic data, not an EVM execution, and introduces no native axiom.

4. Deposit execution uses the already reviewed deposit_theta_slot adapter. The new exit adapter is symmetrical and exact: zero credit and debit preserve the actual entryWorld, then exit_execution identifies Context.execution with the old runExitSystem using identical fuel, code, calldata, world/originalWorld, gas and environment. Context.result's extra outer Theta fuel step is retained. A positive old storage observation yields an actual successful Xi tuple and an existing account in its published world. That account excludes Theta's real empty-world fallback; success_commits_world publishes the very same tuple. The observed slot is read from that same world. No caller/address substitution, absent-world fabrication, or assumed poststate agreement occurs.

5. Three exact same-predicate refutations are established:
   - Deposit cap operand at byte offset 304 changes 64 to 32. The old actual successful result has HEAD=32 while the independent cap-64 DrainSlots rule requires HEAD=64 with length 65.
   - Deposit partial-head SSTORE operand at offset 483 changes slot 2 to slot 9. The old actual successful result has slot 9=64, whereas the pre-world slot 9 is 0x5500*2^240. Since slot 9 is at least 4, this contradicts the same all-stale-slot preservation clause.
   - Exit cap operand at offset 244 changes 16 to 8. The old actual successful result has HEAD=8 while the independent cap-16 rule requires HEAD=16 with length 17.
Each contradiction instantiates DirectGuarantees.PDrain itself with the domain-105 fixture, its represented physical queue, and the actual completed Theta tuple. It does not replace PDrain with a mutant-specific Boolean or make its domain vacuous. Refuting one required conjunct is sufficient; the proof need not fabricate additional return-byte observations.

6. Axiom accounting is as claimed. The two domain reports contain only propext, Classical.choice and Quot.sound. Each PDrain refutation additionally contains exactly its existing historical native execution axiom:
   - PDrain1Mutant.deposit_cap_mutant_halves_the_over_cap_drain._native.native_decide.ax_1_1
   - PDrain1Mutant.head_slot_mutant_overwrites_a_drained_word._native.native_decide.ax_1_1
   - PDrain1Mutant.cap_mutant_halves_the_over_cap_drain._native.native_decide.ax_1_1
The new source contains no native_decide, sorry or project axiom. Importing the prior control mutation adapter does not introduce its unused control-receipt axioms into these reported results.

Scope and limitations: these are three finite corroborating execution witnesses against the new universal parameter-code predicate. They cover the two caps and one deposit stale-slot write. They do not provide same-predicate witnesses for the old exit return-size mutant, the additional stale-word mutants, FIFO/order or amount-endian mutations, every possible byte mutation, or protocol-history reachability. The compiled universal pinned PDrain proof remains separate from these historical native receipts. No blocker found for the file's declared scope.
