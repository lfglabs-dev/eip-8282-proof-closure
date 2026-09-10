# Protected source-effect replay audit

Read-only Faraday audit, 2026-09-10. No builds, proof edits, new workers, or new source acquisition. Frozen execution-work integration reviewed at f11f001a47c12dcec001023175fb2530ba313d2d. Existing source bodies are the complete archived Amsterdam tree at EL0cc100eb190b64b23baba72dac0165652eaec252.

## Finding

Gas-erased replay is a plausible next bridge for the two fixed protected runtimes. Their allowed operations contain no GAS, CALL/CREATE family, or other instruction that makes control/data depend on the synthetic old gas grant. Preserve environment, stack/PC, current protected slots, padded memory bytes, owner logs and terminal output; leave gas/refund/original-storage/warmness accounting in the separate actual source ledger. Do not seek equality of old and source gas or the enclosing receipts. No counterexample to this *guarded local effect* strategy was found.

The existing forward theorem is not reversible as stated. `ReferenceRuntimeAction.step` consumes old At + Z + StepOk + H=None + Related + calldata fit + memory cap/host bound, and produces Action/Related. Action is a source-shaped transcription, not a successful source interpreter step certificate. Its pure constructor has no stack overflow guard; memory/copy actions have no host allocation guard; instruction/site agreement is external. A new successful-source boundary must supply those actual admission facts before obtaining old execution.

Concrete counterexample to unguarded Action -> accepted old step: both fixed runtimes start with CALLER. At PC0 let the view stack contain1024 words, with an existing owner, related empty memory/current slots, and pinned environment. `ReferencePureAction.familyAction .caller` returns the caller word prepended (length1025); hence RuntimeAction.base.pure holds. Old Z rejects StackOverflow because 1024-0+1>1024, independent of how much gas is selected. This is a local definitional counterexample to the proposed overly weak interface, **not** a reachable valid-entry source execution counterexample and not a compiled new theorem. The actual successful source push guard excludes it.

## Smallest next producer

First implement a bounded `ReferenceRuntimeAction.deterministic` for fixed kind/parent/instruction/pre-view. Constructor disjointness and deterministic pure Option action/stack decompositions should suffice. This is useful but alone does not produce an old step.

Then implement one local reverse producer (illustrative signature, not existing declaration):

```
replay_step
  (site : RuntimeExecutionScope.At (runtime kind) pre)
  (rel : Related parent v pre)
  (decoded : sourceDecode v.env.code v.pc = some instr)
  (effect : RuntimeAction.Action kind parent instr v next)
  (stackAccepted : next.stack.length <= 1024)
  (cdfit : v.env.calldata.size < UInt256.size)
  (memoryFit : next.memory.size < 2^System.Platform.numBits)
  (gas : ... explicit local old memory+opcode charge and SSTORE sentry budget ...)
  : exists mid post cost,
      Z jumps instr.1 pre = ok(mid,cost) /\
      StepOk (fuel+1) cost instr mid post /\ H post instr.1 = none /\
      Related parent next post
```

Use a precise typed guard record instead of keeping the ellipsis in implementation. It should contain only actual source admission/source representation facts. Input operand existence and store/log permission already follow from Action. Pure PUSH width/value must come from **full decoded instruction equality**, not just opcode membership. Jump destinations follow from the partial pure action and fixed reference jump table. At and full decoder binding derive natural PC fit and exclude foreign truncated PUSH. Refl/terminal EOF must be separate from a nonhalting some-decode step.

A useful proof decomposition avoids duplicating all existing forward effect proofs: construct actual old Z + raw StepOk success from these guards, apply existing forward RuntimeAction.step, then deterministic Action identifies the generated next view with the supplied source next view. Raw instruction totality can be proved over allowedOps and operand shapes, using existing EVM.Proof.step_* and the public pure/raw transport helpers. Existing forward memory/storage lemmas are equalities for actual steps, not totality producers; their actual-step antecedents cannot silently be assumed in the reverse theorem. `ReferenceAcceptedStack` is also forward-only (Z -> pop witnesses).

The source extractor must derive the admission record from the exact successful source instruction body and stack push/pop checks. Naming it source successful execution without that extraction would merely move the gap into a new predicate.

## Synthetic gas and fuel

Search found no generic runtime gas-parametric replay or reverse Action producer. `OrdinaryGas.raw_gas` only says raw ordinary instructions preserve the gas field, **including GAS**, so it does not by itself prove effects are independent of gas. Exclude GAS via actual protected allowedOps. `OrdinaryGas.accepted_step_debit`, RuntimeMemoryFunding, and RuntimeMemoryCharges are useful accounting/metadata equalities for already accepted old steps. SymExec.charged_eq_self and reach_block are specialized constructive block helpers, not arbitrary source trace replay.

A finite action list does not alone imply its old cumulative charge fits the UInt256 gas field. Retain and then discharge the exact finite-sum <UInt256.size obligation. A practical sufficient producer can compare each old opcode charge with its actual source execution charge: old Csstore is at most2100+20000=22100 for arbitrary original/current/warm metadata, while source SSTORE execution is at least100. Old SLOAD is at most2100 vs source at least100. Other supported ordinary prices agree, with COPY and LOG exact operand-based costs. Thus the conservative candidate old opcode cost <=221*source execution cost covers the whole union without requiring old/source original-storage or warmness equality. This inequality is a proposal requiring a new finite-table Lean proof, not already certified here.

Memory cost is the same quadratic formula on corresponding rounded capacities; prove the reverse replay metadata equality and telescope it. It can be included in the same factor221 conservative bound. A spare2301 after the cumulative budget discharges the old SSTORE >2300 sentry, even when its actual cost is only100. Therefore an illustrative initial synthetic budget is 221*source execution-work budget+2301, with its UInt256 fit proved from the actual source frame grant/potential producer. Do not substitute an unproved universal MAX frame grant: transaction allocation bounds top execution, but child stipend/allocation linkage still belongs to source extraction. For actual source budget16777216 this candidate is3707767037, far below UInt256.size; this numerical specialization is conditional on the real grant binding. All finite prefixes have adequate old remaining gas if the total budget is reserved before replay.

Fuel is a separate numeric evaluator resource. For a list of n nonhalting actions plus a successful terminal, choose enough fuel for all n edges, terminal StepOk, and the final X convention (a conservative n+3 avoids the zero raw-step tier). Prove it generically; do not assume old evaluator OutOfFuel corresponds to source gas failure. A finite source trace should be returned by an operational source execution inversion, not supplied as a desired list.

## Effect and representation seams

- Decoder: ReferenceAllDecode.decode_matches covers only fixed sites/EOF. Existing generic foreign PUSH parity is false and remains excluded. Source step must establish current fixed site; start PC0 and induction can use fixed next-site/jump facts.
- Arithmetic/stack: ReferenceWordOps and PureAction implement the audited word formulas/top-first view. Source Python stack is reversed into this view. Its successful stack admission supplies underflow/overflow facts. CALLDATASIZE needs the independently produced actual source calldata bound; arbitrary ByteArray size cannot be silently reduced modulo256 bits.
- Memory: old physical memory is lazy, source memory eager/rounded. Related uses padded byte equality and size=32*activeWords; literal ByteArray equality is wrong. COPY uses padded calldata reads, arbitrary source offset, and zero-length ignores a huge destination. RETURN/REVERT/LOG source unpadded slice agrees only after extension, as existing ReturnSlice/LogView establish. Reverse proof needs source-derived host fit; old platform-sized ByteArray conversion must not wrap. Positive source-paid memory expansion and actual grant bounds can derive this; no arbitrary small offset premise is appropriate.
- Storage: source layered current read/zero override maps to actual owner storage via ReferenceStorageView.Related. Owner existence remains essential for old SSTORE, supplied by source frame/account/code binding. Source created-original override, read tracking, warmth and refund metadata are not equal to old sigma0/substate in general; do not put that equality in the effect relation. Old gas may instead use conservative all-class bounds.
- Logs: view compares all-topic projection at codeOwner. Runtime LOG0 appends the same owner/empty-topics/data; inherited foreign logs and failed ancestor journals require actual source framing/rollback. Full old substate equality is neither needed nor established.
- Environment/value transfer: env equality must reflect actual source code owner, caller, value, calldata, permission and installed bytes at protected entry. A synthetic old XiCall can serve as an effect witness, but it is not the actual source gas receipt. Canonical address and delegated/other-owner exclusions remain source boundary obligations.
- Terminal: implement source-shaped STOP/RETURN/REVERT reverse leaves separately. Source successful finite frame yields old success with matching observations, explicit source REVERT yields old REVERT with matching internal output; source journal then restores effects independently. **Source gas exceptions must not be forced to old exceptions:** generous synthetic old gas can allow success where source allocation fails. Exceptional source rollback should be handled directly by actual source journal settlement, not by an invented matching old failure.

## Integration recommendation

Start with Action determinism + reverse single-step raw/guard construction, preserving the existing forward files. Then an actual source-shaped finite trace inversion/adapter threads the related synthetic old state and accumulates old required cost. Prove source work -> UInt256 old-budget fit from the same source ledger, replay terminal, and expose only current slots/owner logs/output and successful-or-explicit-revert status to existing protected runtime guarantees. The source resource ledger and source frame occurrence tree remain independent witnesses linked at this protected boundary; no foreign global interpreter trace is required.

This does not close source Python refinement simply by introducing another inductive Action trace. The exact archived instruction bodies, decoder/admission extraction, initial frame/environment bindings and actual source journal identities remain the named producer obligations.

## Inspected current source hashes
- `Eip8282/Audit/Integrator/ReferenceRuntimeAction.lean` SHA256 `d2919db661324e7c9ad33b6a2a00bf9839f56623a4a42e9db47c8893314e471b`
- `Eip8282/Audit/Integrator/ReferenceRuntimeView.lean` SHA256 `5242dabdb863c029f1b903ff04b540db135a516d04edb1e12f9bcb0794065d41`
- `Eip8282/Audit/Integrator/ReferencePureAction.lean` SHA256 `0982b4a3bd2161f23f3b6530182afa14425239f110c702fa75d840b9bfa36d82`
- `Eip8282/Audit/Integrator/ReferenceSystemAction.lean` SHA256 `cae8d82edf82f981001d46e77fee4f3642d1cda2fdaaf82baf0755100ae5e537`
- `Eip8282/Audit/Integrator/ReferenceAllDecode.lean` SHA256 `b6938212bfb661d90bfb13ff0138129026a609ceaaf8a0fe09e00a1aac40a8cd`
- `Eip8282/Audit/Integrator/ReferenceMemoryOperations.lean` SHA256 `a72929f02fbdd7487ce17c88cf4ad1364ac933f5a3606efbf97a63d75bb9ea4d`
- `Eip8282/Audit/Integrator/ReferenceStorageView.lean` SHA256 `23db65a073055ccf1a6512e3eccb0521a1d4fcb346abcbeff2931efe27aff998`
- `Eip8282/Audit/Integrator/ReferenceRuntimeCompletion.lean` SHA256 `1b6709e4f4ec621ca5566cf058a8676f5ccc29aa9f52bf32b0a40052aaea1dee`
- `Eip8282/Audit/Integrator/OrdinaryGas.lean` SHA256 `d41661f413814579343e04a37da8cb87624881f63ac132440077beb8dc0adfd4`
- `Eip8282/Audit/Integrator/ReferenceExecutionPotential.lean` SHA256 `05e04fb02caeb2d6868307e8e0c2ee44fa50ed523d00321dcc8640a5b961a9a5`
- `Eip8282/Audit/Integrator/ReferenceExecutionLedger.lean` SHA256 `7c97fb8d5ba5e3787ee52d61735f69352af7921ac16c6c4b16e6e07357775c69`
- `Eip8282/Audit/Integrator/ReferenceAppendCompletedCost.lean` SHA256 `a581b74c022a6309822b689a8c507ae755d43ed07e201ff9c926f63f3cab34d5`
