# Focused local reference transport — independent source review

Reviewer: Dewey. 2026-09-10. Read-only; no build, source mutation, fresh download, normative adoption, or interpreter-equivalence claim.

The proposed adapter is viable as a bounded proof interface, but is not yet proved. It should transport successful reference execution of the exact Deposit/Exit runtime to a pinned execution with shadow gas, then transport the protected-address observables back. It must not assert equality of full call logs or gas. The existing all-topics protected-address projection need not be weakened to LOG0-only.

## Exact scope and source identities

Pinned EVMYulLean: `b62586650b4f96cc6da25f36574aaa8f329a6420`. Proposed, still unadopted execution-specs Amsterdam: `0cc100eb190b64b23baba72dac0165652eaec252`. sys-asm source: `83f9801245ff56878a450b5625801101b9a225a1`.
Deposit runtime: 628 bytes, SHA256 `2c49dcf745b1304f3dac0ea7487eae6d8fd07812ada980d542f79e8e5e53eb8d`.
Exit runtime: 458 bytes, SHA256 `c889ed88730d157d192aae28c2dee61324d0df3bd01ff0078386808b4adb27aa`.

Reused `/tmp/eip-semantics-adequacy-20260909.{md,json}`, `/tmp/eip-runtime-adapter-interface-20260910.md`, and cached exact bodies under `/tmp/eip-adequacy-sources`. Source line citations below are to those cached bodies, corresponding to `src/ethereum/forks/amsterdam/` at the proposed immutable commit. This review checks the focused consumers, not the unchanged whole corpus.

| Cached body | SHA256 |
|---|---|
| vm____init__.py | 664702bc483736fca3c4ac4bb9e459a24c83f5365b495485c4674d5c41fbe993 |
| vm__interpreter.py | 8281535f92be8cfe663033716baf9418ffc37b6c8861f70ac357e41fb6cf4c82 |
| vm__instructions__storage.py | d355855a1c50212a4e4753abb533c338919103635755da13bc1e154fcb3ed11b |
| vm__gas.py | 41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c |
| vm__instructions__log.py | f62f6cb589811e3a58c3a4644fcf7b979a506df1f09213e2a96e7988a4574874 |
| state_tracker.py | ce420ad5682df9051178d298220d1552448e26c37f67be3b604b9f493541cf4a |

## What the local execution actually consumes

`Eip8282/Audit/Integrator/RuntimeOpcodeScope.lean:24` lists the exact decoded union: STOP; ADD/MUL/SUB/DIV; LT/GT/EQ/ISZERO/AND/SHL/SHR; CALLER/CALLVALUE/CALLDATALOAD/CALLDATASIZE/CALLDATACOPY; POP/MSTORE/MSTORE8/SLOAD/SSTORE; JUMP/JUMPI/JUMPDEST; the listed PUSH/DUP/SWAP instructions; LOG0/RETURN/REVERT. PUSH data are not instructions. The checked boundary/decode and jump lemmas are now consumed by `RuntimeExecutionScope.accepted_next`, `cert_local`, `x_no_xi`, and `xi_only_self`. This supersedes the earlier memo's static-only status, but these are still pinned-evaluator facts, not reference facts.

There is no GAS, BALANCE, GASPRICE, external call, creation, SELFDESTRUCT, CLZ, SLOTNUM, delegation opcode, or transient-storage instruction in either local runtime. The live semantic inputs are code/PC, stack, zero-extended memory, caller, apparent value, calldata, persistent storage at current owner, and log/output bytes. Balance and gas do not enter arithmetic control flow directly. Storage's original value and warmth affect charges, so cannot be erased from the resource proof, although they need not appear in the resulting persistent-storage equality.

The focused unresolved obligations are:

1. Same byte decoding, PUSH width/immediates and valid jump destinations, with the reference stack orientation mapped explicitly to the pinned head-first stack. Prove the relation at entry and after each actually executed instruction; do not assume that reference PCs already satisfy the pinned scope theorem.
2. Exact operand order and word semantics for this union. Pinned `EvmYul/Semantics.lean:234–276` dispatches SUB/DIV/LT/GT and uses `flip UInt256.shiftLeft/shiftRight`; its dispatchers lead to `EvmYul/EVM/PrimOps.lean:22,68,104`. Reference bitwise cached lines 171–172 and 201–202 pop shift first, value second. Storage lines 80–170 pop key first then new value. LOG lines 31–86 pop memory offset then size. Prove these precise correspondences, including division by zero, shifts at least 256, modular arithmetic, byte order and zero-padding. Matching opcode names alone is insufficient; this review has not proved all operand lemmas.
3. Memory offsets, expansion, zero-fill and copy lengths must match as naturals without silently wrapping through UInt256. Calldata-size fit comes from root admission or the already derived nested-call data-size theorem, not a fresh per-child size assumption. Checked bounds must cover every conversion actually used by the replay.
4. Successful SLOAD/SSTORE and LOG0 value effects must agree. In reference storage lines 80–170, execution/state charges and stipend/static guards precede `set_storage(current_target,key,new_value)`. Dual pools alter success/OOG eligibility and refunds, not the successful assigned word. LOG creates an entry at `current_target` with the exact memory slice. No additional successful value-transform discrepancy was identified in these checked bodies.

## Proposed theorem interface (not an established theorem)

Inputs: an actual successful reference call to one exact runtime image, an entry relation, and a derived resource certificate for its actual finite instruction trace. The entry relation identifies protected owner with reference current_target, exact code bytes, caller, calldata, apparent value, static capability, initial stack/PC/memory and extensional persistent storage. It maps the existing protected-address log prefix. For a canonical value-bearing call, derive the apparent/transferred-value coherence and funded, nonoverflowing entry transfer from the outer call rule. Do not stipulate a desired final queue, log, or storage state.

Conclusion: there exist a representable pinned shadow gas value and sufficient Nat fuel and an actual pinned successful execution of that image such that output bytes, protected persistent storage, and ordered protected-address log contribution agree. This is enough to instantiate the existing local predicates/receipts and return their concrete observable conclusions to the actual reference call. Installed code and account presence belong in the entry relation or its outer producer; balances may be related only where a consumer needs them.

Prove the core as a forward induction over the actual reference trace with a gas-erased machine relation. At each instruction, expose exact operands, show the pinned charge/guards can be paid, apply the actual pinned step, and re-establish the relation. The absent GAS opcode permits a different gas trajectory without changing computed operands. An arbitrary changed gas value is not enough: SSTORE stipend guards, memory costs, warmth/original-value-dependent charges and gas-width bounds still matter. A backward accumulated legacy charge plus guard slack is a candidate shadow budget; prove it is below UInt256.size using concrete path/resource bounds. A finite trace alone does not establish this representability bound. Derive Nat fuel for the chosen pinned execution and wrapper structure; do not assume its desired successful result or use a per-node no-OutOfFuel premise as the final producer.

Existing local proofs may quantify over gas, but the exact selected receipt must satisfy their resource hypotheses. Do not transport an existing finite fixed-gas receipt merely by renaming its gas. No equality of reference and pinned initial gas, remaining gas, refunds, or transaction gas used is proposed.

Reference REVERT requires a separate trace/output and rollback adapter. Reference OOG requires direct reference rollback/frame reasoning: replay with generous shadow gas may succeed, so equivalence of failure status under shadow gas is false in general. Successful-call transport is a safety direction and cannot establish that mandatory SYSTEM execution succeeds. SYSTEM liveness still needs actual dual-pool accounting for the bounded drain/update path, including the 30M execution grant and reservoir for 16 new writes (cached fork.py:114,761–770), memory/output costs and only control slots 0..3 written by that path. It does not follow just from absence of GAS or from the pinned SYSTEM theorem.

## Exact synthetic transfer-log adapter and counterexample

Cached `vm____init__.py:40–43,252–288` defines:
- emitter `SYSTEM_ADDRESS = 0xfffffffffffffffffffffffffffffffffffffffe`;
- topics `(keccak256("Transfer(address,address,uint256)"), leftPad32(sender), leftPad32(recipient))`;
- data `transfer_amount.to_be_bytes32()`;
- no entry for zero amount.

The emitter is NOT the recipient and NOT the executing runtime's current_target. This explicitly corrects any reading of the earlier memo that treated the synthetic LOG3 as a protected-runtime log.

`vm__interpreter.py:419–436` snapshots transaction state, then performs `move_ether` before child code; only if should_transfer_value, value is nonzero and caller differs from current_target does it append this synthetic entry. `state_tracker.py:590–621` debits sender then credits the updated recipient state. Pinned wrapper transfer order differs, so derive final balance/alias correspondence under funding and checked-add guards; intermediate equality is neither needed nor claimed.

`vm__interpreter.py:437–474` then executes code. Exceptional halt and REVERT settle gas and restore transaction state on error. This restoration alone is NOT an assertion that the Evm object's logs have become empty. Actual log survival is supplied by `vm____init__.py:193–249`: incorporate_child appends child's logs only when child.error is absent; gas returns separately. At the top level, `vm__interpreter.py:295–306` explicitly chooses empty logs for an errored execution. The child CALL implementation invokes process_call and incorporate_child (cached system.py:453 onward). Thus success prepends the synthetic entry to runtime-generated child logs; child failure excludes both that entry and runtime logs from its parent's committed series; a later ancestor failure likewise discards that ancestor's accumulated child logs through the same rule.

Concrete conditional counterexample to FULL raw series equality: any successful positive-value, distinct-sender canonical user submission has the synthetic SYSTEM LOG3 before the runtime's authentic LOG0 in the reference child log list. The pinned runtime/call series has no such synthetic entry. This is a semantic discrepancy, not a report of a newly executed experiment.

`ProtectedCallLogSeries.completed` states full pinned-Theta log equality and therefore must not itself be asserted as a full reference log equation. The global consumer instead uses `ProtectedLogFrame.project` (definition at lines 15–16), retaining every entry at the protected address, in order, irrespective of topics. Derive protectedAddress(kind) != SYSTEM from the canonical addresses, apply the existing `push_away` shape to the source-generated transfer entry, and then transport this address projection. Preserve prefix order and actual settlement guards. No global filtering of arbitrary lookalike LOG3 entries is needed or justified.

The all-topics projection is logically stronger than a claim solely about the number/content of LOG0 entries at that address. For these exact runtimes, only LOG0 can be executed, and the source-defined synthetic transfer emitter is elsewhere; a proved adapter can legitimately preserve that stronger result. The agreed one-LOG0 clause remains unchanged. Do not silently replace the projection with LOG0 filtering, or claim there is only one log globally in an Amsterdam receipt.

## Outer obligations kept outside the local simulation

| Outer consumer | Required reference producer |
|---|---|
| Call entry and ownership | Actual signature/admission, code lookup including 7702 delegation, codeOwner/current_target coherence, alias-safe value transfer, installed canonical image and SYSTEM identity rules. Delegate execution under another owner remains allowed but is not a canonical protected-address invocation. |
| Protected world history | Reference foreign-frame writes, CREATE/collision, SELFDESTRUCT, upgrades and migration framing; pinned ordinary-frame facts alone do not establish these newer rules. |
| Funding and checked credit | Same actual ledger locations, genesis/issuance/withdrawal/migration transport and no-double-counting; numerical envelopes alone are not canonical extraction. |
| Work/event budget | Reference charging of submissions and actual block admission under dual pools; shadow legacy gas is a proof instrument, not reference gas-used evidence. |
| Committed queue/log order | Actual outer CALL/CREATE settlement and chronological receipt extraction; local successful-call transport does not prove ancestor survival. |
| SYSTEM and protocol policy | Authorized schedule, inhibition/migration policy and actual success/resources, with fork selection still pending. |

CLZ/SLOTNUM/7702 and the newer SELFDESTRUCT/CREATE rules are not reasons to demand whole-interpreter equivalence for a local runtime that does not execute them. They remain necessary outer frame/admission/history obligations wherever actual surrounding execution consumes them. No counterexample to the focused successful-observable approach was established here; full raw-log equality and failure equivalence under arbitrary larger shadow gas are concrete invalid strengthenings.
