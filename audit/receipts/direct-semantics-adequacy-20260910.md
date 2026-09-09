# Semantic adequacy inventory — read-only, 2026-09-10

Pinned evaluator: `b62586650b4f96cc6da25f36574aaa8f329a6420`. Proposed, NOT adopted EL reference: Amsterdam `0cc100eb190b64b23baba72dac0165652eaec252`. This review inspected immutable primary source and local pinned files; no builds, tests, repository changes, model jobs, or coordination messages were performed. Source-level differences below are not claimed to be reachable protocol counterexamples.

The current Lean results remain theorems of the pinned evaluator. They do not yet transfer to Amsterdam. A focused adapter can close this gap: exact installed-runtime execution plus reference-level outer-context framing, funding conservation, and event-resource accounting. Whole-interpreter equivalence is neither established nor required by this proposal.

## Transaction Variants — concrete mismatch

Pinned Transaction has only types 0–3; Amsterdam accepts type 4, applies authorizations, resolves delegated code. [Pinned source](https://github.com/lfglabs-dev/EVMYulLean/blob/b62586650b4f96cc6da25f36574aaa8f329a6420/EvmYul/State/Transaction.lean#L116); [Amsterdam source](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/transactions.py#L411).

Minimal closure: Keep all admitted transaction types in a reference history relation. Prove authorization preprocessing preserves installed predeploy code/storage; model arbitrary delegated outer execution with an open-context frame adapter.

## Admission — missing adapter

Pinned Upsilon accepts S_T and presupposes valid transactions; Amsterdam recovers sender, checks nonce, max gas fee plus value, and sender code. [Pinned source](https://github.com/lfglabs-dev/EVMYulLean/blob/b62586650b4f96cc6da25f36574aaa8f329a6420/EvmYul/EVM/Semantics.lean#L830); [Amsterdam source](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/fork.py#L543).

Minimal closure: Use reference admission plus explicit crypto/address assumptions, then map validated entry state. Do not derive funding or SYSTEM exclusion from arbitrary S_T.

## State Gas — concrete mismatch

Single pinned gas counter and SSTORE pricing differ from Amsterdam execution/state pools, spill, refill, and child merge. [Pinned source](https://github.com/lfglabs-dev/EVMYulLean/blob/b62586650b4f96cc6da25f36574aaa8f329a6420/EvmYul/EVM/Gas.lean#L95); [Amsterdam source](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/vm/gas.py#L423).

Minimal closure: Prove a two-pool potential with spill/refund liabilities. Relate installed runtime traces locally; separately budget arbitrary outer execution and all attempted append occurrences.

## New Opcodes — concrete mismatch

Amsterdam decodes CLZ 0x1e and SLOTNUM 0x4b; pinned EvmYul contains neither. [Pinned source](https://github.com/lfglabs-dev/EVMYulLean/blob/b62586650b4f96cc6da25f36574aaa8f329a6420/EvmYul/EVM/Instr.lean); [Amsterdam source](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/vm/instructions/__init__.py#L67).

Minimal closure: Do not simulate all outer bytecode with pinned evaluator. Prove framing, call-entry extraction, and resource conservation directly for reference outer steps, including these opcodes.

## Collision — concrete mismatch

Pinned Lambda rejects nonempty storage as well as nonce/code. Amsterdam account_deployable tests only nonce/code. [Pinned source](https://github.com/lfglabs-dev/EVMYulLean/blob/b62586650b4f96cc6da25f36574aaa8f329a6420/EvmYul/EVM/Semantics.lean#L615); [Amsterdam source](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/state_tracker.py#L348).

Minimal closure: Installed nonempty runtime suffices to block creation at protected address in both. For arbitrary creation, retain reference behavior and prove frame/funding preservation; do not assert universal CREATE equivalence.

## Code Immutability — missing adapter with supporting rules

Amsterdam authorization rejects nonempty nondelegation code; SELFDESTRUCT deletes only accounts created in this transaction. These support, but do not themselves prove, permanent installed code. [Pinned source](https://github.com/lfglabs-dev/EVMYulLean/blob/b62586650b4f96cc6da25f36574aaa8f329a6420/EvmYul/Semantics.lean#L395); [Amsterdam source](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/vm/eoa_delegation.py#L220).

Minimal closure: Induct from exact installation over every reference mutation and fork transition; show protected account never freshly created. Bind current_target/storage owner separately from code address.

## Fuel — missing adapter

Nat interpreter fuel is distinct from EVM gas; OutOfFuel can propagate or be caught, and CREATE catches Lambda errors with an empty account map. [Pinned source](https://github.com/lfglabs-dev/EVMYulLean/blob/b62586650b4f96cc6da25f36574aaa8f329a6420/EvmYul/EVM/Semantics.lean#L290); [Amsterdam source](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/vm/interpreter.py).

Minimal closure: Construct sufficient fuel for extracted finite reference traces and prove stability; do not quantify arbitrary small fuel as real execution or use gas >= fuel.

## Transfer Logs — concrete mismatch

Amsterdam emits EIP-7708 synthetic LOG3 transfer logs. These are not executed LOG0 opcodes or append events. [Pinned source](https://github.com/lfglabs-dev/EVMYulLean/blob/b62586650b4f96cc6da25f36574aaa8f329a6420/EvmYul/Semantics.lean#L395); [Amsterdam source](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/vm/__init__.py#L252).

Minimal closure: Use address/topics/length-filtered append occurrence projection; do not require raw full log-list equality.

## Consequences for the three guarantees

P-SUBMIT-1: local calldata, fee computation, value and queue-update results survive as pinned statements. Actual Amsterdam use requires the exact runtime/owner entry relation, transfer-before-execution mapping, successful execution correspondence under changed gas, and rollback mapping. Apparent DELEGATECALL value is not transferred funding. A delegated or CALLCODE execution of these bytes in another account does not operate the predeploy queue. A target call from such an outer frame remains a legitimate request and cannot be excluded wholesale. Funding must follow actual owner balances and transfers, not raw transaction value or apparent value.

P-DRAIN-1: output/FIFO and local reset proofs require the same storage view and runtime execution adapter. SYSTEM scheduling, ordering, zero actual value, and identity come from the reference block transition. Amsterdam grants 30,000,000 execution gas plus a reservoir of 16 STORAGE_SET charges. The pinned progress hypothesis of 2,500,000 gas and sufficient Nat fuel cannot be discharged solely by comparing 30M >= 2.5M: changed storage pricing and the fuel construction must be checked for this bounded code path. Default scheduling supplies empty calldata; any nonempty drain migration remains an explicit additional protocol choice.

P-CONTROL-1: installed code and initialization history must be established at the chosen boundary. Neither CREATE2 address arithmetic nor constructor execution under arbitrary funded state proves a valid deployment history. Both implementations protect existing nonempty runtime against CREATE collision, despite differing on storage-only collision. Code immutability also needs 7702 exclusion at the installed nondelegation account, EIP-6780 lifecycle induction, and an explicit rule for authorized fork upgrades. Reversible inhibition remains the pinned behavior; BLS trust does not resolve EL/SYSTEM entry obligations.

## Event budget and funding: preserve what is already proved

The reviewed NestedEventArgs/Cert/Extract/Projection modules expose complete actual child structure and local event membership for the pinned evaluator, including exceptional outcomes; NestedFrameOwnership strips trailing true edges to identify structural owners. These are useful reusable proof interfaces. They are not yet a reference Amsterdam trace extractor or history composition theorem. This review does not reassess subsequently edited gas-debit proofs.

Amsterdam LOG0 still charges 375 + 8*size plus nonnegative memory cost (vm/instructions/log.py:58–70; vm/gas.py:257–259). Consequently a successful 68-byte LOG0 costs at least 919 execution gas, and 184-byte LOG0 at least 1847. This source calculation supports the intended lower-bound adapter; it is not a compiled Lean theorem about Amsterdam. Synthetic transfer LOG3s do not meet this marker. Failed/reverted frame attempts still consume execution work; reverted storage can refund state gas/spill. Therefore do not identify the sum of attempted LOG costs with receipt gasUsed or a single monotonically decreasing gas_left. Prove an amortized quantity accounting for withheld child grants, state reservoir, spill repayment and rollback, then connect transaction settlement and block capacity. The missing dual-pool accounting is substantive but need not require every opcode to be simulated by Lean.

Reference admission checks sender balance against max gas fee + actual value using unbounded Uint arithmetic before execution. Pinned word subtraction is not this admission proof. A history supply bound must account for genesis balances, withdrawals, rewards/fees, burns, SYSTEM behavior and upgrades, and preserve no-overflow for actual transfers; self-transfers and forced SELFDESTRUCT transfers must remain included. Bounds on a queue accumulator require relating real paid request events to these transfers, including repeated/self-funded requests and revert. Assume only externally specified initial supply/emission parameters, then prove the desired per-history funding bound; assuming the accumulator bound itself would be circular.

## Exact unresolved choices for Thomas

1. Adopt Amsterdam 0cc100e as the EL semantics target, or keep the claim explicitly limited to pinned EVMYul. Choosing Amsterdam entails the focused adapters above; it does not require rewriting every theorem.
2. Fix an actual installation/checkpoint and upgrade policy, including code hashes, SYSTEM address reachability assumptions and constructor versus trusted checkpoint obligations. A checkpoint can specify initial state but must not silently assert the future desired queue/funding invariants.
3. Decide default empty SYSTEM scheduling versus a specified nonempty drain migration and reversible versus permanent inhibition. These are protocol differences, not missing proof tactics.
4. Specify finite history/resource and external funding inputs. Derive the actual event and safe-fee bounds; do not exclude type-4 transactions, new-opcode callers, necessary withdrawals, failed child calls or forced transfers to simplify the proof.

Recommended implementation order: (a) reference protected-address mutation/framing lemma including 7702 and EIP-6780; (b) local installed-runtime opcode/storage correspondence parameterized by the two gas pools; (c) sufficient-fuel witness; (d) reference call-entry and filtered-event extraction; (e) amortized event debit and block/funding composition. This isolates genuinely needed semantics without adopting pins or asserting global interpreter equivalence.

Primary supplemental citations: [vm/instructions/log.py#L58](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/vm/instructions/log.py#L58), [vm/gas.py#L257](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/vm/gas.py#L257), [vm/gas.py#L503](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/vm/gas.py#L503), [vm/gas.py#L604](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/vm/gas.py#L604), [vm/__init__.py#L220](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/vm/__init__.py#L220), [fork.py#L755](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/fork.py#L755), [vm/instructions/storage.py#L119](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/vm/instructions/storage.py#L119), [vm/instructions/system.py#L778](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/vm/instructions/system.py#L778).
