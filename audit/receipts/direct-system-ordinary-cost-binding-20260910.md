# SYSTEM ordinary execution cost interface

All source bodies are cached at exact EL commit `0cc100eb190b64b23baba72dac0165652eaec252`. No downloads or Lean source edits were made. `/tmp/eip-system-ordinary-cost-sources-russell.json` records immutable URLs, full-file hashes, function spans and full selected bodies. The existing complete source files remain the authority; selected bodies do not replace imports or dispatch bindings.

## Exact minimum pricing map

| Operations | Ordinary execution charge | Source |
|---|---:|---|
| ADD, SUB, LT, GT, EQ, ISZERO, AND, SHL, SHR | 3 | arithmetic/comparison/bitwise bodies, GasCosts VERY_LOW |
| MUL, DIV | 5 | arithmetic bodies, LOW |
| CALLER, CALLVALUE, CALLDATASIZE, POP, PUSH0 | 2 | environment/stack bodies, BASE |
| CALLDATALOAD, PUSH1..32, DUP1..16, SWAP1..16 | 3 | environment/stack bodies, VERY_LOW |
| JUMP | 8 | control_flow.jump, MID |
| JUMPI | 10 | control_flow.jumpi, HIGH |
| JUMPDEST | 1 | control_flow.jumpdest |
| MSTORE, MSTORE8 | 3 plus separate memory expansion | memory bodies, OPCODE_MSTORE_BASE/OPCODE_MSTORE8_BASE |
| SLOAD | warm100 or cold2100, never both | storage.sload actual membership branch |
| STOP | 0 | control_flow.stop has no gas charge |
| RETURN, REVERT | 0 plus separate memory expansion | system.return_/revert |

`SystemPathBudget.Allowed` is the exact runtime union minus LOG0 and CALLDATACOPY. No missing ordinary pricing file or missing download was found for that set. SSTORE is deliberately outside the ordinary table: existing `ReferenceStorageGas.conservative_success` covers all warm/original/current/new combinations with execution12100, state reservoir97920 and its sentry, without relying on refunds. The source SLOAD has no state-gas charge; all the ordinary bodies above call no state-gas charging function.

PUSH/DUP/SWAP partial dispatch bindings in stack.py must stay attached to their integer width/index (already separately audited by ReferenceControlOps/ReferenceStackOps). STOP is absent from charge_gas calls rather than an invented nonzero tier. Memory writers and RETURN/REVERT charge the sum of ordinary base and memory expansion exactly once. The memory expansion component must come from the actual trace meter; assigning2100 to their full charge would be false.

## Smallest concrete Lean producer

Propose exclusive `ReferenceOrdinaryGas.lean` importing SystemPathBudget and ReferenceStorageGas. Define a partial source transcript `ordinaryCost (op : Operation .EVM) (warm : Bool) : Option Nat`: explicit constructors for all allowed non-SSTORE operations above; default `none`. Returning none for SSTORE, LOG0, CALLDATACOPY and unsupported opcodes prevents an accidental free default from entering the bound. It does not interpret execution.

Export these boundaries (exact naming can follow ownership):

```lean
ordinary_defined_bound (ha : SystemPathBudget.Allowed op) (hs : op ≠ .SSTORE) :
  ∃ n, ordinaryCost op warm = some n ∧ n ≤ 2100

ordinary_charge (hc : ordinaryCost op warm = some n)
    (hg : n + memoryDelta ≤ meter.execution) :
  ∃ post, ReferenceStorageGas.chargeExecution meter (n + memoryDelta) = some post ∧
    post.execution = meter.execution - (n + memoryDelta)
```

The second theorem is literal source-shaped meter arithmetic. `memoryDelta` is a parameter of this local equation, not a per-trace arbitrary-charge assumption: the root actual memory annotation must produce it for each memory access, and it is zero for other opcodes. Add a finite opcode predicate distinguishing memory operations if that helps enforce this in the downstream costed-trace relation. A source-shape theorem can identify SLOAD branch charge without assuming warmth stability; the bound holds for either Boolean.

A subsequent root consumer should retain the actual `SystemTraceWitness` operation list. For each non-SSTORE op, annotate a value from `ordinaryCost`; derive the sum ≤2100 times the actual non-SSTORE count (or conservatively full list length). Separately use actual SSTORE weight≤4 and the already derived actual memory difference sum. Do not assume a desired operation list, source success, per-step available gas, or a pre-existing arbitrary Charges history. Prove prefix-payment by an initial remaining-budget invariant, with the SSTORE sentry/reservoir conditions discharged by the reserved12100/97920 amounts.

Conservative arithmetic with the current complete operation bounds (including final RETURN) is: Deposit8501*2100+4*12100+1512=17902012 execution, Exit801*2100+4*12100+123=1730623 execution, and4*97920=391680 state reservoir for either. This intentionally overcounts SSTORE positions in the ordinary baseline; it is safe but can be tightened by subtracting their actual count. These are arithmetic envelopes, not established reference-call resource theorems or protocol gas-limit bindings.

## Remaining actual reference boundary

`charge_gas` emits an evm_trace GasAndRefund event then calls charge_gas_from_meter; the latter checks gas_left≥amount and subtracts it. Any direct correspondence with executable Python must also specify trace-hook behavior and checked numeric representations. The Nat transcript does not silently prove those Python operations. Source GasCosts explicitly says values may be patched by repricing utilities: the exact pinned schedule/configuration is an adapter binding, not a universal schedule claim.

Reference SLOAD reads/warm-set mutation, memory allocation, code/stack/control/world state transport, typed ExecutionGas/StateGas conversions, and all actual error branches remain separate obligations. In particular arbitrary foreign-bytecode replay is ruled out by the concrete truncated-PUSH mismatch. This local ordinary-cost classification supports exact protected-runtime successful-path resource composition only after the root proves the relevant source-to-formalization/execution adapter.

## Full-source hash index

- `vm/instructions/arithmetic.py`: `7bd39760ffa9c27334129a89974d863362579dc1d221d09983532dec4be81d9f`; cached `/tmp/eip-reference-word-ops/arithmetic.py`.
- `vm/instructions/comparison.py`: `45a320c05063bb8d1d281a5383f73a936961552e3b29c08f0e9ac7ccc8916700`; cached `/tmp/eip-reference-word-ops/comparison.py`.
- `vm/instructions/bitwise.py`: `e48944ae09c914f44e348e68de107f3af52233504772a8d6077e6d9bd1449f22`; cached `/tmp/eip-adequacy-sources/vm__instructions__bitwise.py`.
- `vm/instructions/environment.py`: `8c57bd699b99ff8b4d8e41e6a9c89cd1a03dda8160bf1d6dffe091932ec03657`; cached `/tmp/eip-reference-memory-control/vm__instructions__environment.py`.
- `vm/instructions/stack.py`: `1065b389a6d8e4a0ed72945b0be5e67b18484836695041aae83bbc08484caace`; cached `/tmp/eip-reference-memory-control/vm__instructions__stack.py`.
- `vm/instructions/control_flow.py`: `b6b481918211a8e86ded3acd9ec13e940ba05860786e584913478aec13abc0c3`; cached `/tmp/eip-reference-memory-control/vm__instructions__control_flow.py`.
- `vm/instructions/memory.py`: `77fec2a002eb27f34af82bd4ce5db98d593033f220a91eb65f56ff9496135278`; cached `/tmp/eip-reference-memory-control/vm__instructions__memory.py`.
- `vm/instructions/storage.py`: `d355855a1c50212a4e4753abb533c338919103635755da13bc1e154fcb3ed11b`; cached `/tmp/eip-adequacy-sources/vm__instructions__storage.py`.
- `vm/instructions/system.py`: `37c888c4f1dfed62f1947ceb457db349be6978da5519234a5b6604f2e6036890`; cached `/tmp/eip-reference-memory-control/vm__instructions__system.py`.
- `vm/gas.py`: `41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c`; cached `/tmp/eip-reference-memory-control/vm__gas.py`.
