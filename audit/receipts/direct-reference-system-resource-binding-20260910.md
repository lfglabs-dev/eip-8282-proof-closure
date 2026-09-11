> Arithmetic correction confirmed by root kernel check: C(369)=1107+floor(136161/512)=1107+265=1372, not1373. Correct Deposit envelope18,941,372; the touched-span correction remains11784. C(35)=107 and C(400)=1512 are unchanged. Prior correction below is retained as history and superseded numerically where it says1373.

> Correction from subsequent actual writeItem inspection: 11,776/1,088 are RETURN lengths, not memory touched high-water marks. Deposit's last full MSTORE ends at11,784 (369 words, cost1,373); Exit's at1,104 (35 words, cost107). Replace the earlier memory-cost envelope with18,941,373/1,930,107 execution gas. The original text below is preserved as investigation history; its smaller touched-memory bounds are superseded. See /tmp/eip-system-trace-shape-interface-faraday.md.

# Proposed Amsterdam SYSTEM resource interface

Faraday, 2026-09-10. Read-only source and proof-interface investigation; no builds, interpreter execution, downloads, source edits or normative adoption. Exact proposed EL commit `0cc100eb190b64b23baba72dac0165652eaec252`. This is an arithmetic feasibility derivation and a producer specification, not a proved reference execution theorem.

The actual constants leave ample room: a reference SYSTEM trace with at most 9,000 instructions, at most four SSTOREs and memory high-water mark 11,776 bytes consumes at most **18,941,368 execution gas** and **391,680 state gas**, versus the source grants 30,000,000 and 1,566,720. Proving that the actual reference execution satisfies this trace shape is still required. Pinned `SystemProgress.pinned` does not supply that reference fact.

## Exact inspected bodies

| Cached full body | SHA256 |
|---|---|
| `/tmp/eip-adequacy-sources/src__ethereum__forks__amsterdam__fork.py` | `dd0d069cbd0ba3e60e3f927c0e2d41be40958c6415be039ee29d6074eb2950da` |
| `/tmp/eip-adequacy-sources/vm__gas.py` | `41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c` |
| `/tmp/eip-adequacy-sources/vm__instructions__storage.py` | `d355855a1c50212a4e4753abb533c338919103635755da13bc1e154fcb3ed11b` |
| `/tmp/eip-adequacy-sources/vm__interpreter.py` | `8281535f92be8cfe663033716baf9418ffc37b6c8861f70ac357e41fb6cf4c82` |
| `/tmp/eip-adequacy-sources/vm__eoa_delegation.py` | `260a8938958e309011b1c6f49c011ca0505784a580d2dd19929bb5ea18624e24` |
| `/tmp/eip-adequacy-sources/vm____init__.py` | `664702bc483736fca3c4ac4bb9e459a24c83f5365b495485c4674d5c41fbe993` |

## Entry, dispatch and actual grants

`fork.py:114-115` sets execution grant 30,000,000 and SYSTEM_MAX_SSTORES_PER_CALL=16. `fork.py:753-777` creates a fresh TransactionState and TransactionEnvironment: origin SYSTEM, selected recipient, is_create false, value0, data argument, execution_grant30M, state reservoir STORAGE_SET*16, calldata floor0, empty access lists/authorizations/blob hashes, no paid-write accounts. `fork.py:904-925` calls BOTH checked builder contracts with **empty data**, in Deposit then Exit order. Nonempty data is a helper/runtime capability, not the mandatory dispatcher policy observed here.

`vm/interpreter.py:130-221,266 onward`: value0 avoids new-account transfer state charge; no authorizations are processed. Target is warmed. Exact runtime code is not a 23-byte EF0100 delegation designation (`vm/eoa_delegation.py:47-111`), so no delegated-address charge. The frame has caller SYSTEM, static=false, empty stack/memory/logs and no children on this runtime path. Require the actual code lookup to equal pinned runtime, rather than merely nonempty code. `process_checked_system_transaction` at `fork.py:694-725` only checks nonempty code and raises InvalidBlock on returned error; it is not a liveness proof for arbitrary code.

## Source gas rules and accounting order

`vm/gas.py:49-69`: state cost per new storage slot =64*1530=97,920. Grant16 slots=1,566,720. At most4 slot writes cost at most391,680 even if each creates a new slot. At least1,175,040 remains; no state spill is required. This bound uses write occurrences, so it does not depend on assuming original=current, coldness, refund availability, or distinct storage keys.

`vm/gas.py:73-113,181-255` gives exact used-op costs: ADD/SUB/LT/GT/EQ/ISZERO/AND/SHL/SHR and PUSH1..32/DUP/SWAP cost3; MUL/DIV cost5; JUMP8; JUMPI10; JUMPDEST1; CALLER/CALLDATASIZE/POP/PUSH0 cost2. MSTORE/MSTORE8 base3 plus memory extension; RETURN base0 plus extension. SLOAD is100 warm or2100 cold (`storage.py:39-67`). The SYSTEM branch does not execute user fee loop, LOG0, CALLDATACOPY, external calls, CREATE, SELFDESTRUCT or SSTORE inside its drain loop. If a reference trace contains any excluded operation, the proposed certificate has not been established. Constants alone do not prove reference opcode dispatch implements these equations: cached arithmetic/control/memory/stack instruction bodies were not present in this inspected cache; their exact charging/operand dispatch must be pinned/read and proved in the opcode adapter, especially MSTORE/MSTORE8/RETURN.

`storage.py:80-170` SSTORE ordering is concrete:
1. Reject static before state mutation; pop key/new value.
2. Select access2100 cold or100 warm; check execution balance >=max(access,2301) **before** original/current state reads.
3. Mark cold access warm; read original and current values.
4. Add STORAGE_WRITE=10,000 iff original=current and current differs from new. Thus execution charge <=12,100 per write.
5. Adjust signed refund counter; state charge97,920 iff first change from original/current zero. Restore-to-original-zero invokes state refund.
6. Charge execution first, then state reservoir/spill, then actual set_storage.

`vm/gas.py:389-447` execution charge throws if insufficient; state charge draws reservoir before execution spill. `604-626` state refunds restore spill first then add to reservoir; with no spill they cannot decrease execution gas. SSTORE refund counter adjustments do not provide gas spendable by subsequent instructions. REFUND_STORAGE_CLEAR=(10000+2100)*4800//5000=11,616; reverting a prior clear subtracts this refund; restore-original adds10,000. The bound ignores all refunds, so signed cancellation and final refund caps cannot invalidate its available-gas lower bound.

`vm/gas.py:746-814` memory cost C(w)=3w+floor(w²/512), w=ceil(bytes/32); each extension charges C(new)-C(old). Memory only grows, so charges telescope. Deposit64*184=11,776 bytes =>368 words =>C=1,368. Exit16*68=1,088 bytes =>34 words =>C=104. A proof must include all MSTORE/MSTORE8 touched spans, not only final RETURN size. All spans remain small representable naturals; wrap in queue storage-index arithmetic does not enlarge the output index i, but that operand relation needs proof.

## Arithmetic envelope and branch coverage

For Deposit use N<=9,000; for Exit N<=900. Charge2100 for EVERY instruction (dominating all nonmemory base/access charges), then add10,000 for each of at most4 SSTOREs and add telescoping memory once. This deliberately double-overcounts many cheap operations:

- Deposit: 9000*2100+4*10000+1368 = **18,941,368**; remaining >=11,058,632.
- Exit: 900*2100+4*10000+104 = **1,930,104**; remaining >=28,069,896.
- Both leave strictly more than the2301 SSTORE sentry at every prefix, without relying on refunds. Every prefix cost is <=the same nonnegative full envelope; state demand similarly <=391,680.

The candidate shape bounds are grounded in actual pinned path decomposition, not imported as reference truth: `EntryReach/Deposit.lean:781-825,937-1220,1223-1416,1434-1475` gives prefix25, drain130*m+6 (m<=64), head update20, excess update36, final RETURN; `Ends8500` bounds the complete path. `EntryReach/Exit.lean:628 onward,1081 onward` gives `Ends800` (m<=16). Conservative9,000/900 leave slack for endpoint convention. A forward source instruction/path induction must re-establish these on reference execution; there is no permission to infer them from absence of GAS or from pinned sufficient gas.

Every branch uses the same bounded drain first:
- Full or empty queue: reset head and tail (two SSTOREs), then excess/count (two).
- Partial drain: advance head only (one), then excess/count (two).
- Old INHIBITOR: caller SYSTEM takes the system branch before the user inhibition rejection. Empty calldata updates/unlocks according to concrete control flow; nonempty sets inhibitor. No input-enabled premise is needed.
- Empty versus nonempty calldata changes only the bounded control update. It does not copy arbitrary calldata into memory on SYSTEM path. Mandatory source dispatch is empty; nonempty scheduling remains an explicit policy choice.
- Arbitrary original/current control values change storage pricing/refunds but are covered by per-write bounds. For protocol queue interpretation use journal invariants; termination/resource path should aim to admit arbitrary256-bit slots, as the pinned path does.

## Precise producer interfaces (proposed, NOT present Lean definitions)

1. `system_entry`: actual checked dispatcher with exact installed runtime lookup produces an actual reference frame whose code/caller/value/static flag/stack/memory/gas meter match the constructor above, execution gas30M and reservoir16*STORAGE_SET, zero spill. No successful result premise.
2. `system_trace_shape kind`: from that frame, construct its actual gas-erased instruction path ending RETURN; <=9000/900 instructions, <=4 SSTORE occurrences, no child/copy/log operations, memory spans<=11776/1088, correct stack arity/jumps and code bounds. Include every inhibition/data/head-update branch. This needs actual reference decoding/operand proofs and cannot be a premise containing the desired successful call result.
3. `system_meter_prefix`: induct over that same path, derive exact reference charges with original/current slot reads and warmth, cumulative execution<=N*2100+10000*S+C(maxMem), reservoir draw<=S*97920, and sentry payable. Use source charge-before-state order. Derive no OOG and no static/stack/jump exception.
4. `system_completes`: combine1–3 to produce actual `process_top_level`/checked-call success and output for each pinned runtime. Then transport protected output/storage/log observables; this is separate from safety-direction shadow-gas runtime transport.
5. `mandatory_pair`: root composes sequential actual Deposit and Exit checked calls with exact empty-data policy, state-diff incorporation and request extraction. Current memo does not prove this source-to-Lean adapter or adopt the fork.

No concrete counterexample was found under exact installed bytes, SYSTEM caller, write permission, actual grants and finite representable input. This is not a formal nonfailure result. Counterexamples to stronger formulations are immediate but not newly executed here: merely nonempty arbitrary code can loop/OOG and checked dispatcher raises InvalidBlock; non-SYSTEM calls can enter the fee/user path; static calls can reject SSTORE. Huge host-level calldata construction or runtime-patched gas constants fall outside the exact pinned constructor/constants and need explicit exclusions rather than being silently covered. Cached comments permit future repricing; the numeric result binds the exact listed constants, not arbitrary patches.
