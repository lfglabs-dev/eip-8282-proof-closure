# Exact runtime memory/control transport

Read-only audit; no Lean source edits or compiler run. Full immutable bodies, URLs and SHA256 are in `/tmp/eip-reference-memory-control/source-archive.json`; primary Git tree discovery is retained in `tree.json`. Reference commit: `0cc100eb190b64b23baba72dac0165652eaec252`. Confirmed module names: instructions/control_flow.py, memory.py, environment.py, stack.py, system.py; helpers vm/memory.py, vm/stack.py, vm/runtime.py, vm/gas.py, vm/interpreter.py. Existing cached interpreter/gas/opcode table bodies were reused. Source-to-formalization remains audited/trusted until an actual Python adapter exists.

## Findings governing the interface

1. **Generic PUSH decoder parity is false.** Reference push_n reads buffer_read(code,pc+1,n), RIGHT-padding zeros; pinned decode uses extract' and converts only available bytes. PUSH2 followed by byte01 yields256 in reference and1 in pinned. Prove complete immediate spans for the fixed images; do not assert arbitrary-code decoder equivalence.

2. Reference jump scanning handles Amsterdam DUPN/SWAPN/EXCHANGE immediates, including invalid-immediate exceptions to skipping. Pinned argOnNBytesOfInstr lacks these and parses unrecognized bytes as INVALID. Pinned parseInstr is total Some, so D_J's nominal none branch is not itself a divergence for bytes. Scanner parity must exclude extended-immediate opcodes at *linear instruction boundaries*, including unreachable suffixes, not merely executed sites.

3. Diagnostic scans of both main images, both ctor images and the69-byte factory find no truncated PUSH and no0xe6/0xe7/0xe8 at linear boundaries. Jumpdest counts are16 for each main/ctor image,1 for factory. `/tmp/eip-reference-memory-control/scan-diagnostic.json` is a Python diagnostic, NOT a theorem. Existing RuntimeOpcodeScope supplies two runtime site grammars; constructors/factory need corresponding finite facts.

4. **Raw memory arrays differ.** Reference physically zero-extends to multiples of32 before accesses. Pinned memory remains a sparse byte prefix; activeWords records rounded capacity. MSTORE8 at0 produces physical length1 versus32. CALLDATACOPY beyond calldata may leave pinned physical bytes unchanged while increasing activeWords. Compare zero-extended observations, not ByteArray equality.

5. Actual host conversions matter: ByteArray.write casts gap padding to USize; readWithPadding panics for length>=2^64. These cannot be erased by a gas-erased relation. On64-bit platforms readBytes supports huge calldata source offsets through its list fallback for start>=2^64. On32-bit platforms its fast-path test<2^64 is insufficient: require a64-bit platform fact or tighter per-call conversion premises.

6. Reference running PC is a natural Uint. JUMP assigns the first popped word; JUMPI increments only when the second popped word is zero, otherwise validates and assigns destination. Pinned Z checks destination validity before the raw jump step. Relate actual Z+StepOk, not unchecked raw jump helpers, to successful reference execution.

7. **Terminal internal PCs differ.** Reference STOP increments PC; pinned STOP leaves it. Reference RETURN leaves PC; pinned binaryMachineStateOp increments it and pops two arguments. Reference EOF stops without an instruction; pinned decodeAt defaults to STOP, consuming another fuel unit. Use a separate terminal relation comparing output/world/substate/status, not terminal PC, running flag, scratch returnData or counters. Fuel adequacy must cover EOF STOP.

## Minimal proposed relation and theorem shapes

Use a source-transcribed successful *instruction relation*, not another whole interpreter. RefRunning contains natural PC, Python-order List UInt256 stack, code/calldata/memory bytes and the environmental identities actually consumed. Keep resource/control-error relations separate.

```lean
def byteAt (b : ByteArray) (i : Nat) : UInt8 := b[i]?.getD 0
structure MemoryRel (r : ByteArray) (a : MachineState) : Prop where
  rounded_size : r.size = 32 * a.activeWords.toNat
  physical_le : a.memory.size <= r.size
  contents : forall i, i < r.size -> r[i]?.getD 0 = byteAt a.memory i

structure RunningRel (r : RefRunning) (a : EVM.State) : Prop where
  pc : r.pc = a.pc.toNat
  stack : r.stack.reverse = a.stack
  stack_limit : r.stack.length <= 1024
  code : r.code = a.executionEnv.code
  calldata : r.calldata = a.executionEnv.calldata
  memory : MemoryRel r.memory a.toMachineState
  -- explicit caller/codeOwner/value bindings for environmental opcodes

theorem instruction_parity
  (related : RunningRel r pre)
  (site : ExactImageSite image r.pc op arg)
  (numeric : AccessBounds r op)
  (reference_step : RefInstruction r op r')
  (accepted : Z jumps op pre = .ok (mid,cost))
  (executed : StepOk fuel cost (op,arg) mid post) :
  RunningRel r' post

-- RETURN/REVERT/STOP/EOF have a separate output/world relation.
theorem halt_output_parity ... : referenceOutput = actualOutput
```

These are design signatures, not declarations already proved. ExactImageSite must be *derived* by actual entry and checked jump/fallthrough induction, not assumed independently at every iteration. It supplies matching decode/immediate, complete immediate span and valid destinations. RuntimeExecutionScope is a pinned-side producer; reference-side preservation still needs proof.

## Necessary numeric conversion bounds

- Nonhalting increment: pc+1+width<2^256. Fixed-image boundary induction gives the much stronger pc<=image.size+32. Valid jumps are inside code. CALLDATASIZE/CODESIZE need actual byte length<2^256.
- Memory observation: 32*activeWords.toNat<2^System.Platform.numBits, and the same after expansion. This makes capacity multiplication and MSIZE exact. Derive activeWords from actual M; do not assume metadata correctness after every step.
- Positive memory accesses: destination+length fits host width; length<2^64 for readWithPadding. Its extract path additionally needs addr+min(length,physicalMemory.size) to fit when addr<physicalMemory.size. A stronger uniform envelope is acceptable only with an explicit producer. Zero-length accesses expand nothing and should not acquire artificial destination bounds.
- Keep calldata source offsets full U256. Source>=data.size gives zeros; platform64 readBytes falls back for offsets>=2^64, and write checks source>=size before using source indices. Avoid a gratuitous small-source-offset assumption. Host-width facts and actual source/destination branch analyses must justify the casts.
- MSTORE needs exact32-byte big-endian representation; use existing XiTransport/Memory conversion lemmas. MSTORE8 needs lowbyte(v)=UInt8.ofNat v.toNat; Nat mask/mod parity supplies this.

## Concrete instruction pairing

Reference CALldataload uses buffer_read(data,offset,32) and from_be_bytes; pinned State.calldataload uses readBytes then uInt256OfByteArray. CALLDATASIZE binds actual data lengths. CALLDATACOPY pops destination,source,size, expands memory using natural destination+size, obtains right-zero-padded source bytes and writes them. Pinned ByteArray.write may omit new all-zero suffixes, so its result must be observed through activeWords.

Reference MSTORE pops destination then a32-byte value; MSTORE8 masks the lowbyte. Both reference operations extend before writing; pinned MachineState.mstore/mstore8 write a physical prefix then set M-derived activeWords. Reference RETURN pops offset/size, expands then slices output; pinned evmReturn uses readWithPadding and H_return, followed by actual halting H projection. Preserve output, not terminal machine equality.

Reference vm/stack.py pops the list end, pushes by append and rejects push when length==1024. Pinned head-stack reversal is already formalized in ReferenceWordOps. For successful pushes prove initial/updated stack length conditions; exceptional branch order is outside the first gas-erased theorem.

## Proposed proof ownership split

1. ReferenceDecodeSites: exact image-wide scanner and complete PUSH spans; finite jumps-set equality for main/ctor/factory. Keep malformed PUSH counterexample outside scope.
2. ReferenceMemoryView: MemoryRel, zero-extension normalization, actual ByteArray.write overlay parity, including size0/source-out-of-range. Existing write_eq_of_fits/grows, readWithPadding and store readback lemmas are useful; retain their host-width premises.
3. ReferenceControlStep: PUSH/POP/DUP/SWAP/JUMP/JUMPI and ordinary PC updates, consuming actual Z+StepOk and exact-site facts.
4. ReferenceReadReturn: CALLDATASIZE/LOAD/COPY and RETURN/REVERT output through MemoryRel; separate terminal relation handles STOP/EOF and terminal PC differences.
5. Root composes actual trace/resource producers and independent storage/log/value instruction relations. No local table parity replaces source-to-formalization transport.

RuntimeOpcodeScope's union also includes SLOAD/SSTORE/LOG0/CALLER/CALLVALUE; this lane alone cannot close their world/log effects. Constructor/factory add CODECOPY and CREATE2: CODECOPY shares buffer/copy arithmetic; CREATE2 keeps root child/wrapper composition. Archived system/environment bodies support later consumers without claiming their parity complete.

## Foreign-code transport boundary

The kernel-checked truncated PUSH2 01 divergence also prevents a blanket claim that arbitrary foreign bytecode has the same execution or final world in the pinned evaluator and the reference EL. The five fixed image decoder facts support only their own protected runtimes, constructors, and factory. A final reference-history bridge must derive protected-call occurrences, foreign-world framing and the credit ledger from actual reference semantics (or provide a separately justified restricted foreign-code relation). It cannot infer those facts by replaying arbitrary foreign execution in the pinned evaluator. Whole-history and generic trace transport remain open.
