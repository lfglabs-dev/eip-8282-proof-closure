# Remaining CALLDATACOPY / LOG0 local view adapters

Read-only proposal, 2026-09-10. No Lean source or build changed.

## Common actual boundary

Use the existing running view and the same boundary as StorageViewAction:

- `hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre`
- `decoded : decodeAt pre = (CALLDATACOPY, none)` or `(LOG0, none)`
- actual `hz : Z ... (decodeAt pre).1 pre = .ok (mid, cost)`
- actual `hs : StepOk (fuel+1) cost (decodeAt pre) mid post`
- `related : ReferenceRuntimeView.Related parent v pre`
- local resource parameters `post.activeWords.toNat <= cap` and `32*cap < 2^System.Platform.numBits`

The public local theorem derives its pop witnesses from ReferenceAcceptedStack.pop3/pop2 and its natural PC fit from actual At. Exact raw result identification must use `stepPre cost (zMid pre op)`. RuntimeMemoryCharges.accepted_expansion gives the exact post word count, not merely monotonicity. RuntimeMemoryMonotone.accepted gives each positive destination span, and then the host bounds. Zero length needs no bound on offset. Calldata source offset must remain arbitrary UInt256.

Those capacity/host premises are local adapter parameters. Whole user-path transport must derive them from actual user executions; the existing SYSTEM capacities do not cover arbitrary user paths by declaration. CALLDATACOPY and LOG0 remain excluded from SystemPathBudget.Allowed.

## COPY action and genuinely missing byte-array lemmas

Define a new literal action (no changes to existing View):

```
copyMemory v dst src len :=
  if len.toNat = 0 then v.memory else
    splice v.memory dst.toNat (buffer v.env.calldata src.toNat len.toNat)
      (32 * M (words v) dst.toNat len.toNat)
copyAction v dst src len rest :=
  { v with pc := v.pc+1, stack := rest, memory := copyMemory ... }
```

The explicit zero branch avoids applying the existing `store_view` lemma outside its positive-length premise. Alternatively, prove the zero-length splice is the original buffer using the input rounded-memory size and `M ... 0 = words v`. The source's zero-length memory_write is a no-op, even at an arbitrary large destination; no destination-range or extension premise should be imposed in this branch.

Proposed theorem:

```
copy hz hs related hat decoded postcap host :
  exists dst src len rest,
    pre.stack.pop3 = some (rest,dst,src,len) /\
    v.stack = dst::src::len::rest /\
    Related parent (copyAction v dst src len rest) post
```

Reuse exact SymExec.step_CALLDATACOPY (lines 1004-1011), SharedState.calldatacopy, and ReferenceMemoryWrite.write_byte. The missing work is:

1. Prove pointwise equivalence between actual `ByteArray.write calldata src pinnedMemory dst len` and writing the source-padded `buffer calldata src len` at source offset zero into eager extended memory. Use write_byte plus buffer_byte at index `i-dst` inside the destination interval. **Do not** try to use `ReferenceMemoryWrite.congr` with a false global `Same calldata (buffer calldata src len)` premise; the latter is shifted/truncated.
2. Prove actual write physical size is at most `max oldMemory.size (dst+len)` under the derived padding bounds, for arbitrary source offset and source exhaustion. Existing Memory.size_write specializes source offset zero and exact source length, so it does not directly cover COPY. Only an upper bound is needed for coherence. The pinned out-of-range-source branch can leave physical memory shorter than the source eager expansion; equality of physical arrays/sizes is not the desired invariant.
3. Compose the byte relation, exact M, eager size and actual physical-size bound into ReferenceMemoryOperations.Related; carry storage/owner/env/all-topic logs by actual unchanged state fields.

Pinned source: `.lake/packages/evmyul/EvmYul/Wheels.lean:347-369` contains the actual zero/source-exhausted/in-range write branches. Cached EL environment.py:206-243 first pops destination/source/length, charges base+per-word+memory expansion, eagerly extends memory, reads buffer_read(call_data,source,length), and memory_write. This body is in `/tmp/eip-reference-memory-control/vm__instructions__environment.py`, SHA256 `8c57bd699b99ff8b4d8e41e6a9c89cd1a03dda8160bf1d6dffe091932ec03657`.

## LOG0 action and exact ordered prefix

Define:

```
logMemory v off len := returnMemory v off len
payload v off len := (logMemory v off len).extract off.toNat (off.toNat+len.toNat)
logAction v off len rest :=
  { v with pc := v.pc+1, stack := rest,
      memory := logMemory v off len,
      logs := v.logs ++ [ { address := v.env.codeOwner, topics := #[], data := payload ... } ] }
```

Record construction must use actual LogEntry field names; notation here describes the literal fields. ReferenceReturnSlice.output_eq_extract already equates the post-extension unpadded slice to `buffer v.memory off len` for every offset/length, including zero. Although named for RETURN, this byte-array identity is equally applicable to LOG0's identical M expansion.

Proposed theorem:

```
log0 hz hs related hat decoded postcap host :
  exists off len rest,
    pre.stack.pop2 = some (rest,off,len) /\
    v.stack = off::len::rest /\
    v.env.perm = true /\
    Related parent (logAction v off len rest) post
```

- Derive permission from the actual LOG0 static guard in Z, not from an assumed successful source log.
- SymExec.step_LOG0 (1013-1021) identifies actual SharedState.logOp: actual codeOwner, empty topics, memory.readWithPadding payload, logSeries.push, exact M.
- Derive payload host bounds from positive span and post cap; zero length imposes no offset bound.
- Reuse ReturnView-style eager extension coherence/size/bytes proof. Current storage, owner and environment are unchanged.
- Use ProtectedLogFrame.push_self to show the all-topics address projection preserves its full existing prefix and appends exactly this entry, in order. Never filter by topic count, payload authenticity, or an invented identifier.

The exact EL LOG opcode body was not present in the two inspected local source-cache directories. The cached instruction dispatcher identifies `log_instructions.log0`, and the prior interface memo points to pinned `vm/instructions/log.py`. Before claiming exact source static/pop/charge/log ordering, locate the durable archived body or retrieve that exact pinned official source; do not infer it from the synthetic EIP-7708 transfer-log helper. This is a source-acquisition/binding obligation, not a defect in the pinned LOG0 theorem.

## Pricing and whole-execution boundary

These effect adapters alone do not establish charged source execution. Extend the source price layer separately for COPY base + per-word length and LOG0 base + per-byte payload, plus the same actual M cost difference. Use exact cached source constants/order, rather than extending the SYSTEM ordinary <=2100 table to these excluded operations. Bind source warmth/original/current/new and charge events to actual view occurrences when combining effects with payment.

The final full-runtime action union also needs STOP/REVERT terminal cases and user-path resource producers. Current RETURN/decoder and SYSTEM whole-trace proofs do not by themselves assert those outcomes or foreign-code equivalence.
