# Independent continuation reviews

# Independent current-source review

Worktree: /Users/thomas/work/eip-8282/direct-closure-implementation
Review date: 2026-09-09. Source-hash review; final commit review remains separate.

## GetterCall.lean — CLEAN

SHA256: 3aa3a91a8976c655a2309fde4468307b702f2c28d0a8c8f32ff746f1daf2eb12

Read the complete source and checked MessageCall/CallBridge against the actual pinned EVMYulLean Θ implementation. The codeCall is built from Θ's actual transferred world and environment, with the runtime bytes pinned and the fuel offset explicit. Zero actual value and apparentValue = value are required in the public getters. The proof preserves all account lookups through the recipient-credit/sender-debit sequence, including caller = target and absent accounts. It does not incorrectly require structural equality of TreeMaps or a LawfulBEq instance for Account. Settlement handles both branches of the actual empty-world Boolean fallback. Exact 32-byte quote output and unchanged logs are derived from the concrete getter endpoint.

No circular successful-result or model-agreement premise appears in the public getter theorems. quoteWithin completion and gas/interpreter-fuel inequalities are explicit sufficient preconditions. Thus these are conditional success theorems, not a proof every state admits a terminating affordable quote. They do not prove installed-code identity, protocol admission, or transaction gas accounting. These are honest scope limits, not defects in the stated theorems.

## AppendStorage.lean — CLEAN

SHA256: 06e1f4e9e0c0f447c52eff02f853b9f15b511f58b944e8ecb21745e4e54c23eb

Read the complete source and checked the concrete append-state bridge, storage algebra and calldata-word decoding. The expected map is built independently from entry storage, the call source/calldata and ordered logical writes; it does not assume the final operational state. The View induction derives this map from the real sstore/touch/log helpers, and the final theorems connect it to the actual Xi success world. HasOwner prevents the semantics' absent-account sstore no-op from being mistaken for a write. The storage algebra handles updateStorage's zero-value erasure correctly through lookup-with-default, rather than assuming every update is an insert.

AppendFits explicitly rules out record-key/count/tail wraparound and control-slot aliasing; the proof establishes physical record words, exact natural count/tail increments, unchanged excess/head, and all remaining owner storage slots unchanged. recordWord takes exit source from the actual caller field; calldataWord uses the same independently defined big-endian zero-padded load semantics as CALLDATALOAD. There is no assumed encoding/post-world equality or Model invariant.

The public append theorems are Xi-level results, with explicit operational fee completion, gas/fuel, owner, payment branch and no-wrap premises. They do not alone establish actual Θ value transfer, mathematical nonwrapping payment, full byte-level log authenticity, prior FIFO well-formedness, or reachability of AppendFits. No claim to those wider properties should be attached to these modules in isolation.

## Evidence

Existing standalone compiler logs inspected: /tmp/eip-GetterCall-compile.log and /tmp/eip-AppendStorage-local-compile.log. Their printed public theorem/helper axiom sets contain only propext, Classical.choice and Quot.sound. No build or proof-file mutation was performed during this review. Both source hashes were rechecked unchanged at the end of review.

## Exact-commit binding and ExitDrain review — CLEAN

Exact commit: 5e9f63f21cc347ccb2ae7b7d7d8d0b5505098ef3.
The two source hashes above were compared byte-for-byte against their git-show objects at this commit and match. ExitDrain and the integration/documentation files below also match their exact-commit objects.

ExitDrain.lean SHA256: fd854f4e0b223e36c28554392ecf026d37e28340de3adf95b8b0269ddd9c6978

Read the complete ExitDrain source and checked its concrete writeItem/drainMem/base definitions, CommittedSystem output binding, the actual Θ settlement, memory overwrite/prefix lemmas, and the pure byte encoder definitions. The independent encoding is 20 bytes of stored source, 32 bytes of the first pubkey word, and the first 16 bytes of the second pubkey word. The 160-bit source-width premise justifies the shift-left-by-96 encoder identity without word truncation. The underlying toBeBytes helper is a pure fixed-width digit encoder; no abstract Model postcondition is assumed.

For record i, the actual stores begin at 68*i, 68*i+20 and 68*i+52. They end at 68*i+84; bytes [68*i+68, 68*i+84) are the final half-word overhang. The next iteration overwrites that overhang, while the first 68*i bytes remain intact. The induction explicitly proves both memory length (zero for no records, otherwise 68*n+16) and the correct 68*n-byte prefix. The final return excludes the overhang, including at n=0. The cap <=16 proves all small memory-index multiplications and additions are nonwrapping; no unchecked index convention is used.

exitData_bytes binds that prefix to the actual system endpoint's return buffer, and exit_system_fifo composes the same buffer and independent control/storage result through Θ using the actual transferred world and actual target. Owner existence is an input-state premise; absence of the success empty-world fallback is derived through the previously reviewed CommittedSystem/WorldNonempty proofs, not assumed as a postcondition.

The FIFO order remains explicitly word-indexed: base = 4 + 3*(HEAD+i) in UInt256 arithmetic, and count is the cap of modular TAIL-HEAD. This result does not prove HEAD<=TAIL, no storage-address wraparound, source-width preservation through histories, or consistency with an initialized queue of submitted records. These restrictions are disclosed in source/docs. The theorem is a sufficient-resource SYSTEM result, not an arbitrary-gas success inversion. No blocking correctness or scope finding.

Compiler evidence inspected: /tmp/eip-ExitDrain-6.log; drain_bytes and exit_system_fifo report only propext, Classical.choice and Quot.sound. No compilation was performed by this review.

## Exact-commit integration and documentation delta — CLEAN

Reviewed the façade and Trust additions and the complete DIRECT-CLOSURE.md delta at the exact commit above. They retain the open status of all three public IDs, distinguish standalone compilation from the pending full-build receipt, and disclose the source-width/local-bounds/quote-completion premises. No new declaration promotes the conditional components into unconditional public guarantees. The coverage table keeps historical gaps visible (one row could be updated to say AppendStorage supplies the local no-alias result, but its existing conservative wording is not an overclaim).

SHA256s:
- Eip8282/Audit/Integrator.lean: 6222396d2d48d82645d4eb7e5936018d615b5b7b0ac57077168c99de33976f9c
- Eip8282/Audit/Trust.lean: 7097fb03d2b6a12679c426c6dba275374cf9fd39d39eb285c9b07a0d32a42ea9
- audit/DIRECT-CLOSURE.md: b65fe330c45be85cbc14553fa064d7f78773c51bc4ac1ea5e3d326b55bc9df5a

Review independence: ExitRecord was authored by this reviewer and is intentionally not certified here as independently reviewed. This report independently certifies GetterCall, AppendStorage, ExitDrain and the named integration/documentation delta only. A full make-check receipt remains the parent integrator's responsibility.


# Independent source review — CLEAN within stated scope

Reviewed ExitRecord.lean SHA-256 `904013bc2402c018b25ee30c70c1e37b187aff32350a389596499af6dd7b4027` and FeeQuoteGetter.lean at integrated commit `0ccf3d3` (source SHA-256 `c385b9680ae160c0094a968795a9b0e4d5de244bbf6819469700173f24e9479c`). No proof sources edited.

## ExitRecord

The independent record is a fixed-width 20-byte big-endian encoding of the immediate caller followed by all 48 supplied pubkey bytes. The address bound is inherent in AccountAddress. The shift proof establishes the exact 96-bit alignment without wrap; the prefix proof checks each byte using the base-256 digit lemma. CALLDATACOPY staging preserves the first 20 address bytes, overwrites the remaining 12 bytes of the word, and grows the buffer to exactly 68 bytes. The final slice is the complete independently specified record.

`authentic_log` refines the full log series, including its prior prefix, one appended anonymous log, and the actual code-owner emitter. `submission_receipt` derives an actual successful Xi result via EndpointState.exit_append_result and retains both the independent log condition and every other-account lookup. Existing AppendSpec, EndpointState, Exit.stagedMem/appendedSt, ByteArray write/slice lemmas, fixed-width byte encoding definitions, and the pinned word/step semantics were inspected. No circular authentic-record premise or unchecked signature claim was found.

Compilation receipt `/tmp/eip-ExitRecord-compile4.log` contains standard axioms only. This review did not recompile ExitRecord. The theorem still explicitly requires loop completion, payment, permission and gas/fuel bounds; it is a sufficient-success receipt theorem, not inversion of every successful call. It does not yet assert FIFO/storage record correspondence or Theta settlement/value-transfer behavior. Those are separate composition obligations.

## FeeQuoteGetter

The integrated module is unchanged from the reviewed remote d191d4f. Initial `(out,acc,i)=(0,17,1)` agrees with FeeLoopEnds. Existing path proofs supply the actual loop/prefix/getter endpoints and the returned remaining-gas inequality. Bounds 87*n+25, 87*n+4400 and 87*n+4500 correspond to loop, prefix and getter respectively; step bounds 24*n+7, 24*n+60 and 24*n+80 agree with dependencies. The redundant QuoteCompletes premise beside quoteWithin is harmless. The module covers deposits only and makes its conditional-success scope explicit.

Standalone compilation succeeded without warnings; `/tmp/eip-FeeQuoteGetter-review-compile.log` records only propext, Classical.choice and Quot.sound.

## Next bounded inversion theorem

Do not try to invert the existing sufficient-gas fee_loop theorem: 87*n+25 is an upper bound, so arbitrary successful executions should not have to satisfy a guessed sufficient bound. Instead invert the actual finite X execution.

First expose one-step success elimination from the pinned Proof.Execution definitions: when decodeAt pre=(op,arg), Halting op=false and X (fuel+1) vj pre=ok(success final out), derive actual mid/cost/post with Z accepted, StepOk fuel cost (op,arg) mid post, and X fuel vj post=the same success. Z/step errors contradict the success premise; H is none from the nonhalting opcode. No gas, completion or post-agreement premise is needed.

The concrete next theorem is `deposit_fee_iteration_of_success`: from the exact pinned fee-head state at PC 100, nonzero accumulator and an arbitrary successful X fuel result, extract the actual next fee-head state after 24 instructions, with `(out,acc,i)` changed to `(acc+out, X*acc/(i*17), 1+i)`, the same frame/memory and the same eventual success at `fuel-24`; prove `24 <= fuel`. This is a finite 24-instruction inversion task using the existing decoded blocks and word step identities, without sufficient-gas hypotheses. Repeat for exit PC 99.

Strong induction on the successful run's fuel then yields `exists n o i, feeExit numerator n initialOut initialAcc initialI = some (o,i)`: acc=0 is the immediate recurrence base; acc!=0 uses the extracted next iteration and strictly smaller fuel. This proves completion at the loop head without assuming it. Entry dispatch/prefix inversion and suffix price/validation inversion remain separate bounded tasks before a complete-call necessity theorem can be claimed.


