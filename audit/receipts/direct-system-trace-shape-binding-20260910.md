> Arithmetic correction confirmed by root kernel check: C(369)=1107+floor(136161/512)=1107+265=1372, not1373. Correct Deposit envelope18,941,372; the touched-span correction remains11784. C(35)=107 and C(400)=1512 are unchanged. Prior correction below is retained as history and superseded numerically where it says1373.

# Actual SYSTEM trace annotations: producer interface

Faraday, 2026-09-10; read-only existing-proof analysis, no builds or Lean edits. Parent owns reference replay/gas/global composition.

## Concrete correction: memory RETURN length is not memory high-water

Deposit `EntryReach/Deposit.lean:832-856` writeItem uses six full MSTOREs at offsets184*i +0,32,64,96,128,160, plus eight byte stores at80..87. For i=63, last MSTORE ends184*63+192=**11,784**, although RETURN publishes only64*184=11,776. Required allocation rounds to11,808 =369 words, C=3*369+369²//512=**1,373**.

Exit `EntryReach/Exit.lean:675-685` writes full32-byte words at68*i +0,20,52. Last i=15 touches through68*15+84=**1,104**, although RETURN publishes1,088. Allocation rounds to1,120=35 words, C=**107**.

These are direct counterexamples to the previously proposed11776/1088 touched-span bounds, visible in exact source definitions without executing code. `item_offsets` already encodes these facts: Deposit870-903 allows endpoint+192; Exit688-704 explicitly mentions1104. Conservative existing active-word bounds400/40 cost1512/123 are also valid and easier to reuse initially. Corrected reference numeric envelopes with9,000/900 instructions and4writes are18,941,373 /1,930,107, still far below30M. Earlier resource memo now carries this correction; its original smaller memory figures are retained only as superseded investigation history.

## What the existing propositions do and do not retain

`EvmYul/EVM/Proof/Execution.lean:295-312` XStepAt is actual Z success +actual StepOk +nonhalting H. XRuns354-361 indexes an actual List Labelled=(fuel,cost,instruction), with cons label exactly decodeAt pre. `XRuns.length`375-382 gives trace.length+remaining=initialFuel, trans386 onward concatenates traces, head_step389 onward exposes actual predecessor/next state and decoded instruction. Each cons witness contains intermediate states in Prop, though labels themselves do not store memory/PC/stack. Use existence/relations in Prop; no computed-data elimination from proof terms.

`SymExec.Reaches`1072 is forall residual fuel, exists actual XRuns. `EntryReach/Path.lean:211-241` ReachesLe is exists actual count<=K with Reaches; Ends pairs ReachesLe with actual Halt. Thus the nonhalting trace length bound follows generically NOW, and adding terminal RETURN costs one label. Deposit system_returns supplies Ends8500; Exit supplies Ends800. Bounds8501/801 for complete instruction lists are therefore directly extractable from those actual endpoints at chosen enough fuel (9000/900 merely convenient loose limits). Do not use ReachesLe.xRuns_of_fuel alone if needing numeric trace bound: retain its underlying k and residual arithmetic, or strengthen the new extraction theorem to retain length<=K.

Ends does NOT expose SSTORE count, permitted opcode subset per region, intermediate memory spans or program phase. Endpoint storage equality cannot imply <=4 writes: extra overwritten/reverted writes could give the same final state. Likewise final RETURN byte length does not bound touched memory, as the concrete correction shows. Proof irrelevance does not permit inspecting an opaque theorem proof to recover the block sequence used by its author. A general lemma cannot manufacture arbitrary trace annotations solely from unannotated Reaches endpoints.

## Small reusable generic layer

New file proposal `SystemTraceAnnotations.lean`, importing existing execution/path primitives:

- `Edge` is a record of pre, charged-mid, post, fuel, cost and decoded instruction with actual XStepAt evidence. `RunsWith`/`AnnotatedXRuns` mirrors XRuns in Prop while indexing a list of edge summaries or stating all-step predicates. Provide erasure to XRuns and existential enrichment of any XRuns; concatenation and one-step constructors retain the SAME execution.
- `Weight op := if op=SSTORE then1 else0`; accumulated stores =sum labels' weights. Other additive counters can use arbitrary Nat weight. Complete annotations append terminal Halt edge separately, so counts and memory include RETURN.
- `MemorySpan pre op` reads actual stack operands: MSTORE offset+32, MSTORE8 offset+1, RETURN offset+length (zero length gives0). No hypothetical offsets. `NoUserOps` excludes CALL/CREATE family, LOG family, CALLDATACOPY; stronger phase-specific instruction set excludes user fee path.
- Generic composition `annotated_trans`, bound weakening, `ReachesLe` erasure, loop iteration concatenation and count arithmetic. Generic state invariant propagation over actual XStepAt establishes At image and actual opcode scope from RuntimeExecutionScope.entry_at/accepted_next.
- Actual no-child property can already be derived for complete runtime executions with RuntimeExecutionScope.selected_none/cert_local and RuntimeThetaExclusion. This alone does NOT eliminate runtime user LOG0/CALLDATACOPY: allowedOps includes them. SYSTEM phase requires stronger control-path witness.

No bytecode rerun or new interpreter is needed; the annotation consumes actual Z/StepOk evidence already present in leaf path constructors.

## Precise path composition to retain

For BOTH kinds lift the same operational decomposition:

1. system_prefix: at most25 nonhalting steps, no stores/memory/log/copy/child operations, actual SYSTEM jump and head/tail/count operands.
2. drain_body: Deposit at most130, Exit42; **zero SSTORE**, zero usercopy/log/children; retains all actual SLOAD/MSTORE/MSTORE8 operations and item_offsets hi. Use memory offset i<=63/15 and existing typed arithmetic lemmas to prove spans<=11784/1104. The storage base may wrap but output offset does not.
3. drain_loop: induct m with i+m=count; existing code calls body then IH at i+1. Carry storecount0 and max memory bound through append; length130*m+6 /42*m+6. Base case executes exact exit-test branch; no store/memory. Existing Touched relation is about state read/access effects, not opcode-count evidence; do not treat it as zero-store evidence by itself.
4. update_head: full/empty branch contains exactly two SSTOREs to2,3; partial contains one to2. No loop back into this phase. Bound2, memory unchanged.
5. update_excess: every inhibition/empty/nonempty/update branch ends with exactly two SSTOREs to0,1, no loops or memory writes. Keep all branches; no enabled assumption. Bound2.
6. terminal RETURN: actual Halt leaf, no storage writes/children/log; read span length<=11776/1088 is less than staging high-water. Account for terminal edge in full count.

Compose0+0+2+2 stores<=4. All allowed memory writes occur in body. Deposit system_returns proof assembles prefix+loop<=8351 then head20 and update36<=8407, padded to8500. Exit proof assembles prefix+loop<=703 and corresponding bounded head/update, padded to800. These are real path-length proofs; exported annotated variants can retain the same generous public fuel bound.

## Smallest honest source change plan

First add generic annotation types/combinators in new file; no existing theorem statement needs removal. For reusable leaf `block_step`, `reach_sload`, `reach_mstore`, `reach_mstore8`, `reach_sstore`, jump and halt lemmas, add annotated companion forms where their existing proofs already construct actual one-step/straight-block evidence. A generic block-lift from the actual symBlock checked sites can retain opcode list and abstract state predicate through its induction. Export old theorem as erasure if source refactoring is authorized; this avoids maintaining two operational proofs.

Then strengthen (or add companions for) system_prefix, drain_body, drain_loop, update_head, update_excess, system_returns in EntryReach Deposit/Exit. The loop/head/excess companions retain existing case/induction bodies with annotated combinators; no new premise supplying the annotation. These modules are large/frozen, so root must allocate explicit ownership before any edits. A new file alone can prove length extraction immediately and possibly memory monotonicity; it cannot extract <=4stores from opaque existing path signatures without either (a) an independently proved reachable phase invariant or (b) exposing the construction through these annotated companion proofs.

Alternative no-shared-edit route: new phase invariant over actual PC/stack and a bounded storage-write potential, preserved by each accepted step. Every SSTORE decreases potential, every other transition does not increase it; initial potential4. The drain-loop SCC has potential constant and no stores. This avoids old source edits but duplicates detailed reachability/stack control proof; static PC lookup alone is insufficient because dynamic jump operands must be bound to real reachable stacks. It is likely more work than companion annotation.

Memory alone may be recovered more generically: prove memory length monotone for actual no-child runtime ordinary steps and each touched span<=post.memory.size; prove exact endpoint drainMem.size bound by writeItem recursion from empty memory. Then every earlier memory span<=final size by XRuns suffix composition. This is a useful new-file producer requiring no trace postcondition. It must use full written lengths192/84 (or400/40 word bounds), and prove no shrinking through all runtime memory/copy op definitions. It does not recover store count or exclusion of user operations.

## Reference replay interface

`system_pinned_trace` from independent SYSTEM/code/owner/permission and chosen sufficient pinned shadow gas/fuel produces actual complete annotated trace with bounds, not a desired reference-success premise. Later reference transport must replay those same operands/control states and prove reference source instruction effects/charges. Since neither runtime executes GAS, different gas meters do not directly change stack calculations, but accepted source sentries, static checks, memory bounds and original/current gas classifications still need their own proofs. Root's ReferenceStorageGas and future meter-prefix induction consume per-edge real SSTORE inputs. A pinned trace alone is not an actual reference instruction trace or a source liveness theorem.

Recommendation: root first approve corrected memory constants and generic length/annotation interface; then allocate annotated leaf/path companions separately. Do not assert the requested stronger shape solely by wrapping SystemProgress.pinned or Ends8500/800.
