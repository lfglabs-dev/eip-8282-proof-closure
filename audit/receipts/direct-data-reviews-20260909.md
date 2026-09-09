# Independent direct-data reviews

Independent source review — 2026-09-09

Verdict: CLEAN for the frozen sources and their stated sufficient-success scope.
No source edits or builds performed for this review.

SHA256:
- CommittedAppend.lean: 1bae1c578fb56ca68e7a1cd3cb6c2c6e7ac9719e55748e5d1fd2900c86dc7b5b
- QueueArithmetic.lean: 95dd375417bcf6ddd2fa2bf3326807f1db7080e9ddfb0f75c4f2d1f7aa925da9
- SubmissionCall.lean: face1db4310075322e020321797e520da7068221633495912bdd192b0ff1e7b8

Checked full sources and relevant dependencies: AppendStorage, CommittedSystem, ExitDrain, CallBridge, MessageCall, FeeQuote, SystemSpec slot formulas, Deposit fee recurrence/paths, and pinned EVMYulLean Θ. EndpointState, AppendSpec, ExitRecord, UInt256 transport and pinned Ξ were also reviewed in prior exact-source reviews in this session. Inspected successful standalone receipts /tmp/eip-CommittedAppend-local-compile.log, /tmp/eip-QueueArithmetic-3.log, /tmp/eip-SubmissionCall-2.log; exported audited declarations report only propext, Classical.choice, Quot.sound.

CommittedAppend:
- Actual Ξ result determinism joins independently proven storage and authentic LOG0 observations into the same world/substate witness.
- Preserved owner lookup proves returned world cannot equal the empty map, discharging actual Θ fallback.
- Θ/Ξ/X offsets are explicit: c.fuel=steps+1, Context.result calls Θ(c.fuel+1), XiCall.result calls Ξ(steps+1), entry X uses steps.
- One record window and count/tail natural increments are established under explicit AppendFits; remaining storage slots and excess/head are preserved.
- Exactly one appended anonymous log contains raw184 deposit calldata or caller20 || pubkey48 exit bytes.
- Other-account preservation is correctly relative to Θ transferred entryWorld, not pre-transfer world.

QueueArithmetic:
- Ordered head≤tail makes subtraction ordinary natural subtraction.
- Capped count is exactly min(length,64/16).
- Count≤length implies head+count≤tail<2^256, so pointer addition cannot wrap; full iff count=length is valid, including empty queues.
- Actual committed Θ world has reset/partial pointers and every slot with address≥4 unchanged.
- QueueResult deliberately leaves output bytes existential; no deposit endian/FIFO claim is hidden in this theorem.

SubmissionCall:
- Amount is exactly the eight big-endian bytes at offset80 of184-byte calldata.
- Uint64 extraction implies 1e9*amount<1e9*2^64<2^256 without an assumed product-fit condition.
- Real fee comparison implies value≥price, so subtraction does not wrap; the three operational checks are equivalent to amount≥1e9 and price+1e9*amount≤value in Nat.
- Apparent CALLVALUE is explicitly equated to Θ actual transferred value before applying natural payment assumptions, for both kinds.
- Quote is the completed operational word recurrence output divided by17. It is not asserted equal to the natural mathematical tariff without separate intermediate-fit proofs.

Explicit remaining obligations, not review defects:
- These are sufficient-success theorems with completed quote, resource, owner and append-index/pointer premises; they do not invert arbitrary success or establish all proposed guarantees.
- Raw Θ assumes funding admission externally. Its source explicitly comments that an insufficient-funds check must already have passed. The theorem proves payment checks against its supplied actual transfer value, not account solvency or transaction validity.
- Runtime code is pinned, but canonical deployed address and installed account code identity are not proved by these Context theorems.
- Ordered, AppendFits and source-width/history invariants require initialization and preservation proofs; protocol reachable histories are still separate.
- Deposit drain endian/FIFO and arbitrary-success fee completion remain separate work.

Next inversion lemma:
Prove success_symStep from actual X success + decoded instruction + an existing symStep shape. success_continue derives actual Z/step; Z_ok_state and memcost_zero identify its charged state; EVM_step_eq_step, stepPre_eq_withGE, step_withGE and guardOk_of_symStep identify actual post with the symbolic shape plus charged gas/count. This needs no sufficient gas premise. Lift to symBlock, reuse generated six-op fee head and seventeen-op body, and add the JUMPI case to derive exact24-step nonzero-cycle continuation. Strong induction on actual fuel can then derive feeExit completion rather than assume it.

Exact commit binding: verified git objects at 8b9e562 for all three reviewed modules byte-for-byte against the SHA256 values above; all match.


# Independent review: RejectionCases.lean

Result: CLEAN, current frozen source.
SHA256: 305b65343389485af0065f498e53d7471254b77ded8f0689a7e388de032ec2a3
Worktree: /Users/thomas/work/eip-8282/direct-closure-implementation

Read the complete source and its RejectionSpec bridge. Checked each consumed EntryReach rejection theorem's hypotheses, endpoint, gas and step bound, and the previously reviewed CallBridge/MessageCall connection to actual Θ.

The negative predicates are exhaustive over the pinned WORD checks: correctly sized input either underpays or (deposit) fails the amount floor/stake test; other sizes either represent a paid getter or fail both zero and submission-size checks. Their negations are used only to select a concrete reached rejection branch, never to assume its execution result. The quoted price is exactly feeWord of the explicitly completed operational fee loop.

Resource bounds are sufficient: the largest deposit endpoint is Ends (24*n+100), whose Xi transport requires two more fuel levels, covered by steps>=24*n+102. Gas87*n+4600 covers the amount/stake endpoints and dominates the4500 bounds for all other branches. The exit bound is conservatively larger than its maximum endpoint requirement. The separate Context.fuel=steps+1 accounts for the Xi/Θ wrappers.

Each branch derives an actual Xi REVERT with a zero-length return slice and composes it through Θ to the pre-transfer world, original created-account set and complete pre-call substate, with failure=false flag expressed correctly as success=false. No post-world agreement, nonempty-world premise, owner existence or write permission is needed: these rejection paths perform no state writes, and Θ's REVERT journal result handles arbitrary prior transfer. Apparent/actual value equality is unnecessary for the rollback claim, since the predicate deliberately concerns the execution environment's word value.

Scope is honest: enabled non-SYSTEM callers, completed quote and sufficient gas/interpreter fuel remain explicit premises. The predicate concerns UInt256 CALLDATASIZE, not independently bounded natural calldata length, and deposit payment is still the pinned word test. The module does not claim all invalid EVM calls terminate, that every successful fee execution supplies the witness, or that allowed input necessarily succeeds. Inhibited rejection is separately supplied by RejectionSpec. No blocking findings.

Existing compiler evidence inspected: /tmp/eip-RejectionCases-2.log. Both public parents report only propext, Classical.choice and Quot.sound. No proof edits or compilation were performed during this review. Final exact-commit binding remains for the integrator after commit.

Exact-commit binding: 8b9e5628fc6a10e880aa4eff50fc9bc8eecd4d49. Reviewed SHA256 above matches the exact git object byte-for-byte.


## DepositDrain — root independent review, CLEAN

Exact source commit: `8b9e5628fc6a10e880aa4eff50fc9bc8eecd4d49`.
Source SHA256: `7dca8b1b01d837ff73b7b3ece4a8e8dc101c73c7cf8abdd83d22ff5e89aed5d0`.

Reviewed the full source independently of its author. The natural record
specification selects exactly184 bytes and reverses only the eight-byte amount
field. The proof identifies the actual descending MSTORE8 order, rather than
assuming equality with the historical ascending macro. Actual modular offsets
are normalized before memory lemmas are used. Induction includes empty drain,
all capped iterations, overlap and exclusion of the final eight-byte overhang.
The public theorem binds actual Θ result bytes and all storage observations to
the same result via CommittedSystem. No source-record encoding hypothesis,
fee-model agreement or desired output is assumed. Word-indexed queue order,
explicit gas/fuel and owner premises remain; initialized-history invariants
and arbitrary-resource execution classification are not established here.

Standalone compilation: /tmp/eip-DepositDrain-11.log, exit0; all reported
axioms are standard Lean axioms. Full make check passed at the exact commit;
receipt direct-data-build-20260909.json binds the source bytes and log.
