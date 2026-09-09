# Independent local source reviews — 9 September 2026

These reviews certify only the stated source scope. Successful compilation is
recorded separately. No review below accepts the three guarantees as complete,
protocol reachability, or an economic-domain restriction.

## Message-call and history foundation

Commit `1088e40c3be45e64048ffabd2b57a42ba625ec53`. Reviewer `/root/math_fee`.
Verdict: CLEAN for the stated helper scope. Inspected the complete MessageCall
and ReachableCalls sources, pinned Θ/Ξ/X, call-site funding/depth checks, Υ,
AccountMap/Account/Substate/ExecutionEnv/Exception and EvmRunner/Bytecode.
The input world and actual returned world are bound; genuine failure restores
the journal; evaluator OutOfFuel propagates. The upstream empty-world fallback
is retained. Funding/depth authorization, originalWorld/substate continuity,
enclosing transaction rollback, exact initialization and protocol bounds remain
separate obligations.

## Fee mathematics

Commit `96e0fc1d3000cbfa246f5dc1c983b2dcd3098ce4`. Reviewer `/root/control_spec` (not the author).
Verdict: CLEAN. Inspected complete MathFee, FeeQuote/Path and UInt256 semantics,
and the successful standalone compilation log. Natural termination advances
the counter beyond the numerator and then uses strict accumulator descent.
PrefixFits checks every intermediate before division, including denominator
and counter increment, and does not assert completion or reachability. Both
natural and word division by zero return zero. No legacy 256-fuel dependency.
Word-loop termination, actual gas sufficiency and protocol justification of
PrefixFits are not proved by this module.

## Word control, failure journal and finite regression evidence

Commit `96e0fc1d3000cbfa246f5dc1c983b2dcd3098ce4` versus `1088e40c3be45e64048ffabd2b57a42ba625ec53`,
excluding MathFee. Reviewer `/root/math_fee` (not the ControlSpec/script author).
Verdict: CLEAN. False Θ results restore world, substate and created accounts;
OutOfFuel cannot become a history step. ControlSpec matches the pinned operands
and requires intermediate-sum fit for the natural fold. The M−5/count10 example
yields deposit 0 and exit 3 after word wrapping. Reviewed the complete regression
script and receipt: source hash matches, 10 fee/getter cases and 7 other
transactions, and the enclosing revert trace contains inner 5 SSTORE, 1 LOG0
and 1 STOP before rollback. Injected storage is not protocol reachability.

## Hermes fee-loop adapter

Source commit `34c319eb9890d1bf56221df4310c14b52b21be8d`, cherry-picked as `4ce4ba27716b94e0a11cf3e8b55d902dc01b611a`.
Reviewer `/root/control_spec`. Verdict: CLEAN for the conditional loop adapter.
Inspected the complete new FeeQuotePath file, FeeQuote, Deposit.fee_loop and
underlying path/block interfaces. The result reaches PC 127 in at most 24*n+7
steps given a completed quote and 87*n+25 loop-head gas. It proves neither a
returned getter result nor successful-call inversion. Nonblocking limitations:
the explicit QuoteCompletes premise is redundant, and the existing remaining-gas
conclusion is dropped. Hermes owns a separate getter composition follow-up.

## Execution payloads and pinned rejection settlement

Commit `64d8550a3f5ed3902df53d306ab7bc32643e03ad`. Reviewer `/root/math_fee` (independent).
Verdict: CLEAN. Reviewed complete EndpointState, CallBridge and RejectionSpec,
STOP/RETURN charged-step conservation, XiHalts/Ends and inhibited paths. Fuel
aligns Θ(steps+2), Ξ(steps+1), X steps. The actual transferred world is used;
inhibited calls restore the full pre-transfer journal without any fee-completion
premise. Resource, installed-code, funding and protocol obligations remain.

## Independent append receipt and account frame

Commit `38db986f891f759b8734a89d18c4d12d3d835094`. Reviewer `/root/control_spec` (independent).
Verdict: CLEAN. Full prior log sequence plus exactly one anonymous entry at the
executing account; deposit payload exactly the 184-byte calldata. Inspected
memory read/write bounds, including padding, and account-frame composition.
The independent receipt and arbitrary other-account preservation are attached
to the actual Ξ result. The world is post-value-transfer. Exit address/pubkey
identification, append record/control storage and arbitrary-success inversion
remain open.

## Independent SYSTEM storage

Commit `729ba664546a6c9812a3b4038e49acd9fd962d11`. Reviewer `/root/review_fee_helper` (independent).
Verdict: CLEAN. Reviewed complete SystemSpec/ControlSpec, pinned sstore and
updateStorage (including zero-value erasure), Touched, both SYSTEM paths and
Ξ result transport. Every word slot is covered in the actual result world;
owner presence is derived. drainWord caps modular TAIL−HEAD, so this is not yet
an ordinary FIFO/history theorem without queue invariants.

## SYSTEM commitment through Θ

Commit `a8f40cb2b9e46dbc99df77858d6d40f778e7c0af`. Reviewer `/root/review_fee_helper` (independent).
Verdict: CLEAN. WorldNonempty follows the actual TreeMap/DTreeMap boolean
comparison's size-first branch without LawfulBEq Account. CommittedSystem
derives final owner presence from SystemSpec, refutes the empty-world fallback,
and publishes the same world at Θ. The transferred input world and target are
bound definitionally. FIFO, protocol bounds, funding and installed-code identity
remain outside these statements.

## Final integration and metadata

Commit `135b6eeb40461faa84f3f2b17382d8cde4f3ca57`; source commit
`b17e0a5e86af240f4982b3380ae8a3aeab3437e6`.
Reviewer `/root/control_spec`. Verdict: CLEAN, read-only without rebuilding.
Verified all 68 source hashes against both commits, all receipt/hash bindings,
48 Integrator axiom reports and successful full build/mutation markers. All 11
Integrator modules are imported, and proof files match the reviewed commits.
Documentation consistently leaves the three full guarantees open. One obsolete
README heading anchor was identified and corrected in the subsequent
documentation-only commit; no proof or tested source changed.
