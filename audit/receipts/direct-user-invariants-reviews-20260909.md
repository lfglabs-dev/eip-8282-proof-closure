# Independent reviews: actual user-call invariants

# Independent root review: UserStateInvariant.lean

CLEAN. Frozen SHA256 d97bfdb9c02be37a754ff3d0ac57533d759ea50c8cd60592486f795526ea7879.

Read the complete module and all relevant reviewed dependencies. The event weight depends only on actual status and calldata emptiness. Failure uses actual Θ journal restoration; successful empty-input calls use GetterInversion and preserve all target storage. The successful nonempty branch is classified by admission, which supplies exact size, inhibition exclusion and the same operational quote/payment.

The pre-transfer Bounded invariant is transported through actual value transfer and derives AppendFits BEFORE invoking SuccessfulAppend. Its independently proved map is identified with the given actual result world through deterministic equality, not a post-state assumption. AccountedState.append supplies the coupled structural budget+1 bound. EnabledSafe's inhibited alternative is excluded by actual admission, yielding the independent natural numerator bound. SuccessfulUser transports that natural numerator to the operational word without wrapping; the SAME quote and actual natural payment then supply FundedDomain.expected_append_safe under the explicit value ceiling.

No gas, permission, execution completion, desired post-state or local fit premise is introduced. Initial budget/state/safe domain and funding ceiling remain external. Neither prefix budget<2^128 nor protocol validity is propagated without a separate history/accounting proof. The result is one-step preservation of actual completed ordinary user calls; SYSTEM, ancestor rollback extraction and initialization are separate tasks.

Inspected /tmp/eip-UserStateInvariant-final.log: both public results standard Lean axioms. No source edits by reviewer. Final integration validation follows separately.

---

# Independent source review: UserQueueInvariant

Verdict: CLEAN for the stated local, actual completed-user-call queue-preservation scope.

Reviewed source: Eip8282/Audit/Integrator/UserQueueInvariant.lean
SHA256: f269ccf117faa4d30ca13de7cb86631877cc59451bd350b63430ec07a6854bd0
Compiler receipt examined: /tmp/eip-UserQueueInvariant-2.log. All four printed public theorem closures contain only propext, Classical.choice, Quot.sound. No build or proof edits were performed for this review.

The complete new module and complete QueueInvariant dependency were read. AccountedState, SuccessfulAppend, GetterInversion, TransferFrame and MessageCall were checked against their previously examined implementations; the AppendStorage input word encoding and independent expected-map definitions were also reread. Relevant dependency hashes:

- QueueInvariant: 5e15726133885b59340a5ffc4d8650fe33d4cda27639039ad1fe92fe49de5219
- AccountedState: 382a0419905acd948e36c7290e2b81f6d3641f712e4077bb471386340b7b54e7
- SuccessfulAppend: 7dd2fab6f9f754bbd4c75043ef2a87b4df3cce25555d1d7ec004346836313e07
- GetterInversion: 43b9fa209ed9fb674f8d74168dfb3496389afe2a6b938807e85fed52efc52e7b
- TransferFrame: d7344861f8706ed4ef57954f8d0a5464212f45f12a5940976a6ebdd5bd945a1b
- MessageCall: 3f16088bd13b6f6fdf13de417e4843f08e9dcd61fa6dfdddfc6342c250ccf342

Findings:

1. `after` is independent of post-state: its branch reads only actual returned status and input size; its fresh physical word vector uses only input calldata and source address. No post-state agreement or successful-append classification is assumed in its definition.
2. The false-status branch uses actual Theta journal restoration, preserving the pre-transfer target storage. Interpreter OutOfFuel is an error, not fabricated as a completed false result; it is correctly outside the result premise.
3. The true-status branch derives exact getter/append admission from actual execution. The calldata-size fit bound explicitly prevents word-size aliases. Empty calldata uses actual getter account-lookup preservation through both settlement branches; ordinary apparentValue=value is what binds zero CALLVALUE to zero actual transfer.
4. Nonempty successful inputs are proved to have exact 184/48 bytes. Both the queue representation and independent budget predicate transport through actual value transfer. `AccountedState.append_fits` is applied to the pre-entry budget before SuccessfulAppend, so no circular post-state capacity premise occurs.
5. `append_actual_world` extracts world equality from two equalities for the same actual Context.result, then rewrites using independently specified all-slot observations. Thus its representation concerns precisely the world supplied in the public completed-result premise, not an unrelated existential receipt.
6. `Represents` records ordered HEAD/TAIL, physical window fit, exact list length TAIL-HEAD, and every word of each live record. `represents_append` preserves each old physical record using separated natural addresses and extends the list by exactly one fresh vector. Old data are not assumed well-formed; their full vectors are retained.
7. `preserves_prefix` is an elementary property of the independent queue update; combined with the two actual-result representation theorems, it establishes local user non-consumption. `exit_source_width` preserves the 160-bit source-word invariant, deriving the new source width from the actual AccountAddress type rather than calldata or a supplied format assertion.
8. Queue records here are physical vectors (six deposit words / three exit words). Authentic input vectors are specified by AppendStorage.recordWord; the independent byte encodings, source-address log authentication and drain endian conversion remain in their existing dedicated modules. The new module does not silently claim a byte-oriented queue theorem from an uninterpreted vector.

Remaining explicit obligations, not defects in this scope: initial queue representation; deriving and maintaining the external budget < 2^128 over protocol histories and ancestor rollback; installed-target/code authorization; protocol funding; successful SYSTEM drain classification where not yet covered; inter-call/history composition. No funding ceiling, mathematical fee agreement, gas lower bound, fee-completion witness or assumed post-state is needed for these user queue-preservation theorems.

---
