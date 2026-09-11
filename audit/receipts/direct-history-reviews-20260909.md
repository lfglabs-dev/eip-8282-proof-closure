# Independent reviews: complete SYSTEM calls and concrete histories

# Independent root review: SuccessfulSystem.lean

CLEAN. Frozen SHA256 a31902e51e200319607fc2967424214edd1acc409f36009818de615ad4f5616e.

Read the entire module and the reviewed SystemInversion, CallSuccess, TransferFrame and settlement dependencies. Actual success supplies positive fuel and exactly the actual Ξ result, including created set, gas and output. The pre-world owner survives actual value transfer and every pointer/control store; read touches preserve it. This proves the actual successful Ξ world is nonempty rather than assuming the desired settlement branch. The exact same result is then committed by commits_endpoint and identified with the independent all-slot map and actual staged output.

StorageResult is tied to the actual deterministic Θ execution, so its existential world cannot be chosen independently of the input successful result. No gas, evaluator-fuel, permission or post-state premise is present. There is no ordinary CALLVALUE equality requirement for this SYSTEM path, since it does not inspect value; arbitrary transfer storage preservation was already proved. The source correctly limits this result to code pin plus existing input owner; canonical authorization, natural calldata size, queue representation and protocol accounting remain separate.

Inspected /tmp/eip-SuccessfulSystem-2.log: three standard axiom reports and clean stated compile. No proof edits by reviewer; exact-commit integration check follows separately.

---

# Independent root review: SystemStateInvariant.lean

CLEAN. Frozen SHA256 082bde0053b3b50dfb54ded08a5e3cc7f5e647594f8d1a1ae40f506f8e31feac.

Read the entire module, including actual_storage, map_preserves, both FIFO parents and both scalar-only parents. Inspected the previously reviewed SuccessfulSystem, QueueArithmetic, AccountedState, FundedDomain, QueueInvariant and drain-memory encoding proofs.

The actual Bool result selects the failure or success branch. Failure restores the true pre-call world, consumes zero and deliberately makes no return-byte claim. Success obtains the independent map AND output from SuccessfulSystem, then joins the receipt's existential world/output to the actual supplied result by determinism. TransferFrame transports only the true pre-world observations to bytecode entry.

Queue order and representation identify the cap as min(list length,16/64), so the drain count is bounded by real input length and head addition cannot wrap. AccountedState supplies structural bound preservation from the coupled excess+count invariant; FundedDomain supplies enabled safety through exact latch/unlock/fold. The dropped queue and returned bytes use the same cap. Exit SourceWidth is preserved by drop and supplies the actual 160-bit source-word requirement of the writer. Deposit encoding uses the independently proved byte reversal rather than a memory agreement premise.

Scalar wrappers require no queue witness: Bounded.ordered itself derives the capped drain bound. There are no gas, permission, completed-quote or desired-poststate premises. The independent budget<2^128 and initial invariant inputs remain explicit. These word-based control results do not silently conclude a natural nonempty-calldata latch without a size-word fit fact. SYSTEM scheduling/authorization, canonical installation and valid transaction/block extraction remain external.

Inspected /tmp/eip-SystemStateInvariant-2.log: all four exported results standard axioms; reported compile clean. No proof edits by reviewer. Exact-commit full validation follows separately.

---

# ConcreteHistory independent source review — CLEAN

Reviewed exact frozen SHA256 `d1a5d5f8ffd6c40da56215308934ace6d583cb7e52881bd0ec3be9a3a90c345b`, confirmed twice. Read complete ConcreteHistory, ReachableCalls, UserQueueInvariant, InitializedInvariant, relevant UserStateInvariant interfaces/payment preservation, creation-settlement constructor binding and queue/source-width definitions. The SystemStateInvariant dependency was authored by this reviewer and independently reviewed by root; this report independently reviews root's ConcreteHistory composition, not our own underlying file. Parent log `/tmp/eip-ConcreteHistory-3.log` is clean; all five exports have only propext, Classical.choice, Quot.sound. No edits/build.

## Concrete trace and policy

Trace.call requires an actual ReachableCalls.Transition whose `call.world = before` and actual completed Θ result includes exactly `after`. Each call is pinned to the canonical target, expected runtime actually installed in its pre-world, and ordinary actual/apparent CALLVALUE equality. The state cannot be selected independently of execution. Trace.initial uses the same actual initial account map and event count0.

The index is a Nat sum of observable weights: SYSTEM0, otherwise1 exactly for true actual success with nonempty calldata, and0 for failures/getters. Admission inversion supplies the theorem that a successful user nonempty call is an append; this is not assumed by the weight definition. `Allowed` contains only calldata length<2^256 and an actual call-value ceiling for non-SYSTEM users. No Bounded, EnabledSafe, Represents, AppendFits, desired post-state, quote completion or sufficient gas is buried in policy or trace constructors. `forget` preserves the exact existing call relation/policy.

## Joint induction

Each transition derives the pre-owner from installed code and rewrites both the account map and target using actual transition/canonical pinning. SYSTEM branches apply the arbitrary-resource completed-Bool invariant results, preserve the same budget and safe fee domain, and select the actual undrained queue suffix (no removal on failure). User branches apply scalar and queue preservation to the same actual executed result; successful appends extend the queue once and add one to the budget, while failed/getter paths preserve it. Exit source width is preserved for exactly the UserQueueInvariant.after queue chosen by the queue theorem, using the actual caller's intrinsic160-bit type.

`preserves` obtains each prior budget<2^128 from the bound on priorBudget+weight and nonnegativity of Nat weight. It never assumes per-transition storage-fit conclusions. Independent Bounded supplies fit before append interpretation; the strict funding ceiling prevents crossing the safe tariff domain. The initial predicate is independently supplied, then propagated. No circular desired-state premise or synthetic post-world occurs.

## Actual creation parents

Both from_creation results obtain their initial Bounded0/EnabledSafe/empty-queue facts from InitializedInvariant on the actual successful CreationSettlement result. Previously absent target storage, exact init code, collision/resource hypotheses (and exit owner/permission conditions) remain explicit. `haddress` binds the actual returned creation address to the canonical audited address; it is neither inferred from a convenient arbitrary address nor hidden. The exact initial world from that returned tuple becomes Trace.initial. Deposit starts enabled, exit inhibited; empty exit SourceWidth is structural.

## Honest scope

This is a history of contiguous actual account-map transitions at one audited address. It does not establish that arbitrary Ethereum transaction histories, external frames, nested calls, ancestor rollbacks, block scheduling or gas/funding accounting can be extracted into this trace. Transition does not link originalWorld, substate/created-account journals or block/environment fields between calls; the proved invariant is storage/queue based and does not require such links. Parent header explicitly leaves those protocol extraction/accounting obligations open. The final Invariant keeps an existential represented queue/source-width witness, not a published full-history list of receipts or drain outputs; individual transition dependencies retain the exact FIFO behavior. Global event bound and user funding ceiling remain externally justified assumptions. Canonical deployment is explicitly bound but not proved protocol deployment. Interpreter exhaustion cannot extend a trace because it has no completed Θ result.

No concrete correctness, circularity or overclaim findings.

---
