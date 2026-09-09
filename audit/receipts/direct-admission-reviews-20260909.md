# Independent reviews: admission, tariff domain and creation settlement

Frozen source hashes bind the reviewed files. Full-check source binding is recorded separately.

# Independent review: TransferFrame.lean

Result: CLEAN, frozen source SHA256 d7344861f8706ed4ef57954f8d0a5464212f45f12a5940976a6ebdd5bd945a1b.
Worktree: /Users/thomas/work/eip-8282/direct-closure-implementation.

Read the complete208-line source, the MessageCall.entryWorld/actual Θ transfer semantics and ReachableCalls.PinnedCall definition. No proof edits or build performed.

The credited helper exactly reproduces the first transfer phase: absent target plus nonzero actual value inserts a default account with that balance; absent target plus zero value leaves the map alone; an existing target is reinserted with modular balance credit. The debit reads this credited map, not the original world. Therefore the proof correctly covers caller=target, including a previously absent self-recipient, as well as missing callers and arbitrary modular values.

The generic observed theorem preserves only observations insensitive to balance, with missing-account observations defaulted to the corresponding default Account field. This correctly covers zero storage and empty code for newly created recipients. It neither equates an absent account with an existing account nor claims complete account-map/balance neutrality. Existing-account preservation is separately proved through inserts; combining it with code/storage observation preservation yields the exact surviving account statement.

The actual codeCall storage map is transported from Θ's pre-transfer target via entryWorld, so arbitrary storage-only predicates can be moved to bytecode entry without assuming their postconditions. PinnedCall's installed witness is an input-world account whose code equals the pinned execution code; this surviving witness correctly discharges HasOwner and installed-code identity after transfer. No LawfulBEq Account assumption, distinct-address premise, nonempty post-world premise or omitted self-call branch is used.

Scope: the file proves the transfer frame and survival of existing code/accounts, not sufficient sender funds, protocol admission, conservation of balances or history closure. No blocking findings.

Evidence: /tmp/eip-TransferFrame-local-compile.log. All printed public theorem axiom sets are standard propext, Classical.choice and Quot.sound. Source hash rechecked unchanged. Final exact-commit binding remains separate until integration.


---

# Independent review: AdmissionInversion.lean

Result: CLEAN, frozen source SHA256 b77c1eef9df027a365baac47ae2978c78dec6e92948d6c0aa1162779019aa6a0.
Worktree: /Users/thomas/work/eip-8282/direct-closure-implementation.

Read the complete448-line source and the relevant complete SubmissionCall arithmetic bridge. Checked the already reviewed SuccessInversion machinery and the actual Z/RETURN memory frame facts. No proof edits or build performed.

The admission witness is tied to the same successful execution and the same actual price: fee_exit follows the24-instruction recurrence until the actual accumulator-zero branch, returning both feeExit completion and the successful continuation at PC127/126. That continuation carries precisely the same output word used by quoteWithin and subsequently divided by17. The proof does not obtain a free quote witness unrelated to the stack being checked.

Each rejection guard is inverted from success: a taken branch reaches the pinned rejection subroutine, which leads to REVERT and contradicts actual success. The input split covers exact submission size versus all other sizes; the latter must pass both the zero-size and zero-value checks. Deposit submission must pass fee, minimum amount and stake checks; exit submission must pass fee. Successful getter suffixes execute the actual MSTORE and RETURN, proving out=price.toByteArray for this very price. success_effect and success_return_bytes retain accepted Z effects and use the real memory/stack frame theorems; they do not assume a gas envelope or omit a memory mutation.

The natural-input corollaries explicitly require calldata.size<2^256, preventing a truncated CALLDATASIZE equality from being promoted to an exact natural size. Deposit's amount is independently extracted from calldata bytes80..87, is inherently uint64, and hence amount*10^9 fits a word. The fee-paid check prevents subtraction wrap before stake comparison, so the resulting price+stake<=CALLVALUE assertion is ordinary natural arithmetic. No arbitrary stake-product bound or mathematical-fee agreement is assumed.

Scope: these are necessity results at Xi for actual user success and arbitrary resources, not sufficient-success statements. CALLVALUE is the execution environment's apparent value; equality with actual transferred value must be supplied by the enclosing ordinary-call bridge. Mathematical tariff agreement, append receipt/state necessity, installed-code identity and protocol history are separate. No blocking findings.

Evidence: /tmp/eip-AdmissionInversion-final.log. All printed parent/helper axiom sets are standard propext, Classical.choice and Quot.sound. Source hash rechecked unchanged. Final exact-commit binding remains separate until integration.


---

Independent review — FeeSafeDomain.lean — 2026-09-09

Verdict: CLEAN for the explicit mathematical domain 0≤X≤2892.
Reviewed source SHA256: 3f23254c5bcced81f37ca5e510e6575e940ff3dc2455d798c2313348c46d6bbd.
No source edits or Lean builds during this review.

Read the complete frozen module and current MathFee/FeeQuote dependencies. Inspected /tmp/eip-FeeSafeDomain-3.log: upper_fits and upper_stops have no axioms; exported domain/agreement and monotonicity theorems depend only on propext and Quot.sound.

Findings:
- prefixFits_mono preserves representation bounds, the output sum, multiplication BEFORE division, denominator i*17, and counter1+i. Its shared-counter induction is sound, including early stopping of the smaller trajectory.
- completes_mono proves existence of completion for every smaller numerator at the certified budget. Completion is not assumed for the smaller trajectory; upper completion is discharged by the closed upper_stops theorem.
- Structural prefixFitsDecidable matches PrefixFits exactly; decide produces kernel-checkable terms and introduces no oracle or native_decide dependency.
- The upper trajectory starts at output0, accumulator17, counter1; its actual completed output is 1293016615363553351305261411891033154262342899586402592153715843914719896707 after462 nonzero iterations, with terminal counter463. upper_fits includes the terminal represented state and every intermediate product/denominator/counter bound.
- An independent Python integer recomputation agreed with output, counter and462 iterations. Largest predivision product is 114355600538549766260800151926423633524303718159117238312945495336313617267112 < 2^256. This is a cross-check only; the Lean closed certificates are the proof.
- domain_certificate universally quantifies X≤2892 and derives both PrefixFits and completed natural evaluation by monotonicity. It is not an enumeration of2893 examples.
- safe_quote establishes word completion and mathematical agreement with no word/natural completion input premise.
- any_quote_agrees deliberately accepts an arbitrary completed word quote and identifies it with the independently completed certified quote using helper uniqueness. Its n is arbitrary, including values above/below462; PrefixFits is not secretly demanded for that n because the certified completed result is stable.
- 462 appears only as a finite certificate witness, not in the natural tariff/word semantics definitions. No partial result on fuel exhaustion is treated as a tariff.

Scope:
- X≤2892 is an explicit arithmetic domain. The file does not prove it is a protocol invariant, the largest safe domain, or guaranteed by funded reachable calls.
- operational_quote_agrees concerns the effective word numerator; connecting that word to the proposal’s natural excess+max(0,count−target) expression still requires its own nonwrap/domain reasoning.
- This module is helper-level. Actual code success/completion is supplied by separate reviewed inversion theorems; gas sufficiency and universal successful execution are not claimed here.

Next bounded append inversion, for discussion only:
Start with actual success at exitPC165 (after all admission checks), state Exit.st₂ c, original entry memory and empty stack. Reuse generated blocks165/174/187/194/202/208/214/218, success_effect with real SSTORE at173/186/193/201/223, MSTORE207, CALLDATACOPY213 and LOG0 at217. Add success_STOP payload inversion at224. Conclude exact final.toState=Exit.appendedSt c and out=empty at arbitrary gas/fuel, without permission/gas/AppendFits premises (actual success supplies accepted checks). Keep expected state a conclusion. Then recover that suffix entry from actual successful userΞ via user_to_fee_head, fee_exit and short postfee admission traversal. Compose existing independent append storage/record specifications under only their true owner/window conditions and then actual Θ settlement. Deposit analogue follows the same pattern with its six-word window. No edits started for this next work.


---

# Independent review: SuccessfulUser.lean

CLEAN. Frozen SHA256 fb5651794e94dac56439daaeb3ca83aa4c012d6916998cb638b1fdee5e80afff.
Read the complete source and checked the previously reviewed CallSuccess/SuccessfulQuote, AdmissionInversion, TransferFrame and FeeSafeDomain dependencies plus ControlSpec.feeInput_toNat.

Actual Θ success supplies the exact positive-fuel Xi execution, and AdmissionInversion supplies a quote and checks tied to that same output. hactual explicitly binds apparent CALLVALUE to actual transferred value; calldata-size fit is explicit for exact natural admission lengths. Getter output uses precisely the same price as the quote witness.

The mathematical bound is imposed on the independent PRE-TRANSFER natural numerator excess+(count-TARGET), not on the already wrapped effective word. TransferFrame transports both slots, and the<=2892 bound proves the outer addition cannot wrap. The generic arbitrary-budget FeeSafeDomain theorem therefore applies to the exact operational quote and yields the natural tariff at that pre-call numerator. Empty calldata rules out the submission alternative. No gas, quote-completion or desired postcondition premise is introduced.

Scope: mathematical getters remain conditional on the independent numerator domain and actual successful ordinary user execution. The module does not derive that domain from protocol funding/history, nor prove all such calls succeed. Read-only state necessity is in the separate GetterInversion module. No blocking findings.

Evidence inspected: /tmp/eip-SuccessfulUser-1.log, all printed public parents use only propext, Classical.choice, Quot.sound. No builds or proof edits during review. Final exact-commit binding remains separate.


---

# Independent review: FeeBoundary.lean

CLEAN. Frozen SHA256 f687d461bafe1af5a6963ddf979b5dd4af4348afc2421617160c5f90da31f7e2.
Read the complete source and checked the independent untruncated natural/word definitions, natural-quote uniqueness, and prior2892 certificate.

The two decidable stopping certificates establish distinct exact outputs at numerator2893: natural price80668064690921409049190791237320678716946849613533250306370202067869504081 within462 iterations, word price32087365885911168062721653499988857431024628719292649881555161070975172167 within457. Natural uniqueness correctly excludes ANY natural completion witness for the word price; this is not merely inequality between results at an arbitrarily selected cutoff. local_fee_drop compares those exact values with the certified2892 price and proves the advertised opposite inequalities.

The explanatory overflow description is consistent with an independent read-only Python replay: the first wrapping operation is numerator*accumulator at counter167 (166 prior iterations). The formal certificates themselves prove completion/prices and divergence, rather than earliest-stop or first-overflow-step theorems. No protocol reachability or affordable-funding claim is made. No blocking findings.

Evidence inspected: /tmp/eip-FeeBoundary-1.log. natural_quote has no axioms; word_quote/local_fee_drop only propext; uniqueness/counterexample parents only propext and Quot.sound. No native_decide or new axioms. No proof edits or builds during review. Final exact-commit binding remains separate.


---

# Independent root review: GetterInversion.lean

CLEAN. Reviewed source SHA256 43b9fa209ed9fb674f8d74168dfb3496389afe2a6b938807e85fed52efc52e7b.

Read the complete module and actual-success transport dependencies. RETURN state preservation follows accepted Z and actual step; the suffix proof follows generated pinned blocks and real MSTORE/RETURN. Empty calldata rules out the append branch. Actual success supplies the fee exit and zero CALLVALUE without a completion, gas or permission premise. Non-machine state is proved equal to the entry state with two storage touches, which preserve accounts, logs and created accounts.

The Θ wrapper obtains actual Ξ success through CallSuccess, derives zero actual value using the explicit apparentValue=value premise, and covers both empty-world settlement branches. It compares every account lookup to the pre-transfer world; zero-transfer neutrality supplies the non-fallback case. Access bookkeeping is deliberately outside ReadOnly. Output price is separately supplied by AdmissionInversion/SuccessfulUser. No unsupported state equality or desired-poststate premise is used.

Inspected /tmp/eip-GetterInversion-5.log: clean compilation and standard Lean axioms only. The reviewer did not author this module. Full exact-commit integration validation remains separate.


---

# UniversalGate independent source review — CLEAN

Reviewed frozen source SHA256 `251ee50dabe9d3992e004caeef696a8ac42e3596a2dd502838d2fd8382d3ee6b`. Inspected complete UniversalGate, SuccessfulQuote, CallSuccess and MessageCall settlement/journal proofs, and TransferFrame codeCall storage transport. Checked parent compile log `/tmp/eip-UniversalGate-1.log`: both exports use only propext, Classical.choice and Quot.sound. No proof edits or new build.

Both runtimes derive absence of actual successful Θ completion at arbitrary gas/interpreter resources from the successful-call necessary uninhibited condition. Positive interpreter fuel is itself derived from actual success in SuccessfulQuote; no assumed completed quote, sufficient gas, nonempty world or post-state agreement. TransferFrame transports the pre-transfer target slot through the actual credit-then-debit world, including missing/self-account cases. The resulting contradiction therefore refers to the stated pre-call inhibition.

If Θ returns false, MessageCall.failure_restores_journal restores the entire pre-call created-account set, account map and substate (hence logs), including REVERT and ordinary exceptional halts. FailedJournal intentionally does not claim preserved gas or output. Proof-evaluator OutOfFuel returns an Except.error rather than the theorem's completed .ok result: the theorem does not claim termination or enough resources to return a failure, and the source header states this limitation. The code is pinned through explicit hcode; this does not independently assert installed predeploy code or protocol-authorized call histories.

No concrete findings.


---

# Independent root review: CreationSettlement.lean

CLEAN for the stated actual Lambda semantics and conditional constructor specialization.
Frozen SHA256 d95b28f2a46daf588a2aaf15e8a8f77fc28b075116e5f2395360e73152383820.

Read the complete module and compared against the pinned EVM/Semantics.lean Lambda definition (including L_A). result_eq_settle retains the optional encoded address preimage, KEC address, collision-selected invalid instruction, creation-set selection, sender debit before target insertion, and exact failure/success payloads. Creation failure deliberately retains the upstream created-account set and accessed substate; this module does not claim message-call whole-journal rollback for Lambda.

Code-deposit cost, all four failure guards, actual remaining gas and installed-code update are preserved. Success inversion derives the true init result and passing guards from the actual Lambda result. Code and storage postconditions are conclusions, not assumed post-world identities. Installation and entry transfer preserve defaulted storage even at absent/self addresses.

The two constructor results use the reviewed Initialization execution on precisely Lambda's entry world/environment with the correct fuel offset. Runtime identity and storage/log effects are joined through deterministic actual execution. Resource, no-collision, code-pin, encoding and actual creation-success premises remain explicit; the exit additionally requires a present sender and permission. These are conditional installation results, not proof of deployment success, canonical predeploy identity, valid creation transactions or protocol initialization. Deposit preserves prior storage; enabled zero controls require an initial zero fact.

Inspected /tmp/eip-CreationSettlement-local-compile.log: seven printed public theorem reports contain standard Lean axioms only. No proof edits by reviewer. Full exact-commit integration check follows separately.


---

