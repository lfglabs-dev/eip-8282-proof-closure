# Recommendation: register the three conditional direct parents

Read-only recommendation. No proof, registry, YAML or checker files changed. The three canonical public IDs remain unchanged. This note is a registration proposal, not a claim that the complete protocol-domain closure has finished.

## Minimal registration

After the funded LOG0 witness and final exact-source validation, point both `parent` and `evm.theorem` at these existing theorems:

| Public ID | Exact new parent |
|---|---|
| P-SUBMIT-1 | Eip8282.Audit.Integrator.DirectGuarantees.psubmit1_direct |
| P-DRAIN-1 | Eip8282.Audit.Integrator.DirectGuarantees.pdrain1_direct |
| P-CONTROL-1 | Eip8282.Audit.Integrator.DirectGuarantees.pcontrol1_direct |

Each theorem is quantified over both contract kinds and proves the parameter-code predicate at runtimeCode kind (and the pinned initializer for control). Do not conjoin any finite trace, old CFG parent, abstract correspondence obligation, opcode pin or mutant result into these theorem types. Keep the original *_forall_parent definitions and their dependencies unchanged as historical evidence. The direct proof has no need to inherit their native evaluation axioms.

Retain the Registry's same three Id constructors and model/evm layers. Its evm comment should cover actual Θ settlement as well as Ξ execution. Registry.Guarantee currently contains only ID/layer labels, not a typed parent reference; the load-bearing theorem selection is in YAML. AllGuarantees should import the direct module and expose/check its three exact instances so public Lean users see the same selected statements. No new model, new public ID, wrapper predicate or expanded registry framework is necessary.

Add one explicit checker scope, e.g. `THETA_CONDITIONAL_FORALL`; use it for all three rows. Keep `evm.status: CHECKED` limited to this precise conditional theorem scope, while `classification.kind: PARTIAL` and a named OPEN protocol-closure field/next_gate record the unfinished audit obligations. Existing `CONCRETE_TRACES`, `WELL_FORMED_FORALL` and `CFG_FORALL` are inaccurate names for the new statements. Update objective, summary, executes, world, fidelity and next_gate together; do not leave obsolete CFG/model closure prose as the primary description.

The checker currently accepts only those three old scope strings. It also requires parent=evm.theorem, an existing kill-line theorem, canonical ID order and declared assumption IDs. Its theorem-existence test only looks for the short name text anywhere in sources; this is not a Lean type or full-qualified-name check. Keep all pin checks unchanged and supplement metadata validation with Lean compilation and explicit axiom/type inspection. Do not treat a successful Python metadata check as proof of same-predicate mutation refutation.

## Exact conditional scope to publish

Runtime predicates quantify every actual completed Θ tuple, including success=false, at arbitrary evaluator fuel, EVM gas, permission, surrounding AccountMap, original world, header and substate. They are not limited to the historical two-account fixtures. OutOfFuel is an evaluator error, outside the quantified `.ok` tuple; no successful completion is promised for every user call. Actual failed completed calls restore the entry journal; this is not a transaction-fee refund.

The common independent input domain is:

- target account exists before entry transfer;
- apparent CALLVALUE equals actual transferred value;
- natural calldata size is below 2^256;
- an independent natural budget is below 2^128;
- HEAD <= TAIL <= budget, count <= budget, and, when enabled, excess+count <= budget;
- either inhibited or natural fee numerator excess+max(0,count-TARGET) <= 2892.

These are pre-state/input assumptions, with no code pin, desired poststate, path witness, fee-loop-completion hypothesis or funding ceiling inside them. The code parameter is constrained only by the surrounding theorem/predicate instantiation. Fee semantics are untruncated; 2892 is an explicit safe arithmetic domain, not a 256-step meaning of the tariff. The certified terminating upper trajectory does not justify that all protocol states lie in this domain.

Drain additionally requires the independent physical-word queue representation, ordered/nonaliasing physical window, and, for exits, each source word below 2^160. Its successful SYSTEM result is exactly the encoded oldest capped prefix and represented suffix with natural pointers and stale words preserved. Users keep HEAD and preserve the old queue as a prefix, appending exactly one data-derived record on nonempty success. Failed calls retain the world/queue.

Submit covers actual paid nonempty user success with one authentic record/log and an empty return; deposits are exactly 184 calldata bytes and have the actual minimum amount of 10^9 gwei in addition to the mathematical fee+stake check. Exits use caller20 || calldata48. No signature validation is claimed. Successful getters preserve account lookups, created accounts and logs with value zero; access bookkeeping may change. SYSTEM adds no log and preserves all record slots. Do not summarize necessity as unconditional 'well-formed paid input always succeeds'.

Control currently includes THREE conjuncts: RuntimeControl, DirectInitialization.Initializes, and SystemProgress.Progress. Preserve the last two in registration. Runtime control includes the actual fee getter, count/excess transitions and inhibition rollback. SYSTEM progress requires target owner, write permission, gas>=2,500,000 and Context.fuel>=8503 and has no enabled-state assumption. It is a separate sufficient-resource assertion, not an arbitrary-resource liveness claim.

The initializer clause separately quantifies actual successful Lambda creation with address-preimage encoding success, no collision, absent target and the current explicit constructor resources: Context.fuel=steps+1; deposit gas>=1000 and steps>=8; exit permission, gas>=25000, steps>=11 and existing sender. It proves the actually installed runtime, initial controls, empty represented queue and unchanged logs. It does not establish creation success merely from those low init-execution bounds, canonical predeploy address identity or genesis installation.

## Assumption bookkeeping

Preserve A-ABSTRACT-TX and its counterexamples as OPEN historical global-model obligations; remove it from the new direct-parent dependency list rather than announcing it proved. The new correctness theorem does not rely on that correspondence. Likewise old A-REACHABLE packed-storage coverage is historical supporting evidence, not a justification of the direct domains.

Keep A-CLASSICAL-CHOICE for the direct theorem trust declaration. Keep A-NATIVE-DECIDE on historical traces and the five transported legacy mutation receipts, not on the universal parents. Record each exact mutant's transitive axioms separately; do not assume the pending funded LOG0 certificate has native dependencies.

Split local domain assumptions from environmental application obligations in metadata. New descriptive assumption records such as A-DIRECT-DOMAIN and A-PROTOCOL-CLOSURE are acceptable without adding public guarantee IDs; alternatively equivalent explicitly scoped fields can be used. The first lists the exact hypotheses above; the second stays OPEN and explains their extraction from initialized protocol execution. Avoid redefining an old assumption silently so historical claims appear discharged.

A-EVM-WORLD's existing claim that the whole bytecode theorem uses only a synthetic two-account/default-header world is obsolete for direct parents. Archive that scope for finite fixtures. The remaining semantic assumption is adequacy of the exact pinned EVMYul evaluator and correct binding of real calls to its Context. A-PINNED-SOURCE remains OPEN for deployment/protocol provenance; actual Lambda installation proves an internal code result, not canonical genesis allocation. Neither a live codehash check nor constructor correspondence alone proves all history/admission obligations.

## Same-parent kill lines and cross-impact

Use the exact code-parameter predicates, not the older Boolean facts or DirectMutations.SystemPost. Existing direct transports expose these named refutations:

- DirectThetaMutations.gate_refutes_pcontrol and target_refutes_pcontrol (runtime violation implies failure of the full control conjunction, with arbitrary initializer parameter).
- DirectThetaDrainMutations.deposit_cap_refutes_pdrain, deposit_stale_refutes_pdrain and exit_cap_refutes_pdrain.
- Funded LOG0: register only after its actual Θ receipt, independent Domain and `¬ DirectGuarantees.PSubmit .deposit logSizeMutatedDeposit` theorem have all compiled and been independently reviewed. An `.Ξ` result or `actual_empty_log` fact alone is not enough.

A small test-only conjunction theorem per public ID can supply the YAML's single kill_line.theorem field while collecting its relevant refutations. Such a conjunction belongs only in the mutation module; the universal parent must stay unchanged. Check original pinned instances build at the same commit, each mutation is the documented byte cut, each fixture satisfies the same code-independent domain, the actual settled Θ result is used, and the negated predicate is exactly the parent's parameter-code type. Also check nonempty-world settlement and real/apparent value equality; the funded LOG fixture must not equate old untransferred Ξ balances with an actual funded entry world.

Conservative cross-impact matrix at this review:

| Mutation | P-SUBMIT-1 | P-DRAIN-1 | P-CONTROL-1 |
|---|---|---|---|
| Deposit LOG0 size | Pending actual-Θ exact-PSubmit certificate | Universal survival not established | Universal survival not established |
| SYSTEM gate | Not established | Not established | Exact predicate refuted |
| Deposit TARGET | Not established | Not established | Exact predicate refuted |
| Deposit cap | Not established | Exact predicate refuted | Not established |
| Exit cap | Not established | Exact predicate refuted | Not established |
| Deposit stale record slot | Direct consequence of the same receipt/spec; separate refutation not yet checked | Exact predicate refuted | Not established |

For the last row, the actual receipt changes slot9 from `0x5500 * 2^240` to 64 on a successful SYSTEM call. PSubmit.SubmitObserved requires every k>=4 to retain the pre-world value, so that very witness also contradicts PSubmit once instantiated with the common Domain (the drain domain contains its fields). This is an explicit semantic overlap; do not weaken PSubmit to manufacture independence. If marking this cell as a compiled exact-parent refutation, add/check that short theorem first. Other blank/not-established cells are not claims of survival or failure.

The old `log_mutant_leaves_siblings_intact`, `drain_mutants_leave_siblings_intact`, and `control_mutants_leave_psubmit1_intact` quantify only concrete Boolean drainFacts/controlFacts/submitFacts. The old comments saying entire siblings stay true exceed those theorem types when applied to the new universal predicates. Archive them as finite regression discrimination only. Exact-parent negation does NOT require universal sibling survival. If an older campaign acceptance rule demanded that stronger property, it remains unproved and sometimes incompatible with the present overlap; the parent has explicitly instructed that this superseded guideline must not force a false independence claim. Publish no universal independence assertion.

## What registration does not finish

Keep a separate protocol closure gate: actual transaction/call admission and value binding; funding conservation through recursive execution and settlement, account destruction/creation and transaction fees/refunds; externally funded supply/withdrawal bounds; nonduplicated append-event accounting including nested successes later rolled back; block/history extraction and resource envelopes; deployment/genesis binding; and derivation of every local queue/arithmetic domain from those actual histories. ConcreteHistory establishes useful linked-call induction under explicit budget/funding inputs, not these protocol facts automatically. Recently compiled local gas/funding lemmas are supporting progress, not substitutes for this composition.

Register only as the explicit conditional direct result after exact candidate review, full make check, metadata/pin checks and separate trust reports for direct parents versus historical/native mutation evidence. This is a useful change in the public evidence surface; it must not be presented as completion of the still-open full audit objective.

## Source bindings for this recommendation

- `Eip8282/Audit/Integrator/DirectGuarantees.lean`: `9b39dc88aac5acb38b4ef7bac387739e9e0e1ab52f5c0e6994b9e1d0a792850d`
- `Eip8282/Audit/Integrator/DirectInitialization.lean`: `c195ad44ccc597fa534d8337b5b60d4e16976b0b1273f56b615a67019a465458`
- `Eip8282/Audit/Integrator/SystemProgress.lean`: `543378c2b97f1eb7668c68f15742bc23d784c8c0ba9b22c89a6983f7f34d77b7`
- `Eip8282/Audit/Guarantees/Registry.lean`: `1250ee23139d6853e3446a30638aa65aa74d46e636d8539634e7d62686312699`
- `Eip8282/Audit/AllGuarantees.lean`: `fba27ef400436b4d22dc1c90e9652555709b2e2a987ab7e33d4658a1682c1ad2`
- `audit/guarantees.yaml`: `a2b33fe9c37c59ffc130f7acb6f1507df9f332e5525351192dcf7af98d41b97e`
- `audit/assumptions.yaml`: `7a08d31e70fe8ffbe10a132c14a64c53522eb8b776751ded0f898858e676f158`
- `scripts/audit_metadata.py`: `22b140e8212f5bc9da9f7126c98f6774b572d7f6ea1e62492441aea3ffbcbdc5`
- `Eip8282/Tests/DirectThetaMutations.lean`: `c324c198700f99d1255ee86ff485b0eb2693de67498302e614048ee1f4583801`
- `Eip8282/Tests/DirectThetaDrainMutations.lean`: `cf371254f95e1d3e309d0deab724ccd7088e76a81dbc58f4e85dd20e4205f99b`
