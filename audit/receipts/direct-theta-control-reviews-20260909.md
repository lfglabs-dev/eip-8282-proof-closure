# Reviews: ordinary gas and same-predicate Θ control mutants

# Independent integrator review: OrdinaryGas

Source SHA-256: `d41661f413814579343e04a37da8cb87624881f63ac132440077beb8dc0adfd4`.

CLEAN within the ordinary-opcode scope. Ordinary is exactly the complement of CALL, CALLCODE, DELEGATECALL, STATICCALL, CREATE and CREATE2, proved by exhaustive constructor cases. Gas-field preservation is distinguished from the stack value read by GAS; the dispatch proof retains actual cost subtraction and execLength update. SELFDESTRUCT gas projection handles both created-account branches without balance or owner assumptions. INVALID is not trusted through the raw default: accepted_valid derives its impossibility from actual Z. The natural debit gets memory/opcode sufficiency from accepted_gas, so no word underflow or assumed final balance occurs. XRuns support is an explicit property of actual labels and the prefix debit remains valid before later error/revert. This does not yet extract every such prefix from arbitrary X or cover recursive child frames. Final successful halts are linked through actual success_step. Targeted compile /tmp/eip-OrdinaryGas-8.log passed without warnings and with standard axioms only.

---

# Independent review: DirectThetaMutations

Outcome: CLEAN for the claimed finite actual-Θ mutation scope.

Reviewed source: Eip8282/Tests/DirectThetaMutations.lean
SHA-256: c324c198700f99d1255ee86ff485b0eb2693de67498302e614048ee1f4583801
Worktree HEAD during review: 5828bb3ffd38233be0c30542a0339fbf9d1bd479
Read-only review; no build or source edits. Inspected the supplied successful compile/axiom output /tmp/eip-DirectThetaMutations-5.log.

Bindings inspected:
- DirectGuarantees.lean: 9b39dc88aac5acb38b4ef7bac387739e9e0e1ab52f5c0e6994b9e1d0a792850d
- MessageCall.lean: 3f16088bd13b6f6fdf13de417e4843f08e9dcd61fa6dfdddfc6342c250ccf342
- Pinned EVM/Semantics.lean: 8b49f1aee609ce888041ba9e7253bbe55d06fda136252bc46d4e006755110f4b
Also read the old PControl1Mutant receipts, DirectMutations receipt projection, EvmRunner, DirectControl.Observed, SystemDataSpec.ControlSlots, and the WorldNonempty proof.

## Findings

1. The parameter code is installed in the actual fixture account and supplied to actual Θ. The fixture uses SYSTEM, zero actual/apparent value, empty calldata, the old runner's original world/environment/gas, and EXCESS=100, COUNT=5, HEAD=TAIL=0. No original-runtime equality appears in the domain proof. control_domain proves Domain deposit (controlCall code) 105 for every code: owner exists, value agreement, calldata fits, budget is below 2^128, ordered/bounded pointers and control values, and enabled quote numerator 100 is below 2892. control_installed independently confirms parameter-code installation. This is local domain membership, not a protocol-reachability certificate.

2. The transport is a real execution identity. deposit_entry proves the actual credit-then-debit entryWorld equals the old world for these zero-value calls. deposit_execution then identifies Context.execution with the exact old runDepositSystem expression, including fuel. Context.execution invokes Ξ at c.fuel; Context.result invokes Θ at c.fuel+1. There is no off-by-one substitution or replacement interpreter.

3. The published tuple is extracted from the existing successful slot observation. success_of_slot cannot succeed on error, revert, or missing owner. Its actual owner lookup supplies WorldNonempty.beq_empty_false_of_get_some, which rules out Θ's actual empty-world fallback using map size, without assuming lawful Account boolean equality. success_commits_world therefore publishes that same created/world/gas/substate/output tuple with true status. worldSlot_of_receipt reads this same world, rather than an assumed post-world.

4. The gate mutant is the old one-byte EQ-to-LT dispatcher mutation. Its actual successful Θ result retains COUNT=5, contradicting the independent SYSTEM COUNT=0 postcondition. The target mutant is the old PUSH-operand 8-to-9 mutation. Its actual successful Θ result has EXCESS=96, contradicting the independent target-8 result 100+5-8=97. Both counterexamples use the same DirectControl.Observed as the pinned runtime theorem. RuntimeControl is refuted by instantiating its universal quantifiers with this actual result and the code-independent budget-105 domain. PControl is then refuted through its RuntimeControl conjunct for every initializer; the additional initializer/progress conjuncts do not manufacture the contradiction.

5. No new native_decide, sorry, or project axiom occurs in the new file. The reported transport/domain axioms are only propext, Classical.choice, Quot.sound. Each reported counterexample/PControl refutation additionally uses exactly its historical PControl1Mutant native-evaluation axiom: gate_mutant_loses_the_system_subroutine._native.native_decide.ax_1_1 or target_mutant_shifts_only_the_system_recurrence._native.native_decide.ax_1_1. Kernel decide is used only for closed arithmetic contradictions and local domain facts. These remain finite corroborating execution receipts, not native-free universal proofs.

Scope: this closes same-predicate actual-Θ corroboration for these two deposit control mutants. It does not establish exit, submission, drain or constructor mutation coverage, arbitrary-mutant detection, transaction/block admission, or protocol-history reachability. No blocker found within the declared scope.

## Smallest next funding bridge

A narrow actual-CALL entry funding lemma is now straightforward without a new abstract transition:

- Reuse CallFamilyGas.address_word (already implemented): AccountAddress.ofUInt256 (UInt256.ofNat addr.val) = addr. Its proof derives the 256-bit fit from addr's 160-bit Fin bound. No new roundtrip lemma is needed.
- Use the literal AuditedChildGas.context, already bound to the actual CALL child Θ by context_result. Its world is pre.accountMap, caller is the converted codeOwner, and actual value is the stack value.
- From the actual EVM.call gate, value ≤ the codeOwner balance (zero if absent), obtain value.toNat ≤ TransferFunding.worldBalance pre.accountMap pre.executionEnv.codeOwner by case analysis on that lookup and UInt256's natural order. Rewrite the context caller with address_word. This is precisely TransferFunding.entry_funds_le's premise.
- Conclude worldFunds (AuditedChildGas.context ...).entryWorld ≤ worldFunds pre.accountMap; optionally transport an independently supplied pre-world budget. The gate is a pre-execution branch condition, not a desired postcondition. The existing context_result binds the exact selected code and positive child fuel. Step's instruction-count update and Z's gas/memory charging preserve the relevant account map/environment; their existing projection lemmas should bind the gate to the actual dispatcher state.
- CALLCODE has the same checked sender and an alias recipient, which TransferFunding already handles. DELEGATECALL and STATICCALL transfer zero actual value, so the funding premise is automatic, regardless of their distinct source/apparent-value rules.

Do not claim the generic EVM.call helper's gate funds an arbitrary source argument: the gate checks codeOwner while its source parameter is independently supplied. The dispatcher source identity (or zero actual value) is necessary. A completed helper can also take the denied branch; do not infer admission from helper completion alone. An actual child-result witness must be extracted from the admitted branch, or admission must remain an explicit branch premise.

This next lemma establishes one entry-transfer nonincrease. It does not yet establish nonincrease through recursive child execution, CREATE/SELFDESTRUCT/precompiles, Υ settlement, or an externally justified total funding ceiling.
