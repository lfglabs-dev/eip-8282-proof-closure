# Independent inversion and initialization reviews

Exact candidate: `018cd2dc722fc5c0dc900d09b104765eb684e25f`.

# Independent review: CallSuccess

Outcome: CLEAN for the claimed semantic transport scope.

Reviewed complete `Eip8282/Audit/Integrator/CallSuccess.lean`, SHA-256
`fa0714e036da0b40ee638f60d57b9ba70a487635be4ca6678fc13be31938eccc`,
with `MessageCall.lean` settlement and `CallBridge.lean` fuel transport.

True Θ status rules out both interpreter errors and REVERT and yields an actual
successful Ξ execution. Created accounts, remaining gas, and return bytes are
the same. World and substate retain the exact upstream conditional: an empty
execution world selects the pre-call world and substate. The theorem neither
assumes nonempty nor silently identifies Ξ and Θ worlds. `codeCall_of_success`
uses the established exact fuel bridge with `c.fuel = steps + 1`.

No admission, funding, code-installation, resource-sufficiency, or protocol
reachability property is claimed by these transport theorems. This review was
read-only and did not rebuild the module; parent supplied successful compile.


# Independent review: SuccessInversion

Outcome: CLEAN for the stated successful-execution necessity scope.

Reviewed complete `Eip8282/Audit/Integrator/SuccessInversion.lean`, SHA-256
`16296f56350ba53322d29e8cce6c8799ae95c175489d92689ed170d2875297c7`.
Also inspected the underlying X successor equations, symbolic step/block
soundness interfaces, both pinned fee-cycle blocks and entry numerator
definitions, `feeExit`, and the complete `FeeQuote.lean` evaluator interface.
This was a read-only review; parent supplied a successful final compilation.

`success_step` distinguishes interpreter errors, continuation, normal halt,
and REVERT from the actual X result. `success_continue` and the symbolic
inversions preserve the same final state and bytes, recover Z acceptance, and
decrease actual interpreter fuel. The symbolic block shape is a checked local
instruction computation, not an assumed complete post-state. No gas lower
bound or loop completion is supplied by the public consumer.

The nonzero fee cycle is exactly six test instructions, one JUMPI, and seventeen
body instructions including JUMP: 24 instructions. Its word recurrence matches
`feeExit`: accumulator addition; modular numerator-times-accumulator; modular
counter-times-17 before division; modular counter increment. Strong induction
uses the actual smaller continuation fuel. Accumulator zero is a valid base
case at zero additional recurrence budget. There is no 256-iteration cutoff.

The entry-path inversions prove non-SYSTEM calls cannot remain inhibited:
that branch reaches the concrete REVERT instruction, contradicting successful
X execution. Both count branches recover the actual operational numerator.
The Ξ wrapper inversion retains the exact published tuple and bytes, then
derives an existential completed operational quote from the real fee head.

The final statements do not yet identify the returned getter bytes with this
price, classify arbitrary successful appends/payment checks, prove natural
tariff equality, guarantee termination for all inputs, or establish protocol
reachability. Those limits are correctly stated in the source.


# Independent review: SuccessfulQuote.lean

Result: CLEAN, current source.
SHA256: 8acb62d979b209dc403385810fc25e242bd834cbc0ce13f53651660240f452d6
Worktree: /Users/thomas/work/eip-8282/direct-closure-implementation

Read the complete SuccessfulQuote and CallSuccess sources, checked the relevant SuccessInversion chain (actual X step/block/branch inversion, nonzero fee-cycle descent, user entry to fee head and Xi success extraction), the quoteWithin/feeExit adapter, and the actual Ξ/Θ wrappers.

positive_fuel correctly derives c.fuel>0 from an actual Θ success: CallSuccess excludes error and REVERT, producing successful Ξ execution, while Ξ at zero interpreter fuel is OutOfFuel. The public theorems use the derived c.fuel=(c.fuel-1)+1 equality to construct precisely the pinned codeCall index. They do not silently assume a caller-supplied fuel offset or sufficient gas.

The actual successful Θ status supplies successful Ξ execution even if Θ uses the empty-world fallback; CallSuccess preserves the fallback relationship for world/substate instead of assuming equality. SuccessfulQuote only needs the successful execution, so discarding these two equalities is legitimate. codeCall uses Θ's actual transferred entry world and environment, and the huser test c.caller is definitionally the execution source. Both runtime byte strings are explicitly pinned.

The consumed inversion theorem derives uninhibited entry and completion of the exact operational UInt256 fee recurrence from actual user success. The 24-instruction cycle is descended along strictly decreasing interpreter fuel; there is no legacy256 cutoff, sufficient-gas premise, assumed loop completion, natural arithmetic agreement or assumed postcondition. The completed quote starts from output0/accumulator17/counter1 and ends in division by17, matching quoteWithin.

Scope is correctly stated: this proves a necessary condition for successful calls at arbitrary resources, not that every enabled call terminates, that any quote is mathematically correct, or that the final output equals the quoted price (submissions return empty bytes). It also does not establish installed-code identity or upstream protocol funding/authorization. No blocking correctness or scope findings.

Existing compiler receipt inspected: /tmp/eip-SuccessfulQuote-1.log; both public parents report only propext, Classical.choice and Quot.sound. No proof edits or build performed during this review. Final exact-commit binding remains separate until integration.


# Independent review: ResourceBounds.lean

Result: CLEAN, current frozen source.
SHA256: 099a06b7178531f58fb8c889ecd583bbe7fd890d1490ae0261d971f5640d87b6
Worktree: /Users/thomas/work/eip-8282/direct-closure-implementation

Read the complete source and checked the imported AppendFits definition and physical stride values. This is an arithmetic implication over explicitly typed accounting inputs, not a proof of EVM gas accounting or arbitrary protocol histories.

For each BlockUsage, the Fin(2^64) gas field gives gas<=2^64-1 and the explicit charged field gives appends<=gas. Summation therefore yields totalAppends<=numberOfBlocks*(2^64-1). Nodup applies to the projected slot values, not to whole BlockUsage structures; Fintype cardinality correctly bounds numberOfBlocks by 2^64 even if other fields differ. Combining gives at most2^128-2^64 appends, hence strict total<2^128. The weak one-gas-per-append envelope suffices arithmetically and is not smuggled in as an execution fact.

appendFits_of_accounted separately requires actual entry tail and count bounded by that total. With strides3/6, the resulting physical window, counter successor and tail successor all fit below the256-bit modulus. control_sum_fits separately requires excess and count bounded by total, and concludes only their sum fits. It does not cover an inhibited excess value through an omitted exception, and does not claim the fee recurrence's numerator-times-accumulator product fits.

No circular assumed storage postcondition occurs. The unproved obligations are stated clearly: charged must be connected to actual transaction/block gas including nested calls and refunds; distinct64-bit slots and gas fields must be justified for the chosen canonical protocol history; actual tail/count/excess must be linked to the accounting total. The file expressly does not declare those bridges proved. The documentation reference is a pointer to external-source work, not evidence certified by this arithmetic review. No blocking findings.

Existing standalone evidence inspected: /tmp/eip-ResourceBounds-1.log. All three printed theorems report only propext, Classical.choice and Quot.sound. No build or proof edit was performed during this review. Final exact-commit binding remains separate until integration.


## Root independent reviews — CLEAN within stated scope

Initialization, QueueInvariant and DirectMutations were reviewed independently
of their authors. Their exact source bindings at this candidate are:

* `Eip8282/Audit/Integrator/Initialization.lean`: `3a18b65cff2c7ca6ae1500322c283362e89802ebf515092518ead9671ce23c5d`
* `Eip8282/Audit/Integrator/QueueInvariant.lean`: `5e15726133885b59340a5ffc4d8650fe33d4cda27639039ad1fe92fe49de5219`
* `Eip8282/Tests/DirectMutations.lean`: `aa3ec12bc05b491eade0adbd1e7076e288ad9cba06041b194054c19db0002f8d`

Initialization follows the actual init CODECOPY/RETURN and exit SSTORE paths.
The private runtime-pinned template only constructs at_ states; actual execution
uses the substituted init state and init jump destinations. Returned runtime
bytes are proved against pinned byte strings. Owner and zero-control inputs
remain explicit. No CREATE installation or genesis claim is inferred.

QueueInvariant uses independent physical word vectors and natural queue lists.
Window fit supplies separation of old/new/control slots; append extends exactly
one vector and drain retains the suffix. Actual Θ output is identified with the
encoded list prefix. Exit source width follows the actual caller type and is
preserved by append/drop. These local invariants are not protocol histories.

DirectMutations interprets existing finite successful-result observations through
the same direct expectedSlot/AppendedLog predicates. No contradictory runtime-pin
premise is used. The six refutations retain only their existing, specifically
named native receipt dependencies; they are finite corroboration, not new
universal guarantees. Full check passed in an exact detached source checkout.
