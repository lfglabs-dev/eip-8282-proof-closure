# Independent reviews: direct specification and CALL gas candidate


---

# CallGasAccounting — independent source review

**Outcome: CLEAN for the stated actual-helper/local gas-accounting scope.**

Complete file reviewed read-only at SHA-256 `35fc0df6019b4de427b3a1fced13564fa41b9c3a7e16ac40b9a929f8391f78b1`. The supplied `/tmp/eip-CallGasAccounting-final.log` contains seven principal reports, all with only propext, Classical.choice and Quot.sound. No build or source edit performed. The source hash was checked before and after the dependency inspection.

## Actual semantics and recovered result

`child` reproduces the funded branch of the pinned EVM.call: exactly the same child fuel, original account map and σ₀, created accounts, warmed target substate, code resolution, source/recipient/origin, forwarded gas, gas price, actual/apparent values, padded input, incremented depth, header and permission. The helper computes Ccallgas before subtracting its cost. Its gas-only state update does not alter the other child arguments; the definition respects that order.

`call_child_result_gas` starts with an actual successful result of EVM.call and recovers an actual Θ result by case analysis. Child errors contradict that actual helper success. Child status can be true or false. The word equation is recovered from the returned EVM.State; there is no predicted poststate, desired gas equality, or child success premise smuggled in.

The arbitrary source/apparent/permission arguments are legitimate parameters of the helper being proved. They do not establish that the enclosing opcode dispatcher supplied the canonical CALL arguments. The module header and final theorem documentation explicitly retain that missing dispatch layer, including EVM.step's execLength increment. This limitation must remain in the ledger.

## Accepted Z and natural gas

The pinned Proof.Execution.Z first checks/debits memory expansion and then computes/checks C' on that charged state. accepted_call_cost reads the unchanged stack on that same state and selects Ccall with target=recipient, matching ordinary CALL. It does not silently use the pre-memory gas for Cgascap.

The reviewed ActualAppendGas.accepted_gas dependency derives both comparisons from those real checks. accepted_call_forwarded_fit then proves the child allowance fits UInt256 *before any returned-gas assumption*. This is useful: the child's input gas is not identified with a natural budget merely by assuming the desired child result.

The pinned gas definitions are:

- Ccallgas = Cgascap + stipend(value).
- Ccall = Cgascap + Cextra.
- The nonzero-value stipend is 2300; Cextra includes the value-transfer charge 9000, plus nonnegative access/new-account terms.

Therefore stipend≤Cextra and Ccallgas≤Ccall, including zero value. The code correctly uses transferred value, not apparent value, when selecting the stipend. No additional EIP-150 arithmetic or favorable cap branch is assumed; the definitions retain their actual branch/min expressions.

`settlement_nat` explicitly assumes returnedGas≤the real child allowance. Together with accepted cost≤gas, it derives all word casts, debit subtraction and returned-gas addition fits. Its exact identity charges `(child allowance - returned gas) + (Cextra - stipend)`. The subtraction of the stipend from the parent's overhead is necessary because that stipend has already been included in the child's allowance. The arithmetic does not count it twice.

`accepted_call_child_debit` recovers the actual child first and exports the remaining-gas bound as an implication on that same witness. It then adds the *single* real memory-expansion charge to obtain the identity against the original Z input gas. It does not prove the child remaining-gas bound, aggregate subtree gas, or append-event uniqueness. This is a conditional local bridge, and the statement accurately reflects that scope.

## Denied branch

`call_denied_gas` uses the negation of the actual funds/depth conjunction. The pinned branch does not call Θ, uses false status, and returns the full Ccallgas word, including a stipend for nonzero transferred value. The theorem correctly proves x=0 and the exact word equation. It does not claim natural nonwrap or positive net cost without Z acceptance. This also covers raw helper inputs with depth greater than 1024: the branch's false status forces x=0 even though the later Boolean depth test alone uses equality with 1024.

No blocking defect or circular premise found in the claimed scope. The denied branch could subsequently be combined with accepted_call_forwarded_fit and settlement_nat to obtain its natural debit, but that corollary is not required for correctness of the current word theorem.

## Scope not established

- No full CALL opcode/X trace theorem yet: the exact dispatcher update and arguments must be transported.
- No CREATE/CALLCODE/DELEGATECALL/STATICCALL whole-step accounting theorem.
- No proof that every child, including precompiles and exception cases, returns at most its allowance.
- No counting of distinct append occurrences, reverted descendants, transaction totals or protocol gas limits.
- No gas sufficiency hypothesis is being advertised as a protocol invariant.

Dependency hashes inspected:

- EvmYul/EVM/Semantics.lean: `8b49f1aee609ce888041ba9e7253bbe55d06fda136252bc46d4e006755110f4b`
- EvmYul/EVM/Gas.lean: `9f06caccf5cc8f27f7822392cd1963c8353eb816052f4596321a12c2da707436`
- EvmYul/EVM/Proof/Execution.lean: `8c70c77f09ec1b867788afbf1ddb8b6927b4fc5fd1cf8fee40e965a67eff8af5`

ActualAppendGas is an existing implementation of mine, inspected here for the exact dependency interfaces and underlying Z checks; this is not presented as a new independent review of my own module.

## Bounded next balance lemma proposal — no implementation in this review

A narrow, real transfer theorem looks tractable without any foundation changes:

```
worldBalance world addr := ((world.get? addr).map (fun acc => acc.balance.toNat)).getD 0
worldFunds world := (world.toList.map (fun kv => kv.2.balance.toNat)).sum

entry_funds_le (c : MessageCall.Context)
  (hfunded : c.value.toNat ≤ worldBalance c.world c.caller) :
  worldFunds c.entryWorld ≤ worldFunds c.world
```

This refers to the existing exact credit-then-debit `Context.entryWorld`, not a replacement transfer function. It does not claim conservation through code execution. It should include caller=target and missing accounts; no total-supply premise or predicted poststate is necessary for **nonincrease**. For distinct accounts a credit overflow can only lower the natural total, while hfunded prevents the debit underflow. For the same account, `(b+v)-v=b` as words gives an unchanged balance even if the intermediate credit wraps. A missing sender under hfunded forces value=0; new zero-balance map entries do not affect the sum.

The available finite-map lemmas are sufficient starting points and do not require LawfulBEq on Account:

- Std.TreeMap.toList_insert_perm (Std/Data/TreeMap/Lemmas.lean:298): insertion is a permutation of the new pair followed by the old list filtered by key. Its BEq requirement is on addresses only.
- Std.TreeMap.mem_toList_iff_getElem?_eq_some (:899), nodup_keys (:860), distinct_keys_toList (:956), and getElem?_insert/getElem?_insert_self for lookup/sum decomposition.
- Std.TreeMap.foldl_eq_foldl_toList (:976) if the chosen interface uses foldl.
- Existing TransferFrame has the actual transfer decomposition and lookup/owner cases, but its useful internal helper lemmas are private; do not change their visibility just to support this bounded task.

First prove the subtraction-free sum replacement identity:

```
worldFunds (world.insert key account) + worldBalance world key
  = worldFunds world + account.balance.toNat
```

Then prove the funded transfer nonincrease by the actual two map updates. Only three additional arithmetic/lookup ingredients are needed: old balance≤worldFunds; natural word-add≤natural sum; and the self-transfer word cancellation. A stronger equality for distinct accounts can follow under an independently proved total-supply fit, but is not needed for the first bridge.

Alternative if list/permutation proof plumbing dominates: define worldFunds as the finite sum of defaulted balances over AccountAddress (a Fin type), prove insertion by pointwise lookup and a single-key Finset.sum split. This is a symbolic finite sum, with no enumeration or evaluator trace. Do not attempt to normalize its 2^160-element universe. The toList interface is preferable for later concrete accounting/certificates; the two definitions can be related later if needed.

This proposal is source-based feasibility analysis only: no Lean prototype or targeted compile was run. It does not cover Lambda's alias/collision setup, SELFDESTRUCT, Υ fees, rollback trees, or protocol funding; those should remain separate subsequent tasks.

---

# Independent review: actual CALL opcode dispatch gas

Reviewed by the integrator against pinned EvmYul/EVM/Semantics.lean (CALL dispatch and call helper) and the frozen CallGasAccounting interface. No change to semantic pins.

Source SHA-256: `e1c5f79113ed283b4193bf6548adf7b91190a5b37183b00caf19a644460c6d4b`.

CLEAN within stated scope. step_call_helper unfolds the actual step, performs its actual seven-operand pop, increments execLength before the helper, and retains the exact post-helper stack/PC update. Its fuel offset is step(fuel+2) → call(fuel+1) → Θ(fuel). Both success and false child statuses share the returned-gas equation. Accepted Z supplies actual memory cost and sufficient opcode debit. The funded natural identity explicitly requires local child returned≤allowance; it does not assume aggregate event charges. The denied path pushes zero, credits back forwarded gas and creates no child invocation. Overhead minus stipend avoids double counting value-transfer stipend. Variants, CREATE/precompiles, arbitrary exceptional prefixes, remaining-gas monotonicity and tree extraction remain open. Targeted compile /tmp/eip-CallDispatchGas-3.log passed with standard axioms only.

---

# Independent review: AppendDataSpec

Verdict: CLEAN for code-independent data specifications and exact adapters to the existing append predicates.

Reviewed source: Eip8282/Audit/Integrator/AppendDataSpec.lean
SHA256: 6f74417e67adbe2d42fb62bd69e7b53eea17d05a71e0ca53c4c533cf42c6c2d1
Receipt examined: /tmp/eip-AppendDataSpec-1.log (reported exit0, no warning/error; four printed theorem closures use only propext, Classical.choice, Quot.sound). No builds or source edits during review.

Read the complete module, complete AppendSpec and ExitRecord, and all corresponding AppendStorage definitions including StoragePost. Every field matches:

- Read is the ordinary word-to-word storage read map; no executable frame or code pin is in its type.
- stride remains6 deposits/3 exits; count and tail read slots1/3; base is word4+stride*originalTAIL.
- recordKey has the identical recursive word increment and wrap behavior. No natural arithmetic is substituted outside Fits.
- calldataWord uses the same 32-byte big-endian readBytes/uInt256OfByteArray conversion. recordWord has six calldata words for deposits, and actual-source word then two calldata words for exits; the source parameter is a 160-bit AccountAddress.
- put, records and expected preserve the exact overlay order: count increment, all physical record words, then tail increment. Keys and both counter increments are based on the original read-map, not the evolving overlay. This matches old AppendStorage even when addresses alias outside Fits.
- Fits exactly matches the old conjunction: entire record window <=UInt256.size, count successor <UInt256.size, tail successor <UInt256.size. It asserts neither payment nor execution.
- ExpectedPost compares every observed post slot with the independent overlay.
- StoragePost preserves excess/head; states natural count/tail successors; states each authentic record word; and preserves every slot outside count/tail/record keys. None of the old fields or quantifiers is lost, weakened or replaced by an endpoint-state definition.
- record returns verbatim deposit calldata, or ExitRecord.addressBytes(source)++calldata. ExitRecord uses an independent fixed-width20-byte big-endian encoder. No signature or calldata-size validity is asserted by this data predicate.
- AppendedLog and AuthenticLog require the entire previous log sequence followed by exactly one record with the explicit owner and empty topics. They do not merely assert membership of some log.
- OtherAccountsUnchanged preserves exact account lookups at every nonowner address. The Theta consumer must use the transferred entry world as before; the source documentation states this correctly.

The bridge proofs are genuine definitional/inductive equivalences: record-key and records recursion are related by induction; expected instantiates those relations; Fits and StoragePost are field-for-field equivalences; log/frame correspondence is reflexivity. The old pinned XiCall appears only in these adapters. No replacement execution or code agreement premise is hidden inside a specification.

Scope limitations are accurately stated: no new admission/execution theorem, no physical-state reachability proof, no payment/fee-domain proof, and no independently justified fit bound. Arbitrary calldata is permitted as data; behavioral parents must derive exact admission length and bind the supplied source/owner/before-world to actual call inputs. Imports transitively contain old executable proofs, but the specification definitions themselves do not consume code or XiCall.

---

# Independent review: DirectAdmission and FundingBounds

Verdict: **CLEAN within the explicit conditional scopes below.** No incorrect inference or circular specification found. Read-only source review, no edits to proof files and no compilation/build performed by reviewer.

Exact source SHA-256:
- `Eip8282/Audit/Integrator/DirectAdmission.lean`: `6ff3c19de48cc96bb17410ead5074be485a8660149f07de44fe35960a10d379c`
- `Eip8282/Audit/Integrator/FundingBounds.lean`: `32f80b6277840cd0ac76bf355423eb2fb2d539a879bd8f4cd4508add3b4703f9`

HEAD at final hash/dependency sampling: `433d66310e9880a298dbbc5d48ca3550994c43b6`. Review is bound to these source hashes, not a claim that every file already belonged to that commit.

Complete contents of both candidate files read. Compiler evidence inspected: `/tmp/eip-DirectAdmission.log` and `/tmp/eip-FundingBounds-local-compile.log`; both contain the expected axiom reports with no errors/warnings. DirectAdmission reports only propext, Classical.choice, Quot.sound; FundingBounds reports propext and, for the general arithmetic proofs, Quot.sound. Its concrete numeric bounds use kernel `decide`, with no native-decide axiom.

## DirectAdmission

`PaidInput` and `Observed` contain no XiCall, pin, actual-success assumption, supplied execution path, or desired post-state equality. They read the input context, independent pre-world storage, and the supplied output. Context's code field does not occur in either predicate's logical conditions, so a mutant context is not excluded by an impossible original-code premise. The predicate's name “Observed” does not itself assert an execution: the public theorem must retain its actual Θ result hypothesis, as these two instances do.

Both `*_admission` instances start from `SuccessfulUser.*_admission` applied to the same actual successful Θ result. The existential operational `price` is retained, not replaced by an independently chosen affordable fee. Its `quoteWithin ... n = some price` witness comes from inversion of the real fee loop and its subsequent input checks. The same `price` supplies getter bytes or natural payment inequalities.

The storage inhibition test is transported from the actual transferred Ξ entry to the pre-Θ world using `TransferFrame.codeCall_storage`. Resolving `EnabledSafe` with that independently derived enabled fact yields the bound on the pre-world natural numerator. `SuccessfulUser.*_numerator` identifies the effective word numerator's natural value with that exact `E + max(0,C-TARGET)` expression, deriving no-wrap from ≤2892. `FeeSafeDomain.operational_quote_agrees` then identifies the same operational price with `MathQuoteCompletes` of that same natural numerator. TARGET=8/2 is independent of code and is not the next-SYSTEM-excess fold.

`MathQuoteCompletes` is existential completion of the untruncated natural recurrence (initial output0, accumulator17, counter1, numeratorX, denominator17). Fuel exhaustion returns none. FeeSafeDomain uses the kernel-checked upper trajectory and prefix monotonicity; 462 is a sufficient proof certificate budget, not a tariff cutoff and not a restriction on actual call fuel. Uniqueness allows any actual operational quote budget to be matched to that certificate.

Deposit `PaidInput` correctly requires exact length184, actual minimum amount≥10^9, and price+amount×10^9≤actual value in Nat. The amount is the eight BE bytes at calldata offset80. Units matter: amount is in gwei, so the minimum corresponds to 1 ETH, not 1 gwei. `SubmissionCall.deposit_checks` derives multiplication fit from the uint64 mask and subtraction non-underflow from the preceding fee payment check. Exit requires exact length48 and price≤actual value. Getter requires empty input, actual value zero, and exact 32-byte word representation. The ordinary-value equality and calldata size<2^256 remain explicit, avoiding DELEGATECALL/apparent-value confusion and logical-bytearray size truncation.

`paid_of_nonempty` simply eliminates the empty-input branch of this same existential observation. It does not drop or exchange its price.

Scope limitations are correctly documented: necessity of successful user admission only, explicit enabled-safe pre-domain, arbitrary actual execution resources. It proves no liveness, failure rollback, actual append/log/storage effects, protocol funding, or installed-code provenance. Paid-branch empty return bytes are intentionally not part of this admission predicate; they belong to the append receipt. No owner/bounds premise is needed for the stated necessary input/price result.

## FundingBounds

The file is arithmetic over Nat lists, not a semantics of issuance or a conservation theorem. The header and final theorem premises say this accurately.

`sum_le_length_mul` is a standard induction using an independently supplied bound for every list entry. `externalCredits` consistently counts genesis and PoW rewards in wei and withdrawal list entries in gwei, multiplying only the latter aggregate by10^9. Counting every withdrawal (including return of deposited principal) is compatible with an upper bound, provided the explicitly external conservation/coverage bridge is later proved.

`credits_le_envelope` separately bounds PoW entries and count, each withdrawal list's entries/count, and the number of such lists. It weakens strict <2^64 amounts to ≤2^64 safely, then applies monotonicity of multiplication/addition. Genesis<2^96 is weakened to ≤2^96. No disjointness, deduplication, 64-bit index provenance or actual block rule is derived from list lengths; these remain hypotheses as documented.

For perPayload16, the envelope is below2^163; allowing perPayload2^64 yields below2^223. Both comparisons and both inequalities against `FundedDomain.fundingCeiling` are kernel checked. The ceiling is the mathematically certified quote at X=2892 (`certificateOutput/17`), in wei, not an assumed word maximum. No bounded word arithmetic or truncation is used in these list sums.

The final `value_lt_funding_*` theorems chain explicit Nat inequalities: value≤balance≤total≤budget<ceiling. The reserved-fees variant derives value≤balance from value+fees≤balance using nonnegativity; it does not claim that actual EVM admission has checked this inequality. The credits wrapper combines the same chain with the conditional issuance envelope.

Thus the file supplies a useful, deliberately generous numeric margin, but it does **not** discharge ConcreteHistory/FundedDomain's funding premise by itself. Still required: actual genesis/fork issuance inputs and bounds; coverage of all positive credits; actual world-balance conservation or a suitable upper bound; account-to-total comparison; and actual transaction/nested-call funding/admission facts, including pre-transfer balances and rollback/reentrancy treatment. The 16-withdrawal and flexible versions are explicitly alternative assumptions, not current-protocol assertions. No web/protocol fact was needed or independently asserted in this proof review.

## Dependency bindings checked

- SuccessfulUser: `fb5651794e94dac56439daaeb3ca83aa4c012d6916998cb638b1fdee5e80afff`
- AdmissionInversion: `b77c1eef9df027a365baac47ae2978c78dec6e92948d6c0aa1162779019aa6a0`
- SubmissionCall: `face1db4310075322e020321797e520da7068221633495912bdd192b0ff1e7b8`
- FeeSafeDomain: `3f23254c5bcced81f37ca5e510e6575e940ff3dc2455d798c2313348c46d6bbd`
- MathFee: `5db596d01d2d93ea604c3fab7aa7e924248be8301187fa5ac82cc1813aecdf73`
- FundedDomain: `957cb3c9fa8951df7daf57bf0cb0fae883c4b01e7b514c0dee551edf773cd1d7`
- TransferFrame: `d7344861f8706ed4ef57954f8d0a5464212f45f12a5940976a6ebdd5bd945a1b`

These include the previously independently reviewed actual-success and transfer bridges; the relevant natural-payment, safe-domain and recurrence definitions/proofs were rechecked for this composition. No new issue found.

---

# SystemDataSpec — independent review

**CLEAN for actual successful Θ storage observations and their conditional natural projections.**

Complete source reviewed at SHA-256 `0db93120f0ce199f1977f0aba984771d6717965af20cfd4ac823eba72d691495`. `/tmp/eip-SystemDataSpec-final.log` contains five principal reports with standard axioms only; parent reports compilation exit 0. No build or source changes performed.

The specification is a read-map overlay: it accepts an arbitrary map of word slots and does not refer to bytecode, a machine state, or an operational endpoint. Its slot0 branch uses ControlSpec.systemExcess; slot1 resets to zero; slots2/3 implement the word-level full-drain test or partial advance; every remaining key is unchanged. `expected_entry` establishes definitional agreement with the existing state-based specification rather than defining the observation through the operational helper. `Observed` itself contains no code pin, so a mutant's actual outcome can fail it independently of runtime identity.

Both actual-call parents require runtime equality, SYSTEM caller identity, an owner in the pre-transfer world and actual Θ success. They require no sufficient gas, fuel, permission or desired poststate. SuccessfulSystem extracts the actual Ξ outcome, proves owner preservation to rule out Θ's empty-world fallback, and commits that endpoint. SystemDataSpec identifies its existential returned world with the exact world in the supplied actual result before exporting the observation. TransferFrame transports all slot reads across the actual value transfer. Drain counts are transported from the same pre-world; no alternate call, numerator or storage image is substituted.

`drain_projection` needs only ordered pre-pointers. QueueArithmetic derives natural TAIL−HEAD, caps it, and proves HEAD+n cannot wrap because n≤TAIL−HEAD. It also proves the word full-drain test equivalent to n=length, including an empty queue. Thus full drain resets both pointers and partial drain advances HEAD while retaining TAIL. The stale-slot clause covers every word index at least4. These statements concern pointers/storage only, not returned FIFO content, deposit amount recoding, output size, or absence of extra logs.

`control_projection` keeps the independent natural rule separate: nonempty calldata latches; empty calldata unlocks an inhibited input; otherwise excess+count−target is natural saturating subtraction; count resets. The calldata-size fit proves that nonempty natural size cannot become zero through casting. In the enabled branch, AccountedState.Bounded.active and budget<2^256 imply the **intermediate** excess+count sum fits. This is the correct prerequisite for subtraction; no modulo-after-subtract identity is assumed. Inhibition avoids any unnecessary bound on the INHIBITOR word itself. Targets/caps match deposit8/64 and exit2/16.

`projections` combines the two predicates for the same observed actual world, using input invariants only. Establishing Bounded at protocol call entries is separate; no protocol reachability or global funding/gas invariant is proved here. Actual Θ parents also do not claim that code was fetched from a canonical installed predeploy: runtime equality and owner existence are explicit, with installation/admission bound elsewhere.

No blocking defect or overclaim found in the claimed storage/projection scope. Relevant complete dependencies inspected: SuccessfulSystem and QueueArithmetic; relevant AccountedState.Bounded fields and the existing ControlSpec/SystemSpec/TransferFrame interfaces. This does not constitute a new independent review of the older helper modules authored by this reviewer.
