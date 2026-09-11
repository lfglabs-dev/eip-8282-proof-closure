# Independent review: final direct public-parent packaging

Read-only review, 9 September 2026. Worktree HEAD when sampled: `749a1c0d68597f00529631bd6724b9e185993635`. No proof files, parents, YAML, IDs or build artifacts changed; no build or publication performed.

Scope clarification: the current `audit/DIRECT-CLOSURE.md` has no heading literally called “final public-parent packaging”. This report audits its final coverage/remaining-obligation/delivery sections (especially lines 279–355), against the current direct modules and registration machinery. It is a packaging proposal, not a certificate that the proposed parents already exist.

Reviewed interface hashes (SHA-256):

- DIRECT-CLOSURE.md: `d89ad194e05e231f18c679b37d71f977342741fd2a5315e9f00214ccc9f60426`
- Registry.lean: `1250ee23139d6853e3446a30638aa65aa74d46e636d8539634e7d62686312699`
- guarantees.yaml: `a2b33fe9c37c59ffc130f7acb6f1507df9f332e5525351192dcf7af98d41b97e`
- DirectMutations.lean: `aa3ec12bc05b491eade0adbd1e7076e288ad9cba06041b194054c19db0002f8d`
- scripts/audit_metadata.py: `22b140e8212f5bc9da9f7126c98f6774b572d7f6ea1e62492441aea3ffbcbdc5`

## Decision

**Ready to implement a small conditional direct interface; not ready to register it as completed protocol-wide assurance.** The needed runtime behavior is now available from actual arbitrary-resource Θ success/failure. A further general transition model is unnecessary. Use three explicit behavior predicates over the same actual call/result, then three kernel-proved pinned instances, under exactly the existing public IDs. Keep initialized-history and protocol-domain justification as supporting theorems with their real scope.

The current YAML still registers the old CFG/finite-trace parents. Registry only defines three IDs and model/evm layer tags; it neither binds nor certifies theorem strength. Adding direct imports or retaining `.evm` cannot upgrade a parent. The YAML's old “next gate = Ξ agrees with Model” is no longer the appropriate next implementation step for the direct route; that historical theorem is separate and its counterexamples must remain visible.

## Shared boundary, without another model

For each kind and a **parameter bytecode** `code`, quantify a normal message-call `c` executing `code` and its actual complete result:

```
c.result = .ok (created, world', gas', substate', success, output)
```

All postconditions inspect this very tuple. Name natural pre-state reads E, C, H, T from `c.world` at `c.target`; actual value transfer preserves those reads. Use the existing independent record constructors, slot overlays and `QueueInvariant.Represents` list; no `Model.step`, `EndpointAgrees`, post-state equality assumption, supplied successful execution path, fee-loop completion or gas/fuel lower bound.

In particular, do not put a mutant `XiCall` into the specification: its type already carries a pinned runtime constraint. Factor `AppendStorage.expected`/`StoragePost` into a pure overlay parameterized by kind/stride, entry read-map, calldata and caller, then prove that instantiating these inputs from an existing pinned `q` recovers the present specification. The authentic log predicate likewise needs only prior log series, owner and independent record bytes. A corresponding read-map wrapper around system controls avoids exposing operational state constructors. These are data/specification adapters, not a new execution model.

The smallest convenient common input domain is owner presence, ordinary CALLVALUE (`apparentValue=value`), calldata size < 2^256, and independent pre-state `AccountedState.Bounded budget` with budget < 2^128. For mathematical fee clauses add the **pre-state** enabled-safe invariant (`E=INHIBITOR` or `E+max(0,C-TARGET)≤2892`). For FIFO require an arbitrary supplied list representing the pre-state, with exit source-width invariant. These are honest local preconditions, not promised outputs. Conjuncts that do not need them (inhibition/failure journal/admission at operational price) should retain their stronger existing scope where convenient, without multiplying public IDs.

`ConcreteHistory` already derives these pre-invariants from actual linked Θ histories and successful initialization, given an independent total-event bound, the explicit size/funding policy and canonical address. Export or cite that bridge; do not make its pinned-code `Transition` the only domain of the code-parameterized behavior predicate. Otherwise mutation of the last call can make the domain impossible.

Do not require the funding ceiling on an isolated call merely to prove its current receipt; it is needed to preserve the enabled-safe domain along histories. Do not silently turn the 2892 certificate into a protocol rule. For every call, an actual failed result restores created accounts, account map and substate. Remaining gas and output are not restored; interpreter `OutOfFuel` is an error outside the completed-result quantifier.

## Exactly three public parents

### P-SUBMIT-1 — actual paid admission and one authentic append

For each completed non-SYSTEM call, if successful with nonempty calldata, derive all of:

- Entry is enabled; deposit input is exactly 184 bytes or exit input exactly 48 bytes. Deposit amount is the uint64 calldata field. The actual extra minimum is amount ≥ 10^9 gwei; this is stronger than merely charging amount×1 gwei and must be stated accurately.
- A completed operational quote belongs to this same execution. On the enabled-safe domain it equals the unique untruncated natural tariff at `E+max(0,C-TARGET)`; payment covers that price and, for deposit, amount×10^9 wei. Do not use an unrelated arbitrary quoted fee as a premise.
- Output is empty, exactly one independent physical record is appended at the previous tail, HEAD/excess are unchanged, COUNT/TAIL advance by one naturally, and storage outside the exact write set is unchanged. Existing records remain the queue prefix.
- Log series is exactly the previous series plus one log at the target, with no topics and data equal to the 184 input bytes (deposit) or caller20 || pubkey48 (exit). The exit source comes from the actual caller. No signature-validation claim.
- Account preservation outside the target is relative to the actual transferred entry world, as in `CommittedAppend.AppendResult`; it is not equality with the pre-Θ world, whose sender/target balances may change.

For a failed user result, require whole-journal rollback; the inhibitor and malformed/underpaid input clauses force that failed result when execution completes. The successful empty getter belongs to the control clause and does not submit. This is success necessity plus atomic effects. **Do not write “well-formed and paid iff success” at arbitrary resources:** out-of-gas or static-call permission can still make a paid call fail. Existing sufficient-success endpoints may support a separately qualified resource corollary if wanted.

Composition: SuccessfulUser/SuccessfulAppend + FeeSafeDomain and natural numerator bridge; AccountedState derives AppendFits; UserQueueInvariant preserves the prior list; UniversalGate/UniversalRejection and MessageCall handle rejection. The remaining wrapper must project the actual receipt onto a code-independent input/result specification instead of exposing a `codeCall` requiring an original pin in the predicate's type.

### P-DRAIN-1 — exclusive, exact FIFO consumption

For any actual completed call on a represented pre-queue Q:

- Failure leaves the queue/world unchanged.
- A successful user getter leaves HEAD/TAIL and Q unchanged; a successful nonempty user append preserves HEAD and extends Q by exactly one. Thus no user call removes an existing queued record, even if it returns some bytes.
- Successful SYSTEM returns precisely the independent encodings of `Q.take n`, contiguously, where n=min(Q.length,64/16). Deposit amount bytes are recoded BE→LE; exit is stored source20 || pubkey48.
- The represented post-queue is `Q.drop n`. Full drain sets HEAD=TAIL=0; partial drain sets HEAD=H+n and leaves TAIL=T. Every storage slot ≥4 is unchanged, including drained records and unrelated stale slots.

Composition: SystemStateInvariant plus SuccessfulSystem's all-slot result, QueueArithmetic and the independent drain encoders; UserQueueInvariant and GetterInversion for the user partition. Keep excess/count clauses out of this parent except facts strictly needed to interpret its input. Returning bytes alone is not a definition of consumption.

### P-CONTROL-1 — actual caller partition, fee/control updates and initialization

For both kinds, partition only on actual caller=SYSTEM; value and calldata may affect acceptance/control effects but do not select user versus SYSTEM.

- An inhibited non-SYSTEM completed call fails with whole-journal rollback. Successful SYSTEM obeys the same control rule even when initially inhibited. Do not claim every under-resourced SYSTEM call succeeds.
- Successful empty user input has actual value zero, returns exactly the 32-byte mathematical fee at `E+max(0,C-TARGET)`, and preserves account map, created accounts and full substate. Successful nonempty user input increments COUNT by one and leaves EXCESS unchanged.
- Successful SYSTEM resets COUNT=0 and sets EXCESS to INHIBITOR for naturally nonempty calldata, to zero for empty calldata when previously inhibited, or to max(0,E+C-TARGET) otherwise. Natural nonemptiness uses size<2^256; natural folding uses Bounded's derived no-wrap bound. TARGET is 8/2. This is distinct from the fee numerator.
- Add the existing actual initializer execution/installation clause: successful pinned creation at an absent target installs the corresponding runtime and initializes deposit enabled / exit inhibited with empty queue. Preserve its explicit resource preconditions and canonical-address equality. It does not prove those canonical predeploys were CREATE-deployed or bind an unobserved genesis installation.

Composition: UniversalGate, SuccessfulUser/GetterInversion, SuccessfulAppend control projections, SuccessfulSystem/SystemStateInvariant, InitializedInvariant. Initializer parameters belong only in this parent's initialization conjunct; changing a runtime for a mutant does not require changing the initializer, because runtime behavior is independently quantified.

## How the same six mutants must refute these predicates

Define behavior for an arbitrary `code`; prove the pinned instance separately. Having `c.code=code` and even `account.code=code` is fine. Having `c.code=originalRuntime` inside the antecedent after substituting mutant code is not: it makes the purported mutated guarantee vacuously true.

For each mutant provide an actual successful Θ receipt, an explicit independent pre-domain witness, and a violated clause of the **same** behavior predicate. The six existing direct checks provide these distinguishing observations:

| Mutant | Parent clause | Actual vs specified |
|---|---|---|
| Deposit caller EQ→LT | P-CONTROL-1 SYSTEM count reset | COUNT remains 5, must be 0 |
| Deposit TARGET 8→9 | P-CONTROL-1 empty enabled fold | EXCESS 96, must be 97 at (100,5) |
| Exit cap 16→8 | P-DRAIN-1 partial HEAD | HEAD 8, must be 16 for 17 entries |
| Deposit cap 64→32 | P-DRAIN-1 partial HEAD | HEAD 32, must be 64 for 65 entries |
| Deposit HEAD store moved to slot9 | P-DRAIN-1 stale-slot frame | slot9 becomes 64, must retain 0x5500×2^240 |
| Deposit LOG length184→0 | P-SUBMIT-1 authentic anonymous receipt | log data has size0, must equal 184-byte input |

The current DirectMutations module is good supporting evidence, but not these final refutations yet:

1. Its executions are actual Ξ receipts, not Θ receipts. For SYSTEM zero-value fixtures, construct the corresponding context and derive its actual entry/execution and settlement, including target presence/nonempty world. For the paid log fixture, explicitly account for the pre-call funding and transferred world. Reuse a receipt only after proving that equality; otherwise add one accurately funded Θ finite receipt. Do not assume Ξ world equals Θ world or bypass the empty-map branch.
2. Instantiate each pre-state argument to that actual entry world, and construct Bounded/safe/Represents/source-width witnesses for the fixtures. Current refutations intentionally allow arbitrary `pre` constrained on a few slots; that is enough to refute an overlay, not enough to claim initialized protocol reachability.
3. `¬SystemPost` negates an all-slot conjunction. It does not by itself prove `¬ControlPost` or `¬DrainPost` after splitting. Reuse the observed differing slot to derive the relevant projection directly. The LOG test similarly must bind its abstract call/log prefix to the actual context.
4. No universal sibling-independence claim follows from old finite sibling tests. Give selected finite sibling observations for the new projected specifications, or clearly state their scope. In particular a caller-gate mutant can also break SYSTEM draining: demanding that every mutant preserve both other universal parents would be false/unnecessary. The LOG, target and cap/stale cuts demonstrate distinct obligations; use that separation honestly.

No legacy finite Boolean trace conjunct need be inserted into the new universal proof merely to make it mutation-testable. The universal theorem can keep standard kernel axioms, while existing native-evaluated finite mutant receipts remain separately disclosed corroboration. Preserve historical kill-lines and their provenance.

## What still prevents registration/closure

For a **conditional direct registration**, the blockers are concrete and small: write the three explicit code-independent specifications and pinned universal wrapper proofs; join math-payment and actual state/result projections; transport the six same-predicate mutant witnesses to Θ and establish their domains; review actual parent strength and finite independence; add exact Trust reports and run the normal final verification. The metadata checker currently accepts only CONCRETE_TRACES, WELL_FORMED_FORALL and CFG_FORALL. A direct completed-Θ scope needs an accurate supported label (or an explicitly justified existing label), and YAML parent/evm theorem/kill-line/assumptions/reproduction fields must move together. Its regex theorem-existence check is not proof that a namespace or theorem statement is the intended one.

For **protocol-wide closure**, registration mechanics are not the remaining proof. ConcreteHistory covers linked local call worlds under policy, not extraction from validated block/transaction executions, nested calls with ancestor rollback, or full header/original-world/substate coherence. AppendGasPath now derives the real per-call 919/1847 lower bound; RefundAccounting now derives the actual transaction refund formula. Summing nonduplicated call events into gross gas, proving the transaction input bounds, and using protocol block/slot accounting remain open. Likewise funding/supply must justify the explicit ceiling preserving numerator≤2892; UInt256 alone does not do so, and FeeBoundary refutes unrestricted agreement at2893. Canonical installation, scheduling and the selected normative inhibition version remain explicit external/protocol obligations.

Thus publish the precise conditional direct statements when implemented and checked, with their environment limitations visible. Do not postpone useful direct packaging until a global Model equivalence is proved, and do not mark all three original protocol guarantees closed merely because the packaging compiles.
