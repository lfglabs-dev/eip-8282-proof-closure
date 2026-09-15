# Direct guarantee clause map

Lean statements are authoritative. The three registered theorems quantify
completed calls to the pinned bytecode under explicit input conditions.
They do not assume the desired post-state or a particular execution path.

## Registered guarantees

All names below are under `Eip8282.Audit.Integrator`.

| ID | Registered theorem | Predicate |
| --- | --- | --- |
| P-SUBMIT-1 | `DirectGuarantees.psubmit1_direct` | `DirectGuarantees.PSubmit` |
| P-DRAIN-1 | `DirectGuarantees.pdrain1_direct` | `DirectGuarantees.PDrain` |
| P-CONTROL-1 | `DirectGuarantees.pcontrol1_direct` | `DirectGuarantees.PControl` |

## Clause coverage

| Clause | Proof / predicate | Qualification |
| --- | --- | --- |
| Only well-formed paid users append | `DirectSubmit.completed`, `DirectAppend.user_append` | Successful nonempty user call; deposits pay fee + amount × 1 gwei, exits pay the fee. |
| Authentic record and one LOG0 | `DirectSubmit.Observed`, `AppendDataSpec.AppendedLog` | Deposit: exactly 184 calldata bytes. Exit: caller address followed by the 48-byte supplied public key. Signatures are not checked. |
| Append updates storage and counters | `AppendDataSpec.StoragePost`, `DirectControl.AppendControls` | One record appended, count and TAIL incremented, excess unchanged. |
| Failed calls restore the queue and counters | `MessageCall.failure_restores_journal`, `UniversalGate.FailedJournal` | Completed failure result; evaluator OutOfFuel is a separate error. |
| Only SYSTEM consumes | `DirectDrain.Observed`, `DirectDrain.completed_call` | Users, including getters, preserve the queue pointers. |
| Capped FIFO output | `DirectDrain.Observed` | Oldest min(length, cap) records; caps 64 deposits / 16 exits. Deposit amounts are encoded little-endian in output. |
| Queue pointers | `DirectDrain.Observed` | Full drain resets HEAD and TAIL; partial drain advances HEAD and leaves TAIL. |
| Old record slots survive a drain | `SystemDataSpec.DrainSlots` | Every storage word at slot ≥ 4 is unchanged. |
| Caller selects the path | `DirectControl.Observed` | The fixed SYSTEM caller selects the SYSTEM branch; authorization and scheduling are protocol assumptions. |
| Getter returns the mathematical fee | `DirectControl.Getter`, `GetterCall.ReturnsQuote` | Enabled user, empty calldata, zero value; successful quote returns 32 bytes and preserves persistent state. |
| SYSTEM resets count and updates inhibition | `SystemDataSpec.ControlSlots`, `DirectControl.Observed` | Nonempty calldata inhibits; empty calldata unlocks an inhibited contract, otherwise applies max(0, excess + count − TARGET). TARGET is 8 / 2. |
| Constructors install the runtime | `DirectInitialization.pinned` | Actual initializer execution under its separate domain: deposits enabled, exits inhibited. |
| SYSTEM progress | `SystemProgress.pinned` | Installed target and stated execution inputs; gas ≥ 2,500,000 and evaluator fuel ≥ 8,503. |
| Untruncated mathematical fee | `FeeSafeDomain.any_quote_agrees`, `MathFee` | Agreement on the safe domain; the fee is not defined by a fixed iteration cutoff. |

[Original requested clauses](release/ORIGINAL-GUARANTEES.md) remain available for
comparison. The source predicates give the full types and exact quantifiers.

## Conditions and the resource derivation

`DirectGuarantees.Domain` requires an installed target, coherent transferred and
apparent value, word-sized calldata, bounded counters and a safe fee input.
`DirectDrain.Domain` also requires physical queue representation and exit address
width. Initializer and SYSTEM-progress inputs are separate.

`ResourceAssumptions.from_deployment` derives the local numerical conditions,
queue representation and all three observations from verified deployment, a
linked admitted history, transaction-entry supply below 10^68 wei and counted
execution work below 2^128. The count includes qualifying LOG0 instructions in
rolled-back execution. See [the exact resource assumptions](release/RESOURCE-ASSUMPTIONS.md).

These are properties of the pinned Lean evaluator. Canonical installation,
activation, SYSTEM authorization/scheduling, normative fork selection and
complete Ethereum history/admission extraction remain open. BLS validation,
consensus processing and builder bidding are outside these guarantees.

## Supporting evidence and trust

`FactoryHistoryGuarantees` composes actual linked factory deployments.
`ReferenceCheckedSystemBlock` constructs the deposit/exit SYSTEM block pair
under explicit source-adapter inputs. `ReferenceCanonicalHooks` records the
remaining canonical-producer interfaces. None establishes full Ethereum
semantic equivalence.

`Tests.DirectThetaKills` registers six bytecode refutations of the same direct
predicates. The LOG0 witness is kernel checked. Five finite drain/control
witnesses retain historical native-evaluation axioms (A-NATIVE-DECIDE).
`Audit.Trust` rejects additional axioms in the three correctness parents and the
LOG0 witness, and reports the separate drain/control closures.

Run `make check` for pins, metadata, library boundaries, all retained Lean proofs
and tests. See [VERIFY.md](../VERIFY.md). Dated candidate logs, review outputs and
old release manifests are in Git history rather than the delivery tree.
