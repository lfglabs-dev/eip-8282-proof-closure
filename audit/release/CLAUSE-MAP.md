# Original clause → revised claim → theorem → domain → commit

All `Release*` names below are under `Eip8282.Audit.Integrator`. **RC** means
the exact source commit resolved in `MANIFEST.json`; it is not an unspecified
future version. The manifest gives every complete source SHA, relevant prior
commit and verification receipt. D = `ReleaseCandidate.History` and
`CallInput`, fully expanded in `PREMISES.json`. R = same returned actual pinned
Θ receipt; no success is assumed unless the row says so. C = checked local
adapter context; it is not an Ethereum execution-equivalence premise.

| Original clause | Revised established claim | Theorem / predicate consumer | Domain and material qualification | Commit |
|---|---|---|---|---|
| All three guarantees together | All three predicates on one complete call receipt | `ReleaseCandidate.composed` / `.call` → `JournalGuarantees.completed` | D, calldata width, R; internal owner/invariant/budget/safe fee derived | RC |
| Only well-formed paid users append | Successful nonempty user implies mathematical admission and one append | `DirectSubmit.completed`, `DirectAppend.user_append` via `.call` | D,R; malformed or underpaid inputs cannot successfully append | RC |
| Well-formed paid enabled submission | Successful append is constructed with all three guarantees and next invariant | `ReleaseSubmitProgress.after_history` | D, non-SYSTEM, enabled, permission, mathematical PaidInput, actual sender funds; gas≥230194, fuel≥11241 in pinned scalar semantics | RC |
| Deposit payment | fee + amount·10^9 wei; minimum amount 10^9 gwei | `DirectAdmission.PaidInput`, `SubmissionCall.deposit_submission` | Original did not explicitly state the minimum; now made explicit. No multiplication wrap in this domain | RC |
| Deposit exact184 bytes | Physical record and LOG0 bytes equal original calldata | `AppendDataSpec.record`, `DirectAppend.Observed` | Successful nonempty Deposit in D; no BLS verification | RC |
| Exit caller authentication | Exact caller20||48 supplied pubkey bytes | `ExitRecord.record`, `DirectAppend.Observed` | Caller comes from execution environment; no externally supplied source_address | RC |
| Exactly one LOG0 | One extra owner log with empty topics and authentic record | `DirectAppend.Observed` | Local message success; ancestor rollback may discard it | RC |
| Every inhibited user fails | Returned result has false status and restored journal | `UniversalGate.deposit_inhibited`, `.exit_inhibited`, `DirectControl.Observed` | Code pin and non-SYSTEM caller; interpreter OutOfFuel remains separately classified | RC |
| Only SYSTEM drains | User/getter preserves queue; successful SYSTEM drains FIFO | `DirectDrain.Observed`, `DirectDrain.completed_call` | D,R; successful effects and resource sufficiency distinguished | RC |
| FIFO, min(length,cap), contiguous output | Same physical prequeue supplies exact prefix output | `JournalGuarantees.domains`, `DirectDrain.Observed` | Queue/slot representation derived from exact history | RC |
| Full drain resets both pointers | HEAD=TAIL=0 | `DirectDrain.Observed` | n=length in successful SYSTEM | RC |
| Partial drain | HEAD increases by n; TAIL unchanged | `DirectDrain.Observed` | n<length in successful SYSTEM | RC |
| Caps64/16 | Fixed Deposit64 / Exit16 | `SystemDataSpec.cap`, `DirectDrain.Observed` | Pinned runtime bytes | RC |
| Deposit amount endianness | Big-endian input/storage amount emitted little-endian | `DirectDrain.Observed` and record encoding dependencies | Exact output bytes, not merely an abstract list length | RC |
| Exit return as stored | caller20||pubkey48 | `DirectDrain.Observed` | Derived queue integrity/source width | RC |
| Old record slots remain | Every slot≥4 preserved during SYSTEM drain | `DirectGuarantees.SubmitObserved`, `SystemDataSpec.Observed` | Success; failure restores journal | RC |
| Length=TAIL−HEAD | Natural ordered packed queue at slots2/3 | `JournalInvariant`, `AccountedState`, `QueueInvariant.Represents` | Ordering/no collision derived from D; not assumed as noWrap | RC |
| Caller selects path | Branch classification uses c.caller alone | `DirectControl.Observed`, `DirectGuarantees.SubmitObserved` | SYSTEM address identity is fixed; who may invoke it in Ethereum remains external | RC |
| SYSTEM never inhibited | Successful SYSTEM constructed independently of initial INH | `SystemProgress.pinned`, `ProtocolSystemCalls.completes` | Installed target, permission, scalar gas≥2500000 and fuel≥8503; does not promise success without resources | RC |
| Empty zero-value getter | Successful read-only mathematical quote is constructed | `ReleaseGetterProgress.after_history` | D, enabled, non-SYSTEM, empty data, zero value; gas≥44694, fuel≥11171 | RC |
| Getter fee32 and no persistent writes | Same account lookups, created accounts and logs; exact32-byte fee | `GetterCall.ReturnsQuote`, `DirectControl.Getter` | Gas and access bookkeeping may change; transaction charges are outside message read-only claim | RC |
| Append count+1/excess unchanged | Natural count successor and same excess | `DirectControl.AppendControls` | D and successful append; safe domain preserved for funded progress theorem | RC |
| SYSTEM count=0 and nonempty latch | Exact slot0=INH and count0 | `SystemDataSpec.ControlSlots`, `ReleaseInhibitionCycle.after_history` | Any nonempty calldata fitting word size; still drains queue | RC |
| Empty SYSTEM unlock | INH→0, count0 | `ReleaseInhibitionCycle.after_history` | Two actual linked successful SYSTEM calls, both kinds; no permanence or policy adoption | RC |
| Enabled SYSTEM fold | max(0, excess+count−TARGET) | `DirectControl.Observed`, `SystemDataSpec.ControlSlots` | D derives no intermediate addition wrap; unrestricted raw-word fold differs outside D | RC |
| TARGET8/2; quote numerator differs | e+max(0,c−T) vs max(0,e+c−T) | `SuccessfulUser.numerator`, `ControlSpec.feeInputNat`, `SystemDataSpec.ControlSlots` | Exact operation order preserved | RC |
| Constructor activation | Exact Deposit enabled / Exit INH and empty queue | `FactoryHistoryGuarantees.two_seeds` and initializer consumers | Actual CREATE2/Υ receipt, independent factory/gas/hash/collision inputs | RC |
| Mathematical fake exponential | Bytecode equals unbounded natural quote | `FeeSafeDomain.any_quote_agrees`, `DirectControl.Getter`, `ReleaseCandidate.enabled_numerator` | Input≤2892 derived in enabled D; unrestricted equality refuted at2893 | RC |
| No artificial256 iterations | Every finite completed operational loop, with arbitrary witness budget | `EntryReach.quoteWithin_unique`, `FeeSafeDomain.any_quote_agrees`, `MathFee` | 462 is sufficient on certified interval, not an execution ceiling; general word termination not claimed | RC |
| Nested appends and rollback | Exact nonduplicated retained calls determine physical final queue/logs; executed work retains failed ancestors | `ReleaseCandidate.composed` → `FactoryHistoryGuarantees.from_genesis_both`, `TransactionCommittedEffects.Effects`, `JournalRetainedWork` | Actual pinned Θ/Υ full tree; source/Amsterdam tree identification remains open | RC |
| Computed source-shaped terminal/EOF | Same non-resource observations feed all three predicates with history-derived domain | `ReleaseCandidate.checked_terminal`, `.checked_eof` | C: slots/warm binding, actual computed outcome, source potential≤30M. Synthetic replay resources; no full source account-world identity | RC |
