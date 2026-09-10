# EIP-8282 audit release candidate — scoped claims

This candidate establishes conditional bytecode theorems for P-SUBMIT-1,
P-DRAIN-1 and P-CONTROL-1 in EVMYulLean at
`b62586650b4f96cc6da25f36574aaa8f329a6420`, for the Deposit and Exit artifacts
locked in `audit/artifacts.lock.json`. It does not establish that canonical
Ethereum executions satisfy the domain below, or adopt Amsterdam or an
inhibition policy. The exact source candidate d46fa07 passed full compilation, axiom/mutation
checks and independent review; MANIFEST.json resolves the immutable receipts.

The original requested clauses are preserved in `ORIGINAL-GUARANTEES.md`.
The revised claims retain their functional content on the derived safe-history
domain. They explicitly condition successful effects on successful execution;
resource sufficiency and mandatory SYSTEM scheduling are separate claims.

## Revised guarantees

**P-SUBMIT-1.** In the domain below, every returned protected call satisfies
`DirectGuarantees.SubmitObserved`. A successful nonempty user call is enabled,
well formed and paid; it appends exactly one authentic record and emits exactly
one owner LOG0 with that record. Deposit copies 184 calldata bytes, checks the
minimum amount of 10^9 gwei, and requires amount times 10^9 wei plus the fee;
it does not validate BLS. Exit takes exactly 48 pubkey bytes and prepends the
actual caller's 20-byte address. Getters and SYSTEM do not append. A returned
failure restores the complete pre-transfer message-call journal.

**P-DRAIN-1.** The same receipt satisfies `DirectDrain.Observed`, with its
physical prequeue derived from initialization and history. Successful SYSTEM
returns the oldest min(length,64/16) records contiguously; full drains reset
HEAD/TAIL, partial drains advance HEAD only. Deposit's amount changes to
little-endian in the output; Exit returns caller||pubkey unchanged. Old record
slots remain intact. Users/getters cannot pop. Failed calls do not commit a
drain. This safety claim does not itself promise successful SYSTEM execution.

**P-CONTROL-1.** The same receipt satisfies `DirectControl.Observed`: caller
alone selects the branch, inhibition blocks every user, successful getters
have zero value and return the 32-byte mathematical tariff without persistent
writes; successful appends increment count and preserve excess. SYSTEM clears
count, latches on nonempty calldata, unlocks on empty calldata from INHIBITOR,
or stores the specified natural excess fold on enabled states. The quote's
numerator and SYSTEM's stored fold remain different formulas. Exact constructor
execution establishes Deposit enabled and Exit inhibited. An explicit
sufficient-resource SYSTEM sequence is proved separately; its scheduling is
not asserted.

## Independently meaningful domain

The primary result uses actual Θ/Υ evaluations in the pinned Lean semantics,
not a supplied queue, desired log, append count or postcondition. It starts
with two linked exact factory deployment transactions, then a finite linked
history of admitted transactions (including failure/ancestor rollback),
zero-value SYSTEM calls to either pinned runtime, funded balance transfers and
explicit external credits. The source files define every input precisely.

The history requires the pinned semantics' transaction admission, calldata
size below 2^256, and sufficient evaluator fuel (a proof-computation resource,
not EVM gas). Its same transaction receipts are grouped into blocks with
unsigned 64-bit slot/gas values, distinct slots, and the sum of *these old
receipts' charged gas* within each block's gas value. A literal credit ledger
bounds the same total credits: PoW batches at most 14.0625 ETH, withdrawal
items at most (2^64−1) gwei, at most 2^64 batches and 16·2^64 withdrawal items,
and zero migration issuance. These are conditional input restrictions, not
asserted Ethereum rules. The ledger need not be the identical operation
sequence; it supplies an arithmetic bound only.

From these inputs the proofs derive funding bounds, both installed queue
invariants, bounded counters and collision-free record slots, exact retained
occurrence lists and their logs, and enabled natural fee numerator ≤2892.
They do not assume noWrap, a per-call TAIL bound, a safe post-state, or fee
termination. Upgrade transitions are outside this history; any upgrade ends
this candidate's applicability until separately justified.

## Stronger connections implemented during the release hour

`ReleaseCandidate.composed` connects every past receipt and the next call on
one history. `ReleaseCandidate.invariants`, `.call`, and `.enabled_numerator` expose the
same history-derived domain at the next actual protected call, rather than
requiring the caller to supply an invariant, structural budget or safe fee
numerator. `ReferenceCheckedTheta` and `ReleaseCandidate.checked_terminal` /
`.checked_eof` connect computed checked outcomes to all three predicates, with
entry-owner existence derived from installed code. Their replay gas/fuel are
synthetic; source gas and full source account/journal identity are not equated.
`ReleaseGetterProgress.after_history` constructs successful mathematical quotes
with scalar gas≥44694 and fuel≥11171. `ReleaseSubmitProgress.after_history`
constructs successful authentic appends and the next invariant from actual
sender funds and mathematical payment, with gas≥230194 and fuel≥11241.
Both derive termination, installed ownership and storage fit; the payment
predicate is nonvacuous because a mathematical price is proved to exist.
`ReleaseInhibitionCycle.after_history` constructs two linked actual SYSTEM
calls for either kind, proving latch→unlock, both complete guarantees and the
extended history invariant. The exact verified subset is listed in the manifest.

## Arithmetic and applicability limits

The operational fee follows every word operation in bytecode order, for any
finite completed loop, without a 256-iteration ceiling. Agreement with the
unbounded natural algorithm is proved for independently computed input ≤2892,
including all intermediate operations. Within the primary safe-history domain
that input bound is derived for enabled states. Outside it, unrestricted
agreement is false at 2893; exact word fidelity is not advertised as the
original mathematical tariff. Finite injected tests, artificially funded
histories, and canonical reachability are kept separate.

Ethereum/Amsterdam applicability remains unproved: scalar versus dual gas,
type-4/delegation, source dictionary/full journal correspondence, actual source
frame occurrence coverage and settlement, canonical credits and withdrawals,
SYSTEM admission/schedule, hash bindings and upgrade policy all require their
own justification. The conditional Lean theorem does not turn these missing
application proofs into accepted assumptions of Ethereum.
