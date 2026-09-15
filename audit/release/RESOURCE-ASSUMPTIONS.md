# Supply and request-processing limits

The history-facing proofs can use two readable numerical assumptions:

- Total available ETH stays below **10^50 ETH** (10^68 wei).
- Counted execution work stays below **2^128 events** over the contract history.

`ResourceAssumptions.from_deployment` derives the queue representation and all
three local guarantee observations from these limits, a verified factory
initialization, and a linked admitted execution history. The caller supplies
neither the safe-fee formula nor intermediate queue invariants. The existing
registered direct parents and their mutation checks are unchanged.

## What the assumptions mean precisely

`SupplyBound receipts` bounds the finite sum of balances in the actual input
world of every transaction receipt. The deployment input is bounded separately.
This is a circulating-funds bound, **not** a bound on all ETH ever issued.
The proof starts the existing funding argument afresh at each transaction;
admission and the nested execution funding theorems bound values at its inner
calls, including calls inside ancestors that later roll back. Bounding only
the final world's supply would not suffice.

`ActualJournalHistory.work receipts` sums `NestedJournalBudget.events` over
the ordered receipts. The count includes completed LOG0 instructions whose
actual length operand is at least 68 bytes, throughout their actual execution
trees. This conservatively includes both contracts' append events, unrelated
matching LOG0 instructions, and events later rolled back. It is not the final
queue length or only the number of successful requests. SYSTEM drains do not
subtract work. The bound applies to all finite prefixes of a lifetime history.

## Derived conditions

`ResourceAssumptions.supply_below_fee_boundary` proves in the Lean kernel that
10^68 wei is strictly below `FundedDomain.fundingCeiling`, the certified
mathematical fee at numerator 2892. `preserves` inducts over the actual history;
`domains` exposes the derived counter bounds, physical queue representation and
inhibition-or-safe-fee condition. In particular, for an enabled contract:

```
excess + max(0, count - TARGET) <= 2892
```

At 2893 an **intermediate multiplication** overflows the EVM word; the
operational and natural fee calculations diverge. This is not a claim that
the final quoted fee itself exceeds 256 bits.

`completed_call` applies the three registered parents to a next completed call,
including SYSTEM, using those derived domains. It assumes the actual receipt
and calldata-width bound, and does not promise scheduling or success.

`guarantees` gives every listed transaction its represented input queue,
committed queue/log effects, and all three observations at actual protected
calls, including calls later rolled back. `from_deployment` also derives the
initial seed from the actual factory transaction. Exit source-width safety is
retained inside the derived `JournalInvariant.Invariant`.

## Remaining assumptions

The two numbers do not establish arbitrary storage safety. The contracts must
start from the verified initialization and evolve through the represented
execution history. Factory installation, address/hash binding, transaction
admission, calldata width and sufficient evaluator fuel remain explicit typed
inputs. Plain CALL/coherent ownership, funding gates, checkpoint restoration
and frame preservation use the existing execution proofs.

The proofs concern the pinned evaluator. Canonical Ethereum installation,
activation, SYSTEM authorization/scheduling, the chosen normative version and
complete protocol-history extraction remain open. These wrappers do not make
those external assumptions disappear or prove unconditional call success.

## Evidence

- `Eip8282/Audit/Integrator/ResourceAssumptions.lean`: eight new kernel-checked
  declarations, with individual axiom reports in that module.
- `ActualJournalHistory.lean`: linked actual transactions, SYSTEM calls,
  transfers and credits; no intermediate invariant in its constructors.
- `NestedProtectedJournal.inputs_from_history`: inner-call input bounds.
- `TransactionCommittedEffects.receipt_effects` and
  `TransactionJournal.observed`: committed effects and local guarantees.
- `FactoryHistoryGuarantees.deployment_seed`: verified initialization producer.
- `audit/receipts/resource-assumptions.json`: exact premises and build receipts.
