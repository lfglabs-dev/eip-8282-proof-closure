import Eip8282.Audit.Integrator.ReferenceAdmissionExtraction
import Eip8282.Audit.Integrator.TransactionFunding
import Eip8282.Audit.Integrator.FactoryHistoryGuarantees
import Eip8282.Audit.Integrator.ActualJournalHistory
import Eip8282.Audit.Integrator.ReferenceSourcePrepaidCheckpoint

/-! Canonical-producer hook interfaces for the three named Ethereum-semantic
raccordements listed in DIRECT-CLOSURE.md remaining obligation 4.

This module names the *interface* a canonical producer of Ethereum semantics
must supply so that the existing conditional theorems can be discharged. It
adds no new premise, adopts no new protocol policy, and does not identify
any new bytecode with a reference implementation. Each declaration below is
a *type* — a `structure` bundling the exact hypotheses downstream theorems
already consume — plus a small structural theorem projecting the bundle to
the raw fields those theorems accept.

The three named hooks:

* `CompleteAdmission` — bundles the audited partial admission
  (`ReferenceAdmissionExtraction.SourceChecks`) with the funding
  admission (`TransactionFunding.Admission`), the sender read, and the
  represented-recipient recovery. It does not add signature recovery,
  full blob validation, capacity checks or type-4 authorization; those
  remain OPEN, and callers must widen this structure once a canonical
  Ethereum admission machinery becomes available.

* `Deployment` — bundles the two factory-deployment `Inputs` records for
  the deposit and exit contracts, together with the linked-worlds
  condition. This is exactly the shape `FactoryHistoryGuarantees.two_seeds`
  consumes; canonical Ethereum production of these records remains
  external.

* `SystemAuthorization` — bundles the empty-data zero-value SYSTEM
  invocation guards (`caller = sysAddr`, `value = 0`,
  `calldata.size < UInt256.size`) that
  `ActualJournalHistory.Trace.system` consumes. It does not adopt a
  schedule, does not identify the caller's authorization source and does
  not claim the pinned reference invokes any particular SYSTEM address
  automatically.

For each hook the module exposes a `.project` theorem returning the raw
fields the downstream conditional theorem accepts, so a canonical producer
can hand off its bundle and let the existing composition run without
pattern-matching on the internal structure.

The three declarations remain `Prop`-valued obligations: they are neither
axioms nor claimed satisfactions. Their purpose is to make the exact
interface auditable at a single site. -/
namespace Eip8282.Audit.Integrator.ReferenceCanonicalHooks

open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open TransactionAppendBudget (Receipt)
open ReferenceAdmissionExtraction (SourceChecks)
set_option autoImplicit false

/-! ## Hook 1 — Complete admission -/

/-- Interface a canonical Ethereum admission producer must supply for a
represented nonblob ordinary call. Combines the audited partial admission
(`SourceChecks`) with the funding admission and the sender/recipient
correspondence. Complete Ethereum admission (signature recovery, full blob
validation, capacity, type-4 authorization) remains OPEN and must widen
this structure. -/
structure CompleteAdmission (tx : RefundAccounting.Context) (kind : Contract)
    (sender : Account .EVM) : Prop where
  /-- Audited partial admission over represented inputs. -/
  checks : SourceChecks tx sender
  /-- Prepayment/nonce/priority admission consumed by transaction funding. -/
  funding : TransactionFunding.Admission tx sender
  /-- Sender lookup in the pre-transaction world. -/
  senderRead : tx.world.get? tx.sender = some sender
  /-- Represented recipient equals the audited pinned target. -/
  recipient : tx.transaction.base.recipient = some (ReachableCalls.address kind)
  /-- Nonblob transaction (blob validation remains an OPEN separate hook). -/
  nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob tx.transaction

/-- Projection: a canonical producer hands off the five fields the
downstream fee-block theorems already accept as separate arguments. -/
theorem CompleteAdmission.project {tx : RefundAccounting.Context} {kind : Contract}
    {sender : Account .EVM}
    (h : CompleteAdmission tx kind sender) :
    SourceChecks tx sender ∧ TransactionFunding.Admission tx sender ∧
      tx.world.get? tx.sender = some sender ∧
      tx.transaction.base.recipient = some (ReachableCalls.address kind) ∧
      ReferenceSourcePrepaidCheckpoint.Nonblob tx.transaction :=
  ⟨h.checks, h.funding, h.senderRead, h.recipient, h.nonblob⟩

/-! ## Hook 2 — Deployment -/

/-- Interface a canonical Ethereum deployment producer must supply. Bundles
the two `FactoryHistoryGuarantees.Inputs` records for the deposit and exit
contracts with the linked-worlds condition. This is the exact input
`FactoryHistoryGuarantees.two_seeds` consumes; canonical production of the
records remains external. The structure is Type-valued (not Prop-valued)
because `Inputs` carries data fields (steps, sender account, factory
account) beyond pure propositions. -/
structure Deployment (deposit exit : Receipt) where
  depositInputs : FactoryHistoryGuarantees.Inputs .deposit deposit.call
  exitInputs : FactoryHistoryGuarantees.Inputs .exit exit.call
  linked : exit.call.world = deposit.world

/-- Convenience wrapper naming the linked-worlds hypothesis explicitly.
The `Inputs` fields are Type-valued and are directly accessible as
`.depositInputs` / `.exitInputs` on the structure itself; no separate
projection theorem is required for them. -/
theorem Deployment.linked_hypothesis {deposit exit : Receipt}
    (h : Deployment deposit exit) : exit.call.world = deposit.world := h.linked

/-! ## Hook 3 — SYSTEM authorization -/

/-- Interface a canonical SYSTEM caller/scheduler must supply for a single
empty-data zero-value SYSTEM invocation. This is exactly the field set
`ActualJournalHistory.Trace.system` accepts. It does not adopt a schedule,
does not identify the caller's authorization source and does not claim any
particular SYSTEM address is invoked by the pinned reference automatically. -/
structure SystemAuthorization (c : MessageCall.Context) : Prop where
  caller : c.caller = Eip8282.Audit.EvmRunner.sysAddr
  zeroValue : c.value = ⟨0⟩
  dataFit : c.calldata.size < UInt256.size

/-- Projection: hands off the three fields the SYSTEM Trace step accepts. -/
theorem SystemAuthorization.project {c : MessageCall.Context}
    (h : SystemAuthorization c) :
    c.caller = Eip8282.Audit.EvmRunner.sysAddr ∧ c.value = ⟨0⟩ ∧
      c.calldata.size < UInt256.size :=
  ⟨h.caller, h.zeroValue, h.dataFit⟩

/-! ## Combined interface -/

/-- A single bundle containing all three canonical hooks. Consumers that
require the whole set can accept `AllHooks` and dispatch to each hook via
the `.admission`, `.deployment`, `.authorization` accessors below. This is
still purely interface: no protocol policy is asserted, no schedule is
adopted, and the bundle carries no output field. Type-valued because the
inner `Deployment` carries data fields. -/
structure AllHooks (tx : RefundAccounting.Context) (kind : Contract)
    (sender : Account .EVM) (deposit exit : Receipt)
    (systemCall : MessageCall.Context) where
  admission : CompleteAdmission tx kind sender
  deployment : Deployment deposit exit
  authorization : SystemAuthorization systemCall

/-- Convenience wrapper projecting the two Prop-valued hooks. The
Type-valued `Deployment` field is directly accessible as `.deployment`
on the structure itself. -/
theorem AllHooks.propHooks {tx : RefundAccounting.Context} {kind : Contract}
    {sender : Account .EVM} {deposit exit : Receipt} {systemCall : MessageCall.Context}
    (h : AllHooks tx kind sender deposit exit systemCall) :
    CompleteAdmission tx kind sender ∧ SystemAuthorization systemCall :=
  ⟨h.admission, h.authorization⟩

#print axioms CompleteAdmission.project
#print axioms Deployment.linked_hypothesis
#print axioms SystemAuthorization.project
#print axioms AllHooks.propHooks

end Eip8282.Audit.Integrator.ReferenceCanonicalHooks
