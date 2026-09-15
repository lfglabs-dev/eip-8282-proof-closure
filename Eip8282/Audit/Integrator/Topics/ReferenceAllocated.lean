import Eip8282.Audit.Integrator.ReferenceAdmissionExtraction
import Eip8282.Audit.Integrator.Topics.ReferenceCheckpoint
import Eip8282.Audit.Integrator.Topics.Reference6
import Eip8282.Audit.Integrator.Topics.ReferenceRuntime2
import Eip8282.Audit.Integrator.ReferenceRuntimeTransactionPayment
import Eip8282.Audit.Integrator.ReferenceSourceDispatch
import Eip8282.Audit.Integrator.ReferenceSourcePrepaidCheckpoint

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceAllocatedEntry -/

/-! Allocated entry for represented ordinary (non-creation, non-type4) calls.
Intrinsic execution follows transactions.py713-774 and gas.py154-164: zero/nonzero
data tokens, recipient/value cost, access-list execution cost plus its data-floor
cost. No old intrinsicGas equality is asserted. The two intrinsic validation
checks are independently meaningful source admission clauses, not a desired
post-meter. SourceChecks supplies the existing nonce/fee/floor clauses, with
explicit represented sender presence. Consumers: allocated all3/failure APIs. -/
namespace Eip8282.Audit.Integrator.ReferenceAllocatedEntry
open EvmYul EvmYul.EVM
open ReferenceSourcePrepaidCheckpoint
open ReferenceAdmissionExtraction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def zeroBytes (data : ByteArray) : Nat := data.data.toList.count 0

def dataTokens (data : ByteArray) : Nat :=
  let zeros := zeroBytes data
  let nonzeros := data.size-zeros
  zeros+nonzeros*4

/-- Fold order is address charge then key charge, followed by the floor surcharge. -/
def accessCost (tx : Transaction) : Nat :=
  let cost := tx.getAccessList.foldl (fun cost entry => cost+(3000-100)+entry.2.size*(2100-100)) 0
  cost+accessListFloorTokens tx*16

/-- Call branch only: no creation initcode charge and no type4 authorization tuples. -/
def intrinsic (tx : RefundAccounting.Context) : Nat :=
  let dataCost := dataTokens tx.transaction.base.data*4
  let base := 12000+recipientExecution tx.transaction tx.sender
  base+0+dataCost+accessCost tx.transaction+0

def CostChecks (tx : RefundAccounting.Context) : Prop :=
  intrinsic tx ≤ tx.transaction.base.gasLimit.toNat ∧ intrinsic tx ≤ 16777216

def meter (tx : RefundAccounting.Context) : ReferenceMeterRollback.Meter :=
  ReferenceTransactionWork.initial tx.transaction.base.gasLimit.toNat (intrinsic tx)

theorem zeroes_fit (data : ByteArray) : zeroBytes data ≤ data.size := by
  exact List.count_le_length

/-- Derive the old funding consumer and calldata width from source-shaped
clauses. Nonblob discharges old blob compatibility; presence stays explicit. -/
theorem admission {tx : RefundAccounting.Context} {sender : EvmYul.Account .EVM}
    (checks : SourceChecks tx sender) (found : tx.world.get? tx.sender = some sender)
    (nonblob : Nonblob tx.transaction) :
    TransactionFunding.Admission tx sender ∧ tx.transaction.base.data.size < UInt256.size := by
  have compatible : OldBlobFeeCovered tx.header tx.transaction := by
    cases h : tx.transaction <;> simp [Nonblob,h] at nonblob <;> simp [OldBlobFeeCovered]
  exact ⟨ReferenceAdmissionExtraction.admission checks ⟨found,compatible⟩,
    ReferenceCalldataAdmission.data_fit _ (ReferenceAdmissionExtraction.gate checks)⟩

/-- Exact allocation pool conservation plus the derived executable-potential cap.
These are real source-shaped pools, never the synthetic old replay resources. -/
theorem allocated (tx : RefundAccounting.Context) (checks : CostChecks tx) :
    zeroBytes tx.transaction.base.data ≤ tx.transaction.base.data.size ∧
    intrinsic tx+(meter tx).execution+(meter tx).reservoir = tx.transaction.base.gasLimit.toNat ∧
    ReferenceExecutionPotential.potential (meter tx) ≤ 16777216 := by
  have h := ReferenceTransactionGas.allocation tx.transaction.base.gasLimit.toNat (intrinsic tx) checks.1 checks.2
  exact ⟨zeroes_fit _,h.2.1,ReferenceSourceDispatch.allocated_bound _ _⟩

/-- Same actual before-journal observations select the no-charge dispatch
prefix, after successful prepayment. Its read journal is the one already used
by the transfer/checked-evaluator consumers. No successful probe is assumed. -/
theorem dispatched {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (tx : RefundAccounting.Context) (kind : ReachableCalls.Contract)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    {sender : EvmYul.Account .EVM} (checks : SourceChecks tx sender)
    (found : tx.world.get? tx.sender = some sender) (nonblob : Nonblob tx.transaction)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash parent before tx.world)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash parent before.accounts codeParent before.codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    ReferenceSourceDispatch.probe emptyHash parent (prepaid emptyHash parent before tx).2 codeParent (ReachableCalls.address kind) tx.transaction.base.value =
      (.ready (ReachableCalls.runtime kind),ReferenceTransferredFailure.fetched emptyHash parent (prepaid emptyHash parent before tx).2 codeParent (ReachableCalls.address kind)) := by
  have current := ReferenceSourcePrepaidCheckpoint.loaded emptyHash parent before tx codeParent (ReachableCalls.address kind)
    (admission checks found nonblob).1 nonblob balances
  rw [loaded] at current
  exact ReferenceSourceDispatch.ready_fetched emptyHash parent _ codeParent kind _ current

/-- Value-entry continuation of the ready probe. Public consumers derive the
ready tag before using this continuation; other probe tags are not executed here. -/
noncomputable def entered {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (tx : RefundAccounting.Context) (kind : ReachableCalls.Contract)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) :=
  ReferenceSourceValueTransfer.enter emptyHash parent
    (ReferenceSourceDispatch.probe emptyHash parent (prepaid emptyHash parent before tx).2 codeParent
      (ReachableCalls.address kind) tx.transaction.base.value).2
    tx.sender (ReachableCalls.address kind) tx.transaction.base.value true

theorem entered_eq {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (tx : RefundAccounting.Context) (kind : ReachableCalls.Contract)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    {sender : EvmYul.Account .EVM} (checks : SourceChecks tx sender)
    (found : tx.world.get? tx.sender = some sender) (nonblob : Nonblob tx.transaction)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash parent before tx.world)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash parent before.accounts codeParent before.codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    entered emptyHash parent before tx kind codeParent =
      ReferenceTransferredFailure.entry (ReferenceCheckpointCall.call kind tx) emptyHash parent
        (prepaid emptyHash parent before tx).2 codeParent true := by
  unfold entered
  rw [dispatched emptyHash parent before tx kind codeParent checks found nonblob balances loaded]
  rfl

#print axioms zeroes_fit
#print axioms admission
#print axioms allocated
#print axioms dispatched
#print axioms entered_eq
end Eip8282.Audit.Integrator.ReferenceAllocatedEntry

end

section

/-! ## ReferenceAllocatedFailure -/

/-! Same three-guarantee / failed-frame consumers from actual computed dispatch
read journal and source allocated meter. Selected source nonce/fee/floor checks
plus represented sender presence derive funding admission and calldata width.
Explicit intrinsic admission clauses justify every allocation subtraction.
The source constructor bridge remains scoped: represented nonblob call without
authorizations, pinned nondelegating code, protected-owner logs. No full Python
extraction, canonical admission/history, synthetic/source gas equality, global
ancestor commitment or guaranteed termination is claimed. -/
namespace Eip8282.Audit.Integrator.ReferenceAllocatedFailure
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceCheckedDispatch ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

open ReferenceCheckpointCall (call)
open ReferenceSourcePrepaidCheckpoint (prepaid)
private theorem code (kind : Contract) (transaction : RefundAccounting.Context) :
    (call kind transaction).code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by
  cases kind <;> rfl

theorem settled {deposit exit : TransactionAppendBudget.Receipt} {Hash LoadError : Type} [DecidableEq Hash]
    (kind : Contract) (transaction : RefundAccounting.Context)
    (history : ReleaseCandidate.History deposit exit transaction.world)
    {sender : EvmYul.Account .EVM}
    (checks : ReferenceAdmissionExtraction.SourceChecks transaction sender)
    (found : transaction.world.get? transaction.sender = some sender)
    (recipient : transaction.transaction.base.recipient = some (ReachableCalls.address kind))
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob transaction.transaction)
    (costs : ReferenceAllocatedEntry.CostChecks transaction)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError)
    {parent : ReferenceStorageView.Parent} {partialWarm : Warm} {partialMeter : Meter}
    {fuel : Nat} {events : List Event} {view : View} {output : ByteArray} {fault : Fault}
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites (call kind transaction).target).1 = .ok (call kind transaction).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before transaction.world)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent (ReferenceInitialAccess.destinations (call kind transaction).code) parent ByteArray.empty fuel
      (ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).2.accounts
      (initial (CallBridge.codeCall (call kind transaction) (code kind transaction) 0) (ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).2.storage)
      (ReferenceInitialAccess.warm transaction) (ReferenceAllocatedEntry.meter transaction) = some ((events,.failed fault view partialWarm partialMeter output),finalAccounts))
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (call kind transaction).target q.toByteArray = SystemSpec.worldSlot transaction.world (call kind transaction).target q)
    :
    ReferenceSourceDispatch.probe emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent
      (ReachableCalls.address kind) transaction.transaction.base.value =
      (.ready (ReachableCalls.runtime kind),fetched emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent (ReachableCalls.address kind)) ∧
    ReferenceAllocatedEntry.zeroBytes transaction.transaction.base.data ≤ transaction.transaction.base.data.size ∧
    ReferenceAllocatedEntry.intrinsic transaction+(ReferenceAllocatedEntry.meter transaction).execution+
      (ReferenceAllocatedEntry.meter transaction).reservoir = transaction.transaction.base.gasLimit.toNat ∧
    ReferenceExecutionPotential.potential (ReferenceAllocatedEntry.meter transaction) ≤ 16777216 ∧
    (prepaid emptyHash accountsParent before transaction).1 = .ok () ∧
    TransactionEventBounds.request transaction = .theta transaction.fuel
      (TransactionEventBounds.message transaction (ReachableCalls.address kind)) ∧
    (0 < transaction.fuel → (call kind transaction).result =
      (NestedEvents.Request.theta transaction.fuel (TransactionEventBounds.message transaction (ReachableCalls.address kind))).eval) ∧
    let live := {(ReferenceAllocatedEntry.entered emptyHash accountsParent before transaction kind codeParent).2 with accounts := finalAccounts, storage := view.storage}
    let restored := restore live (prepaid emptyHash accountsParent before transaction).2
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent restored (call kind transaction).world ∧
    ∃ receipt,
      ReferenceCheckedFrameOutcome.settle (prepaid emptyHash accountsParent before transaction).2.storage [] (ReferenceInitialAccess.warm transaction) (.failed fault view partialWarm partialMeter output) = .returned receipt ∧
      receipt.beforeSettlement = view ∧ receipt.output = ByteArray.empty ∧
      receipt.meter.execution = 0 ∧ receipt.meter.reservoir = partialMeter.baseline ∧
      receipt.meter.spill = 0 ∧ receipt.meter.refund = 0 ∧
      receipt.meter.committedSpill = partialMeter.committedSpill ∧
      receipt.logsForParent = [] ∧ receipt.warmForParent = none ∧
      receipt.storage = restored.storage ∧
      restored.accounts.writes = (prepaid emptyHash accountsParent before transaction).2.accounts.writes ∧
      restored.codeWrites = (prepaid emptyHash accountsParent before transaction).2.codeWrites ∧ restored.transient = (prepaid emptyHash accountsParent before transaction).2.transient ∧
      restored.accounts.reads = finalAccounts.reads ∧
      restored.storage.reads = view.storage.reads ∧ restored.storage.created = view.storage.created ∧
      ∀ p address key, ReferenceStorageView.current p restored.storage address key =
        ReferenceStorageView.current p (prepaid emptyHash accountsParent before transaction).2.storage address key := by
  have admitted := ReferenceAllocatedEntry.admission checks found nonblob
  have allocated := ReferenceAllocatedEntry.allocated transaction costs
  have dispatch := ReferenceAllocatedEntry.dispatched emptyHash accountsParent before transaction kind codeParent
    checks found nonblob balances loaded
  have entered := ReferenceAllocatedEntry.entered_eq emptyHash accountsParent before transaction kind codeParent
    checks found nonblob balances loaded
  have bound : ReferenceExecutionPotential.potential (ReferenceAllocatedEntry.meter transaction) ≤ 30000000 := by
    have cap := allocated.2.2
    omega
  rw [entered] at actual ⊢
  refine ⟨dispatch,allocated.1,allocated.2.1,allocated.2.2,?_⟩
  exact ReferenceInitializedFailure.settled kind transaction history admitted.1 recipient nonblob emptyHash accountsParent before
    codeParent loaded balances actual slots bound admitted.2

#print axioms settled
end Eip8282.Audit.Integrator.ReferenceAllocatedFailure

end

section

/-! ## ReferenceAllocatedReceipt -/

/-! Resource certificates and all three guarantees share the same actual
returned message receipt. Success/REVERT certificates identify the exact trace
and source-allocated sufficient initial grants with reservoir-first spill; exceptional failures retain the
actual error/rollback, without claiming a source exceptional replay. -/
namespace Eip8282.Audit.Integrator.ReferenceAllocatedReceipt
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Correspondence (runtimeCode)
open ReachableCalls (Contract PinnedCall)
open JournalInvariant (Invariant modelKind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeTransactionPayment
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2400000

def Observed {kind : Kind} (c : MessageCall.Context) (codeEq : c.code = runtimeCode kind)
    (steps cap : Nat) (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx) (w : Warm)
    (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (substate : Substate) (success : Bool) (out : ByteArray) : Prop :=
  let frame := CallBridge.codeCall c codeEq steps
  if success then
    ∃ post : EVM.State,
      (post.createdAccounts,post.accountMap,post.gasAvailable,post.substate) =
        (created,world,gas,substate) ∧
      SuccessPayment kind parent tx.created steps cap frame.entry post out (initial frame tx) w
  else
    world = c.world ∧ substate = c.substate ∧ created = c.created ∧
      ((frame.result = .ok (.revert gas out) ∧
          RevertPayment kind parent tx.created steps cap frame.entry gas out (initial frame tx) w) ∨
        ∃ e, frame.result = .error e ∧ (e == ExecutionException.OutOfFuel) = false ∧
          gas = UInt256.ofNat 0 ∧ out = ByteArray.empty)

/-- Attach certificates to the already observed receipt. All runtime witnesses
come from that receipt; only source initial bindings and resources remain inputs. -/
theorem strengthen {kind : Kind} (c : MessageCall.Context) (codeEq : c.code = runtimeCode kind)
    (steps cap : Nat) (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx) (w : Warm)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (observed : ReferenceRuntimeResourceReceipt.Observed c codeEq steps cap parent tx w created world gas substate success out)
    (threshold : RuntimeMemoryFunding.energy (CallBridge.codeCall c codeEq steps).entry <
      ReferenceMemoryCapacity.cost (cap+1)) :
    Observed c codeEq steps cap parent tx w created world gas substate success out := by
  let frame := CallBridge.codeCall c codeEq steps
  have hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) frame.entry := by
    cases kind
    · exact ⟨frame.code_pinned,Or.inl RuntimeExecutionScope.deposit.entry⟩
    · exact ⟨frame.code_pinned,Or.inl RuntimeExecutionScope.exit.entry⟩
  cases success with
  | true =>
    obtain ⟨post,payload,viewed⟩ := observed
    exact ⟨post,payload,ReferenceRuntimeTransactionPayment.success viewed hat threshold⟩
  | false =>
    obtain ⟨hw,hs,hc,hcase⟩ := observed
    refine ⟨hw,hs,hc,?_⟩
    rcases hcase with ⟨actual,viewed⟩ | exceptional
    · exact Or.inl ⟨actual,ReferenceRuntimeTransactionPayment.revert viewed hat threshold⟩
    · exact Or.inr exceptional

/-- Same pre-world, full receipt, all three guarantee predicates and complete
source-resource certificates. Canonical history must still produce invariant,
budget and source bindings; AllocatedPaymentFor gives sufficient transaction limits, not their
protocol admission. -/
theorem guarantees (kind : Contract) (c : MessageCall.Context) (pinned : PinnedCall kind c)
    (codeEq : c.code = runtimeCode (modelKind kind)) (steps : Nat) (hf : c.fuel = steps+1)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (actual : c.result = .ok (created,world,gas,substate,success,out))
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx) (w : Warm)
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c codeEq steps).entry.toState)
    (warm : WarmRelated w (CallBridge.codeCall c codeEq steps).entry)
    (cap : Nat) (cdfit : c.calldata.size < UInt256.size)
    (threshold : RuntimeMemoryFunding.energy (CallBridge.codeCall c codeEq steps).entry <
      ReferenceMemoryCapacity.cost (cap+1)) (host : 32*cap < 2^System.Platform.numBits)
    {budget : Nat} (invariant : Invariant kind budget c.world) (bound : budget < 2^128) :
    NestedProtectedJournal.Observed kind c created world substate success out ∧
      Observed c codeEq steps cap parent tx w created world gas substate success out := by
  obtain ⟨guards,viewed⟩ := ReferenceRuntimeResourceReceipt.guarantees kind c pinned codeEq steps hf actual
    parent tx w slots warm cap cdfit threshold host invariant bound
  exact ⟨guards,strengthen c codeEq steps cap parent tx w viewed threshold⟩

#print axioms strengthen
#print axioms guarantees
end Eip8282.Audit.Integrator.ReferenceAllocatedReceipt

end
