import Eip8282.Audit.Integrator.ReferenceCheckpointCall
import Eip8282.Audit.Integrator.ReferenceSourceDispatch
import Eip8282.Audit.Integrator.ReferenceSourcePrepaidCheckpoint
import Eip8282.Audit.Integrator.ReferenceAdmissionExtraction

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
