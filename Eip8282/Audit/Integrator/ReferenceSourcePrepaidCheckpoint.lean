import Eip8282.Audit.Integrator.ReferenceSourcePrepayment
import Eip8282.Audit.Integrator.ReferenceCheckpointCall

/-! Source prepayment supplies the old checkpoint's balance observation for
represented nonblob transactions. Both source and old blob charges are zero;
no equality of their different blob tariffs is assumed. This additional domain
belongs to the stronger pretransaction-source-journal APIs, not the unchanged
checkpoint APIs. The source nonce is updated naturally; equality of full nonce/
account payloads with the old world is not claimed from balance correspondence.
-/
namespace Eip8282.Audit.Integrator.ReferenceSourcePrepaidCheckpoint
open EvmYul EvmYul.EVM
open ReferenceSourceValueTransfer ReferenceSourceTransferFunding
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def Nonblob : Transaction → Prop
  | .blob _ => False
  | _ => True

def executionFee (transaction : RefundAccounting.Context) : Nat :=
  transaction.transaction.base.gasLimit.toNat * transaction.effectivePrice.toNat

noncomputable def prepaid {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (before : Tx Hash) (transaction : RefundAccounting.Context) :=
  ReferenceSourcePrepayment.pay emptyHash parent before transaction.sender (executionFee transaction) 0

private theorem upfront {transaction : RefundAccounting.Context} (nonblob : Nonblob transaction.transaction) :
    TransactionFunding.upfront transaction = executionFee transaction := by
  unfold TransactionFunding.upfront executionFee
  have blob : calcBlobFee transaction.header transaction.transaction = 0 := by
    cases h : transaction.transaction <;> simp [Nonblob,h] at nonblob <;> simp [calcBlobFee,getTotalBlobGas]
  rw [blob,Nat.add_zero]

/-- Source resolved-fee affordability comes from the actual same admission and
pretransaction balance reads; it is not a successful-prepayment premise. -/
theorem funded {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (before : Tx Hash) (transaction : RefundAccounting.Context)
    {sender : EvmYul.Account .EVM} (admission : TransactionFunding.Admission transaction sender)
    (nonblob : Nonblob transaction.transaction)
    (balances : BalancesRelated emptyHash parent before transaction.world) :
    executionFee transaction+0 ≤ (account emptyHash parent before transaction.sender).balance.toNat := by
  have paid := admission.funded
  rw [upfront nonblob] at paid
  rw [balances transaction.sender]
  unfold TransferFunding.worldBalance
  rw [admission.sender]
  simp only [Option.map_some,Option.getD_some]
  omega

theorem success {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (before : Tx Hash) (transaction : RefundAccounting.Context)
    {sender : EvmYul.Account .EVM} (admission : TransactionFunding.Admission transaction sender)
    (nonblob : Nonblob transaction.transaction)
    (balances : BalancesRelated emptyHash parent before transaction.world) :
    (prepaid emptyHash parent before transaction).1 = .ok () :=
  (ReferenceSourcePrepayment.successful_account emptyHash parent before transaction.sender transaction.sender
    (executionFee transaction) 0 (funded emptyHash parent before transaction admission nonblob balances)).1

private theorem lookup_insert (world : AccountMap .EVM) (sender address : AccountAddress) (a : EvmYul.Account .EVM) :
    (world.insert sender a).get? address = if sender = address then some a else world.get? address :=
  (Std.TreeMap.getElem?_insert (t := world) (k := sender) (a := address) (v := a)).trans
    (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)

/-- All post-prepayment balances are derived at the same actual old checkpoint.
A separate after-state BalancesRelated assumption is removed by this producer. -/
theorem balances {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (before : Tx Hash) (transaction : RefundAccounting.Context)
    {sender : EvmYul.Account .EVM} (admission : TransactionFunding.Admission transaction sender)
    (nonblob : Nonblob transaction.transaction)
    (related : BalancesRelated emptyHash parent before transaction.world) :
    BalancesRelated emptyHash parent (prepaid emptyHash parent before transaction).2 transaction.checkpoint := by
  have enough := funded emptyHash parent before transaction admission nonblob related
  have oldBalance : (account emptyHash parent before transaction.sender).balance.toNat = sender.balance.toNat := by
    rw [related transaction.sender]
    simp only [TransferFunding.worldBalance,admission.sender,Option.map_some,Option.getD_some]
  have debited := TransactionFunding.debited_balance transaction admission
  rw [upfront nonblob] at debited
  intro address
  unfold prepaid
  rw [(ReferenceSourcePrepayment.successful_account emptyHash parent before transaction.sender address
    (executionFee transaction) 0 enough).2]
  rw [TransactionFunding.checkpoint_eq transaction admission]
  unfold TransferFunding.worldBalance
  rw [lookup_insert]
  by_cases same : address = transaction.sender
  · subst address
    simp only [if_true,Option.map_some,Option.getD_some]
    change ((account emptyHash parent before transaction.sender).balance.toNat-executionFee transaction-0) % UInt256.size =
      (TransactionFunding.debited transaction sender).balance.toNat
    have bound : (account emptyHash parent before transaction.sender).balance.toNat-executionFee transaction < UInt256.size :=
      (Nat.sub_le _ _).trans_lt (account emptyHash parent before transaction.sender).balance.val.isLt
    rw [Nat.sub_zero,Nat.mod_eq_of_lt bound,oldBalance]
    omega
  · simp only [if_neg same,if_neg (Ne.symm same)]
    exact related address

/-- Code and all storage bindings can be transported from before prepayment. -/
theorem fields {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (before : Tx Hash) (transaction : RefundAccounting.Context) :
    (prepaid emptyHash parent before transaction).2.storage = before.storage ∧
    (prepaid emptyHash parent before transaction).2.codeWrites = before.codeWrites ∧
    (prepaid emptyHash parent before transaction).2.transient = before.transient ∧
    (prepaid emptyHash parent before transaction).2.accounts.reads = insert transaction.sender before.accounts.reads :=
  ReferenceSourcePrepayment.fields emptyHash parent before transaction.sender (executionFee transaction) 0

theorem loaded {Hash LoadError : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (before : Tx Hash) (transaction : RefundAccounting.Context)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (address : AccountAddress)
    {sender : EvmYul.Account .EVM} (admission : TransactionFunding.Admission transaction sender)
    (nonblob : Nonblob transaction.transaction)
    (related : BalancesRelated emptyHash parent before transaction.world) :
    (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash parent
      (prepaid emptyHash parent before transaction).2.accounts codeParent
      (prepaid emptyHash parent before transaction).2.codeWrites address).1 =
    (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash parent before.accounts codeParent before.codeWrites address).1 :=
  ReferenceSourcePrepayment.successful_load emptyHash parent before codeParent transaction.sender address
    (executionFee transaction) 0 (funded emptyHash parent before transaction admission nonblob related)

/-- The next-call API's source observations are supplied before prepayment.
The consumer receives derived success, code, balance and protected slot facts
at the actual checkpoint, all for the same computed prepayment state. -/
theorem bindings {Hash LoadError : Type} [DecidableEq Hash] (emptyHash : Hash)
    (accountsParent : Parent Hash) (before : Tx Hash) (transaction : RefundAccounting.Context)
    (kind : ReachableCalls.Contract)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError)
    (parent : ReferenceStorageView.Parent)
    {sender : EvmYul.Account .EVM} (admission : TransactionFunding.Admission transaction sender)
    (nonblob : Nonblob transaction.transaction)
    (related : BalancesRelated emptyHash accountsParent before transaction.world)
    (code : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind))
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (ReachableCalls.address kind) q.toByteArray =
      SystemSpec.worldSlot transaction.world (ReachableCalls.address kind) q) :
    (prepaid emptyHash accountsParent before transaction).1 = .ok () ∧
    (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (prepaid emptyHash accountsParent before transaction).2.accounts codeParent
      (prepaid emptyHash accountsParent before transaction).2.codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind) ∧
    BalancesRelated emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 transaction.checkpoint ∧
    ∀ q, ReferenceStorageView.current parent (prepaid emptyHash accountsParent before transaction).2.storage (ReachableCalls.address kind) q.toByteArray =
      SystemSpec.worldSlot transaction.checkpoint (ReachableCalls.address kind) q := by
  refine ⟨success emptyHash accountsParent before transaction admission nonblob related,
    (loaded emptyHash accountsParent before transaction codeParent (ReachableCalls.address kind) admission nonblob related).trans code,
    balances emptyHash accountsParent before transaction admission nonblob related,?_⟩
  intro q
  rw [(fields emptyHash accountsParent before transaction).1,slots]
  exact (TransactionJournalEdges.checkpoint_frame transaction admission (ReachableCalls.address kind)).storage q |>.symm

#print axioms bindings

#print axioms funded
#print axioms success
#print axioms balances
#print axioms fields
#print axioms loaded
end Eip8282.Audit.Integrator.ReferenceSourcePrepaidCheckpoint
