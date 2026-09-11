import Eip8282.Audit.Integrator.ReferenceSourceTransferFunding

/-! Ordered update_sender_state (pinned Amsterdam fork.py929-967): capture the
sender balance, resolve execution/blob charges, increment nonce, subtract the
two charges with Uint underflow checks, convert to U256, set balance. The source
modify_state empty-account branch is retained; increment makes it unreachable.
Error states retain the already executed nonce/read effects. They are not
classified as caught EVM opcode faults or assigned an outer rollback policy.
The fee parameters are resolved source amounts; agreement with the old blob
price is NOT presumed. ReferencePrepaidGuarantees and ReferencePrepaidFailure
consume this operation to derive their source input journal from the pretransaction
journal. Source Python extraction and raw write-event correspondence remain open.
-/
namespace Eip8282.Audit.Integrator.ReferenceSourcePrepayment
open EvmYul
open ReferenceSourceValueTransfer
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

noncomputable def increment {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (sender : AccountAddress) : Tx Hash :=
  let old := account emptyHash parent tx sender
  let next := {old with nonce := old.nonce+1}
  let read := {tx with accounts := ReferenceAccountLookup.tracked tx.accounts sender}
  if next.nonce = 0 ∧ next.codeHash = emptyHash ∧ next.balance = ⟨0⟩ then
    writeAccount {read with storage := eraseStorage read.storage sender} sender none
  else writeAccount read sender (some next)

inductive Error where
  | executionFeeUnderflow
  | blobFeeUnderflow

/-- Fee computation errors precede this resolved-fee operation. Both subtraction
failures occur after increment_nonce, exactly as in update_sender_state. -/
noncomputable def pay {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (sender : AccountAddress)
    (executionFee blobFee : Nat) : Except Error Unit × Tx Hash :=
  let old := account emptyHash parent tx sender
  let read := {tx with accounts := ReferenceAccountLookup.tracked tx.accounts sender}
  let incremented := increment emptyHash parent read sender
  if executionFee ≤ old.balance.toNat then
    if blobFee ≤ old.balance.toNat-executionFee then
      (.ok (),modifyBalance emptyHash parent incremented sender
        (UInt256.ofNat (old.balance.toNat-executionFee-blobFee)))
    else (.error .blobFeeUnderflow,incremented)
  else (.error .executionFeeUnderflow,incremented)

private theorem account_write {Hash : Type} (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender address : AccountAddress) (value : Option (Account Hash)) :
    account emptyHash parent (writeAccount tx sender value) address =
      if address = sender then value.getD (empty emptyHash) else account emptyHash parent tx address := by
  classical
  by_cases same : address = sender <;> simp [account,writeAccount,ReferenceAccountLookup.peek,same]

theorem increment_form {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (sender : AccountAddress) :
    increment emptyHash parent tx sender =
      writeAccount {tx with accounts := ReferenceAccountLookup.tracked tx.accounts sender} sender
        (some {(account emptyHash parent tx sender) with nonce := (account emptyHash parent tx sender).nonce+1}) := by
  simp only [increment,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,false_and,if_false]

theorem increment_account {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (sender address : AccountAddress) :
    account emptyHash parent (increment emptyHash parent tx sender) address =
      if address = sender then {(account emptyHash parent tx sender) with nonce := (account emptyHash parent tx sender).nonce+1}
      else account emptyHash parent tx address := by
  rw [increment_form,account_write]
  rfl

/-- A successful fee debit changes nonce/balance at the sender, retaining its
presence even when the resulting balance is zero. -/
theorem successful_account {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (sender address : AccountAddress)
    (executionFee blobFee : Nat)
    (funded : executionFee+blobFee ≤ (account emptyHash parent tx sender).balance.toNat) :
    (pay emptyHash parent tx sender executionFee blobFee).1 = .ok () ∧
    account emptyHash parent (pay emptyHash parent tx sender executionFee blobFee).2 address =
      if address = sender then
        {(account emptyHash parent tx sender) with
          nonce := (account emptyHash parent tx sender).nonce+1
          balance := UInt256.ofNat ((account emptyHash parent tx sender).balance.toNat-executionFee-blobFee)}
      else account emptyHash parent tx address := by
  have first : executionFee ≤ (account emptyHash parent tx sender).balance.toNat := by omega
  have second : blobFee ≤ (account emptyHash parent tx sender).balance.toNat-executionFee := by omega
  unfold pay
  rw [if_pos first,if_pos second]
  refine ⟨rfl,?_⟩
  unfold modifyBalance
  rw [increment_account]
  simp only [if_true,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,false_and,if_false]
  rw [account_write]
  by_cases same : address = sender
  · simp only [if_pos same,Option.getD_some]
    rfl
  · simp only [if_neg same]
    change account emptyHash parent (increment emptyHash parent
      {tx with accounts := ReferenceAccountLookup.tracked tx.accounts sender} sender) address = _
    rw [increment_account]
    simp only [if_neg same]
    rfl

/-- Nonce increment prevents sender empty cleanup even if all balance is paid.
Storage/code/transient components survive both success and partial fee errors. -/
theorem fields {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (sender : AccountAddress) (executionFee blobFee : Nat) :
    (pay emptyHash parent tx sender executionFee blobFee).2.storage = tx.storage ∧
    (pay emptyHash parent tx sender executionFee blobFee).2.codeWrites = tx.codeWrites ∧
    (pay emptyHash parent tx sender executionFee blobFee).2.transient = tx.transient ∧
    (pay emptyHash parent tx sender executionFee blobFee).2.accounts.reads = insert sender tx.accounts.reads := by
  unfold pay
  dsimp only
  split
  · split
    · unfold modifyBalance
      rw [increment_account]
      simp only [if_true,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,false_and,if_false]
      simp [increment_form,writeAccount,ReferenceAccountLookup.tracked]
    · simp [increment_form,writeAccount,ReferenceAccountLookup.tracked]
  · simp [increment_form,writeAccount,ReferenceAccountLookup.tracked]

theorem successful_hash {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (sender address : AccountAddress)
    (executionFee blobFee : Nat)
    (funded : executionFee+blobFee ≤ (account emptyHash parent tx sender).balance.toNat) :
    hashAt emptyHash parent (pay emptyHash parent tx sender executionFee blobFee).2 address =
      hashAt emptyHash parent tx address := by
  unfold hashAt
  rw [(successful_account emptyHash parent tx sender address executionFee blobFee funded).2]
  split <;> simp_all

private theorem load_hash {Hash LoadError : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (address : AccountAddress) :
    (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash parent tx.accounts codeParent tx.codeWrites address).1 =
      ReferenceCodeAccountPresence.getCode emptyHash codeParent tx.codeWrites (hashAt emptyHash parent tx address) := by
  unfold ReferenceCodeAccountPresence.load hashAt account
  cases ReferenceAccountLookup.peek parent tx.accounts address <;> rfl

/-- Code loading after source prepayment uses the same before-transaction
hash/code observation; it is not a fresh assumed after-state binding. -/
theorem successful_load {Hash LoadError : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (sender address : AccountAddress)
    (executionFee blobFee : Nat)
    (funded : executionFee+blobFee ≤ (account emptyHash parent tx sender).balance.toNat) :
    (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash parent
      (pay emptyHash parent tx sender executionFee blobFee).2.accounts codeParent
      (pay emptyHash parent tx sender executionFee blobFee).2.codeWrites address).1 =
    (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash parent tx.accounts codeParent tx.codeWrites address).1 := by
  rw [load_hash,load_hash,successful_hash emptyHash parent tx sender address executionFee blobFee funded,
    (fields emptyHash parent tx sender executionFee blobFee).2.1]

#print axioms fields
#print axioms successful_hash
#print axioms successful_load

#print axioms increment_form
#print axioms increment_account
#print axioms successful_account
end Eip8282.Audit.Integrator.ReferenceSourcePrepayment
