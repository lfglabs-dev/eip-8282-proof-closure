import Eip8282.Audit.Integrator.Topics.Reference

/-! Literal balance mutation order from pinned state_tracker.move_ether:
debit sender, then credit recipient using the updated state. Arithmetic checks
precede each update; recipient overflow preserves the completed debit and its
read metadata until an enclosing source boundary handles it. modify_state
cleans empty accounts, including the source storage-write-to-read conversion.
This functional journal projection is not yet a Python/world representation
proof or a claim that admission rules discharge transfer errors. LOG3 emission
belongs to process_call after this operation and is not omitted from that
outstanding frame-entry obligation.
-/
namespace Eip8282.Audit.Integrator.ReferenceSourceValueTransfer
open EvmYul
set_option autoImplicit false
set_option maxHeartbeats 1600000

structure Account (Hash : Type) where
  nonce : Nat
  balance : UInt256
  codeHash : Hash

structure Tx (Hash : Type) where
  accounts : ReferenceAccountLookup.Tx (Account Hash)
  storage : ReferenceStorageView.Tx
  codeWrites : Hash → Option ByteArray
  transient : AccountAddress → ByteArray → Option UInt256

abbrev Parent (Hash : Type) := ReferenceAccountLookup.Parent (Account Hash)

def empty {Hash : Type} (emptyHash : Hash) : Account Hash := ⟨0,⟨0⟩,emptyHash⟩
def account {Hash : Type} (emptyHash : Hash) (parent : Parent Hash) (tx : Tx Hash)
    (address : AccountAddress) : Account Hash :=
  (ReferenceAccountLookup.peek parent tx.accounts address).getD (empty emptyHash)
def hashAt {Hash : Type} (emptyHash : Hash) (parent : Parent Hash) (tx : Tx Hash)
    (address : AccountAddress) : Hash := (account emptyHash parent tx address).codeHash

noncomputable def eraseStorage (tx : ReferenceStorageView.Tx) (address : AccountAddress) : ReferenceStorageView.Tx :=
  {tx with
    writes := fun a k => if a = address then none else tx.writes a k
    reads := {p | p ∈ tx.reads ∨ (p.1 = address ∧ (tx.writes p.1 p.2).isSome)}}

noncomputable def writeAccount {Hash : Type} (tx : Tx Hash) (address : AccountAddress)
    (value : Option (Account Hash)) : Tx Hash :=
  {tx with accounts := {tx.accounts with
    writes := fun a => if a = address then some value else tx.accounts.writes a}}

/-- Both get_account and account_exists_and_is_empty record the address; sets
make their duplicate read extension idempotent. Empty cleanup changes storage
only at this address, while preserving created-account metadata. -/
noncomputable def modifyBalance {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (address : AccountAddress) (balance : UInt256) : Tx Hash :=
  let old := account emptyHash parent tx address
  let next := {old with balance := balance}
  let read := {tx with accounts := ReferenceAccountLookup.tracked tx.accounts address}
  if next.nonce = 0 ∧ next.codeHash = emptyHash ∧ next.balance = ⟨0⟩ then
    let erased := {read with storage := eraseStorage read.storage address}
    writeAccount erased address none
  else writeAccount read address (some next)

inductive Error where
  | underfundedAssertion
  | creditOverflow

/-- An error retains the actual partially modified state; it is not declared a
caught EVM opcode fault and no restoration is built into this operation. -/
noncomputable def move {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender recipient : AccountAddress) (value : UInt256) : Except Error Unit × Tx Hash :=
  let senderAccount := account emptyHash parent tx sender
  let senderRead := {tx with accounts := ReferenceAccountLookup.tracked tx.accounts sender}
  if value.toNat ≤ senderAccount.balance.toNat then
    let debited := modifyBalance emptyHash parent senderRead sender
      (UInt256.ofNat (senderAccount.balance.toNat-value.toNat))
    let recipientAccount := account emptyHash parent debited recipient
    let recipientRead := {debited with accounts := ReferenceAccountLookup.tracked debited.accounts recipient}
    if recipientAccount.balance.toNat+value.toNat < UInt256.size then
      (.ok (),modifyBalance emptyHash parent recipientRead recipient
        (UInt256.ofNat (recipientAccount.balance.toNat+value.toNat)))
    else (.error .creditOverflow,recipientRead)
  else (.error .underfundedAssertion,senderRead)

private theorem account_read {Hash : Type} (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (read address : AccountAddress) :
    account emptyHash parent {tx with accounts := ReferenceAccountLookup.tracked tx.accounts read} address =
      account emptyHash parent tx address := rfl

private theorem account_write {Hash : Type} (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (key address : AccountAddress) (value : Option (Account Hash)) :
    account emptyHash parent (writeAccount tx key value) address =
      if address = key then value.getD (empty emptyHash) else account emptyHash parent tx address := by
  classical
  by_cases same : address = key <;>
    simp [account,writeAccount,ReferenceAccountLookup.peek,same]

theorem modify_hash {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (key address : AccountAddress) (balance : UInt256) :
    hashAt emptyHash parent (modifyBalance emptyHash parent tx key balance) address =
      hashAt emptyHash parent tx address := by
  classical
  unfold modifyBalance
  dsimp only
  split
  · rename_i deleted
    unfold hashAt
    rw [account_write]
    by_cases same : address = key
    · subst address
      simpa [empty] using deleted.2.1.symm
    · simp only [if_neg same]
      rfl
  · unfold hashAt
    rw [account_write]
    by_cases same : address = key <;> simp [same,account_read]

theorem modify_protected_storage {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (key address : AccountAddress) (balance : UInt256)
    (nonempty : hashAt emptyHash parent tx address ≠ emptyHash)
    (storageParent : ReferenceStorageView.Parent) (slot : ByteArray) :
    ReferenceStorageView.current storageParent (modifyBalance emptyHash parent tx key balance).storage address slot =
      ReferenceStorageView.current storageParent tx.storage address slot := by
  classical
  unfold modifyBalance
  dsimp only
  split
  · rename_i deleted
    have different : address ≠ key := by
      intro same
      subst address
      exact nonempty deleted.2.1
    simp [writeAccount,eraseStorage,ReferenceStorageView.current,different]
  · rfl

theorem move_hash {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender recipient address : AccountAddress) (value : UInt256) :
    hashAt emptyHash parent (move emptyHash parent tx sender recipient value).2 address =
      hashAt emptyHash parent tx address := by
  unfold move
  dsimp only
  split
  · split
    · dsimp only
      rw [modify_hash]
      change hashAt emptyHash parent (modifyBalance emptyHash parent
        {tx with accounts := ReferenceAccountLookup.tracked tx.accounts sender} sender _) address = _
      rw [modify_hash]
      rfl
    · dsimp only
      change hashAt emptyHash parent (modifyBalance emptyHash parent
        {tx with accounts := ReferenceAccountLookup.tracked tx.accounts sender} sender _) address = _
      rw [modify_hash]
      rfl
  · rfl

theorem move_protected_storage {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender recipient address : AccountAddress) (value : UInt256)
    (nonempty : hashAt emptyHash parent tx address ≠ emptyHash)
    (storageParent : ReferenceStorageView.Parent) (slot : ByteArray) :
    ReferenceStorageView.current storageParent (move emptyHash parent tx sender recipient value).2.storage address slot =
      ReferenceStorageView.current storageParent tx.storage address slot := by
  unfold move
  dsimp only
  split
  · split
    · dsimp only
      rw [modify_protected_storage]
      · exact modify_protected_storage emptyHash parent {tx with accounts := ReferenceAccountLookup.tracked tx.accounts sender} sender address _ nonempty storageParent slot
      · change hashAt emptyHash parent (modifyBalance emptyHash parent
          {tx with accounts := ReferenceAccountLookup.tracked tx.accounts sender} sender _) address ≠ _
        rw [modify_hash]
        exact nonempty
    · dsimp only
      exact modify_protected_storage emptyHash parent {tx with accounts := ReferenceAccountLookup.tracked tx.accounts sender} sender address _ nonempty storageParent slot
  · rfl

/-- Guard is from process_call, not inferred from balance mutation semantics. -/
noncomputable def enter {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender recipient : AccountAddress) (value : UInt256) (shouldTransfer : Bool) : Except Error Unit × Tx Hash :=
  if shouldTransfer ∧ value ≠ ⟨0⟩ then move emptyHash parent tx sender recipient value else (.ok (),tx)

theorem enter_hash {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender recipient address : AccountAddress) (value : UInt256) (shouldTransfer : Bool) :
    hashAt emptyHash parent (enter emptyHash parent tx sender recipient value shouldTransfer).2 address =
      hashAt emptyHash parent tx address := by
  unfold enter
  split
  · exact move_hash emptyHash parent tx sender recipient address value
  · rfl

theorem enter_protected_storage {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender recipient address : AccountAddress) (value : UInt256) (shouldTransfer : Bool)
    (nonempty : hashAt emptyHash parent tx address ≠ emptyHash)
    (storageParent : ReferenceStorageView.Parent) (slot : ByteArray) :
    ReferenceStorageView.current storageParent (enter emptyHash parent tx sender recipient value shouldTransfer).2.storage address slot =
      ReferenceStorageView.current storageParent tx.storage address slot := by
  unfold enter
  split
  · exact move_protected_storage emptyHash parent tx sender recipient address value nonempty storageParent slot
  · rfl


private theorem modify_code {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (address : AccountAddress) (balance : UInt256) :
    (modifyBalance emptyHash parent tx address balance).codeWrites = tx.codeWrites := by
  unfold modifyBalance
  dsimp only
  split <;> rfl

theorem enter_code {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender recipient : AccountAddress) (value : UInt256) (shouldTransfer : Bool) :
    (enter emptyHash parent tx sender recipient value shouldTransfer).2.codeWrites = tx.codeWrites := by
  unfold enter
  split
  · unfold move
    dsimp only
    split
    · split
      · dsimp only
        rw [modify_code]
        exact modify_code emptyHash parent _ sender _
      · exact modify_code emptyHash parent _ sender _
    · rfl
  · rfl

private theorem modify_reads {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (key address : AccountAddress) (balance : UInt256)
    (read : address ∈ tx.accounts.reads) :
    address ∈ (modifyBalance emptyHash parent tx key balance).accounts.reads := by
  unfold modifyBalance
  dsimp only
  split <;> exact Set.mem_insert_of_mem _ read

theorem enter_reads {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender recipient address : AccountAddress) (value : UInt256) (shouldTransfer : Bool)
    (read : address ∈ tx.accounts.reads) :
    address ∈ (enter emptyHash parent tx sender recipient value shouldTransfer).2.accounts.reads := by
  unfold enter
  split
  · unfold move
    dsimp only
    split
    · split
      · apply modify_reads
        apply Set.mem_insert_of_mem
        apply modify_reads
        exact Set.mem_insert_of_mem _ read
      · apply Set.mem_insert_of_mem
        apply modify_reads
        exact Set.mem_insert_of_mem _ read
    · exact Set.mem_insert_of_mem _ read
  · exact read

private theorem load_hash {Hash LoadError : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (address : AccountAddress) :
    (ReferenceCodeAccountPresence.load Account.codeHash emptyHash parent tx.accounts codeParent tx.codeWrites address).1 =
      ReferenceCodeAccountPresence.getCode emptyHash codeParent tx.codeWrites (hashAt emptyHash parent tx address) := by
  unfold ReferenceCodeAccountPresence.load hashAt account
  cases ReferenceAccountLookup.peek parent tx.accounts address <;> rfl

theorem loaded_nonempty_hash {Hash LoadError : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (address : AccountAddress) {code : ByteArray}
    (loaded : (ReferenceCodeAccountPresence.load Account.codeHash emptyHash parent tx.accounts codeParent tx.codeWrites address).1 = .ok code)
    (nonempty : code ≠ ByteArray.empty) : hashAt emptyHash parent tx address ≠ emptyHash := by
  intro same
  rw [load_hash, same] at loaded
  simp only [ReferenceCodeAccountPresence.getCode,if_true] at loaded
  exact nonempty (Except.ok.inj loaded).symm

theorem enter_load {Hash LoadError : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError)
    (sender recipient address : AccountAddress) (value : UInt256) (shouldTransfer : Bool) :
    (ReferenceCodeAccountPresence.load Account.codeHash emptyHash parent
      (enter emptyHash parent tx sender recipient value shouldTransfer).2.accounts codeParent
      (enter emptyHash parent tx sender recipient value shouldTransfer).2.codeWrites address).1 =
    (ReferenceCodeAccountPresence.load Account.codeHash emptyHash parent tx.accounts codeParent tx.codeWrites address).1 := by
  rw [load_hash,load_hash,enter_hash,enter_code]

/-- Source code fetch occurred before transfer. Its read survives; re-observing
code for the existing failure consumer adds no account-read metadata. -/
theorem enter_loaded_reads {Hash LoadError : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError)
    (sender recipient address : AccountAddress) (value : UInt256) (shouldTransfer : Bool)
    (read : address ∈ tx.accounts.reads) :
    (ReferenceCodeAccountPresence.load Account.codeHash emptyHash parent
      (enter emptyHash parent tx sender recipient value shouldTransfer).2.accounts codeParent
      (enter emptyHash parent tx sender recipient value shouldTransfer).2.codeWrites address).2 =
    (enter emptyHash parent tx sender recipient value shouldTransfer).2.accounts := by
  have mem := enter_reads emptyHash parent tx sender recipient address value shouldTransfer read
  change ReferenceAccountLookup.tracked _ address = _
  unfold ReferenceAccountLookup.tracked
  rw [Set.insert_eq_of_mem mem]

#print axioms enter_code
#print axioms enter_reads
#print axioms loaded_nonempty_hash
#print axioms enter_load
#print axioms enter_loaded_reads

#print axioms move_protected_storage
#print axioms enter_hash
#print axioms enter_protected_storage
#print axioms modify_hash
#print axioms modify_protected_storage
#print axioms move_hash
end Eip8282.Audit.Integrator.ReferenceSourceValueTransfer
