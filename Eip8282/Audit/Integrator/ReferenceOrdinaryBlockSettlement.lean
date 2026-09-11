import Eip8282.Audit.Integrator.ReferenceFullFeeBlockReceipt

/-! Incorporation consumes the actual ordinary fee-finalized dictionary.
Account BAL updates precede storage BAL updates; both use unmerged parents.
Only then are writes and reads merged and a fresh transaction journal returned.
No final dictionary support, nonce conversion or successful BAL premise is
supplied to the certificate consumer. Complete Python containers/serialization,
final block BAL size and canonical admission remain external boundaries. -/
namespace Eip8282.Audit.Integrator.ReferenceOrdinaryBlockSettlement
open EvmYul EvmYul.EVM ReferenceSourceValueTransfer
open ReferenceOrdinaryBlockAccess ReferenceFullFeeBlockReceipt
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

structure Block (Hash Error : Type) where
  accounts : Parent Hash
  code : ReferenceCodeAccountPresence.CodeParent Hash Error
  storage : ReferenceStorageView.Parent
  accountReads : Set AccountAddress
  storageReads : Set (AccountAddress × ByteArray)
  builder : Builder

def commitAccounts {Hash : Type} (parent : Parent Hash) (tx : Tx Hash) : Parent Hash :=
  {parent with writes := fun a => (tx.accounts.writes a).orElse (fun _ => parent.writes a)}

def commitCode {Hash Error : Type} (parent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (tx : Tx Hash) : ReferenceCodeAccountPresence.CodeParent Hash Error :=
  {parent with writes := fun h => (tx.codeWrites h).orElse (fun _ => parent.writes h)}

def merged {Hash Error : Type} (block : Block Hash Error) (tx : Tx Hash) (builder : Builder) : Block Hash Error :=
  {accounts := commitAccounts block.accounts tx,code := commitCode block.code tx,
    storage := ReferenceStorageView.commit block.storage tx.storage,
    accountReads := block.accountReads ∪ tx.accounts.reads,
    storageReads := block.storageReads ∪ tx.storage.reads,builder := builder}

noncomputable def incorporate {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash)
    (block : Block Hash Error) (owner : AccountAddress) (tx : Tx Hash)
    (addresses : List AccountAddress) (keys : List UInt256) : Option (Block Hash Error × Tx Hash) :=
  (ReferenceOrdinaryBlockAccess.update emptyHash block.accounts block.code tx.codeWrites
    (ReferenceOrdinaryBlockAccess.entries tx.accounts addresses) block.builder).bind fun accounts =>
    (ReferenceSystemBlockAccess.update block.storage owner
      (ReferenceSystemBlockAccess.entries owner tx.storage keys) accounts.storage).map fun storage =>
        (merged block tx {accounts with storage := storage},ReferenceCheckedSystemEntry.before Hash)

theorem commit_read {Hash : Type} (emptyHash : Hash) (parent : Parent Hash) (tx : Tx Hash) (a : AccountAddress) :
    ((ReferenceAccountLookup.parentRead (commitAccounts parent tx) a).getD (empty emptyHash)) = account emptyHash parent tx a := by
  cases h : tx.accounts.writes a <;> simp [commitAccounts,ReferenceAccountLookup.parentRead,account,ReferenceAccountLookup.peek,h]

noncomputable def settled {Hash Error : Type} [DecidableEq Hash] {kind : ReachableCalls.Contract}
    {tx : RefundAccounting.Context} {signature : UInt256} {emptyHash : Hash} {accountsParent : Parent Hash}
    {before : Tx Hash} {codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error} {parent : ReferenceStorageView.Parent}
    (cert : Certificate kind tx signature emptyHash accountsParent before codeParent parent) :=
  journal kind tx emptyHash accountsParent before codeParent cert.finalAccounts cert.receipt

private theorem read_write {Hash : Type} {emptyHash : Hash} {parent : Parent Hash}
    {tx : Tx Hash} {a : AccountAddress} {value : Option (ReferenceSourceValueTransfer.Account Hash)}
    (written : tx.accounts.writes a = some value) : account emptyHash parent tx a = value.getD (empty emptyHash) := by
  simp only [account,ReferenceAccountLookup.peek,written,Option.getD_some]

/-- Every actual changed nonce is either unchanged from the parent (no U64
conversion) or the derived admitted sender increment. No global nonce cap is
assumed for untouched accounts or for unchanged arbitrary parent nonces. -/
theorem entries_valid {Hash Error : Type} [DecidableEq Hash] {kind : ReachableCalls.Contract}
    {tx : RefundAccounting.Context} {signature : UInt256} {emptyHash : Hash} {accountsParent : Parent Hash}
    {before : Tx Hash} {codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error} {parent : ReferenceStorageView.Parent}
    (cert : Certificate kind tx signature emptyHash accountsParent before codeParent parent) :
    ∀ pair ∈ ReferenceOrdinaryBlockAccess.entries (settled cert).accounts (addresses kind tx),
      Valid emptyHash accountsParent pair := by
  intro pair member
  obtain ⟨a,value⟩ := pair
  have written := ReferenceOrdinaryBlockAccess.entries_sound (settled cert).accounts (addresses kind tx) (a,value) member
  have observed := read_write (emptyHash := emptyHash) (parent := accountsParent) written
  have initial : account emptyHash accountsParent before a =
      (ReferenceAccountLookup.parentRead accountsParent a).getD (empty emptyHash) := by
    simp only [account,ReferenceAccountLookup.peek,cert.beforeAccounts,Option.getD_none]
  have hash := cert.hashes a
  change (account emptyHash accountsParent (settled cert) a).codeHash = _ at hash
  rw [observed] at hash
  refine ⟨?_,hash.symm⟩
  by_cases sender : a = tx.sender
  · subst a
    right
    refine ⟨UInt64.ofNat (tx.transaction.base.nonce.toNat+1),?_⟩
    rw [← observed]
    exact cert.senderNonce
  · left
    have nonce := cert.nonces a
    change (account emptyHash accountsParent (settled cert) a).nonce = _ at nonce
    rw [observed,initial,if_neg sender,Nat.add_zero] at nonce
    exact nonce.symm

theorem entries_complete {Hash Error : Type} [DecidableEq Hash] {kind : ReachableCalls.Contract}
    {tx : RefundAccounting.Context} {signature : UInt256} {emptyHash : Hash} {accountsParent : Parent Hash}
    {before : Tx Hash} {codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error} {parent : ReferenceStorageView.Parent}
    (cert : Certificate kind tx signature emptyHash accountsParent before codeParent parent) :
    ∀ a value, (settled cert).accounts.writes a = some value →
      (a,value) ∈ ReferenceOrdinaryBlockAccess.entries (settled cert).accounts (addresses kind tx) := by
  intro a value written
  have present : a ∈ addresses kind tx := by
    by_contra outside
    have absent := cert.accountSupport a outside
    change (settled cert).accounts.writes a = none at absent
    rw [absent] at written
    contradiction
  refine List.mem_filterMap.mpr ⟨a,?_,?_⟩
  · simpa only [List.mem_dedup] using present
  · simp only [written,Option.map_some]

/-- Actual full account and storage write dictionaries are consumed exactly
once, after duplicate candidate addresses/keys are removed. Source dictionary
insertion-order representation remains a separate semantic binding. -/
theorem incorporated {Hash Error : Type} [DecidableEq Hash] {kind : ReachableCalls.Contract}
    {tx : RefundAccounting.Context} {signature : UInt256} {emptyHash : Hash} {before : Tx Hash}
    (block : Block Hash Error)
    (cert : Certificate kind tx signature emptyHash block.accounts before block.code block.storage) :
    ∃ builder,
      incorporate emptyHash block (ReachableCalls.address kind) (settled cert) (addresses kind tx) cert.keys =
        some (merged block (settled cert) builder,ReferenceCheckedSystemEntry.before Hash) ∧
      builder.storage.index = block.builder.storage.index := by
  obtain ⟨accountBuilder,first⟩ := ReferenceOrdinaryBlockAccess.update_total emptyHash block.accounts block.code
    (settled cert).codeWrites (entries_valid cert) block.builder
  obtain ⟨storageBuilder,second⟩ := ReferenceSystemBlockAccess.update_total (parent := block.storage) (owner := ReachableCalls.address kind)
    (ReferenceSystemBlockAccess.entries_typed (ReachableCalls.address kind) (settled cert).storage cert.keys) accountBuilder.storage
  refine ⟨{accountBuilder with storage := storageBuilder},?_,?_⟩
  · simp only [incorporate,first,Option.bind_some,second,Option.map_some]
  · exact (ReferenceSystemBlockAccess.update_index second).trans (ReferenceOrdinaryBlockAccess.update_index first)

#print axioms commit_read
#print axioms entries_valid
#print axioms entries_complete
#print axioms incorporated
end Eip8282.Audit.Integrator.ReferenceOrdinaryBlockSettlement
