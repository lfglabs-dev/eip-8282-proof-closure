import Eip8282.Audit.Integrator.ReferenceCheckedSystemPair

/-! Source block incorporation for the derived empty-account-write SYSTEM
case, state_tracker.py796-822 at the archived EL pin. BAL update precedes
merge; cumulative reads are retained; all transaction journals are cleared.
Account/code parents remain unchanged because their actual write overlays
are empty, not because a SYSTEM label is assumed to imply that fact.
This is a successful functional projection, not a Python exception-state
semantics, a final BAL validation, or canonical Ethereum reachability. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemBlockSettlement
open EvmYul EvmYul.EVM ReferenceCheckedSystemEntry
open ReferenceCheckedSystemPair ReferenceSystemBlockAccess
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

structure Block (Hash Error : Type) where
  accounts : ReferenceSourceValueTransfer.Parent Hash
  code : ReferenceCodeAccountPresence.CodeParent Hash Error
  storage : ReferenceStorageView.Parent
  accountReads : Set AccountAddress
  storageReads : Set (AccountAddress × ByteArray)
  builder : Builder

structure NoAccountChanges {Hash : Type} (tx : ReferenceSourceValueTransfer.Tx Hash) : Prop where
  accounts : tx.accounts.writes = fun _ => none
  code : tx.codeWrites = fun _ => none

def merged {Hash Error : Type} (block : Block Hash Error) (tx : ReferenceSourceValueTransfer.Tx Hash)
    (builder : Builder) : Block Hash Error :=
  { block with
    storage := ReferenceStorageView.commit block.storage tx.storage
    accountReads := block.accountReads ∪ tx.accounts.reads
    storageReads := block.storageReads ∪ tx.storage.reads
    builder := builder }

/-- The proof argument identifies the source branch with empty account/code
write dictionaries. The public consumer derives it from the actual journal.
Only successful BAL completion can return the merged block and fresh journal. -/
noncomputable def incorporate {Hash Error : Type} (block : Block Hash Error)
    (owner : AccountAddress) (tx : ReferenceSourceValueTransfer.Tx Hash) (keys : List UInt256)
    (_scope : NoAccountChanges tx) : Option (Block Hash Error × ReferenceSourceValueTransfer.Tx Hash) :=
  (update block.storage owner (entries owner tx.storage keys) block.builder).map
    (fun builder => (merged block tx builder,before Hash))

noncomputable def settled {Hash Error : Type} [DecidableEq Hash] {kind : ReachableCalls.Contract}
    {c : Context} {emptyHash : Hash} {accountsParent : ReferenceSourceValueTransfer.Parent Hash}
    {codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error} {parent : ReferenceStorageView.Parent}
    (cert : Certificate kind c emptyHash accountsParent codeParent parent) : ReferenceSourceValueTransfer.Tx Hash :=
  ReferenceSettledAccountJournal.journal (before Hash)
    (entered kind c emptyHash accountsParent codeParent).2 cert.finalAccounts cert.receipt

theorem no_account_changes {Hash Error : Type} [DecidableEq Hash] {kind : ReachableCalls.Contract}
    {c : Context} {emptyHash : Hash} {accountsParent : ReferenceSourceValueTransfer.Parent Hash}
    {codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error} {parent : ReferenceStorageView.Parent}
    (cert : Certificate kind c emptyHash accountsParent codeParent parent) : NoAccountChanges (settled cert) :=
  ⟨cert.journal.1,cert.journal.2.2.1⟩

theorem incorporate_certificate {Hash Error : Type} [DecidableEq Hash] {kind : ReachableCalls.Contract}
    {c : Context} {emptyHash : Hash} {accountsParent : ReferenceSourceValueTransfer.Parent Hash}
    {codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error} {parent : ReferenceStorageView.Parent}
    (cert : Certificate kind c emptyHash accountsParent codeParent parent) (block : Block Hash Error) :
    ∃ builder, incorporate block (ReachableCalls.address kind) (settled cert) cert.keys (no_account_changes cert) =
      some (merged block (settled cert) builder,before Hash) ∧ builder.index = block.builder.index := by
  obtain ⟨builder,updated⟩ := update_total (parent := block.storage) (owner := ReachableCalls.address kind)
    (entries_typed (ReachableCalls.address kind) (settled cert).storage cert.keys) block.builder
  exact ⟨builder,by simp only [incorporate,updated,Option.map_some],update_index updated⟩

/-- This is the same storage dictionary as the actual receipt, and its
enumeration includes every write. It does not enumerate executed appends. -/
theorem complete_dictionary {Hash Error : Type} [DecidableEq Hash] {kind : ReachableCalls.Contract}
    {c : Context} {emptyHash : Hash} {accountsParent : ReferenceSourceValueTransfer.Parent Hash}
    {codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error} {parent : ReferenceStorageView.Parent}
    (cert : Certificate kind c emptyHash accountsParent codeParent parent) :
    (settled cert).storage = cert.receipt.storage ∧
    ((entries (ReachableCalls.address kind) (settled cert).storage cert.keys).map Prod.fst).Nodup ∧
    (∀ pair ∈ entries (ReachableCalls.address kind) (settled cert).storage cert.keys,
      (settled cert).storage.writes (ReachableCalls.address kind) pair.1 = some pair.2) ∧
    ∀ a key value, (settled cert).storage.writes a key = some value →
      a = ReachableCalls.address kind ∧
        (key,value) ∈ entries (ReachableCalls.address kind) (settled cert).storage cert.keys := by
  have storage := cert.journal.2.2.2.2.1
  change (settled cert).storage = cert.receipt.storage at storage
  refine ⟨storage,entries_unique _ _ _,entries_sound _ _ _,?_⟩
  rw [storage]
  exact entries_complete cert.support

/-- Both source block merges and fresh-journal resets are produced. Exit's
actual evaluator receives the first merged storage parent; its account/code
parents are precisely those preserved by that first empty-write merge. -/
theorem two {Hash Error : Type} [DecidableEq Hash]
    {c : Context} {emptyHash : Hash} {accountsParent : ReferenceSourceValueTransfer.Parent Hash}
    {codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error} {builder : Builder}
    (dep : Certificate .deposit c emptyHash accountsParent codeParent (storageParent c))
    (world : AccountMap .EVM)
    (ext : Certificate .exit {c with world := world} emptyHash accountsParent codeParent
      (ReferenceStorageView.commit (storageParent c) dep.receipt.storage))
    (accountReads : Set AccountAddress) (storageReads : Set (AccountAddress × ByteArray)) :
    let block : Block Hash Error := ⟨accountsParent,codeParent,storageParent c,accountReads,storageReads,builder⟩
    ∃ middle final,
      incorporate block (ReachableCalls.address .deposit) (settled dep) dep.keys
        (no_account_changes dep) = some (middle,before Hash) ∧
      middle.accounts = accountsParent ∧ middle.code = codeParent ∧
      middle.storage = ReferenceStorageView.commit (storageParent c) dep.receipt.storage ∧
      runOn .exit {c with world := world} emptyHash middle.accounts middle.code middle.storage =
        some ((ext.events,.terminal ext.ended),ext.finalAccounts) ∧
      incorporate middle (ReachableCalls.address .exit) (settled ext) ext.keys
        (no_account_changes ext) = some (final,before Hash) ∧
      final.accounts = accountsParent ∧ final.code = codeParent ∧
      final.builder.index = builder.index ∧
      final.storage = ReferenceStorageView.commit
        (ReferenceStorageView.commit (storageParent c) dep.receipt.storage) ext.receipt.storage ∧
      final.accountReads = (accountReads ∪ dep.finalAccounts.reads) ∪ ext.finalAccounts.reads ∧
      final.storageReads = (storageReads ∪ dep.receipt.storage.reads) ∪ ext.receipt.storage.reads := by
  dsimp only
  let block : Block Hash Error := ⟨accountsParent,codeParent,storageParent c,accountReads,storageReads,builder⟩
  obtain ⟨middleBuilder,first,middleIndex⟩ := incorporate_certificate dep block
  let middle := merged block (settled dep) middleBuilder
  obtain ⟨finalBuilder,second,finalIndex⟩ := incorporate_certificate ext middle
  let final := merged middle (settled ext) finalBuilder
  have depStorage := (complete_dictionary dep).1
  have extStorage := (complete_dictionary ext).1
  have depReads := dep.journal.2.1
  have extReads := ext.journal.2.1
  change (settled dep).accounts.reads = dep.finalAccounts.reads at depReads
  change (settled ext).accounts.reads = ext.finalAccounts.reads at extReads
  refine ⟨middle,final,first,rfl,rfl,?_,?_,second,rfl,rfl,finalIndex.trans middleIndex,?_,?_,?_⟩
  · change ReferenceStorageView.commit _ (settled dep).storage = _
    rw [depStorage]
  · simpa only [middle,merged,block,depStorage] using ext.actual
  · change ReferenceStorageView.commit (ReferenceStorageView.commit _ (settled dep).storage)
      (settled ext).storage = _
    rw [depStorage,extStorage]
  · change (accountReads ∪ (settled dep).accounts.reads) ∪ (settled ext).accounts.reads = _
    rw [depReads,extReads]
  · change (storageReads ∪ (settled dep).storage.reads) ∪ (settled ext).storage.reads = _
    rw [depStorage,extStorage]

#print axioms no_account_changes
#print axioms incorporate_certificate
#print axioms complete_dictionary
#print axioms two
end Eip8282.Audit.Integrator.ReferenceSystemBlockSettlement
