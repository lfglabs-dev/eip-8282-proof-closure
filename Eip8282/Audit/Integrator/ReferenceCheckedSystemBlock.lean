import Eip8282.Audit.Integrator.ReferenceSystemBlockWorld

/-! Composed mandatory SYSTEM block pair on checked executions and complete
local journals. Deposit's actual merge produces Exit's storage parent and the
same intermediate replay world used by all three predicates. Both global
storage relations and journal invariants are derived. Replay resources only
prove effects/invariant preservation; actual gas remains in each certificate.
Canonical History production, source/Python representation, final BAL limit,
fork adoption and account/code payload correspondence remain external scope.
-/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemBlock
open EvmYul EvmYul.EVM ReferenceCheckedSystemEntry
open ReferenceCheckedSystemPair ReferenceSystemBlockWorld
open ReferenceSystemBlockSettlement
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

theorem verified {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (c : Context) (history : ReleaseCandidate.History deposit exit c.world)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (builder : ReferenceSystemBlockAccess.Builder)
    (accountReads : Set AccountAddress) (storageReads : Set (AccountAddress × ByteArray))
    (loaded : ∀ kind, (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    ∃ dep : Certificate .deposit c emptyHash accountsParent codeParent (storageParent c),
    ∃ (depExtra : Nat) (depPost : EVM.State),
    ∃ ext : Certificate .exit {c with world := depPost.accountMap} emptyHash accountsParent codeParent
        (ReferenceStorageView.commit (storageParent c) dep.receipt.storage),
    ∃ (extExtra : Nat) (extPost : EVM.State),
      (ReferenceCheckedTheta.replay (call .deposit c) dep.events depExtra).result =
        .ok (depPost.createdAccounts,depPost.accountMap,depPost.gasAvailable,depPost.substate,true,dep.ended.output) ∧
      (ReferenceCheckedTheta.replay (call .exit {c with world := depPost.accountMap}) ext.events extExtra).result =
        .ok (extPost.createdAccounts,extPost.accountMap,extPost.gasAvailable,extPost.substate,true,ext.ended.output) ∧
      NestedProtectedJournal.Observed .deposit (ReferenceCheckedTheta.replay (call .deposit c) dep.events depExtra)
        depPost.createdAccounts depPost.accountMap depPost.substate true dep.ended.output ∧
      NestedProtectedJournal.Observed .exit (ReferenceCheckedTheta.replay (call .exit {c with world := depPost.accountMap}) ext.events extExtra)
        extPost.createdAccounts extPost.accountMap extPost.substate true ext.ended.output ∧
      (∀ kind, JournalInvariant.Invariant kind (ActualJournalHistory.work history.receipts) depPost.accountMap) ∧
      (∀ kind, JournalInvariant.Invariant kind (ActualJournalHistory.work history.receipts) extPost.accountMap) ∧
      let block : Block Hash Error := ⟨accountsParent,codeParent,storageParent c,accountReads,storageReads,builder⟩
      ∃ middle final,
        incorporate block (ReachableCalls.address .deposit) (settled dep) dep.keys (no_account_changes dep) =
          some (middle,before Hash) ∧
        Reads middle.storage depPost.accountMap ∧
        runOn .exit {c with world := depPost.accountMap} emptyHash middle.accounts middle.code middle.storage =
          some ((ext.events,.terminal ext.ended),ext.finalAccounts) ∧
        incorporate middle (ReachableCalls.address .exit) (settled ext) ext.keys (no_account_changes ext) =
          some (final,before Hash) ∧
        Reads final.storage extPost.accountMap ∧
        final.accounts = accountsParent ∧ final.code = codeParent ∧
        final.builder.index = builder.index ∧
        final.accountReads = (accountReads ∪ dep.finalAccounts.reads) ∪ ext.finalAccounts.reads ∧
        final.storageReads = (storageReads ∪ dep.receipt.storage.reads) ∪ ext.receipt.storage.reads := by
  have initialInv := (ReleaseCandidate.invariants history).2.2.2
  have bound := (ReleaseCandidate.invariants history).2.2.1
  obtain ⟨pair⟩ := ReferenceCheckedSystemPair.verified c history emptyHash accountsParent codeParent builder loaded
  obtain ⟨depExtra,depPost,_,depResult,depClaims,depReads⟩ := committed pair.deposit (ReferenceSystemBlockWorld.initial c)
  let depTransition : ReachableCalls.Transition .deposit c.world depPost.accountMap :=
    { call := ReferenceCheckedTheta.replay (call .deposit c) pair.deposit.events depExtra
      pinned := ⟨rfl,rfl,(initialInv .deposit).1,rfl⟩
      pre := rfl, created := depPost.createdAccounts,gas := depPost.gasAvailable
      substate := depPost.substate,success := true,output := pair.deposit.ended.output,executed := depResult }
  have middleInv : ∀ kind, JournalInvariant.Invariant kind (ActualJournalHistory.work history.receipts) depPost.accountMap :=
    fun kind => SystemJournal.preserves depTransition rfl rfl (by change 0 < UInt256.size; decide) bound (initialInv kind)
  obtain ⟨ext⟩ := rebase pair.exit depPost.accountMap depReads (middleInv .exit) bound
    (bindings .exit c history emptyHash accountsParent codeParent (loaded .exit)).2.2.2 (loaded .exit)
  obtain ⟨extExtra,extPost,_,extResult,extClaims,extReads⟩ := committed ext depReads
  let extTransition : ReachableCalls.Transition .exit depPost.accountMap extPost.accountMap :=
    { call := ReferenceCheckedTheta.replay (call .exit {c with world := depPost.accountMap}) ext.events extExtra
      pinned := ⟨rfl,rfl,(middleInv .exit).1,rfl⟩
      pre := rfl, created := extPost.createdAccounts,gas := extPost.gasAvailable
      substate := extPost.substate,success := true,output := ext.ended.output,executed := extResult }
  have finalInv : ∀ kind, JournalInvariant.Invariant kind (ActualJournalHistory.work history.receipts) extPost.accountMap :=
    fun kind => SystemJournal.preserves extTransition rfl rfl (by change 0 < UInt256.size; decide) bound (middleInv kind)
  obtain ⟨middle,final,first,_,_,middleStorage,actualExit,second,accounts,code,index,finalStorage,accountReadsEq,storageReadsEq⟩ :=
    two pair.deposit depPost.accountMap ext accountReads storageReads
  exact ⟨pair.deposit,depExtra,depPost,ext,extExtra,extPost,depResult,extResult,depClaims,extClaims,middleInv,finalInv,
    middle,final,first,by rw [middleStorage]; exact depReads,actualExit,second,
    by rw [finalStorage]; exact extReads,accounts,code,index,accountReadsEq,storageReadsEq⟩

#print axioms verified
end Eip8282.Audit.Integrator.ReferenceCheckedSystemBlock
