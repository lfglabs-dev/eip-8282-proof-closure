import Eip8282.Audit.Integrator.ReferenceSystemBlockSettlement
import Eip8282.Audit.Integrator.SystemFrame

/-! Global storage correspondence after an actual SYSTEM receipt merge.
Typed reads at every address match the same complete replay's world, not only
the owner projection. Replay gas remains synthetic, and this is not equality
of source account payloads, dictionaries or canonical protocol histories. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemBlockWorld
open EvmYul EvmYul.EVM ReferenceCheckedSystemEntry
open ReferenceCheckedSystemPair ReferenceStorageView ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def Reads (parent : Parent) (world : AccountMap .EVM) : Prop :=
  ∀ a key, parentRead parent a key.toByteArray = SystemSpec.worldSlot world a key

theorem initial (c : Context) : Reads (storageParent c) c.world := by
  intro a key
  change SystemSpec.worldSlot c.world a (ProtocolSystemDispatchExtraction.keyOf key.toByteArray) = _
  rw [ProtocolSystemDispatchExtraction.keyOf_toByteArray]

/-- The owner's relation comes from the same checked terminal. Other
addresses use both the actual runtime frame and the derived source footprint. -/
theorem committed {Hash Error : Type} [DecidableEq Hash] {kind : ReachableCalls.Contract}
    {c : Context} {emptyHash : Hash} {accountsParent : ReferenceSourceValueTransfer.Parent Hash}
    {codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error} {parent : Parent}
    (cert : Certificate kind c emptyHash accountsParent codeParent parent)
    (beforeReads : Reads parent c.world) :
    ∃ extra post,
      ReferenceCheckedCompletion.Observations parent cert.ended.view post ∧
      (ReferenceCheckedTheta.replay (call kind c) cert.events extra).result =
        .ok (post.createdAccounts,post.accountMap,post.gasAvailable,post.substate,true,cert.ended.output) ∧
      NestedProtectedJournal.Observed kind (ReferenceCheckedTheta.replay (call kind c) cert.events extra)
        post.createdAccounts post.accountMap post.substate true cert.ended.output ∧
      Reads (commit parent cert.receipt.storage) post.accountMap := by
  obtain ⟨extra,post,observed,result,claims⟩ := cert.claims
  have frame := (SystemFrame.system_frame (JournalInvariant.modelKind kind)
    (ReferenceCheckedTheta.replay (call kind c) cert.events extra) (code kind c) rfl result).2
  refine ⟨extra,post,observed,result,claims,?_⟩
  intro a key
  by_cases owner : a = ReachableCalls.address kind
  · subst a
    rw [commit_read,cert.receiptFields.2.1]
    have slots := observed.storage key
    change current parent cert.ended.view.storage post.executionEnv.codeOwner key.toByteArray = _ at slots
    have ownerEq : post.executionEnv.codeOwner = ReachableCalls.address kind := by
      rw [←observed.env,cert.owner]
    rw [ownerEq] at slots
    rw [←SystemSpec.worldSlot_state] at slots
    simpa only [ownerEq] using slots
  · rw [ReferenceSystemBlockFootprint.foreign_commit cert.support parent a owner key.toByteArray,beforeReads]
    have foreign := frame a owner
    have storage := congrArg (fun found : Option (Account .EVM) =>
      (found.map (fun account => account.lookupStorage key)).getD ⟨0⟩) foreign
    change SystemSpec.worldSlot post.accountMap a key =
      SystemSpec.worldSlot (ReferenceCheckedTheta.replay (call kind c) cert.events extra).entryWorld a key at storage
    rw [TransferFrame.entry_storage] at storage
    exact storage.symm

/-- Rebuild the three predicates over the actual intermediate replay world.
Only a meaningful initial invariant and storage relation are inputs here;
the ordered consumer derives both from its first complete receipt. -/
theorem rebase {Hash Error : Type} [DecidableEq Hash] {kind : ReachableCalls.Contract}
    {c : Context} {emptyHash : Hash} {accountsParent : ReferenceSourceValueTransfer.Parent Hash}
    {codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error} {parent : Parent}
    (cert : Certificate kind c emptyHash accountsParent codeParent parent)
    (world : AccountMap .EVM) (reads : Reads parent world) {budget : Nat}
    (invariant : JournalInvariant.Invariant kind budget world) (bound : budget < 2^128)
    (context : ReferenceCheckedStackControlStep.DestinationContext (JournalInvariant.modelKind kind)
      (ReferenceInitialAccess.destinations (call kind c).code))
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    Nonempty (Certificate kind {c with world := world} emptyHash accountsParent codeParent parent) := by
  let next := {c with world := world}
  have input : ReachableCalls.PinnedCall kind (call kind next) := ⟨rfl,rfl,invariant.1,rfl⟩
  have slots : ReferenceStorageView.Related parent
      (entered kind next emptyHash accountsParent codeParent).2.storage (xi kind next).entry.toState := by
    rw [(ready kind next emptyHash accountsParent codeParent loaded).2]
    intro key
    change parentRead parent (ReachableCalls.address kind) key.toByteArray = _
    rw [reads]
    exact (TransferFrame.codeCall_storage (call kind next) (code kind next) 0 key).symm
  have warm : ReferenceSourceReadings.WarmRelated (∅ : ReferenceSourceReadings.Warm) (xi kind next).entry := by
    intro a key
    change (a,key.toByteArray) ∈ (∅ : ReferenceSourceReadings.Warm) ↔
      (∅ : Std.TreeSet _ _).contains (a,key) = true
    simp
  have actual : runOn kind next emptyHash accountsParent codeParent parent =
      some ((cert.events,.terminal cert.ended),cert.finalAccounts) := cert.actual
  have erased := (ReferenceCheckedAccountEvaluator.evaluated context actual (by simp [ReferenceRuntimeView.initial])
    (ReferenceActionMemoryBounds.empty_aligned _ rfl)).1
  have complete := ReferenceCheckedTheta.terminal input context erased slots warm
    (by change 30000000 ≤ 30000000; rfl) invariant bound (by change 0 < UInt256.size; decide)
  have claims : ReferenceCheckedTheta.Completed kind (call kind next) parent cert.events cert.ended.view true cert.ended.output := by
    simpa only [cert.halt,ne_eq,reduceCtorEq,not_false_eq_true,decide_true] using complete
  exact ⟨{cert with actual := actual,claims := claims}⟩

#print axioms initial
#print axioms committed
#print axioms rebase
end Eip8282.Audit.Integrator.ReferenceSystemBlockWorld
