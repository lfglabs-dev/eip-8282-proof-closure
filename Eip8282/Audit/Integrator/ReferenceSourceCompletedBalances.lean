import Eip8282.Audit.Integrator.ReferenceSourceBalanceOutcome
import Eip8282.Audit.Integrator.RuntimeBalancePreservation

/-! Same existential replay receipt, same three guarantees, and source-shaped
settled balance observations of that exact receipt world. This strengthens the
previous account-write result without presuming a post-world equality. Only
balances are related here; complete source frame/nonce/hash/gas and ancestor
composition remain separate obligations. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceCompletedBalances
open EvmYul EvmYul.EVM
open ReferenceSourceValueTransfer ReferenceSourceTransferFunding
open ReferenceTransferredFailure
open ReachableCalls (Contract)
open ReferenceRuntimeView ReferenceSourceReadings
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- Internal execution balance changes become visible only if this frame succeeds. -/
def settledTx {Hash : Type} (before live : Tx Hash) (success : Bool) : Tx Hash :=
  if success then live else restore live before

/-- The receipt witness, all three predicates and balance world are shared. -/
def Completed {Hash : Type} (emptyHash : Hash) (accountsParent : Parent Hash)
    (before live : Tx Hash) (kind : Contract) (c : MessageCall.Context)
    (parent : ReferenceStorageView.Parent) (events : List ReferenceMeterPath.Event)
    (view : View) (success : Bool) (output : ByteArray) : Prop :=
  ∃ extra post,
    ReferenceCheckedCompletion.Observations parent view post ∧
    let created := if success then post.createdAccounts else c.created
    let world := if success then post.accountMap else c.world
    let substate := if success then post.substate else c.substate
    (ReferenceCheckedTheta.replay c events extra).result = .ok (created,world,post.gasAvailable,substate,success,output) ∧
    NestedProtectedJournal.Observed kind (ReferenceCheckedTheta.replay c events extra) created world substate success output ∧
    BalancesRelated emptyHash accountsParent (settledTx before live success) world

/-- Runtime preservation is applied to the exact replay receipt already supplied
by the computed endpoint. Entry presence follows from installed pinned code. -/
theorem of_completed {Hash : Type} (emptyHash : Hash) (accountsParent : Parent Hash)
    (before live : Tx Hash) {kind : Contract} {c : MessageCall.Context}
    (pinned : ReachableCalls.PinnedCall kind c)
    {parent : ReferenceStorageView.Parent} {events : List ReferenceMeterPath.Event}
    {view : View} {success : Bool} {output : ByteArray}
    (actual : ReferenceCheckedTheta.Completed kind c parent events view success output)
    (balances : BalancesRelated emptyHash accountsParent before c.world)
    (internalBalances : BalancesRelated emptyHash accountsParent live c.entryWorld) :
    Completed emptyHash accountsParent before live kind c parent events view success output := by
  obtain ⟨extra,post,observed,receipt,guarantees⟩ := actual
  have code : c.code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by
    cases kind <;> exact pinned.code
  obtain ⟨old,installed,_⟩ := pinned.installed
  obtain ⟨current,entryPresent,_⟩ := TransferFrame.entry_existing_account c installed
  have preserved := RuntimeBalancePreservation.theta_balances (ReferenceCheckedTheta.replay c events extra)
    code ⟨current,entryPresent⟩ receipt
  refine ⟨extra,post,observed,receipt,guarantees,?_⟩
  intro address
  rw [preserved address]
  cases success with
  | false => exact ReferenceSourceBalanceOutcome.restored emptyHash accountsParent live before c.world balances address
  | true => exact internalBalances address

theorem original {Hash : Type} {emptyHash : Hash} {accountsParent : Parent Hash}
    {before live : Tx Hash} {kind : Contract} {c : MessageCall.Context}
    {parent : ReferenceStorageView.Parent} {events : List ReferenceMeterPath.Event}
    {view : View} {success : Bool} {output : ByteArray}
    (h : Completed emptyHash accountsParent before live kind c parent events view success output) :
    ReferenceCheckedTheta.Completed kind c parent events view success output := by
  obtain ⟨extra,post,observed,receipt,guarantees,_⟩ := h
  exact ⟨extra,post,observed,receipt,guarantees⟩

#print axioms of_completed
#print axioms original
end Eip8282.Audit.Integrator.ReferenceSourceCompletedBalances
