import Eip8282.Audit.Integrator.ReferenceCodeAccountPresence
import Eip8282.Audit.Integrator.ReferenceCheckedAccountEvaluator

/-! Derive absence of the source owner assertion from the actual nonempty
code read, then transport it through the same computed protected evaluation.
This only excludes the owner assertion. Conversion faults and full source
exception settlement have separate obligations. Code fetch address equals the
storage owner here; delegated/CALLCODE ownership is not silently identified.
-/
namespace Eip8282.Audit.Integrator.ReferenceAccountFaults
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem store_after_no_owner {parent : ReferenceStorageView.Parent} {v : View}
    {warm finalWarm : Warm} {meter final : Meter} {key value : UInt256} {rest : List UInt256} {next : View} :
    ReferenceCheckedStorageStep.storeAfterPop true parent v warm meter key value rest ≠
      .error (.missingOwnerAssertion,next,finalWarm,final) := by
  intro actual
  unfold ReferenceCheckedStorageStep.storeAfterPop at actual
  dsimp only at actual
  simp only [if_true] at actual
  repeat' first | split at actual | cases actual

private theorem store_no_owner {parent : ReferenceStorageView.Parent} {v next : View}
    {warm finalWarm : Warm} {meter final : Meter} :
    ReferenceCheckedStorageStep.store true parent v warm meter ≠
      .error (.missingOwnerAssertion,next,finalWarm,final) := by
  intro actual
  unfold ReferenceCheckedStorageStep.store at actual
  repeat' first | split at actual | cases actual
  exact store_after_no_owner actual

private theorem load_no_owner {parent : ReferenceStorageView.Parent} {v next : View}
    {warm finalWarm : Warm} {meter final : Meter} :
    ReferenceCheckedStorageStep.load parent v warm meter ≠
      .error (.missingOwnerAssertion,next,finalWarm,final) := by
  intro actual
  unfold ReferenceCheckedStorageStep.load at actual
  dsimp only at actual
  repeat' first | split at actual | cases actual

private theorem handler_no_owner {handler : Handler} {destinations : List Nat}
    {parent : ReferenceStorageView.Parent} {v next : View} {warm finalWarm : Warm}
    {meter final : Meter} {output finalOutput : ByteArray} :
    runHandler handler destinations true parent v warm meter output ≠
      .failed (.storage .missingOwnerAssertion) next finalWarm final finalOutput := by
  intro actual
  cases handler <;> simp only [runHandler] at actual
  all_goals repeat' first | split at actual | cases actual
  all_goals first
    | exact load_no_owner (by assumption)
    | exact store_no_owner (by assumption)

/-- Every final dispatcher with a present owner avoids this assertion,
regardless of earlier charges, successful storage effects or any other fault. -/
theorem dispatch_no_owner {destinations : List Nat} {parent : ReferenceStorageView.Parent}
    {v next : View} {warm finalWarm : Warm} {meter final : Meter} {output finalOutput : ByteArray} :
    ReferenceCheckedDispatch.run destinations true parent v warm meter output ≠
      .failed (.storage .missingOwnerAssertion) next finalWarm final finalOutput := by
  intro actual
  unfold ReferenceCheckedDispatch.run at actual
  cases selected : read v.env.code v.pc <;> simp only [selected] at actual
  all_goals first | (solve | cases actual) | exact handler_no_owner actual

/-- A complete same-run trace yields its final dispatcher, so no separately
selected prefix or terminal state can smuggle in a missing-owner assertion. -/
theorem evaluated_no_owner {kind : Kind} {destinations : List Nat}
    {parent : ReferenceStorageView.Parent} {v next : View} {warm finalWarm : Warm}
    {meter final : Meter} {output finalOutput : ByteArray} {fuel : Nat} {events : List Event}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations) :
    ReferenceCheckedEvaluator.eval destinations true parent output fuel v warm meter ≠
      some (events,.failed (.storage .missingOwnerAssertion) next finalWarm final finalOutput) := by
  intro actual
  obtain ⟨_,_,_,_,last,_⟩ := ReferenceCheckedEvaluator.extract context actual
  exact dispatch_no_owner last

/-- Presence is derived from a completed nonempty source code fetch at the
same owner, not assumed as a desired assertion-free postcondition. -/
theorem code_fetch_no_owner {Account Hash Error : Type} [DecidableEq Hash]
    (codeHash : Account → Hash) (emptyHash : Hash)
    (accountsParent : ReferenceAccountLookup.Parent Account) (accounts : ReferenceAccountLookup.Tx Account)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (codeWrites : Hash → Option ByteArray)
    {kind : Kind} {destinations : List Nat} {parent : ReferenceStorageView.Parent}
    {v next : View} {warm finalWarm : Warm} {meter final : Meter} {output finalOutput : ByteArray}
    {fuel : Nat} {events : List Event} {finalAccounts : ReferenceAccountLookup.Tx Account}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (loaded : (ReferenceCodeAccountPresence.load codeHash emptyHash accountsParent accounts codeParent codeWrites
      v.env.codeOwner).1 = .ok v.env.code)
    (nonempty : v.env.code ≠ ByteArray.empty)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v) :
    ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent output fuel
      (ReferenceCodeAccountPresence.load codeHash emptyHash accountsParent accounts codeParent codeWrites v.env.codeOwner).2
      v warm meter ≠
      some ((events,.failed (.storage .missingOwnerAssertion) next finalWarm final finalOutput),finalAccounts) := by
  intro actual
  obtain ⟨account,present⟩ := ReferenceCodeAccountPresence.nonempty_present codeHash emptyHash
    accountsParent accounts codeParent codeWrites v.env.codeOwner loaded nonempty
  obtain ⟨checked,_⟩ := ReferenceCheckedAccountEvaluator.evaluated context actual stack aligned
  simp only [ReferenceCodeAccountPresence.load,ReferenceAccountLookup.tracked_peek,present] at checked
  exact evaluated_no_owner context checked

#print axioms dispatch_no_owner
#print axioms evaluated_no_owner
#print axioms code_fetch_no_owner
end Eip8282.Audit.Integrator.ReferenceAccountFaults
