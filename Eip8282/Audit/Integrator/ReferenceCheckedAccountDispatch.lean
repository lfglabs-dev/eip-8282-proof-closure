import Eip8282.Audit.Integrator.ReferenceAccountLookup
import Eip8282.Audit.Integrator.ReferenceCheckedPrefix

/-! Bind the SSTORE assertion boolean to the literal optional-account lookup.
The pure peek is not a recorded source read: reads are added only when the
last, post-charge assertion is reached. No account payload/write changes in a
protected instruction. This supplies a concrete account-presence adapter for
checked dispatch; it does not establish deployment or a canonical account map.
-/
namespace Eip8282.Audit.Integrator.ReferenceCheckedAccountDispatch
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- SSTORE reads the optional owner only after all guards and gas charges.
A successful store or its missing-owner assertion reaches that read. -/
def assertionReached (selected : Dispatch) (outcome : Outcome) : Bool :=
  match selected,outcome with
  | .handler .store,.continued .. => true
  | .handler .store,.failed (.storage .missingOwnerAssertion) .. => true
  | _,_ => false

noncomputable def run {Account : Type} (accountsParent : ReferenceAccountLookup.Parent Account)
    (accounts : ReferenceAccountLookup.Tx Account) (destinations : List Nat)
    (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm) (meter : Meter)
    (output : ByteArray) : Outcome × ReferenceAccountLookup.Tx Account :=
  let result := ReferenceCheckedDispatch.run destinations
    (ReferenceAccountLookup.peek accountsParent accounts v.env.codeOwner).isSome parent v warm meter output
  (result,if assertionReached (read v.env.code v.pc) result
    then ReferenceAccountLookup.tracked accounts v.env.codeOwner else accounts)

theorem result {Account : Type} (accountsParent : ReferenceAccountLookup.Parent Account)
    (accounts : ReferenceAccountLookup.Tx Account) (destinations : List Nat)
    (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm) (meter : Meter) (output : ByteArray) :
    (run accountsParent accounts destinations parent v warm meter output).1 =
    ReferenceCheckedDispatch.run destinations
      (ReferenceAccountLookup.peek accountsParent accounts v.env.codeOwner).isSome parent v warm meter output := rfl

/-- No account write, including a deletion, is hidden by the presence adapter. -/
theorem writes {Account : Type} (accountsParent : ReferenceAccountLookup.Parent Account)
    (accounts : ReferenceAccountLookup.Tx Account) (destinations : List Nat)
    (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm) (meter : Meter) (output : ByteArray) :
    (run accountsParent accounts destinations parent v warm meter output).2.writes = accounts.writes := by
  unfold run
  dsimp only
  split <;> rfl

/-- Presence at every address is unchanged, including an explicit deletion. -/
theorem lookup {Account : Type} (accountsParent : ReferenceAccountLookup.Parent Account)
    (accounts : ReferenceAccountLookup.Tx Account) (destinations : List Nat)
    (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm) (meter : Meter) (output : ByteArray)
    (a : AccountAddress) :
    ReferenceAccountLookup.peek accountsParent
      (run accountsParent accounts destinations parent v warm meter output).2 a =
      ReferenceAccountLookup.peek accountsParent accounts a := by
  unfold ReferenceAccountLookup.peek
  rw [writes]

/-- Same continued result supplies environment preservation. This identifies
which lookup is used by the next instruction; no independent owner Bool. -/
theorem continued {Account : Type} {accountsParent : ReferenceAccountLookup.Parent Account}
    {accounts nextAccounts : ReferenceAccountLookup.Tx Account} {kind : Kind}
    {destinations : List Nat} {parent : ReferenceStorageView.Parent}
    {v next : View} {warm nextWarm : Warm} {meter nextMeter : Meter} {output : ByteArray} {event : Event}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : run accountsParent accounts destinations parent v warm meter output =
      (.continued next nextWarm nextMeter event,nextAccounts))
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v) :
    next.env = v.env ∧ next.stack.length ≤ 1024 ∧ ReferenceActionMemoryBounds.Aligned next ∧
      ReferenceAccountLookup.peek accountsParent nextAccounts next.env.codeOwner =
        ReferenceAccountLookup.peek accountsParent accounts v.env.codeOwner := by
  have checked := congrArg Prod.fst actual
  rw [result] at checked
  obtain ⟨action,_,_,_,nextStack⟩ := (ReferenceCheckedDispatch.step context checked).sound stack aligned
  have env := ReferenceCheckedPrefix.action_env action
  refine ⟨env,nextStack,ReferenceActionMemoryBounds.preserves_alignment action aligned,?_⟩
  have same := lookup accountsParent accounts destinations parent v warm meter output v.env.codeOwner
  rw [actual] at same
  simpa only [env] using same

#print axioms result
#print axioms writes
#print axioms lookup
#print axioms continued
end Eip8282.Audit.Integrator.ReferenceCheckedAccountDispatch
