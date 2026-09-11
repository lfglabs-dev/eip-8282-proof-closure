import Eip8282.Audit.Integrator.ReferenceCheckedPrefix
import Eip8282.Audit.Integrator.ReferenceCheckedAccountEvaluator

/-! Reachable pinned-code sites cannot select an unsupported checked handler.
This consumes the same completed prefix, not an assumed successful endpoint or
an unrestricted decoder equivalence. The finite image table is distinct from
arbitrary finite evaluation length. Consumer: exhaustive allocated-call safety. -/
namespace Eip8282.Audit.Integrator.ReferenceSupportedOutcome
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def supportedRead : Dispatch → Bool
  | .unsupported _ => false
  | _ => true

def Supported : Outcome → Prop
  | .unsupported .. => False
  | _ => True

def Finalized : Outcome → Prop
  | .continued .. | .unsupported .. => False
  | _ => True

theorem site_table (kind : Kind) :
    (ReferenceDecodeSites.sites (ReferenceRuntimeSites.reference kind)).all
      (fun pc => supportedRead (read (ReferenceDecodeSites.code (ReferenceRuntimeSites.reference kind)) pc)) = true := by
  cases kind <;> decide +kernel

theorem read_supported {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View} {post : EVM.State}
    (related : Related parent v post)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) post) :
    supportedRead (read v.env.code v.pc) = true := by
  rw [related.env,related.pc,site.1,ReferenceRuntimeSites.code_eq]
  rcases ReferenceRuntimeSites.site_or_eof site with member | eof
  · exact List.all_eq_true.mp (site_table kind) _ member
  · rw [eof]
    cases kind <;> decide +kernel

theorem handler_supported (h : Handler) (destinations : List Nat) (ownerExists : Bool)
    (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm) (meter : Meter) (output : ByteArray) :
    Supported (runHandler h destinations ownerExists parent v warm meter output) := by
  cases h <;> unfold runHandler
  all_goals repeat' (split <;> try dsimp only)
  all_goals trivial

theorem run_supported {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View} {post : EVM.State}
    (related : Related parent v post) (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) post)
    (destinations : List Nat) (ownerExists : Bool) (warm : Warm) (meter : Meter) (output : ByteArray) :
    Supported (run destinations ownerExists parent v warm meter output) := by
  have allowed := read_supported related site
  unfold run
  cases h : read v.env.code v.pc with
  | eof => trivial
  | invalid tag => trivial
  | unsupported tag => simp [h,supportedRead] at allowed
  | handler handler => exact handler_supported handler destinations ownerExists parent v warm meter output

/-- The final dispatcher of the same computed checked evaluation lies at a
proved runtime site. No unsupported result is admitted through the theorem. -/
theorem evaluated {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm : Warm} {pre : Meter} {fuel : Nat}
    {events : List ReferenceMeterPath.Event} {result : Outcome} {destinations : List Nat} {ownerExists : Bool}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent ByteArray.empty fuel
      (initial c tx) warm pre = some (events,result))
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (cdfit : c.env.calldata.size < UInt256.size) : Finalized result := by
  obtain ⟨finish,finalWarm,final,post,last,related,site,_⟩ :=
    ReferenceCheckedPrefix.evaluated_bounds c context actual slots owner warmRelated grant cdfit
  have supported := run_supported related site destinations ownerExists finalWarm final ByteArray.empty
  rw [last] at supported
  obtain ⟨_,_,_,_,_,ended⟩ := ReferenceCheckedEvaluator.extract context actual
  cases result <;> simp_all [Supported,Finalized,ReferenceCheckedEvaluator.Ended]

theorem account_evaluated {Account : Type} {accountsParent : ReferenceAccountLookup.Parent Account}
    {accounts finalAccounts : ReferenceAccountLookup.Tx Account}
    {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm : Warm} {pre : Meter} {fuel : Nat}
    {events : List ReferenceMeterPath.Event} {result : Outcome} {destinations : List Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel accounts
      (initial c tx) warm pre = some ((events,result),finalAccounts))
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (cdfit : c.env.calldata.size < UInt256.size) : Finalized result := by
  have erased := ReferenceCheckedAccountEvaluator.evaluated context actual
    (by simp [initial]) (ReferenceActionMemoryBounds.empty_aligned (initial c tx) rfl)
  exact evaluated c context erased.1 slots owner warmRelated grant cdfit

#print axioms site_table
#print axioms read_supported
#print axioms handler_supported
#print axioms run_supported
#print axioms evaluated
#print axioms account_evaluated
end Eip8282.Audit.Integrator.ReferenceSupportedOutcome
