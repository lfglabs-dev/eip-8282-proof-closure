import Eip8282.Audit.Integrator.ReferenceAccountFaults
import Eip8282.Audit.Integrator.ReferenceCheckedConversionSafety
import Eip8282.Audit.Integrator.ReferenceCheckedFrameOutcome

/-! Same evaluated protected failure supplies its own catch classification.
The account assertion is excluded by the actual nonempty code-hash fetch;
conversion errors are excluded by entry calldata and derived final-PC bounds.
No caught-fault, selected terminal, old success or desired rollback is assumed.
The old HasOwner input supports the existing PC replay proof; release history
can derive it. Actual source dictionary/code-address bindings and complete
account/value-transfer snapshot identity remain outside this local projection.
-/
namespace Eip8282.Audit.Integrator.ReferenceDerivedFailure
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem nonempty {kind : Kind} (c : XiCall kind) : c.env.code ≠ ByteArray.empty := by
  rw [c.code_pinned]
  cases kind <;> decide +kernel

/-- The same account-aware failed computation excludes every represented
uncaught host fault; source gas failure remains an actual exceptional halt. -/
theorem caught {Account Hash Error : Type} [DecidableEq Hash] {kind : Kind}
    (c : XiCall kind) (codeHash : Account → Hash) (emptyHash : Hash)
    (accountsParent : ReferenceAccountLookup.Parent Account) (accounts : ReferenceAccountLookup.Tx Account)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (codeWrites : Hash → Option ByteArray)
    {parent : ReferenceStorageView.Parent} {tx : ReferenceStorageView.Tx}
    {warm partialWarm : Warm} {pre partialMeter : Meter} {fuel : Nat} {events : List Event}
    {view : View} {output : ByteArray} {fault : Fault} {destinations : List Nat}
    {finalAccounts : ReferenceAccountLookup.Tx Account}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (loaded : (ReferenceCodeAccountPresence.load codeHash emptyHash accountsParent accounts codeParent codeWrites
      c.env.codeOwner).1 = .ok c.env.code)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel
      (ReferenceCodeAccountPresence.load codeHash emptyHash accountsParent accounts codeParent codeWrites c.env.codeOwner).2
      (initial c tx) warm pre = some ((events,.failed fault view partialWarm partialMeter output),finalAccounts))
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (oldOwner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (calldata : c.env.calldata.size < UInt256.size) : ReferenceCheckedFaultClass.caught fault = true := by
  have stack : (initial c tx).stack.length ≤ 1024 := by simp [initial]
  have aligned := ReferenceActionMemoryBounds.empty_aligned (initial c tx) rfl
  obtain ⟨checked,_⟩ := ReferenceCheckedAccountEvaluator.evaluated context actual stack aligned
  obtain ⟨finish,finalWarm,final,post,last,_,_,_,cdFit,pcFit⟩ :=
    ReferenceCheckedPrefix.evaluated_bounds c context checked slots oldOwner warmRelated grant calldata
  have conversions := ReferenceCheckedConversionSafety.dispatch last cdFit pcFit
  apply (ReferenceCheckedFaultClass.caught_iff fault).mpr
  refine ⟨conversions.1,conversions.2,?_⟩
  intro equal
  subst fault
  exact ReferenceAccountFaults.code_fetch_no_owner codeHash emptyHash accountsParent accounts
    codeParent codeWrites context loaded (nonempty c) stack aligned actual

/-- The derived catch classification now discharges projected settlement for
this exact evaluated failure, including partial effects before failure. Full
source account snapshot/value-transfer restoration is not asserted here. -/
theorem settled {Account Hash Error : Type} [DecidableEq Hash] {kind : Kind}
    (c : XiCall kind) (codeHash : Account → Hash) (emptyHash : Hash)
    (accountsParent : ReferenceAccountLookup.Parent Account) (accounts : ReferenceAccountLookup.Tx Account)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (codeWrites : Hash → Option ByteArray)
    {parent : ReferenceStorageView.Parent} {tx : ReferenceStorageView.Tx}
    {warm partialWarm : Warm} {pre partialMeter : Meter} {fuel : Nat} {events : List Event}
    {view : View} {output : ByteArray} {fault : Fault} {destinations : List Nat}
    {finalAccounts : ReferenceAccountLookup.Tx Account}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (loaded : (ReferenceCodeAccountPresence.load codeHash emptyHash accountsParent accounts codeParent codeWrites
      c.env.codeOwner).1 = .ok c.env.code)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel
      (ReferenceCodeAccountPresence.load codeHash emptyHash accountsParent accounts codeParent codeWrites c.env.codeOwner).2
      (initial c tx) warm pre = some ((events,.failed fault view partialWarm partialMeter output),finalAccounts))
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (oldOwner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (calldata : c.env.calldata.size < UInt256.size) :
    ∃ receipt,
      ReferenceCheckedFrameOutcome.settle tx [] warm (.failed fault view partialWarm partialMeter output) = .returned receipt ∧
      receipt.beforeSettlement = view ∧ receipt.output = ByteArray.empty ∧
      receipt.meter.execution = 0 ∧ receipt.meter.reservoir = partialMeter.baseline ∧
      receipt.meter.spill = 0 ∧ receipt.meter.refund = 0 ∧
      receipt.meter.committedSpill = partialMeter.committedSpill ∧
      receipt.logsForParent = [] ∧ receipt.warmForParent = none ∧
      receipt.storage.created = view.storage.created ∧ receipt.storage.reads = view.storage.reads ∧
      ∀ p address key, ReferenceStorageView.current p receipt.storage address key =
        ReferenceStorageView.current p tx address key := by
  exact ReferenceCheckedFrameOutcome.failed tx [] warm partialWarm fault view partialMeter output
    (caught c codeHash emptyHash accountsParent accounts codeParent codeWrites context loaded actual
      slots oldOwner warmRelated grant calldata)

#print axioms caught
#print axioms settled
end Eip8282.Audit.Integrator.ReferenceDerivedFailure
