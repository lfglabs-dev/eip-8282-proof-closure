import Eip8282.Audit.Integrator.ReferenceCheckedSystemExecution

/-! Three predicates and literal receipt settlement for the same computed
SYSTEM outcome. No user fee path is used; any caught failure has actual local
rollback. Excluding failure and establishing successful drain with the existing
source resource witness is a separate pending composition. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemOutcome
open EvmYul EvmYul.EVM ReferenceCheckedSystemEntry
open ReferenceRuntimeView ReferenceSourceReadings ReferenceCheckedDispatch
open ReferenceCheckedFrameOutcome (Receipt Boundary settle success failure)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

def Claims (kind : ReachableCalls.Contract) (c : Context) (events : List ReferenceMeterPath.Event) : Outcome → Prop
  | .terminal result => ReferenceCheckedTheta.Completed kind (call kind c) (storageParent c) events
      result.view (decide (result.halt ≠ .reverted)) result.output
  | .eof view _ _ output => output = ByteArray.empty ∧
      ReferenceCheckedTheta.Completed kind (call kind c) (storageParent c) events view true output
  | .failed fault .. => ReferenceCheckedFaultClass.caught fault = true
  | .continued .. | .unsupported .. => False

theorem proved {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (history : ReleaseCandidate.History deposit exit c.world)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind))
    {events result finalAccounts}
    (actual : ReferenceCheckedSystemExecution.run kind c emptyHash accountsParent codeParent = some ((events,result),finalAccounts))
    (supported : ReferenceSupportedOutcome.Finalized result) (finalWarm : Warm) :
    Claims kind c events result ∧
    ∃ receipt, settle (before Hash).storage [] finalWarm result = .returned receipt := by
  obtain ⟨slots,owner,warm,context⟩ := bindings kind c history emptyHash accountsParent codeParent loaded
  have input := (constructed kind c history).2.1
  have grant : ReferenceExecutionPotential.potential (meter kind c) ≤ 30000000 := by rw [(constructed kind c history).2.2.2]
  have fit : (call kind c).calldata.size < UInt256.size := by change 0 < UInt256.size; decide
  cases result with
  | continued v w m event => exact False.elim supported
  | unsupported tag v w m out => exact False.elim supported
  | terminal result =>
    have claims := (ReferenceAccountGuarantees.terminal history input context actual slots warm grant fit).1
    refine ⟨claims,?_⟩
    by_cases reverted : result.halt = .reverted
    · exact ⟨failure (before Hash).storage result.view finalWarm (ReferenceChildMeter.settle .reverted result.meter) result.output .reverted,
        by simp only [settle,if_pos reverted]⟩
    · exact ⟨success [] result.view finalWarm result.meter result.output,by simp only [settle,if_neg reverted]⟩
  | eof view lastWarm lastMeter output =>
    have claims := ReferenceAccountGuarantees.eof history input context actual slots warm grant fit
    exact ⟨⟨claims.1,claims.2.1⟩,success [] view lastWarm lastMeter output,rfl⟩
  | failed fault view partialWarm partialMeter output =>
    have replay := actual
    unfold ReferenceCheckedSystemExecution.run at replay
    rw [(ready kind c emptyHash accountsParent codeParent loaded).2] at replay
    have slots' := slots
    rw [(ready kind c emptyHash accountsParent codeParent loaded).2] at slots'
    have caught := ReferenceDerivedFailure.caught (xi kind c) ReferenceSourceValueTransfer.Account.codeHash emptyHash
      accountsParent (before Hash).accounts codeParent (before Hash).codeWrites context loaded replay slots' owner warm grant fit
    refine ⟨caught,failure (before Hash).storage view partialWarm (ReferenceChildMeter.settle .exceptional partialMeter) ByteArray.empty (.exceptional fault),?_⟩
    simp only [settle,caught,if_true]

#print axioms proved
end Eip8282.Audit.Integrator.ReferenceCheckedSystemOutcome
