import Eip8282.Audit.Integrator.Topics.ReferenceCall2
import Eip8282.Audit.Integrator.ReferenceCheckedAccountEvaluator
import Eip8282.Audit.Integrator.Topics.ReferenceChecked
import Eip8282.Audit.Integrator.ReferenceCheckedFrameOutcome
import Eip8282.Audit.Integrator.Topics.Reference
import Eip8282.Audit.Integrator.ReferenceLogPrefixEvaluation
import Eip8282.Audit.Integrator.Topics.ReferenceRuntime
import Eip8282.Audit.Integrator.ReferenceSourceReplayTrace
import Eip8282.Audit.Integrator.ReferenceSourceTransferFunding
import Eip8282.Audit.Integrator.ReleaseCandidate
import Eip8282.Audit.Integrator.TransactionCommittedEffects

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceAccountFaults -/

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

end

section

/-! ## ReferenceAccountGuarantees -/

/-! Concrete consumers of account-aware checked evaluation. All three
observations use its same computed terminal/EOF; owner presence is obtained
from the layered account lookup rather than an independent Bool. Installed
old owner/invariants remain derived from the actual initialized history.
This does not identify the layered source account payloads with the old World,
source frame snapshots, or Ethereum history. Replay resources remain synthetic.
-/
namespace Eip8282.Audit.Integrator.ReferenceAccountGuarantees
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open JournalInvariant (modelKind)
open TransactionAppendBudget (Receipt)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem code {kind : Contract} {c : MessageCall.Context} (pinned : ReleaseCandidate.CallInput kind c) :
    c.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
  cases kind <;> exact pinned.code

/-- Computed terminal from the same transferred entry consumes the derived
history domain. No assumed old success, old trace, owner, queue, safe fee input
or 2^128 budget is required. Source grant and storage/warm bindings are explicit. -/
theorem terminal {deposit exit : Receipt} {kind : Contract} {c : MessageCall.Context}
    (history : ReleaseCandidate.History deposit exit c.world) (pinned : ReleaseCandidate.CallInput kind c)
    {Account : Type} {accountsParent : ReferenceAccountLookup.Parent Account}
    {accounts finalAccounts : ReferenceAccountLookup.Tx Account}
    {parent : ReferenceStorageView.Parent} {tx : ReferenceStorageView.Tx}
    {warm : Warm} {pre : Meter} {fuel : Nat} {events : List Event}
    {result : ReferenceCheckedTerminalStep.End} {destinations : List Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel accounts
      (initial (CallBridge.codeCall c (code pinned) 0) tx) warm pre = some ((events,.terminal result),finalAccounts))
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c (code pinned) 0).entry.toState)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code pinned) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : c.calldata.size < UInt256.size) :
    ReferenceCheckedTheta.Completed kind c parent events result.view
      (decide (result.halt ≠ .reverted)) result.output ∧ finalAccounts.writes = accounts.writes := by
  have stack : (initial (CallBridge.codeCall c (code pinned) 0) tx).stack.length ≤ 1024 := by simp [initial]
  have aligned := ReferenceActionMemoryBounds.empty_aligned (initial (CallBridge.codeCall c (code pinned) 0) tx) rfl
  obtain ⟨checked,writes⟩ := ReferenceCheckedAccountEvaluator.evaluated context actual stack aligned
  exact ⟨ReleaseCandidate.checked_terminal history pinned context checked slots warmRelated grant fit,writes⟩

/-- Genuine computed EOF is covered by the same history-derived predicates. -/
theorem eof {deposit exit : Receipt} {kind : Contract} {c : MessageCall.Context}
    (history : ReleaseCandidate.History deposit exit c.world) (pinned : ReleaseCandidate.CallInput kind c)
    {Account : Type} {accountsParent : ReferenceAccountLookup.Parent Account}
    {accounts finalAccounts : ReferenceAccountLookup.Tx Account}
    {parent : ReferenceStorageView.Parent} {tx : ReferenceStorageView.Tx}
    {warm finalWarm : Warm} {pre final : Meter} {fuel : Nat} {events : List Event}
    {view : View} {output : ByteArray} {destinations : List Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel accounts
      (initial (CallBridge.codeCall c (code pinned) 0) tx) warm pre = some ((events,.eof view finalWarm final output),finalAccounts))
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c (code pinned) 0).entry.toState)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code pinned) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : c.calldata.size < UInt256.size) :
    output = ByteArray.empty ∧ ReferenceCheckedTheta.Completed kind c parent events view true output ∧ finalAccounts.writes = accounts.writes := by
  have stack : (initial (CallBridge.codeCall c (code pinned) 0) tx).stack.length ≤ 1024 := by simp [initial]
  have aligned := ReferenceActionMemoryBounds.empty_aligned (initial (CallBridge.codeCall c (code pinned) 0) tx) rfl
  obtain ⟨checked,writes⟩ := ReferenceCheckedAccountEvaluator.evaluated context actual stack aligned
  obtain ⟨empty,observed⟩ := ReleaseCandidate.checked_eof history pinned context checked slots warmRelated grant fit
  exact ⟨empty,observed,writes⟩

#print axioms terminal
#print axioms eof
end Eip8282.Audit.Integrator.ReferenceAccountGuarantees

end

section

/-! ## ReferenceActionDeterminism -/

/-! Source-shaped protected actions are deterministic at a fixed input view.
This supports guarded effect replay: an independently constructed accepted old
step and its forward adapter must produce the same source action result. It
does not assert that Action itself contains source admission guards. -/
namespace Eip8282.Audit.Integrator.ReferenceActionDeterminism
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceStorageView ReferenceRuntimeView
set_option autoImplicit false
set_option maxHeartbeats 2000000

private theorem base_deterministic {kind : Kind} {p : Parent} {instr : Instruction} {v a b : View}
    (first : ReferenceSystemAction.Action kind p instr v a)
    (second : ReferenceSystemAction.Action kind p instr v b) : a = b := by
  cases first <;> cases second <;>
    simp_all [ReferencePureAction.action,ReferencePureAction.classify]

private theorem base_not_copy {kind : Kind} {p : Parent} {v next : View}
    (h : ReferenceSystemAction.Action kind p (.CALLDATACOPY,none) v next) : False := by
  cases h
  simp_all [ReferencePureAction.action,ReferencePureAction.classify]

private theorem base_not_log {kind : Kind} {p : Parent} {v next : View}
    (h : ReferenceSystemAction.Action kind p (.LOG0,none) v next) : False := by
  cases h
  simp_all [ReferencePureAction.action,ReferencePureAction.classify]

theorem deterministic {kind : Kind} {p : Parent} {instr : Instruction} {v a b : View}
    (first : ReferenceRuntimeAction.Action kind p instr v a)
    (second : ReferenceRuntimeAction.Action kind p instr v b) : a = b := by
  cases first with
  | base first =>
    cases second with
    | base second => exact base_deterministic first second
    | copy => exact False.elim (base_not_copy first)
    | log => exact False.elim (base_not_log first)
  | copy stack =>
    cases second with
    | base second => exact False.elim (base_not_copy second)
    | copy stack' => simp_all
  | log permission stack =>
    cases second with
    | base second => exact False.elim (base_not_log second)
    | log permission' stack' => simp_all

/-- A local injected counterexample to reversing an unchecked action as an
admitted opcode. PC0 is CALLER in both images, but the action lacks the source
stack guard: with1024 incoming elements it computes1025. Such a frame state
still needs a reachability proof and is not claimed constructor-reachable. -/
theorem unchecked_caller (kind : Kind) (v : View) (length : v.stack.length = 1024) :
    ∃ next, ReferencePureAction.action kind (.CALLER,none) v = some next ∧ next.stack.length = 1025 := by
  refine ⟨ReferencePureAction.advance v (UInt256.ofNat v.env.source.val::v.stack),rfl,?_⟩
  simp [ReferencePureAction.advance,stackAction,length]

theorem full_stack_caller_rejected {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    (length : pre.stack.length = 1024) : Z vj .CALLER pre ≠ .ok (mid,cost) := by
  intro accepted
  have h := (ReferenceAcceptedStack.bounds accepted).2
  simp only [δ,α,Option.getD_some,length] at h
  omega

#print axioms deterministic
#print axioms unchecked_caller
#print axioms full_stack_caller_rejected
end Eip8282.Audit.Integrator.ReferenceActionDeterminism

end

section

/-! ## ReferenceAdmissionHistory -/

/-! Source calldata-floor admission feeds the existing actual history and
committed-effect consumers directly. It is not converted into the different
pinned intrinsicGas gate. Source transaction/state/execution and full validator
extraction are still required to identify these inputs with Ethereum. -/
namespace Eip8282.Audit.Integrator.ReferenceAdmissionHistory
open EvmYul EvmYul.EVM
open NestedEvents
open TransactionAppendBudget (Receipt)
open ReachableCalls (Contract address)
open JournalInvariant (Invariant modelKind)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem append {initial before : World} {receipts : List Receipt} {credits : Nat}
    (history : ActualJournalHistory.Trace initial receipts credits before)
    (r : Receipt) (linked : r.call.world = before) (account : Account .EVM)
    (funded : TransactionFunding.Admission r.call account)
    {recipientExecution accessTokens : Nat}
    (floorGate : ReferenceCalldataAdmission.Gate r.call.transaction.base.data.size recipientExecution accessTokens)
    (resources : 5*(r.call.entryGas.toNat+1) ≤ r.call.fuel) :
    ActualJournalHistory.Trace initial (receipts++[r]) credits r.world :=
  ActualJournalHistory.Trace.transaction history r linked account funded
    (ReferenceCalldataAdmission.data_fit r.call.transaction.base.data floorGate) resources

theorem receipt_effects {kind : Contract} {genesis : World} {credits budget : Nat}
    (r : Receipt) {account : Account .EVM}
    (history : FundingHistory.Trace genesis credits r.call.world)
    (funded : TransactionFunding.Admission r.call account)
    {recipientExecution accessTokens : Nat}
    (floorGate : ReferenceCalldataAdmission.Gate r.call.transaction.base.data.size recipientExecution accessTokens)
    (funds : TransferFunding.worldFunds genesis+credits < FundedDomain.fundingCeiling)
    (resources : 5*(r.call.entryGas.toNat+1) ≤ r.call.fuel)
    (invariant : Invariant kind budget r.call.world)
    (bound : budget+NestedJournalBudget.events r < 2^128)
    (queue : JournalPathQueues.Queue kind)
    (represented : QueueInvariant.Represents (modelKind kind)
      (SystemSpec.worldSlot r.call.world (address kind)) queue) :
    TransactionCommittedEffects.Effects kind r queue :=
  TransactionCommittedEffects.receipt_effects r history funded funds
    (ReferenceCalldataAdmission.data_fit r.call.transaction.base.data floorGate)
    resources invariant bound queue represented

#print axioms append
#print axioms receipt_effects
end Eip8282.Audit.Integrator.ReferenceAdmissionHistory

end

section

/-! ## ReferenceDerivedFailure -/

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

end

section

/-! ## ReferenceIntrinsicGap -/

/-! A local arithmetic/representation witness, not an admitted signed Ethereum
transaction. The source calldata-floor gates do not imply the pinned old
intrinsic-gas gate. Signatures are deliberately empty and no world/history or
execution outcome is claimed. The full source validator remains separate. -/
namespace Eip8282.Audit.Integrator.ReferenceIntrinsicGap
open EvmYul EvmYul.EVM
open ReferenceCalldataAdmission
set_option autoImplicit false

def sample : Transaction := .legacy
  { nonce := ⟨0⟩, gasLimit := ⟨12000⟩, recipient := some ⟨1,by decide⟩,
    value := ⟨0⟩, r := ByteArray.empty, s := ByteArray.empty,
    data := ByteArray.empty, gasPrice := ⟨0⟩, w := ⟨27⟩ }

/-- Empty data, zero access tokens, and zero recipient cost model the source
empty self-transfer cost branch. This checks only the two floor comparisons. -/
theorem source_floor_gates :
    floor sample.base.data.size 0 0 = 12000 ∧ Gate sample.base.data.size 0 0 ∧
      floor sample.base.data.size 0 0 ≤ sample.base.gasLimit.toNat := by
  unfold Gate floor
  decide +kernel

theorem old_intrinsic : intrinsicGas sample = 21000 := by decide +kernel

/-- A proof adapter may use the source size bound directly; substituting an
old intrinsic admission assumption from these source floor gates is invalid. -/
theorem no_floor_implication :
    ¬ (Gate sample.base.data.size 0 0 ∧
        floor sample.base.data.size 0 0 ≤ sample.base.gasLimit.toNat →
      intrinsicGas sample ≤ sample.base.gasLimit.toNat) := by
  unfold Gate floor
  decide +kernel

#print axioms source_floor_gates
#print axioms old_intrinsic
#print axioms no_floor_implication
end Eip8282.Audit.Integrator.ReferenceIntrinsicGap

end

section

/-! ## ReferenceLogPrefixSettlement -/

/-! Transport full logs emitted inside a frame through source settlement.
`incoming` here is newly emitted by the current frame (e.g. its transfer LOG3),
not inherited parent logs. Thus the replay prefix passed to settle is empty.
A successful frame forwards this list once; a failed frame discards it while
preserving its internal execution observations. Ancestor commitment is separate.
-/
namespace Eip8282.Audit.Integrator.ReferenceLogPrefixSettlement
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceCheckedDispatch
open ReferenceCheckedFrameOutcome ReferenceLogPrefixHandlers
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def receipt (incoming : List LogEntry) (r : Receipt) : Receipt :=
  {r with beforeSettlement := view incoming r.beforeSettlement, logsForParent := if r.error.isNone then incoming++r.logsForParent else r.logsForParent}

def boundary (incoming : List LogEntry) : Boundary → Boundary
  | .returned r => .returned (receipt incoming r)
  | .uncaught e v w m o => .uncaught e (view incoming v) w m o
  | .unsupported t v w m o => .unsupported t (view incoming v) w m o
  | .running v w m e => .running (view incoming v) w m e

theorem settled (incoming : List LogEntry) (snapshot : ReferenceStorageView.Tx) (w : Warm) (r : Outcome) :
    settle snapshot [] w (outcome incoming r) = boundary incoming (settle snapshot [] w r) := by
  cases r <;> simp only [outcome,ending,settle]
  all_goals repeat' (split <;> try simp_all only [boundary,receipt,success,failure,view,List.length_nil,List.drop_zero,Option.isNone_none,Option.isNone_some,if_true,if_false])
  all_goals rfl

theorem successful (incoming : List LogEntry) (r : Receipt) (ok : r.error = none) :
    (receipt incoming r).logsForParent = incoming++r.logsForParent := by simp [receipt,ok]

theorem failed (incoming : List LogEntry) (r : Receipt) (error : Error) (bad : r.error = some error) :
    (receipt incoming r).logsForParent = r.logsForParent := by simp [receipt,bad]

theorem unchanged (incoming : List LogEntry) (r : Receipt) :
    (receipt incoming r).storage = r.storage ∧ (receipt incoming r).meter = r.meter ∧
    (receipt incoming r).output = r.output ∧ (receipt incoming r).error = r.error ∧
    (receipt incoming r).localWarm = r.localWarm ∧ (receipt incoming r).warmForParent = r.warmForParent :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms settled
#print axioms successful
#print axioms failed
#print axioms unchanged
end Eip8282.Audit.Integrator.ReferenceLogPrefixSettlement

end

section

/-! ## ReferenceParentEquivalence -/

/-! Parent storage overlays may contain earlier writes from the same block.
Flattening their visible reads is observationally exact for protected actions
and their prices; the original-value reading is retained, not replaced by the
current transaction value. This algebra does not identify an actual block
state with a world: the source state producer must establish that relation. -/
namespace Eip8282.Audit.Integrator.ReferenceParentEquivalence
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings
open ReferenceRuntimeReadings ReferenceMeterPath
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Equality of all visible parent reads, including pending block writes. -/
def Equivalent (p q : Parent) : Prop := ∀ a k, parentRead p a k = parentRead q a k

def flatten (p : Parent) : Parent := {writes := fun _ _ => none, pre := parentRead p}

theorem flatten_equivalent (p : Parent) : Equivalent p (flatten p) := by
  intro a k
  rfl

theorem current_eq {p q : Parent} (same : Equivalent p q) (tx : Tx) (a : AccountAddress) (k : ByteArray) :
    current p tx a k = current q tx a k := by
  simp only [current,same a k]

theorem original_eq {p q : Parent} (same : Equivalent p q) (tx : Tx) (a : AccountAddress) (k : ByteArray) :
    original p tx a k = original q tx a k := by
  classical
  simp only [original,same a k]

theorem reading_eq {p q : Parent} (same : Equivalent p q) (v : View) (warm : Warm) :
    sourceReading p v warm = sourceReading q v warm := by
  classical
  simp only [sourceReading,current_eq same,original_eq same]

theorem action {p q : Parent} (same : Equivalent p q) {kind : Kind}
    {instr : Instruction} {v next : View}
    (actual : ReferenceRuntimeAction.Action kind p instr v next) :
    ReferenceRuntimeAction.Action kind q instr v next := by
  cases actual with
  | base h =>
    apply ReferenceRuntimeAction.Action.base
    cases h with
    | pure h => exact .pure h
    | @load v key rest shape =>
      have load : loadAction p v key rest = loadAction q v key rest := by
        simp only [loadAction,current_eq same]
      rw [load]
      exact .load shape
    | store permission shape => exact .store permission shape
    | word shape => exact .word shape
    | byte shape => exact .byte shape
  | copy shape => exact .copy shape
  | log permission shape => exact .log permission shape

theorem price {p q : Parent} (same : Equivalent p q) {v next : View} {warm : Warm}
    {op : Operation .EVM} {event : Event} (actual : Price p v warm next op event) :
    Price q v warm next op event := by
  simpa only [Price,reading_eq same] using actual

/-- The same finite source-shaped run, with precisely the same actions, views,
access sets and paid event list, survives parent-overlay normalization. -/
theorem run {p q : Parent} (same : Equivalent p q) {kind : Kind}
    {v finish : View} {warm finalWarm : Warm} {events : List Event}
    (actual : ReferenceSourceReplayTrace.Run kind p v warm finish finalWarm events) :
    ReferenceSourceReplayTrace.Run kind q v warm finish finalWarm events := by
  induction actual with
  | refl => exact .refl _ _
  | cons effect priced bounded tail ih =>
    exact .cons (action same effect) (price same priced) bounded ih

/-- Committing the same transaction preserves read equivalence, even when it
writes zero. This uses the source overlay precedence, not arithmetic addition. -/
theorem commit_equivalent {p q : Parent} (same : Equivalent p q) (tx : Tx) :
    Equivalent (commit p tx) (commit q tx) := by
  intro a k
  rw [commit_read,commit_read,current_eq same]

#print axioms flatten_equivalent
#print axioms current_eq
#print axioms original_eq
#print axioms reading_eq
#print axioms action
#print axioms price
#print axioms run
#print axioms commit_equivalent
end Eip8282.Audit.Integrator.ReferenceParentEquivalence

end

section

/-! ## ReferenceRepresentedSourceNonce -/

/-! Source nonce derivation from the represented-parent overlay.

The two public consumers `ReferenceFullFeeBlockTotal.verified` and
`ReferenceCheckedSystemBlock.verified` currently take the read-nonce equality
`(ReferenceSourceValueTransfer.account emptyHash parent tx tx.sender).nonce =
sender.nonce.toNat` as a separate explicit premise, alongside a `found` lookup
identity and a balance-only coherence `BalancesRelated`. The balance-only
coherence does not force any nonce equality, and the abstract `parent : Parent
Hash` has no imposed shape, so read-nonce is a genuinely independent premise in
the current abstract framing.

This module records the elementary derivation: when the parent overlay is
literally the represented image of a source world (`representedParent codeHash
world`) and the transaction accounts journal writes nothing at the address of
interest (fresh journal at that address), the read-nonce equality follows
directly from `world.get? address = some a` alone. The lemma exposes the
condition under which the read-nonce premise is derivable — the represented
parent shape — and is a proven step-(a) building block toward eliminating the
sourceNonce premise from the public consumers by threading a `parent =
representedParent codeHash tx.world` constraint through the downstream
`ReferenceFullFeeBlockNonce` / `ReferenceFullFeeBlockReceipt` chain.

No public consumer signature is changed by this module; it registers the
derivation as a reusable, whitelist-clean lemma. -/
namespace Eip8282.Audit.Integrator.ReferenceRepresentedSourceNonce

open EvmYul
open ReferenceSourceValueTransfer (Account Tx account empty)
open ReferenceSourceTransferFunding (representedParent BalancesRelated)
open TransferFunding (worldBalance)

set_option autoImplicit false

/-- Read-nonce equality holds automatically when the parent overlay is the
    represented image of a world and the transaction accounts journal does not
    override the address under consideration. Requires only the world lookup
    identity `found`; no balance coherence, no code-hash choice, and no
    nonce premise. -/
theorem sourceNonce_of_represented {Hash : Type} (codeHash : ByteArray → Hash)
    (world : AccountMap .EVM) (tx : Tx Hash) (emptyHash : Hash)
    (address : AccountAddress) (a : EvmYul.Account .EVM)
    (freshAccountsAt : tx.accounts.writes address = none)
    (found : world.get? address = some a) :
    (account emptyHash (representedParent codeHash world) tx address).nonce =
      a.nonce.toNat := by
  unfold account ReferenceAccountLookup.peek ReferenceAccountLookup.parentRead representedParent
  dsimp only
  rw [freshAccountsAt, Option.getD_none, Option.getD_none, found]
  rfl

#print axioms sourceNonce_of_represented

/-- The globally-fresh accounts journal case: `tx.accounts.writes = fun _ => none`
    delivers the pointwise `freshAccountsAt` for any address. Convenience form. -/
theorem sourceNonce_of_represented_freshAll {Hash : Type} (codeHash : ByteArray → Hash)
    (world : AccountMap .EVM) (tx : Tx Hash) (emptyHash : Hash)
    (address : AccountAddress) (a : EvmYul.Account .EVM)
    (freshAccounts : tx.accounts.writes = fun _ => none)
    (found : world.get? address = some a) :
    (account emptyHash (representedParent codeHash world) tx address).nonce =
      a.nonce.toNat :=
  sourceNonce_of_represented codeHash world tx emptyHash address a
    (by rw [freshAccounts])
    found

#print axioms sourceNonce_of_represented_freshAll

/-- Balance-coherence identity at a single address, under `parent =
    representedParent codeHash world` and pointwise-fresh accounts journal.
    This is the balance analog of `sourceNonce_of_represented`, generalizing
    `ReferenceSourceTransferFunding.represented_balances` in that it drops the
    `tx = representedTx …` shape requirement — only `tx.accounts.writes address
    = none` is needed, independent of `tx.storage`, `tx.codeWrites`, and
    `tx.transient`. -/
theorem sourceBalance_of_represented {Hash : Type} (codeHash : ByteArray → Hash)
    (world : AccountMap .EVM) (tx : Tx Hash) (emptyHash : Hash)
    (address : AccountAddress)
    (freshAccountsAt : tx.accounts.writes address = none) :
    (account emptyHash (representedParent codeHash world) tx address).balance.toNat =
      worldBalance world address := by
  unfold account ReferenceAccountLookup.peek ReferenceAccountLookup.parentRead worldBalance
    representedParent
  dsimp only
  rw [freshAccountsAt, Option.getD_none, Option.getD_none]
  cases world.get? address <;> rfl

#print axioms sourceBalance_of_represented

/-- `BalancesRelated` follows from the represented-parent shape and a globally
    fresh accounts journal, for any `tx.storage`, `tx.codeWrites`, and
    `tx.transient`. This drops the `tx = representedTx …` requirement of
    `ReferenceSourceTransferFunding.represented_balances`, since `BalancesRelated`
    only reads `tx.accounts`. Composed with `sourceNonce_of_represented_freshAll`,
    it proves that both `balances` and `sourceNonce` premises of the public
    consumers are simultaneously derivable from a single `parent =
    representedParent codeHash tx.world` overlay assumption together with fresh
    accounts, world lookup, and — for nonce — the found witness. -/
theorem BalancesRelated_of_represented_freshAll {Hash : Type}
    (codeHash : ByteArray → Hash) (world : AccountMap .EVM) (tx : Tx Hash)
    (emptyHash : Hash) (freshAccounts : tx.accounts.writes = fun _ => none) :
    BalancesRelated emptyHash (representedParent codeHash world) tx world :=
  fun address => sourceBalance_of_represented codeHash world tx emptyHash address
    (by rw [freshAccounts])

#print axioms BalancesRelated_of_represented_freshAll

end Eip8282.Audit.Integrator.ReferenceRepresentedSourceNonce

end

section

/-! ## ReferenceSupportedOutcome -/

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

end
