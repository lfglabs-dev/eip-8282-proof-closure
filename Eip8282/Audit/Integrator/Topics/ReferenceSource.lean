import Eip8282.Audit.Integrator.Topics.Reference2
import Eip8282.Audit.Integrator.Topics.Reference5
import Eip8282.Audit.Integrator.ReferenceSourceBalanceTransport
import Eip8282.Audit.Integrator.Topics.ReferenceSource2
import Eip8282.Audit.Integrator.ReferenceSourceTransferFunding
import Eip8282.Audit.Integrator.ReferenceTransferredFailure
import Eip8282.Audit.Integrator.RuntimeBalancePreservation

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceSourceAppendCost -/

/-! Mandatory append costs from the same finite source-shaped completed call.
Synthetic old success is constructed, never supplied. Ordered actual instruction
markers align with the replayed source event trace; old gas is not the measure.
Actual source frame/price/entry extraction and global occurrence coverage remain
separate producers. No queue invariant, no-wrap assumption or loop cap occurs. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceAppendCost
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings
open ReferenceMeterPath ReferenceExecutionLedger ReferenceSourceReplayTrace
open ReferenceAppendOccurrences ReferenceAppendPrice ReferenceTraceAgreement
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem exit_cost (c : XiCall .exit) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    (source : Run .exit parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (bound : work events ≤ 30000000) (halt : instruction finish = (.STOP,none))
    (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 48) :
    1419 ≤ work events := by
  obtain ⟨middle,post,trace,coupled,decoded,actual,_⟩ :=
    ReferenceSourceReplayCompletion.stop c source slots owner warmRelated bound halt
  let replay := ReferenceSourceReplayEntry.call c events 0
  have actual' : X (events.length+2) exitJumpdests replay.entry = .ok (.success post ByteArray.empty) := by
    change X _ (D_J exitRuntime ⟨0⟩) _ = _ at actual
    rw [exit_D_J] at actual
    exact actual
  obtain ⟨rem,exit,marked,stopped,_⟩ := ReferenceAppendEntry.exit_entry replay user size actual'
  have marked' : Marked (D_J (ReferenceRuntimeSites.runtime .exit).code ⟨0⟩)
      (events.length+2) replay.entry rem exit exitMarkers := by
    change Marked (D_J exitRuntime ⟨0⟩) _ _ _ _ _
    rw [exit_D_J]
    exact marked
  obtain ⟨markerTrace,markerRun,_⟩ := marked'.erase
  obtain ⟨_,sameRem,sameExit⟩ := complete_unique markerRun coupled.viewed.erase
    (blocked_of_stop stopped) (blocked_of_stop decoded)
  have aligned : Marked (D_J (ReferenceRuntimeSites.runtime .exit).code ⟨0⟩)
      (events.length+2) replay.entry 2 middle exitMarkers := by
    simpa only [sameRem,sameExit] using marked'
  have cost := selected_cost aligned coupled
  rw [exact_marker_costs.1] at cost
  exact cost

theorem deposit_cost (c : XiCall .deposit) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    (source : Run .deposit parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (bound : work events ≤ 30000000) (halt : instruction finish = (.STOP,none))
    (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 184) :
    2647 ≤ work events := by
  obtain ⟨middle,post,trace,coupled,decoded,actual,_⟩ :=
    ReferenceSourceReplayCompletion.stop c source slots owner warmRelated bound halt
  let replay := ReferenceSourceReplayEntry.call c events 0
  have actual' : X (events.length+2) depositJumpdests replay.entry = .ok (.success post ByteArray.empty) := by
    change X _ (D_J depositRuntime ⟨0⟩) _ = _ at actual
    rw [deposit_D_J] at actual
    exact actual
  obtain ⟨rem,exit,marked,stopped,_⟩ := ReferenceAppendEntry.deposit_entry replay user size actual'
  have marked' : Marked (D_J (ReferenceRuntimeSites.runtime .deposit).code ⟨0⟩)
      (events.length+2) replay.entry rem exit depositMarkers := by
    change Marked (D_J depositRuntime ⟨0⟩) _ _ _ _ _
    rw [deposit_D_J]
    exact marked
  obtain ⟨markerTrace,markerRun,_⟩ := marked'.erase
  obtain ⟨_,sameRem,sameExit⟩ := complete_unique markerRun coupled.viewed.erase
    (blocked_of_stop stopped) (blocked_of_stop decoded)
  have aligned : Marked (D_J (ReferenceRuntimeSites.runtime .deposit).code ⟨0⟩)
      (events.length+2) replay.entry 2 middle depositMarkers := by
    simpa only [sameRem,sameExit] using marked'
  have cost := selected_cost aligned coupled
  rw [exact_marker_costs.2] at cost
  exact cost

#print axioms exit_cost
#print axioms deposit_cost
end Eip8282.Audit.Integrator.ReferenceSourceAppendCost

end

section

/-! ## ReferenceSourceFundedEntry -/

/-! Common entry producer for successful and failed protected calls. The same
before-transfer code, slots and balances derive transfer admission and runtime
slots. No post-transfer condition is assumed. Python context construction and
pre-state representation are separate application obligations. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceFundedEntry
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem code {kind : Contract} {c : MessageCall.Context} (input : ReleaseCandidate.CallInput kind c) :
    c.code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by
  cases kind <;> exact input.code

theorem prepared {deposit exit : TransactionAppendBudget.Receipt} {Hash LoadError : Type} [DecidableEq Hash]
    {kind : Contract} (c : MessageCall.Context)
    (history : ReleaseCandidate.History deposit exit c.world) (input : ReleaseCandidate.CallInput kind c)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    (parent : ReferenceStorageView.Parent)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites c.target).1 = .ok c.code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before c.world)
    (funded : c.value.toNat ≤ TransferFunding.worldBalance c.world c.caller)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage c.target q.toByteArray = SystemSpec.worldSlot c.world c.target q) :
    (entry c emptyHash accountsParent before codeParent shouldTransfer).1 = .ok () ∧
    ReferenceStorageView.Related parent (entry c emptyHash accountsParent before codeParent shouldTransfer).2.storage
      (CallBridge.codeCall c (code input) 0).entry.toState := by
  let start := fetched emptyHash accountsParent before codeParent c.target
  have startBalances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent start c.world := balances
  refine ⟨ReferenceSourceTransferFunding.after_history emptyHash accountsParent start c shouldTransfer history startBalances funded,?_⟩
  have fetchedLoad : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      start.accounts codeParent start.codeWrites c.target).1 = .ok c.code := loaded
  have nonempty : c.code ≠ ByteArray.empty := by
    rw [code input]
    cases kind <;> decide +kernel
  have hashNonempty := ReferenceSourceValueTransfer.loaded_nonempty_hash emptyHash accountsParent start codeParent c.target fetchedLoad nonempty
  intro q
  change ReferenceStorageView.current parent (ReferenceSourceValueTransfer.enter emptyHash accountsParent start c.caller c.target c.value shouldTransfer).2.storage c.target q.toByteArray = _
  rw [ReferenceSourceValueTransfer.enter_protected_storage emptyHash accountsParent start c.caller c.target c.target c.value shouldTransfer hashNonempty]
  exact (slots q).trans (TransferFrame.codeCall_storage c (code input) 0 q).symm

#print axioms prepared
end Eip8282.Audit.Integrator.ReferenceSourceFundedEntry

end

section

/-! ## ReferenceSourceFundedFailure -/

/-! Source transfer admission is derived before applying the same failed
runtime/snapshot consumer. The independent inputs are pre-transfer balance
read correspondence and sender funding, not transfer success, recipient fit,
chosen wealth maximum or failure post-state. Full source frame/world bindings
and canonical admission remain open. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceFundedFailure
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceCheckedDispatch ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem code {kind : Contract} {c : MessageCall.Context} (input : ReleaseCandidate.CallInput kind c) :
    c.code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by
  cases kind <;> exact input.code

theorem settled {deposit exit : TransactionAppendBudget.Receipt} {Hash LoadError : Type} [DecidableEq Hash]
    {kind : Contract} (c : MessageCall.Context)
    (history : ReleaseCandidate.History deposit exit c.world) (input : ReleaseCandidate.CallInput kind c)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    {parent : ReferenceStorageView.Parent} {warm partialWarm : Warm} {pre partialMeter : Meter}
    {fuel : Nat} {events : List Event} {view : View} {output : ByteArray} {fault : Fault} {destinations : List Nat}
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    (context : ReferenceCheckedStackControlStep.DestinationContext (JournalInvariant.modelKind kind) destinations)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites c.target).1 = .ok c.code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before c.world)
    (funded : c.value.toNat ≤ TransferFunding.worldBalance c.world c.caller)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel
      (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts
      (initial (CallBridge.codeCall c (code input) 0) (entry c emptyHash accountsParent before codeParent shouldTransfer).2.storage)
      warm pre = some ((events,.failed fault view partialWarm partialMeter output),finalAccounts))
    (slots : ∀ q, ReferenceStorageView.current parent before.storage c.target q.toByteArray = SystemSpec.worldSlot c.world c.target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code input) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (calldata : c.calldata.size < UInt256.size) :
    let live := {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := view.storage}
    let restored := restore live before
    ∃ receipt,
      ReferenceCheckedFrameOutcome.settle before.storage [] warm (.failed fault view partialWarm partialMeter output) = .returned receipt ∧
      receipt.beforeSettlement = view ∧ receipt.output = ByteArray.empty ∧
      receipt.meter.execution = 0 ∧ receipt.meter.reservoir = partialMeter.baseline ∧
      receipt.meter.spill = 0 ∧ receipt.meter.refund = 0 ∧
      receipt.meter.committedSpill = partialMeter.committedSpill ∧
      receipt.logsForParent = [] ∧ receipt.warmForParent = none ∧
      receipt.storage = restored.storage ∧
      restored.accounts.writes = before.accounts.writes ∧
      restored.codeWrites = before.codeWrites ∧ restored.transient = before.transient ∧
      restored.accounts.reads = finalAccounts.reads ∧
      restored.storage.reads = view.storage.reads ∧ restored.storage.created = view.storage.created ∧
      ∀ p address key, ReferenceStorageView.current p restored.storage address key =
        ReferenceStorageView.current p before.storage address key := by
  have entered := (ReferenceSourceFundedEntry.prepared c history input emptyHash accountsParent before codeParent shouldTransfer
    parent loaded balances funded slots).1
  exact ReferenceTransferredFailure.settled c history input emptyHash accountsParent before codeParent shouldTransfer
    context loaded entered actual slots warmRelated grant calldata

#print axioms settled
end Eip8282.Audit.Integrator.ReferenceSourceFundedFailure

end

section

/-! ## ReferenceSourceFundedGuarantees -/

/-! All three same-outcome checked guarantee consumers now start before source
value transfer. Initialized funding plus initial balance correspondence derives
transfer success; code/slot preservation derives runtime slots. The output
still uses the explicit synthetic replay/old-world observation boundary of
ReferenceCheckedTheta.Completed; source gas and canonical Ethereum are not
identified with those receipts. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceFundedGuarantees
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open JournalInvariant (modelKind)
open TransactionAppendBudget (Receipt)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem code {kind : Contract} {c : MessageCall.Context} (pinned : ReleaseCandidate.CallInput kind c) :
    c.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
  cases kind <;> exact pinned.code

theorem terminal {deposit exit : Receipt} {kind : Contract} {c : MessageCall.Context}
    (history : ReleaseCandidate.History deposit exit c.world) (pinned : ReleaseCandidate.CallInput kind c)
    {Hash LoadError : Type} [DecidableEq Hash]
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    {parent : ReferenceStorageView.Parent}
    {warm : Warm} {pre : Meter} {fuel : Nat} {events : List Event}
    {result : ReferenceCheckedTerminalStep.End} {destinations : List Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts
      (initial (CallBridge.codeCall c (code pinned) 0) (entry c emptyHash accountsParent before codeParent shouldTransfer).2.storage) warm pre = some ((events,.terminal result),finalAccounts))
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites c.target).1 = .ok c.code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before c.world)
    (funded : c.value.toNat ≤ TransferFunding.worldBalance c.world c.caller)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage c.target q.toByteArray = SystemSpec.worldSlot c.world c.target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code pinned) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : c.calldata.size < UInt256.size) :
    (entry c emptyHash accountsParent before codeParent shouldTransfer).1 = .ok () ∧
    ReferenceCheckedTheta.Completed kind c parent events result.view
      (decide (result.halt ≠ .reverted)) result.output ∧ finalAccounts.writes = (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts.writes := by
  have ready := ReferenceSourceFundedEntry.prepared c history pinned emptyHash accountsParent before codeParent shouldTransfer
    parent loaded balances funded slots
  exact ⟨ready.1,ReferenceAccountGuarantees.terminal history pinned context actual ready.2 warmRelated grant fit⟩

theorem eof {deposit exit : Receipt} {kind : Contract} {c : MessageCall.Context}
    (history : ReleaseCandidate.History deposit exit c.world) (pinned : ReleaseCandidate.CallInput kind c)
    {Hash LoadError : Type} [DecidableEq Hash]
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    {parent : ReferenceStorageView.Parent}
    {warm finalWarm : Warm} {pre final : Meter} {fuel : Nat} {events : List Event}
    {view : View} {output : ByteArray} {destinations : List Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts
      (initial (CallBridge.codeCall c (code pinned) 0) (entry c emptyHash accountsParent before codeParent shouldTransfer).2.storage) warm pre = some ((events,.eof view finalWarm final output),finalAccounts))
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites c.target).1 = .ok c.code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before c.world)
    (funded : c.value.toNat ≤ TransferFunding.worldBalance c.world c.caller)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage c.target q.toByteArray = SystemSpec.worldSlot c.world c.target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code pinned) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : c.calldata.size < UInt256.size) :
    (entry c emptyHash accountsParent before codeParent shouldTransfer).1 = .ok () ∧
    output = ByteArray.empty ∧ ReferenceCheckedTheta.Completed kind c parent events view true output ∧ finalAccounts.writes = (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts.writes := by
  have ready := ReferenceSourceFundedEntry.prepared c history pinned emptyHash accountsParent before codeParent shouldTransfer
    parent loaded balances funded slots
  exact ⟨ready.1,ReferenceAccountGuarantees.eof history pinned context actual ready.2 warmRelated grant fit⟩

#print axioms terminal
#print axioms eof
end Eip8282.Audit.Integrator.ReferenceSourceFundedGuarantees

end

section

/-! ## ReferenceSourceBalanceOutcome -/

/-! Balance observations of the same account-aware execution used by the three
checked guarantees. An internal endpoint retains the entry transfer even when
its outcome will revert; settlement instead restores the pre-transfer balances.
This does not identify the replay post-world, source frame construction, gas or
ancestor settlement with the source evaluator. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceBalanceOutcome
open EvmYul EvmYul.EVM
open ReferenceSourceValueTransfer ReferenceSourceTransferFunding
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceCheckedDispatch ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- Reads, code/storage writes and transient state do not change account balance
observations when the account write overlay is unchanged. -/
theorem same_writes {Hash : Type} (emptyHash : Hash) (parent : Parent Hash)
    (before after : Tx Hash) (world : AccountMap .EVM)
    (related : BalancesRelated emptyHash parent before world)
    (writes : after.accounts.writes = before.accounts.writes) :
    BalancesRelated emptyHash parent after world := by
  intro address
  change ((ReferenceAccountLookup.peek parent after.accounts address).getD (empty emptyHash)).balance.toNat = _
  unfold ReferenceAccountLookup.peek
  rw [writes]
  exact related address

/-- Same finite completed evaluation as the guarantee consumers: its internal
account balances match the transferred entry world. This is deliberately a
pre-settlement observation, including failed and reverted outcomes. -/
theorem evaluated {deposit exit : TransactionAppendBudget.Receipt} {Hash LoadError : Type} [DecidableEq Hash]
    (emptyHash : Hash) (accountsParent : Parent Hash) (before : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError)
    (c : MessageCall.Context) (shouldTransfer : Bool)
    (history : ReleaseCandidate.History deposit exit c.world)
    (balances : BalancesRelated emptyHash accountsParent before c.world)
    (funded : c.value.toNat ≤ TransferFunding.worldBalance c.world c.caller)
    (mode : shouldTransfer = true ∨ c.value = ⟨0⟩)
    {destinations : List Nat} {parent : ReferenceStorageView.Parent} {output : ByteArray}
    {fuel : Nat} {v : View} {warm : Warm} {meter : Meter} {events : List Event} {result : Outcome}
    {finalAccounts : ReferenceAccountLookup.Tx (Account Hash)}
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent output fuel
      (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts v warm meter =
      some ((events,result),finalAccounts)) :
    BalancesRelated emptyHash accountsParent
      {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts} c.entryWorld := by
  have fetchedBalances : BalancesRelated emptyHash accountsParent
      (fetched emptyHash accountsParent before codeParent c.target) c.world := balances
  have transported := ReferenceSourceBalanceTransport.after_history emptyHash accountsParent
    (fetched emptyHash accountsParent before codeParent c.target) c shouldTransfer history fetchedBalances funded mode
  exact same_writes emptyHash accountsParent _ _ _ transported (ReferenceCheckedAccountEvaluator.writes actual)

/-- Frame restoration recovers the pre-transfer balances while retaining live
read metadata. Ancestor commit/rollback is a separate operation. -/
theorem restored {Hash : Type} (emptyHash : Hash) (parent : Parent Hash)
    (live before : Tx Hash) (world : AccountMap .EVM)
    (balances : BalancesRelated emptyHash parent before world) :
    BalancesRelated emptyHash parent (restore live before) world :=
  same_writes emptyHash parent before (restore live before) world balances rfl

#print axioms same_writes
#print axioms evaluated
#print axioms restored
end Eip8282.Audit.Integrator.ReferenceSourceBalanceOutcome

end

section

/-! ## ReferenceSourceBalancedFailure -/

/-! The same failed runtime and source snapshot now recover the original
balance observation as well as the four write components and storage observation.
No successful value transfer, post-balance or caught-fault premise is assumed.
Initial source/world balance correspondence and sender funding remain inputs;
actual source frame extraction and ancestor settlement remain separate. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceBalancedFailure
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceCheckedDispatch ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem code {kind : Contract} {c : MessageCall.Context} (input : ReleaseCandidate.CallInput kind c) :
    c.code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by
  cases kind <;> exact input.code

theorem settled {deposit exit : TransactionAppendBudget.Receipt} {Hash LoadError : Type} [DecidableEq Hash]
    {kind : Contract} (c : MessageCall.Context)
    (history : ReleaseCandidate.History deposit exit c.world) (input : ReleaseCandidate.CallInput kind c)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    {parent : ReferenceStorageView.Parent} {warm partialWarm : Warm} {pre partialMeter : Meter}
    {fuel : Nat} {events : List Event} {view : View} {output : ByteArray} {fault : Fault} {destinations : List Nat}
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    (context : ReferenceCheckedStackControlStep.DestinationContext (JournalInvariant.modelKind kind) destinations)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites c.target).1 = .ok c.code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before c.world)
    (funded : c.value.toNat ≤ TransferFunding.worldBalance c.world c.caller)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel
      (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts
      (initial (CallBridge.codeCall c (code input) 0) (entry c emptyHash accountsParent before codeParent shouldTransfer).2.storage)
      warm pre = some ((events,.failed fault view partialWarm partialMeter output),finalAccounts))
    (slots : ∀ q, ReferenceStorageView.current parent before.storage c.target q.toByteArray = SystemSpec.worldSlot c.world c.target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code input) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (calldata : c.calldata.size < UInt256.size) :
    let live := {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := view.storage}
    let restored := restore live before
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent restored c.world ∧
    ∃ receipt,
      ReferenceCheckedFrameOutcome.settle before.storage [] warm (.failed fault view partialWarm partialMeter output) = .returned receipt ∧
      receipt.beforeSettlement = view ∧ receipt.output = ByteArray.empty ∧
      receipt.meter.execution = 0 ∧ receipt.meter.reservoir = partialMeter.baseline ∧
      receipt.meter.spill = 0 ∧ receipt.meter.refund = 0 ∧
      receipt.meter.committedSpill = partialMeter.committedSpill ∧
      receipt.logsForParent = [] ∧ receipt.warmForParent = none ∧
      receipt.storage = restored.storage ∧
      restored.accounts.writes = before.accounts.writes ∧
      restored.codeWrites = before.codeWrites ∧ restored.transient = before.transient ∧
      restored.accounts.reads = finalAccounts.reads ∧
      restored.storage.reads = view.storage.reads ∧ restored.storage.created = view.storage.created ∧
      ∀ p address key, ReferenceStorageView.current p restored.storage address key =
        ReferenceStorageView.current p before.storage address key := by
  refine ⟨ReferenceSourceBalanceOutcome.restored emptyHash accountsParent _ before c.world balances, ?_⟩
  exact ReferenceSourceFundedFailure.settled c history input emptyHash accountsParent before codeParent shouldTransfer
    context loaded balances funded actual slots warmRelated grant calldata

#print axioms settled
end Eip8282.Audit.Integrator.ReferenceSourceBalancedFailure

end

section

/-! ## ReferenceSourceCompletedBalances -/

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

end

section

/-! ## ReferenceSourceBalancedGuarantees -/

/-! Same three guarantees and source settled balances of the very same replay
receipt world. The computed runtime endpoint and source transfer are shared;
old-runtime balance preservation closes the post-world connection. The additional
transfer-mode condition scopes these stronger exports, not earlier guarantees.
Full Python frame extraction, source gas and ancestor settlement remain open. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceBalancedGuarantees
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open JournalInvariant (modelKind)
open TransactionAppendBudget (Receipt)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem code {kind : Contract} {c : MessageCall.Context} (pinned : ReleaseCandidate.CallInput kind c) :
    c.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
  cases kind <;> exact pinned.code

theorem terminal {deposit exit : Receipt} {kind : Contract} {c : MessageCall.Context}
    (history : ReleaseCandidate.History deposit exit c.world) (pinned : ReleaseCandidate.CallInput kind c)
    {Hash LoadError : Type} [DecidableEq Hash]
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    {parent : ReferenceStorageView.Parent}
    {warm : Warm} {pre : Meter} {fuel : Nat} {events : List Event}
    {result : ReferenceCheckedTerminalStep.End} {destinations : List Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts
      (initial (CallBridge.codeCall c (code pinned) 0) (entry c emptyHash accountsParent before codeParent shouldTransfer).2.storage) warm pre = some ((events,.terminal result),finalAccounts))
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites c.target).1 = .ok c.code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before c.world)
    (funded : c.value.toNat ≤ TransferFunding.worldBalance c.world c.caller)
    (mode : shouldTransfer = true ∨ c.value = ⟨0⟩)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage c.target q.toByteArray = SystemSpec.worldSlot c.world c.target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code pinned) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : c.calldata.size < UInt256.size) :
    (entry c emptyHash accountsParent before codeParent shouldTransfer).1 = .ok () ∧
    ReferenceSourceCompletedBalances.Completed emptyHash accountsParent before
      {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := result.view.storage}
      kind c parent events result.view (decide (result.halt ≠ .reverted)) result.output ∧ finalAccounts.writes = (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts.writes ∧
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent
      {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts} c.entryWorld := by
  have original := ReferenceSourceFundedGuarantees.terminal history pinned emptyHash accountsParent before codeParent shouldTransfer
    context actual loaded balances funded slots warmRelated grant fit
  have sameBalances := ReferenceSourceBalanceOutcome.evaluated emptyHash accountsParent before codeParent c shouldTransfer
    history balances funded mode actual
  have completed := ReferenceSourceCompletedBalances.of_completed emptyHash accountsParent before
    {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := result.view.storage}
    (ReleaseCandidate.installed_call history pinned) original.2.1 balances sameBalances
  exact ⟨original.1,completed,original.2.2,sameBalances⟩

theorem eof {deposit exit : Receipt} {kind : Contract} {c : MessageCall.Context}
    (history : ReleaseCandidate.History deposit exit c.world) (pinned : ReleaseCandidate.CallInput kind c)
    {Hash LoadError : Type} [DecidableEq Hash]
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    {parent : ReferenceStorageView.Parent}
    {warm finalWarm : Warm} {pre final : Meter} {fuel : Nat} {events : List Event}
    {view : View} {output : ByteArray} {destinations : List Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts
      (initial (CallBridge.codeCall c (code pinned) 0) (entry c emptyHash accountsParent before codeParent shouldTransfer).2.storage) warm pre = some ((events,.eof view finalWarm final output),finalAccounts))
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites c.target).1 = .ok c.code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before c.world)
    (funded : c.value.toNat ≤ TransferFunding.worldBalance c.world c.caller)
    (mode : shouldTransfer = true ∨ c.value = ⟨0⟩)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage c.target q.toByteArray = SystemSpec.worldSlot c.world c.target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code pinned) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : c.calldata.size < UInt256.size) :
    (entry c emptyHash accountsParent before codeParent shouldTransfer).1 = .ok () ∧
    output = ByteArray.empty ∧ ReferenceSourceCompletedBalances.Completed emptyHash accountsParent before
      {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := view.storage}
      kind c parent events view true output ∧ finalAccounts.writes = (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts.writes ∧
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent
      {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts} c.entryWorld := by
  have original := ReferenceSourceFundedGuarantees.eof history pinned emptyHash accountsParent before codeParent shouldTransfer
    context actual loaded balances funded slots warmRelated grant fit
  have sameBalances := ReferenceSourceBalanceOutcome.evaluated emptyHash accountsParent before codeParent c shouldTransfer
    history balances funded mode actual
  have completed := ReferenceSourceCompletedBalances.of_completed emptyHash accountsParent before
    {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := view.storage}
    (ReleaseCandidate.installed_call history pinned) original.2.2.1 balances sameBalances
  exact ⟨original.1,original.2.1,completed,original.2.2.2,sameBalances⟩

#print axioms terminal
#print axioms eof
end Eip8282.Audit.Integrator.ReferenceSourceBalancedGuarantees

end

section

/-! ## ReferenceSourcePreparedBounds -/

/-! Source entry producer factored at the numeric bound actually consumed.
ReferenceCheckpointGuarantees derives this bound from the history BEFORE the
transaction and its literal prepayment, avoiding an artificial intermediate
History assumption. The earlier history-based public entry is unchanged. -/
namespace Eip8282.Audit.Integrator.ReferenceSourcePreparedBounds
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem code {kind : Contract} {c : MessageCall.Context} (input : ReleaseCandidate.CallInput kind c) :
    c.code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by
  cases kind <;> exact input.code

theorem prepared {Hash LoadError : Type} [DecidableEq Hash]
    {kind : Contract} (c : MessageCall.Context)
    (input : ReleaseCandidate.CallInput kind c)
    (total : TransferFunding.worldFunds c.world < UInt256.size)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    (parent : ReferenceStorageView.Parent)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites c.target).1 = .ok c.code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before c.world)
    (funded : c.value.toNat ≤ TransferFunding.worldBalance c.world c.caller)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage c.target q.toByteArray = SystemSpec.worldSlot c.world c.target q) :
    (entry c emptyHash accountsParent before codeParent shouldTransfer).1 = .ok () ∧
    ReferenceStorageView.Related parent (entry c emptyHash accountsParent before codeParent shouldTransfer).2.storage
      (CallBridge.codeCall c (code input) 0).entry.toState := by
  let start := fetched emptyHash accountsParent before codeParent c.target
  have startBalances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent start c.world := balances
  refine ⟨ReferenceSourceTransferFunding.enter_success emptyHash accountsParent start c shouldTransfer startBalances funded total,?_⟩
  have fetchedLoad : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      start.accounts codeParent start.codeWrites c.target).1 = .ok c.code := loaded
  have nonempty : c.code ≠ ByteArray.empty := by
    rw [code input]
    cases kind <;> decide +kernel
  have hashNonempty := ReferenceSourceValueTransfer.loaded_nonempty_hash emptyHash accountsParent start codeParent c.target fetchedLoad nonempty
  intro q
  change ReferenceStorageView.current parent (ReferenceSourceValueTransfer.enter emptyHash accountsParent start c.caller c.target c.value shouldTransfer).2.storage c.target q.toByteArray = _
  rw [ReferenceSourceValueTransfer.enter_protected_storage emptyHash accountsParent start c.caller c.target c.target c.value shouldTransfer hashNonempty]
  exact (slots q).trans (TransferFrame.codeCall_storage c (code input) 0 q).symm

#print axioms prepared
end Eip8282.Audit.Integrator.ReferenceSourcePreparedBounds

end
