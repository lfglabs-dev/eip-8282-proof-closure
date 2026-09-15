import Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction
import Eip8282.Audit.Integrator.ReferenceCheckedEvaluator
import Eip8282.Audit.Integrator.ReferenceCheckedPureForward
import Eip8282.Audit.Integrator.Topics.ReferenceChecked
import Eip8282.Audit.Integrator.ReferenceFullGasTotal
import Eip8282.Audit.Integrator.ReferenceSettledAccountJournal
import Eip8282.Audit.Integrator.Topics.ReferenceSystem2

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceCheckedSystemEntry -/

/-! Mandatory empty-data SYSTEM entry into the checked account evaluator.
The existing dispatcher supplies caller/value, fresh transaction journal,
empty warmth and both gas pools. Code load remains an independently meaningful
initial source observation; the storage parent is the represented block world.
No ordinary transaction fee/admission rule is applied to SYSTEM. Consumers:
ReferenceCheckedSystemExecution and ReferenceCheckedSystemTotal. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemEntry
open EvmYul EvmYul.EVM
open ReferenceSourceValueTransfer
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

structure Context where
  world : AccountMap .EVM
  genesis : BlockHeader
  blocks : ProcessedBlocks
  header : BlockHeader
  baseFee : UInt256

def call (kind : ReachableCalls.Contract) (c : Context) : MessageCall.Context :=
  ProtocolSystemCalls.call kind c.world c.genesis c.blocks c.header c.baseFee 8503 ByteArray.empty

theorem code (kind : ReachableCalls.Contract) (c : Context) :
    (call kind c).code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by cases kind <;> rfl

def xi (kind : ReachableCalls.Contract) (c : Context) := CallBridge.codeCall (call kind c) (code kind c) 0
def before (Hash : Type) : Tx Hash :=
  ⟨⟨fun _ => none,∅⟩,ProtocolSystemDispatchExtraction.freshTx,fun _ => none,fun _ _ => none⟩
def storageParent (c : Context) := ProtocolSystemDispatchExtraction.blockParent c.world
def meter (kind : ReachableCalls.Contract) (c : Context) :=
  let fields := ProtocolSystemDispatchExtraction.mandatory kind c.baseFee
  ReferenceChildMeter.init fields.executionGasGrant fields.stateGasReservoir

noncomputable def entered {Hash Error : Type} [DecidableEq Hash] (kind : ReachableCalls.Contract)
    (c : Context) (emptyHash : Hash) (accountsParent : Parent Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) :=
  ReferenceSourceValueTransfer.enter emptyHash accountsParent
    (ReferenceSourceDispatch.probe emptyHash accountsParent (before Hash) codeParent
      (ReachableCalls.address kind) (call kind c).value).2
    (call kind c).caller (call kind c).target (call kind c).value true

theorem constructed {deposit exit : TransactionAppendBudget.Receipt} (kind : ReachableCalls.Contract)
    (c : Context) (history : ReleaseCandidate.History deposit exit c.world) :
    ProtocolSystemDispatchExtraction.frame (ProtocolSystemDispatchExtraction.mandatory kind c.baseFee)
      c.world c.genesis c.blocks c.header 8503 = call kind c ∧
    ReleaseCandidate.CallInput kind (call kind c) ∧
    (∀ signature, ReferenceCallEntry.logs (call kind c) true signature = []) ∧
    ReferenceExecutionPotential.potential (meter kind c) = 30000000 := by
  have installed := (ReleaseCandidate.invariants history).2.2.2 kind |>.1
  refine ⟨ProtocolSystemDispatchExtraction.mandatory_call kind c.world c.genesis c.blocks c.header c.baseFee 8503 installed,
    ⟨rfl,rfl,rfl⟩,?_,rfl⟩
  intro signature
  simp [ReferenceCallEntry.logs,call,ProtocolSystemCalls.call,show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl]

theorem ready {Hash Error : Type} [DecidableEq Hash] (kind : ReachableCalls.Contract)
    (c : Context) (emptyHash : Hash) (accountsParent : Parent Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    ReferenceSourceDispatch.probe emptyHash accountsParent (before Hash) codeParent
      (ReachableCalls.address kind) (call kind c).value =
      (.ready (ReachableCalls.runtime kind),ReferenceTransferredFailure.fetched emptyHash accountsParent (before Hash) codeParent (ReachableCalls.address kind)) ∧
    entered kind c emptyHash accountsParent codeParent =
      (.ok (),ReferenceTransferredFailure.fetched emptyHash accountsParent (before Hash) codeParent (ReachableCalls.address kind)) := by
  have probe := ReferenceSourceDispatch.ready_fetched emptyHash accountsParent (before Hash) codeParent kind (call kind c).value loaded
  refine ⟨probe,?_⟩
  unfold entered
  rw [probe]
  simp [ReferenceSourceValueTransfer.enter,call,ProtocolSystemCalls.call]

theorem bindings {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (history : ReleaseCandidate.History deposit exit c.world)
    (emptyHash : Hash) (accountsParent : Parent Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    ReferenceStorageView.Related (storageParent c) (entered kind c emptyHash accountsParent codeParent).2.storage (xi kind c).entry.toState ∧
    SystemSpec.HasOwner (xi kind c).entry.toState ∧
    ReferenceSourceReadings.WarmRelated (∅ : ReferenceSourceReadings.Warm) (xi kind c).entry ∧
    ReferenceCheckedStackControlStep.DestinationContext (JournalInvariant.modelKind kind)
      (ReferenceInitialAccess.destinations (call kind c).code) := by
  rw [(ready kind c emptyHash accountsParent codeParent loaded).2]
  have installed := ReleaseCandidate.installed_call history (constructed kind c history).2.1
  refine ⟨?_,TransferFrame.pinned_codeCall_hasOwner (call kind c) installed (code kind c) 0,?_,?_⟩
  · intro k
    change SystemSpec.worldSlot c.world (ReachableCalls.address kind) (ProtocolSystemDispatchExtraction.keyOf k.toByteArray) = _
    rw [ProtocolSystemDispatchExtraction.keyOf_toByteArray]
    exact (TransferFrame.codeCall_storage (call kind c) (code kind c) 0 k).symm
  · intro a k
    change (a,k.toByteArray) ∈ (∅ : ReferenceSourceReadings.Warm) ↔ (∅ : Std.TreeSet _ _).contains (a,k) = true
    simp
  · have hc : (call kind c).code = ReferenceDecodeSites.code (ReferenceRuntimeSites.reference (JournalInvariant.modelKind kind)) := by cases kind <;> rfl
    unfold ReferenceCheckedStackControlStep.DestinationContext
    rw [hc]
    unfold ReferenceInitialAccess.destinations
    rw [ReferenceDecodeSites.scan_eq_sites]
    rfl

#print axioms code
#print axioms constructed
#print axioms ready
#print axioms bindings
end Eip8282.Audit.Integrator.ReferenceCheckedSystemEntry

end

section

/-! ## ReferenceCheckedSystemExecution -/

/-! Actual mandatory SYSTEM evaluation with computational fuel derived from
its source gas potential. This produces a supported completed local outcome;
it does not equate computational completion with successful EVM execution.
The extracted final dispatch, journal and events feed SystemTotal directly. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemExecution
open EvmYul EvmYul.EVM ReferenceCheckedSystemEntry
open ReferenceRuntimeView ReferenceSourceReadings ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

def fuel (kind : ReachableCalls.Contract) (c : Context) := ReferenceExecutionPotential.potential (meter kind c)+1

noncomputable def run {Hash Error : Type} [DecidableEq Hash] (kind : ReachableCalls.Contract)
    (c : Context) (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) :=
  ReferenceCheckedAccountEvaluator.eval accountsParent
    (ReferenceInitialAccess.destinations (call kind c).code) (storageParent c) ByteArray.empty (fuel kind c)
    (entered kind c emptyHash accountsParent codeParent).2.accounts
    (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage) ∅ (meter kind c)

theorem computed {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (history : ReleaseCandidate.History deposit exit c.world)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    ∃ events result finalAccounts,
      run kind c emptyHash accountsParent codeParent = some ((events,result),finalAccounts) ∧
      ReferenceSupportedOutcome.Finalized result := by
  obtain ⟨slots,owner,warm,context⟩ := bindings kind c history emptyHash accountsParent codeParent loaded
  have stack : (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage).stack.length ≤ 1024 := by simp [initial]
  have aligned := ReferenceActionMemoryBounds.empty_aligned (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage) rfl
  have enough : run kind c emptyHash accountsParent codeParent ≠ none :=
    ReferenceCheckedAccountEvaluator.sufficient context stack aligned (Nat.lt_succ_self _)
  cases actual : run kind c emptyHash accountsParent codeParent with
  | none => exact False.elim (enough actual)
  | some pair =>
    rcases pair with ⟨⟨events,result⟩,finalAccounts⟩
    refine ⟨events,result,finalAccounts,rfl,?_⟩
    exact ReferenceSupportedOutcome.account_evaluated (xi kind c) context actual slots owner warm
      (by rw [(constructed kind c history).2.2.2]) (by change 0 < UInt256.size; decide)

theorem extracted {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (history : ReleaseCandidate.History deposit exit c.world)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind))
    {events result finalAccounts}
    (actual : run kind c emptyHash accountsParent codeParent = some ((events,result),finalAccounts)) :
    ∃ finish finalWarm final,
      ReferenceCheckedRuntimeTrace.Run (JournalInvariant.modelKind kind) (storageParent c)
        (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage) ∅ (meter kind c)
        finish finalWarm final events ∧
      ReferenceCheckedDispatch.run (ReferenceInitialAccess.destinations (call kind c).code)
        (ReferenceAccountLookup.peek accountsParent (entered kind c emptyHash accountsParent codeParent).2.accounts (ReachableCalls.address kind)).isSome
        (storageParent c) finish finalWarm final ByteArray.empty = result ∧
      finalAccounts.writes = (entered kind c emptyHash accountsParent codeParent).2.accounts.writes := by
  obtain ⟨_,_,_,context⟩ := bindings kind c history emptyHash accountsParent codeParent loaded
  have erased := ReferenceCheckedAccountEvaluator.evaluated context actual
    (by simp [initial]) (ReferenceActionMemoryBounds.empty_aligned _ rfl)
  obtain ⟨finish,finalWarm,final,trace,last,_⟩ := ReferenceCheckedEvaluator.extract context erased.1
  exact ⟨finish,finalWarm,final,trace,last,erased.2⟩

#print axioms computed
#print axioms extracted
end Eip8282.Audit.Integrator.ReferenceCheckedSystemExecution

end

section

/-! ## ReferenceCheckedSystemJournal -/

/-! SYSTEM has no value movement or fee credits. Its actual runtime preserves
account writes; settlement retains live reads and uses the same receipt's
storage. Full source account observations are unchanged for every outcome,
without asserting full account equality between source and replay semantics. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemJournal
open EvmYul EvmYul.EVM ReferenceSourceValueTransfer ReferenceCheckedSystemEntry
open ReferenceSettledAccountJournal (journal)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem unchanged {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (emptyHash : Hash)
    (accountsParent : Parent Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind))
    (finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash))
    (receipt : ReferenceCheckedFrameOutcome.Receipt)
    (writes : finalAccounts.writes = (entered kind c emptyHash accountsParent codeParent).2.accounts.writes) :
    let settled := journal (before Hash) (entered kind c emptyHash accountsParent codeParent).2 finalAccounts receipt
    settled.accounts.writes = (before Hash).accounts.writes ∧
    settled.accounts.reads = finalAccounts.reads ∧
    settled.codeWrites = (before Hash).codeWrites ∧ settled.transient = (before Hash).transient ∧
    settled.storage = receipt.storage ∧
    ∀ a, account emptyHash accountsParent settled a = account emptyHash accountsParent (before Hash) a := by
  have entryEq := (ready kind c emptyHash accountsParent codeParent loaded).2
  rw [entryEq] at writes ⊢
  have beforeWrites : finalAccounts.writes = (before Hash).accounts.writes := writes
  dsimp only
  unfold journal
  dsimp only
  split
  · refine ⟨beforeWrites,rfl,rfl,rfl,rfl,?_⟩
    intro a
    unfold account ReferenceAccountLookup.peek
    rw [beforeWrites]
  · exact ⟨rfl,rfl,rfl,rfl,rfl,fun _ => rfl⟩

#print axioms unchanged
end Eip8282.Audit.Integrator.ReferenceCheckedSystemJournal

end

section

/-! ## ReferenceCheckedSystemOutcome -/

/-! Three predicates and literal receipt settlement for the same computed
SYSTEM outcome. No user fee path is used; any caught failure has actual local
rollback. The stronger ReferenceCheckedSystemDrainTotal now connects the
existing source resource witness to actual successful drain. -/
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

end

section

/-! ## ReferenceCheckedSystemReturn -/

/-! Accept the very RETURN paid by Whole, preserving its actual storage/logs,
full meter and exact extended output. Consumer: successful SYSTEM evaluation. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemReturn
open EvmYul EvmYul.EVM ReferenceRuntimeView ReferenceSourceReadings
open ReferenceMeterRollback ReferenceMeterBoundary
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def result (v : View) (off len : UInt256) (rest : List UInt256) (final : Meter) : ReferenceCheckedTerminalStep.End :=
  ⟨.returned,{v with stack := rest,memory := ReferenceReturnView.returnMemory v off len},final,
    (ReferenceReturnView.returnMemory v off len).extract off.toNat (off.toNat+len.toNat)⟩

theorem accepted {v : View} {off len : UInt256} {rest : List UInt256} {meter final : Meter}
    (shape : v.stack = off::len::rest) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (paid : runFull [.ordinary (ReferenceSystemSourcePayment.terminalCost v off len)] meter = some final)
    (previousOutput : ByteArray) :
    ReferenceCheckedTerminalStep.run .returned v meter previousOutput = .ok (result v off len rest final) := by
  have price := (ReferenceMemoryExpansionSource.aligned (words v) off.toNat len.toNat).2
  rw [←aligned] at price
  have amount : ReferenceSystemSourcePayment.terminalCost v off len =
      (ReferenceMemoryExpansionSource.calculate v.memory.size off.toNat len.toNat).cost := by
    unfold ReferenceSystemSourcePayment.terminalCost
    simp only [ReferenceReturnView.returnMemory,ReferenceMemoryOperations.extend,ReferenceMemoryView.buffer_size]
    simpa using price.symm
  rw [amount] at paid
  obtain ⟨charged,hc,rfl⟩ := ReferenceCheckedPureForward.ordinary_paid paid
  have capacity := ReferenceCheckedCopyLogStep.expanded_capacity v off len aligned
  simp only [ReferenceCheckedTerminalStep.run,show ReferenceCheckedTerminalStep.Halt.returned ≠ .stop by decide,
    if_false,shape,ReferenceSourceStackAdmission.pop,hc,ReferenceCheckedCopyLogStep.expanded,capacity,result,
    ReferenceReturnView.returnMemory]

theorem evaluated {v : View} {off len : UInt256} {rest : List UInt256} {meter final : Meter}
    {destinations : List Nat} {parent : ReferenceStorageView.Parent} {warm : Warm}
    (decoded : ReferenceDecodeSites.referenceDecode v.env.code v.pc = some (.RETURN,none))
    (shape : v.stack = off::len::rest) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (paid : runFull [.ordinary (ReferenceSystemSourcePayment.terminalCost v off len)] meter = some final)
    (budget : Nat) (output : ByteArray) :
    ReferenceCheckedEvaluator.eval destinations true parent output (budget+1) v warm meter =
      some ([],.terminal (result v off len rest final)) := by
  have selected := ReferenceCheckedSourceSelection.read (h := .terminal .returned) decoded
  have actual := accepted shape aligned paid output
  simp only [ReferenceCheckedEvaluator.eval,ReferenceCheckedDispatch.run,selected,
    ReferenceCheckedDispatch.runHandler,actual]

#print axioms accepted
#print axioms evaluated
end Eip8282.Audit.Integrator.ReferenceCheckedSystemReturn

end

section

/-! ## ReferenceCheckedSystemTraceForward -/

/-! The paid SYSTEM prefix is the actual checked evaluator prefix, with the
same views, warmth, ordered meter events and arbitrary continuation budget.
Consumer: successful mandatory SYSTEM return on the already computed run. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemTraceForward
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceMeterPath ReferenceCheckedDispatch ReferenceSystemReadingsTrace
open ReferenceSourceReplayTrace (instruction)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def isHandler : Dispatch → Bool
  | .handler _ => true
  | _ => false

theorem site_table (kind : Kind) :
    (ReferenceDecodeSites.sites (ReferenceRuntimeSites.reference kind)).all
      (fun pc => isHandler (read (ReferenceDecodeSites.code (ReferenceRuntimeSites.reference kind)) pc)) = true := by
  cases kind <;> decide +kernel

theorem selected {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View} {pre post : EVM.State}
    (related : Related parent v pre) (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (nonhalting : H post.toMachineState (decodeAt pre).1 = none) :
    ∃ h, read v.env.code v.pc = .handler h := by
  have member := ReferenceRuntimeSites.nonhalting_site site nonhalting
  have yes := List.all_eq_true.mp (site_table kind) _ member
  rw [←ReferenceRuntimeSites.code_eq,←site.1,←related.env,←related.pc] at yes
  cases selected : read v.env.code v.pc with
  | handler h => exact ⟨h,rfl⟩
  | eof => simp [selected,isHandler] at yes
  | invalid t => simp [selected,isHandler] at yes
  | unsupported t => simp [selected,isHandler] at yes

/-- No post-stack premise: the actual Z guard and literal same action derive it.
The continuation equation identifies this prefix inside the executable fold. -/
theorem coupled {kind : Kind} {parent : ReferenceStorageView.Parent} {created : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {warm finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    {destinations : List Nat} {meter final : Meter}
    (coupled : Coupled kind parent created fuel pre v warm trace rem post finish finalWarm events)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (aligned : ReferenceActionMemoryBounds.Aligned v)
    (paid : runFull events meter = some final) :
    ReferenceCheckedRuntimeTrace.Run kind parent v warm meter finish finalWarm final events ∧
    ∀ budget output, ReferenceCheckedEvaluator.eval destinations true parent output (events.length+budget) v warm meter =
      (ReferenceCheckedEvaluator.eval destinations true parent output budget finish finalWarm final).map
        (fun (tail,result) => (events++tail,result)) := by
  induction coupled generalizing meter final with
  | refl =>
    have eq : meter = final := by simpa [runFull,ReferenceMeterPath.run,core,update] using paid
    subst final
    refine ⟨.refl _ _ _,?_⟩
    intro budget output
    simp only [List.length_nil,Nat.zero_add,List.nil_append]
    cases ReferenceCheckedEvaluator.eval destinations true parent output budget _ _ _ <;> rfl
  | @cons edgeFuel gasCost rem pre middle post v next finish warm finalWarm trace event events
      actual decoded related nextRelated warmRelated createdEq action readings oldPrice sourcePrice tail ih =>
    obtain ⟨mid,hz,hs,hh⟩ := actual
    obtain ⟨h,hread⟩ := selected related site hh
    obtain ⟨arg,hdecode⟩ := read_handler hread
    have instrEq : instruction v = (opcode h,arg) := by
      simp only [instruction,hdecode,Option.getD_some]
    have oldInstr : decodeAt pre = (opcode h,arg) := decoded.trans instrEq
    have act : ReferenceSystemAction.Action kind parent (instruction v) v next := by
      rw [instrEq,←oldInstr]; exact action
    have bounds := ReferenceAcceptedStack.bounds hz
    rw [oldInstr,←related.stack] at bounds
    have postbound := ReferenceSystemStackBound.handler (by rw [←oldInstr]; exact action) bounds.1 bounds.2
    have pcfit : v.pc+1 < UInt256.size := by
      have fit := ReferenceRuntimeSites.pc_fit site
      rw [related.pc]
      omega
    change runFull ([event]++events) meter = some final at paid
    rw [ReferenceCheckedRuntimeTrace.runFull_append] at paid
    obtain ⟨nextMeter,headPaid,tailPaid⟩ := Option.bind_eq_some_iff.mp paid
    have hprice : SourcePrice parent v warm next (instruction v).1 event := by
      rw [instrEq,←oldInstr]; exact sourcePrice
    have actualRun : ∀ output, run destinations true parent v warm meter output =
        .continued next (warmAfter (decodeAt pre).1 v warm) nextMeter event := by
      intro output
      rw [ReferenceCheckedDispatch.run,hread]
      simpa only [instrEq,oldInstr] using ReferenceCheckedSystemForward.handler output context
        (congrArg Prod.fst instrEq) act hprice postbound aligned pcfit headPaid
    have nextSite := RuntimeExecutionScope.accepted_next site hz hs hh
    have nextAligned := ReferenceActionMemoryBounds.preserves_alignment (.base act) aligned
    obtain ⟨checked,continuation⟩ := ih nextSite nextAligned tailPaid
    refine ⟨.cons (ReferenceCheckedDispatch.step context (actualRun ByteArray.empty)) checked,?_⟩
    intro budget output
    simp only [List.length_cons,Nat.add_right_comm _ 1 budget,ReferenceCheckedEvaluator.eval,actualRun]
    rw [continuation]
    simp only [Option.map_map]
    congr 1

#print axioms site_table
#print axioms selected
#print axioms coupled
end Eip8282.Audit.Integrator.ReferenceCheckedSystemTraceForward

end
