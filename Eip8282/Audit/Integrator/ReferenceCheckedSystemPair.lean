import Eip8282.Audit.Integrator.ReferenceSystemBlockParent
import Eip8282.Audit.Integrator.ReferenceSystemBlockAccess

/-! Ordered checked Deposit/Exit computations with actual receipt storage
incorporation. Exit's evaluator is run on Deposit's committed parent. The
three local predicates retain the initial-world owner projection: the foreign
commit theorem proves that projection unchanged for Exit. The further
ReferenceCheckedSystemBlock consumer reconstructs the sequential replay worlds
and their global storage relations; neither theorem asserts canonical blocks.
The source BAL storage update precedes each merge; account/code writes are
proved empty and the next call receives a fresh transaction journal. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemPair
open EvmYul EvmYul.EVM ReferenceCheckedSystemEntry
open ReferenceRuntimeView ReferenceSourceReadings ReferenceCheckedDispatch
open ReferenceSystemBlockFootprint ReferenceSystemBlockAccess
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

noncomputable def runOn {Hash Error : Type} [DecidableEq Hash] (kind : ReachableCalls.Contract)
    (c : Context) (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (parent : ReferenceStorageView.Parent) :=
  ReferenceCheckedAccountEvaluator.eval accountsParent
    (ReferenceInitialAccess.destinations (call kind c).code) parent ByteArray.empty (ReferenceCheckedSystemExecution.fuel kind c)
    (entered kind c emptyHash accountsParent codeParent).2.accounts
    (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage) ∅ (meter kind c)

structure Certificate {Hash Error : Type} [DecidableEq Hash] (kind : ReachableCalls.Contract)
    (c : Context) (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (parent : ReferenceStorageView.Parent) where
  events : List ReferenceMeterPath.Event
  ended : ReferenceCheckedTerminalStep.End
  finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)
  finalWarm : Warm
  receipt : ReferenceCheckedFrameOutcome.Receipt
  keys : List UInt256
  actual : runOn kind c emptyHash accountsParent codeParent parent = some ((events,.terminal ended),finalAccounts)
  claims : ReferenceCheckedTheta.Completed kind (call kind c) parent events ended.view true ended.output
  halt : ended.halt = .returned
  owner : ended.view.env.codeOwner = ReachableCalls.address kind
  settled : ReferenceCheckedFrameOutcome.settle (before Hash).storage [] finalWarm (.terminal ended) = .returned receipt
  resources : ReferenceSystemOutputMeter.Facts (ProtocolSystemDispatchExtraction.mandatory kind c.baseFee).stateGasReservoir receipt.meter
  receiptFields : receipt.error = none ∧ receipt.storage = ended.view.storage ∧ receipt.output = ended.output ∧
    receipt.meter = ended.meter ∧ receipt.logsForParent = ended.view.logs
  support : Support (ReachableCalls.address kind) receipt.storage keys
  coherent : ReferenceSystemBlockParent.CompletedRun (JournalInvariant.modelKind kind) parent
    (ReferenceInitialAccess.destinations (call kind c).code)
    (ReferenceAccountLookup.peek accountsParent (entered kind c emptyHash accountsParent codeParent).2.accounts (ReachableCalls.address kind)).isSome
    (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage) ∅ (meter kind c)
    events ended finalWarm
  journal :
    let settled := ReferenceSettledAccountJournal.journal (before Hash)
      (entered kind c emptyHash accountsParent codeParent).2 finalAccounts receipt
    settled.accounts.writes = (before Hash).accounts.writes ∧
    settled.accounts.reads = finalAccounts.reads ∧
    settled.codeWrites = (before Hash).codeWrites ∧ settled.transient = (before Hash).transient ∧
    settled.storage = receipt.storage ∧
    ∀ a, ReferenceSourceValueTransfer.account emptyHash accountsParent settled a =
      ReferenceSourceValueTransfer.account emptyHash accountsParent (before Hash) a

theorem one {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (history : ReleaseCandidate.History deposit exit c.world)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    Nonempty (Certificate kind c emptyHash accountsParent codeParent (storageParent c)) := by
  obtain ⟨events,ended,accounts,warm,receipt,keys,actual,claims,halt,owner,settled,resources,
    error,storage,output,gas,logs,support,coherent,journal⟩ :=
    ReferenceSystemBlockReceipt.verified kind c history emptyHash accountsParent codeParent loaded
  have completion : ReferenceCheckedTheta.Completed kind (call kind c) (storageParent c) events ended.view true ended.output := by
    simpa only [ReferenceCheckedSystemOutcome.Claims,halt,ne_eq,reduceCtorEq,not_false_eq_true,decide_true] using claims
  exact ⟨⟨events,ended,accounts,warm,receipt,keys,actual,completion,halt,owner,settled,resources,
    ⟨error,storage,output,gas,logs⟩,support,coherent,journal⟩⟩

theorem on_parent {Hash Error : Type} [DecidableEq Hash] {kind : ReachableCalls.Contract}
    {c : Context} {emptyHash : Hash} {accountsParent : ReferenceSourceValueTransfer.Parent Hash}
    {codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error} {p q : ReferenceStorageView.Parent}
    (cert : Certificate kind c emptyHash accountsParent codeParent p)
    (context : ReferenceCheckedStackControlStep.DestinationContext (JournalInvariant.modelKind kind)
      (ReferenceInitialAccess.destinations (call kind c).code))
    (same : ReferenceSystemBlockParent.AtOwner q p (ReachableCalls.address kind)) :
    Nonempty (Certificate kind c emptyHash accountsParent codeParent q) := by
  have equal := ReferenceSystemBlockParent.evaluated context accountsParent
    (ReferenceCheckedSystemExecution.fuel kind c)
    (entered kind c emptyHash accountsParent codeParent).2.accounts
    (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage)
    ∅ (meter kind c) ByteArray.empty same (by simp [initial])
    (ReferenceActionMemoryBounds.empty_aligned _ rfl)
  refine ⟨{cert with actual := equal.trans cert.actual, claims := ?_, coherent := ?_}⟩
  · exact ReferenceSystemBlockParent.completion (by simpa only [cert.owner] using same) cert.claims
  · exact ReferenceSystemBlockParent.completed_run (fun key => (same key).symm) cert.coherent
      (by simp [initial]) (ReferenceActionMemoryBounds.empty_aligned _ rfl)

structure Pair {Hash Error : Type} [DecidableEq Hash]
    (c : Context) (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (builder : Builder) where
  deposit : Certificate .deposit c emptyHash accountsParent codeParent (storageParent c)
  middleBuilder : Builder
  depositIncorporated : incorporate (storageParent c) (ReachableCalls.address .deposit)
    deposit.receipt.storage deposit.keys builder =
      some (ReferenceStorageView.commit (storageParent c) deposit.receipt.storage,middleBuilder)
  exit : Certificate .exit c emptyHash accountsParent codeParent
    (ReferenceStorageView.commit (storageParent c) deposit.receipt.storage)
  finalBuilder : Builder
  exitIncorporated : incorporate (ReferenceStorageView.commit (storageParent c) deposit.receipt.storage)
    (ReachableCalls.address .exit) exit.receipt.storage exit.keys middleBuilder =
      some (ReferenceStorageView.commit (ReferenceStorageView.commit (storageParent c) deposit.receipt.storage)
        exit.receipt.storage,finalBuilder)

/-- No supplied intermediate equality, trace or successful outcome: both
certificates and their sequential parent are constructed from the entry domain. -/
theorem verified {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (c : Context) (history : ReleaseCandidate.History deposit exit c.world)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (builder : Builder)
    (loaded : ∀ kind, (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    Nonempty (Pair c emptyHash accountsParent codeParent builder) := by
  obtain ⟨dep⟩ := one .deposit c history emptyHash accountsParent codeParent (loaded .deposit)
  obtain ⟨middle,builtDeposit⟩ := incorporated (storageParent c) (ReachableCalls.address .deposit)
    dep.receipt.storage dep.keys builder
  obtain ⟨independentExit⟩ := one .exit c history emptyHash accountsParent codeParent (loaded .exit)
  have same := ReferenceSystemBlockParent.foreign dep.support (storageParent c)
    (ReachableCalls.address .exit) (by decide +kernel)
  obtain ⟨ext⟩ := on_parent independentExit
    (bindings .exit c history emptyHash accountsParent codeParent (loaded .exit)).2.2.2 same
  obtain ⟨final,builtExit⟩ := incorporated (ReferenceStorageView.commit (storageParent c) dep.receipt.storage)
    (ReachableCalls.address .exit) ext.receipt.storage ext.keys middle
  exact ⟨⟨dep,middle,builtDeposit,ext,final,builtExit⟩⟩

#print axioms one
#print axioms on_parent
#print axioms verified
end Eip8282.Audit.Integrator.ReferenceCheckedSystemPair
