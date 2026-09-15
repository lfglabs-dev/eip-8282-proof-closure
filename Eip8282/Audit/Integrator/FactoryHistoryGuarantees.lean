import Eip8282.Audit.Integrator.Topics.Factory2
import Eip8282.Audit.Integrator.HistoryCommittedGuarantees
import Eip8282.Audit.Integrator.LedgerCreditSafety

/-! Composition from an actual factory deployment receipt through all later
admitted transaction histories. Neither an initialized protected invariant nor
a numerical wealth ceiling is supplied: the former is produced by deployment,
the latter by the literal genesis/credit ledger. Canonical factory installation,
hash binding, admission and ledger/block reference extraction remain explicit. -/
namespace Eip8282.Audit.Integrator.FactoryHistoryGuarantees
open EvmYul EvmYul.EVM
open NestedEvents FactoryRuntimeEntry FactoryChildResources
open ReachableCalls (Contract address)
open JournalInvariant (modelKind Invariant)
open TransactionAppendBudget (Receipt BlockReceipt)
open TransactionCommittedEffects
open QueueInvariant SystemSpec
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Independent deployment inputs, with no desired post-world, call-success,
fee-loop termination, protected invariant or recipient balance premise. -/
structure Inputs (kind : Contract) (c : RefundAccounting.Context) where
  steps : Nat
  sender : Account .EVM
  factory : Account .EVM
  admission : TransactionFunding.Admission c sender
  installed : c.world.get? factoryAddress = some factory
  code : factory.code = FactoryRuntimeEntry.runtime
  nonce : factory.nonce.toNat < 2^64-1
  distinct : c.sender ≠ factoryAddress
  recipient : c.transaction.base.recipient = some factoryAddress
  data : c.transaction.base.data = calldata (modelKind kind)
  gas : 1000000 ≤ c.entryGas.toNat
  gasLimit : c.transaction.base.gasLimit.toNat ≤ 2^64
  stepsBound : 13 ≤ steps
  fuel : c.fuel = steps+19
  collision : ((childArgs (modelKind kind)
    (FactoryCallEntry.args (TransactionFactoryEntry.call c)) c.entryGas 0).context
    (steps+1)).collision (CreationSettlement.address (preimage (modelKind kind))) = false
  addressBinding : CreationSettlement.address (preimage (modelKind kind)) = address kind

/-- The invariant belongs to the final world of this exact real Υ receipt.
Its successful status and empty log/deletion sets are derived, not assumed. -/
theorem deployment_seed {kind : Contract} (r : Receipt) (inputs : Inputs kind r.call)
    (funds : TransferFunding.worldFunds r.call.world < UInt256.size) :
    r.success = true ∧ Invariant kind 0 r.world ∧
      r.substate.logSeries = #[] ∧ r.substate.selfDestructSet = ∅ ∧
      ∀ other budget, other ≠ kind → Invariant other budget r.call.world → Invariant other budget r.world := by
  obtain ⟨w,ss,used,he,hi,hl,hs,hother⟩ := FactoryInitializedTransaction.initializes kind r.call
    inputs.steps inputs.sender inputs.factory inputs.admission inputs.installed inputs.code
    inputs.nonce inputs.distinct inputs.recipient funds inputs.data inputs.gas inputs.gasLimit
    inputs.stepsBound inputs.fuel inputs.collision inputs.addressBinding
  have same := r.executed.symm.trans he
  simp only [Except.ok.injEq,Prod.mk.injEq] at same
  obtain ⟨hw,hss,hz,_⟩ := same
  rw [hw,hss,hz]
  exact ⟨rfl,hi,hl,hs,hother⟩

/-- The funding history uses the very same committed transaction receipt. -/
theorem funding_seed {kind : Contract} (r : Receipt) (inputs : Inputs kind r.call)
    {genesis : World} {credits : Nat}
    (prior : FundingHistory.Trace genesis credits r.call.world) :
    FundingHistory.Trace genesis credits r.world := by
  simpa only [Nat.add_zero] using FundingHistory.Trace.next prior
    (FundingHistory.Step.transaction r.call inputs.sender inputs.admission r.executed)

/-- All three guarantees and committed effects at any later receipt position,
with the initial protected invariant produced by the actual factory transaction.
Canonical ledger extraction and protocol admission are not adopted by this
conditional theorem. The same literal ledger derives every numeric funds bound. -/
theorem from_genesis_deployment {kind : Contract} (deployment : Receipt)
    (inputs : Inputs kind deployment.call) {final : World}
    {baseCredits credits pow withdrawals migrations : Nat} {receipts : List Receipt}
    (prior : FundingHistory.Trace GenesisFundingWorld.world baseCredits deployment.call.world)
    (history : ActualJournalHistory.Trace deployment.world receipts credits final)
    (ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world pow withdrawals migrations
      (baseCredits+credits) final)
    (counts : ProtocolCreditEnvelope.Counts pow withdrawals migrations)
    (blocks : List BlockReceipt) (listed : receipts = blocks.flatMap (fun b => b.receipts))
    (slots : (blocks.map (fun b => b.slot)).Nodup)
    {i : Nat} {r : Receipt} (atIndex : receipts[i]? = some r) :
    deployment.success = true ∧ ∃ queue : JournalPathQueues.Queue kind,
      Represents (modelKind kind) (worldSlot r.call.world (address kind)) queue ∧
      Effects kind r queue ∧ LocalGuarantees kind r ∧
      (ProtectedLogFrame.project (address kind) r.substate).length =
        JournalRetainedWork.count kind (TransactionEventBounds.request r.call)
          (TransactionEventBounds.request r.call).eval (TransactionAppendBudget.tree r) := by
  have hbudget := LedgerCreditSafety.genesis_budget ledger counts
  have hprior := FundingHistory.trace_funds prior
  have hworld : TransferFunding.worldFunds deployment.call.world < UInt256.size := by omega
  obtain ⟨hs,hi,_,_,_⟩ := deployment_seed deployment inputs hworld
  exact ⟨hs,HistoryCommittedGuarantees.from_genesis_ledger history
    (funding_seed deployment inputs prior) hi ledger counts blocks listed slots atIndex⟩

/-- Two sequential actual deployment receipts establish both initial
invariants in the same final world. Deploying Exit preserves Deposit's records,
code and controls through every enclosing settlement. -/
theorem two_seeds (deposit exit : Receipt) (dep : Inputs .deposit deposit.call)
    (ext : Inputs .exit exit.call) (linked : exit.call.world = deposit.world)
    {genesis : World} {credits : Nat}
    (prior : FundingHistory.Trace genesis credits deposit.call.world)
    (funds : TransferFunding.worldFunds genesis+credits < UInt256.size) :
    deposit.success = true ∧ exit.success = true ∧
      FundingHistory.Trace genesis credits exit.world ∧
      ∀ kind, Invariant kind 0 exit.world := by
  have hdBound := (FundingHistory.trace_funds prior).trans_lt funds
  obtain ⟨hd,hdInv,_,_,_⟩ := deployment_seed deposit dep hdBound
  have hdFunding := funding_seed deposit dep prior
  have heFunding : FundingHistory.Trace genesis credits exit.call.world := by
    rw [linked]
    exact hdFunding
  obtain ⟨he,heInv,_,_,hother⟩ := deployment_seed exit ext
    ((FundingHistory.trace_funds heFunding).trans_lt funds)
  have hdInv' : Invariant .deposit 0 exit.call.world := by rw [linked]; exact hdInv
  refine ⟨hd,he,funding_seed exit ext heFunding,?_⟩
  intro kind
  cases kind with
  | deposit => exact hother .deposit 0 (by decide) hdInv'
  | exit => exact heInv

/-- Both pinned contracts, one actual deployment/history/ledger, and all three
guarantees at every subsequent transaction position. Protocol representation
and policy choices remain explicit unresolved producers of these inputs. -/
theorem from_genesis_both (deposit exit : Receipt) (dep : Inputs .deposit deposit.call)
    (ext : Inputs .exit exit.call) (linked : exit.call.world = deposit.world)
    {final : World} {baseCredits credits pow withdrawals migrations : Nat}
    {receipts : List Receipt}
    (prior : FundingHistory.Trace GenesisFundingWorld.world baseCredits deposit.call.world)
    (history : ActualJournalHistory.Trace exit.world receipts credits final)
    (ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world pow withdrawals migrations
      (baseCredits+credits) final)
    (counts : ProtocolCreditEnvelope.Counts pow withdrawals migrations)
    (blocks : List BlockReceipt) (listed : receipts = blocks.flatMap (fun b => b.receipts))
    (slots : (blocks.map (fun b => b.slot)).Nodup)
    {i : Nat} {r : Receipt} (atIndex : receipts[i]? = some r) :
    deposit.success = true ∧ exit.success = true ∧
    ∀ kind, ∃ queue : JournalPathQueues.Queue kind,
      Represents (modelKind kind) (worldSlot r.call.world (address kind)) queue ∧
      Effects kind r queue ∧ LocalGuarantees kind r ∧
      (ProtectedLogFrame.project (address kind) r.substate).length =
        JournalRetainedWork.count kind (TransactionEventBounds.request r.call)
          (TransactionEventBounds.request r.call).eval (TransactionAppendBudget.tree r) := by
  have hbudget := LedgerCreditSafety.genesis_budget ledger counts
  obtain ⟨hd,he,hfunds,hinv⟩ := two_seeds deposit exit dep ext linked prior (by omega)
  exact ⟨hd,he,fun kind => HistoryCommittedGuarantees.from_genesis_ledger history hfunds
    (hinv kind) ledger counts blocks listed slots atIndex⟩

#print axioms deployment_seed
#print axioms funding_seed
#print axioms from_genesis_deployment
#print axioms two_seeds
#print axioms from_genesis_both
end Eip8282.Audit.Integrator.FactoryHistoryGuarantees
