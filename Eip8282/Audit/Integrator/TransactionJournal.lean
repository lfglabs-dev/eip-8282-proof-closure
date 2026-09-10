import Eip8282.Audit.Integrator.JournalCheckpoints
import Eip8282.Audit.Integrator.TransactionJournalEdges

/-!
# The actual transaction carries the recursive journal through settlement

The literal Υ checkpoint supplies root coherence and deletion exclusion. Its
real provisional result supplies the final journal; the same result's refund,
beneficiary payment and cleanup preserve protected code and persistent slots.
Funding histories and execution work are linked to this very transaction. The
external-credit bound and protocol admission still require protocol producers.
-/
namespace Eip8282.Audit.Integrator.TransactionJournal
open EvmYul EvmYul.EVM
open NestedEvents RefundAccounting JournalExecution
open ReachableCalls (Contract address runtime)
open TransactionEventBounds (request)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Admission debits only balance/nonce. The actual entry starts with an empty
deletion set, and actual code selection supplies protected owner coherence. -/
theorem ready {kind : Contract} (c : Context) {account : Account .EVM}
    (ha : TransactionFunding.Admission c account) {budget : Nat}
    (hi : JournalInvariant.Invariant kind budget c.world) :
    Ready kind budget (request c) := by
  have hj : Journal kind budget c.checkpoint c.entrySubstate :=
    ⟨JournalInvariant.frame hi (TransactionJournalEdges.checkpoint_frame c ha (address kind)),
      by change address kind ∉ (∅ : Std.TreeSet AccountAddress compare); simp⟩
  unfold request
  split
  · exact hj
  · rename_i target ht
    refine ⟨hj,?_⟩
    intro he
    constructor
    · change toExecute .EVM c.checkpoint target = _
      change target = address kind at he
      rw [he]
      exact CallOwnerCoherence.installed_toExecute hj.1.1
    · rfl

/-- This is a concrete evaluator resource choice, separate from EVM gas. -/
theorem adequate (c : Context) (h : 5*(c.entryGas.toNat+1) ≤ c.fuel) :
    FuelAdequacy.Adequate (request c) := by
  apply FuelAdequacy.uniform_bound
  rw [TransactionEventBounds.request_gas]
  have hf : (request c).fuel = c.fuel := by unfold request; split <;> rfl
  rw [hf]
  exact h

theorem data_fit (c : Context) (h : c.transaction.base.data.size < UInt256.size) :
    NestedCallDataFit.RootFits (request c) := by
  unfold request
  split
  · trivial
  · exact h

/-- The actual Υ provisional tuple is obtained from the certified root result,
including both transaction statuses, rather than from an assumed post-state. -/
theorem provisional {kind : Contract} (c : Context)
    {budget : Nat} (done_ : Done kind budget (request c) (request c).eval)
    {world : World} {remaining : UInt256} {ss : Substate} {status : Bool}
    (hp : c.provisional = .ok (world,remaining,ss,status)) : Journal kind budget world ss := by
  rcases TransactionJournalEdges.provisional_cases c hp with ⟨hr,target,created,out,he⟩ |
    ⟨target,hr,created,out,he⟩
  · unfold request at done_
    rw [hr] at done_
    exact done_ target created world remaining ss status out he
  · unfold request at done_
    rw [hr] at done_
    exact done_ created world remaining ss status out he

/-- Finalization retains the same protected journal, including status=false.
The deletion exclusion consumed by cleanup is derived from actual execution. -/
theorem settled {kind : Contract} (c : Context) {budget : Nat}
    (done_ : Done kind budget (request c) (request c).eval)
    {world : World} {ss : Substate} {status : Bool} {used : UInt256}
    (hr : c.result = .ok (world,ss,status,used)) : Journal kind budget world ss := by
  rw [TransactionFunding.result_equation] at hr
  cases hp : c.provisional with
  | error err => simp only [hp,Bind.bind,Except.bind] at hr; cases hr
  | ok result =>
    obtain ⟨pw,remaining,a,z⟩ := result
    have hj := provisional c done_ hp
    have hf := TransactionJournalEdges.settled_codeAt_frame c pw remaining a hj.1.1 hj.2
    simp only [hp,Bind.bind,Except.bind,pure,Except.pure] at hr
    cases hr
    exact ⟨JournalInvariant.frame hj.1 hf,hj.2⟩

/-- One initialized pre-journal and one linked funding history imply the
complete actual transaction's post-journal and all nested call checkpoints.
No intermediate storage invariant, child postcondition or no-fuel-exception
condition is supplied. The event budget counts work, not surviving records. -/
theorem completed {kind : Contract} {initial : World} {credits budget : Nat}
    (c : Context) {account : Account .EVM}
    (history : FundingHistory.Trace initial credits c.world)
    (ha : TransactionFunding.Admission c account)
    (funds : TransferFunding.worldFunds initial+credits < FundedDomain.fundingCeiling)
    (fit : c.transaction.base.data.size < UInt256.size)
    (resources : 5*(c.entryGas.toNat+1) ≤ c.fuel)
    (hi : JournalInvariant.Invariant kind budget c.world)
    {world : World} {ss : Substate} {status : Bool} {used : UInt256}
    (hr : c.result = .ok (world,ss,status,used)) (bound : budget+used.toNat < 2^128) :
    ∃ tree, Cert (request c) (request c).eval tree ∧ tree.count ≤ used.toNat ∧
      Journal kind (budget+tree.count) world ss ∧
      ∀ (path : EventTree.Address) (f : Nat) (a : ThetaArgs) (r : ThetaResult),
        ThetaAt (request c) (request c).eval tree path f a r →
        Ready kind (budget+NestedJournalBudget.before tree path) (.theta f a) := by
  obtain ⟨tree,cert,_,hcount,_⟩ := TransactionEventBounds.transaction_events c hr
  have inputs := NestedProtectedJournal.inputs_from_history c history ha funds (data_fit c fit) tree
  obtain ⟨done_,calls⟩ := JournalCheckpoints.from_resources cert (adequate c resources)
    budget (by omega) (ready c ha hi) inputs
  exact ⟨tree,cert,hcount,settled c done_ hr,calls⟩

/-- Each protected call's three observations bind to the actual transaction
trace and actual local result, even when an ancestor later rolls it back. -/
theorem observed {kind : Contract} {initial : World} {credits budget : Nat}
    (c : Context) {account : Account .EVM}
    (history : FundingHistory.Trace initial credits c.world)
    (ha : TransactionFunding.Admission c account)
    (funds : TransferFunding.worldFunds initial+credits < FundedDomain.fundingCeiling)
    (fit : c.transaction.base.data.size < UInt256.size)
    (resources : 5*(c.entryGas.toNat+1) ≤ c.fuel)
    (hi : JournalInvariant.Invariant kind budget c.world)
    {tree : EventTree} (cert : Cert (request c) (request c).eval tree)
    (bound : budget+tree.count < 2^128)
    {path : EventTree.Address} {fuel : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt (request c) (request c).eval tree path (fuel+1) a r)
    (ht : a.target = address kind)
    {created : Created} {world : World} {gas : UInt256} {ss : Substate}
    {status : Bool} {out : ByteArray}
    (hr : r = .ok (created,world,gas,ss,status,out)) :
    ∃ inner, Cert (.theta (fuel+1) a) r inner ∧
      Journal kind (budget+NestedJournalBudget.before tree path+inner.count) world ss ∧
      NestedProtectedJournal.Observed kind (a.context fuel (runtime kind))
        created world ss status out := by
  exact JournalCheckpoints.observed cert (adequate c resources) budget bound (ready c ha hi)
    (NestedProtectedJournal.inputs_from_history c history ha funds (data_fit c fit) tree) loc ht hr

#print axioms ready
#print axioms adequate
#print axioms data_fit
#print axioms provisional
#print axioms settled
#print axioms completed
#print axioms observed
end Eip8282.Audit.Integrator.TransactionJournal
