import Eip8282.Audit.Integrator.ActualJournalHistory

/-! Actual transaction positions expose their real prefix history. The prefix
includes earlier SYSTEM calls and credits, and its invariant is derived from
the initialized seed. Nested observations bind to that transaction's canonical
certificate. Equal receipt values at different list positions stay separate. -/
namespace Eip8282.Audit.Integrator.ActualHistoryCalls
open EvmYul EvmYul.EVM
open NestedEvents ActualJournalHistory
open TransactionAppendBudget (Receipt BlockReceipt)
open ReachableCalls (Contract address runtime)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Every list position has the actual preceding world history and original
input admission/resources, including positions before later failed calls. -/
theorem transaction_prefix {initial final : World} {receipts : List Receipt} {credits : Nat}
    (h : Trace initial receipts credits final) {i : Nat} {r : Receipt}
    (atIndex : receipts[i]? = some r) :
    ∃ prefixCredits, prefixCredits ≤ credits ∧
      Trace initial (receipts.take i) prefixCredits r.call.world ∧
      ∃ account, TransactionFunding.Admission r.call account ∧
        r.call.transaction.base.data.size < UInt256.size ∧
        5*(r.call.entryGas.toNat+1) ≤ r.call.fuel := by
  induction h generalizing i r with
  | initial => simp at atIndex
  | @transaction receipts credits before prior last linked account admission fit resources ih =>
    by_cases hi : i < receipts.length
    · rw [List.getElem?_append_left hi] at atIndex
      obtain ⟨pc,hpc,ht,acc,ha,hfit,hres⟩ := ih atIndex
      refine ⟨pc,hpc,?_,acc,ha,hfit,hres⟩
      rw [List.take_append_of_le_length (Nat.le_of_lt hi)]
      exact ht
    · have hil := (List.getElem?_eq_some_iff.mp atIndex).1
      have hei : i = receipts.length := by simp only [List.length_append,List.length_singleton] at hil; omega
      subst i
      rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.getElem?_cons_zero] at atIndex
      cases atIndex
      refine ⟨credits,Nat.le_refl _,?_,account,admission,fit,resources⟩
      rw [List.take_append_length,linked]
      exact prior
  | system prior t sender zero fit ih => exact ih atIndex
  | credit prior recipient amount ih =>
    obtain ⟨pc,hpc,ht,account,ha,hfit,hres⟩ := ih atIndex
    exact ⟨pc,by omega,ht,account,ha,hfit,hres⟩

/-- Prefix work plus this same transaction's full marked work is bounded by
all receipt work. No Finset quotient or persistent-record interpretation. -/
theorem position_work {receipts : List Receipt} {i : Nat} {r : Receipt}
    (atIndex : receipts[i]? = some r) :
    work (receipts.take i)+NestedJournalBudget.events r ≤ work receipts := by
  induction receipts generalizing i with
  | nil => simp at atIndex
  | cons first rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at atIndex
      subst r
      simp [work]
    | succ i =>
      have ht := ih atIndex
      simpa only [List.take_succ_cons,work,List.map_cons,List.sum_cons,Nat.add_assoc] using
        Nat.add_le_add_left ht (NestedJournalBudget.events first)

/-- The outer seed, total credit envelope and actual receipt position supply
the call's funding and queue domain. No per-transaction invariant is assumed. -/
theorem observed {kind : Contract} {genesis initial final : World}
    {baseCredits credits : Nat} {receipts : List Receipt}
    (history : Trace initial receipts credits final)
    (seedFunds : FundingHistory.Trace genesis baseCredits initial)
    (seed : JournalInvariant.Invariant kind 0 initial)
    (funds : TransferFunding.worldFunds genesis+(baseCredits+credits) < FundedDomain.fundingCeiling)
    (bound : work receipts < 2^128)
    {i : Nat} {receipt : Receipt} (atIndex : receipts[i]? = some receipt)
    {path : EventTree.Address} {fuel : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt (TransactionEventBounds.request receipt.call)
      (TransactionEventBounds.request receipt.call).eval (TransactionAppendBudget.tree receipt)
      path (fuel+1) a r) (ht : a.target = address kind)
    {created : Created} {world : World} {gas : UInt256} {ss : Substate}
    {status : Bool} {out : ByteArray}
    (hr : r = .ok (created,world,gas,ss,status,out)) :
    ∃ inner, Cert (.theta (fuel+1) a) r inner ∧
      JournalExecution.Journal kind
        (work (receipts.take i)+NestedJournalBudget.before (TransactionAppendBudget.tree receipt) path+inner.count)
        world ss ∧
      NestedProtectedJournal.Observed kind (a.context fuel (runtime kind)) created world ss status out := by
  obtain ⟨pc,hpc,prefixHistory,account,ha,fit,resources⟩ := transaction_prefix history atIndex
  have hw := position_work atIndex
  have hfund : TransferFunding.worldFunds genesis+(baseCredits+pc) < FundedDomain.fundingCeiling := by omega
  have hi := ActualJournalHistory.preserves prefixHistory seedFunds seed hfund (by omega)
  have hf := ActualJournalHistory.funding prefixHistory seedFunds
  exact TransactionJournal.observed receipt.call hf ha hfund fit resources hi
    (TransactionAppendBudget.tree_cert receipt) (by exact lt_of_le_of_lt hw bound) loc ht hr

/-- The typed block envelope is tied to the same chronological receipt list
before it supplies the all-position actual nested guarantee consumer. -/
theorem observed_in_blocks {kind : Contract} {genesis initial final : World}
    {baseCredits credits : Nat} {receipts : List Receipt}
    (history : Trace initial receipts credits final)
    (seedFunds : FundingHistory.Trace genesis baseCredits initial)
    (seed : JournalInvariant.Invariant kind 0 initial)
    (funds : TransferFunding.worldFunds genesis+(baseCredits+credits) < FundedDomain.fundingCeiling)
    (blocks : List BlockReceipt) (listed : receipts = blocks.flatMap (fun b => b.receipts))
    (slots : (blocks.map (fun b => b.slot)).Nodup)
    {i : Nat} {receipt : Receipt} (atIndex : receipts[i]? = some receipt)
    {path : EventTree.Address} {fuel : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt (TransactionEventBounds.request receipt.call)
      (TransactionEventBounds.request receipt.call).eval (TransactionAppendBudget.tree receipt)
      path (fuel+1) a r) (ht : a.target = address kind)
    {created : Created} {world : World} {gas : UInt256} {ss : Substate}
    {status : Bool} {out : ByteArray}
    (hr : r = .ok (created,world,gas,ss,status,out)) :
    ∃ inner, Cert (.theta (fuel+1) a) r inner ∧
      JournalExecution.Journal kind
        (work (receipts.take i)+NestedJournalBudget.before (TransactionAppendBudget.tree receipt) path+inner.count)
        world ss ∧
      NestedProtectedJournal.Observed kind (a.context fuel (runtime kind)) created world ss status out :=
  observed history seedFunds seed funds (work_lt_of_blocks receipts blocks listed slots) atIndex loc ht hr

#print axioms transaction_prefix
#print axioms position_work
#print axioms observed
#print axioms observed_in_blocks
end Eip8282.Audit.Integrator.ActualHistoryCalls
