import Eip8282.Audit.Integrator.JournalRetainedCalls
import Eip8282.Audit.Integrator.JournalCheckpoints
import Eip8282.Audit.Integrator.NestedAppendCount

/-! Successful nonempty user calls selected from the complete surviving-call
predicate. Counts identify actual invocation addresses, not byte payloads.
Their owned marked events bound this surviving subset without treating all
executed work as committed work. -/
namespace Eip8282.Audit.Integrator.JournalRetainedWork
open EvmYul EvmYul.EVM
open NestedEvents JournalExecution JournalRetainedCalls
open ReachableCalls (Contract address runtime)
open JournalInvariant (modelKind)
open MessageCall CallBridge
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def Submitted (kind : Contract) (q : Request) (result : q.Outcome) (tree : EventTree)
    (path : EventTree.Address) : Prop :=
  ∃ fuel a cr world gas ss out,
    Survives kind q result tree path fuel a (.ok (cr,world,gas,ss,true,out)) ∧
    a.source ≠ Eip8282.Audit.EvmRunner.sysAddr ∧ a.data.size ≠ 0

theorem survives_target {kind : Contract} {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {fuel : Nat} {a : ThetaArgs} {r : ThetaResult}
    (h : Survives kind q result tree path fuel a r) : 0 < fuel ∧ a.target = address kind := by
  induction h with
  | here hp ht => exact ⟨hp,ht⟩
  | xNextChild _ _ _ _ _ ih | xNextTail _ _ _ _ _ ih | xHalt _ _ _ _ _ ih => exact ih
  | xi _ _ _ ih | thetaCode _ _ _ _ _ _ ih | lambdaInit _ _ _ _ _ ih | stepChild _ _ _ _ ih => exact ih

theorem Submitted.retained {kind : Contract} {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} (h : Submitted kind q result tree path) : Retained kind q result tree path := by
  obtain ⟨f,a,cr,w,g,ss,out,loc,_,_⟩ := h
  exact ⟨f,a,_,loc⟩

noncomputable def submittedList (kind : Contract) (q : Request) (result : q.Outcome)
    (tree : EventTree) : List EventTree.Address := by
  classical
  exact (retainedList kind q result tree).filter (fun p => decide (Submitted kind q result tree p))

theorem mem_submittedList_iff {kind : Contract} {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} : path ∈ submittedList kind q result tree ↔ Submitted kind q result tree path := by
  classical
  simp only [submittedList,List.mem_filter,decide_eq_true_eq,retainedList_mem_iff]
  exact ⟨And.right,fun h => ⟨h.retained,h⟩⟩

theorem submittedList_nodup (kind : Contract) (q : Request) (result : q.Outcome) (tree : EventTree) :
    (submittedList kind q result tree).Nodup := by
  classical
  exact (retainedList_nodup kind q result tree).filter _

theorem submittedList_order (kind : Contract) (q : Request) (result : q.Outcome) (tree : EventTree) :
    (submittedList kind q result tree).Sublist (nodePaths tree) := by
  classical
  exact List.filter_sublist.trans (retainedList_order kind q result tree)

noncomputable def count (kind : Contract) (q : Request) (result : q.Outcome) (tree : EventTree) : Nat :=
  (submittedList kind q result tree).length

/-- Actual canonical successful Theta calls select the same-path successful
pinned Xi invocation. Both pinning and value coherence come from the initial
journal through actual checkpoints; calldata size comes from actual success. -/
theorem submitted_appendFrame {kind : Contract} {q : Request} {result : q.Outcome} {tree : EventTree}
    (cert : Cert q result tree) (budget : Nat) (hb : budget+tree.count < 2^128)
    (ready : Ready kind budget q) (inputs : NestedProtectedJournal.Inputs q result tree)
    (adequate : FuelAdequacy.Adequate q) {path : EventTree.Address}
    (h : Submitted kind q result tree path) : NestedAppendCount.IsAppendFrame q result tree path := by
  obtain ⟨fuel,a,cr,world,gas,ss,out,survives,hu,hn⟩ := h
  obtain ⟨positive,ht⟩ := survives_target survives
  cases fuel with
  | zero => omega
  | succ n =>
    have loc := survives.actual
    have readyCall := JournalCheckpoints.call_ready loc budget hb ready (inputs_every inputs)
      (FuelAdequacy.every_no_out_of_fuel cert adequate)
    have hc := (readyCall.2 ht).1
    let c := a.context n (runtime kind)
    have hcode : c.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
      cases kind <;> rfl
    have he : c.result = .ok (cr,world,gas,ss,true,out) :=
      (thetaArgs_result a n (runtime kind) hc).symm.trans loc.sound_inner
    have hv : c.apparentValue = c.value := (readyCall.2 ht).2
    have hd : c.calldata.size < UInt256.size := (inputs path (n+1) a _ loc).1
    have hsize := ProtectedJournalStep.successful_nonempty_size kind c hcode hu hv hd hn he
    have hf : c.fuel = (n-1)+1 := by
      have hp := SuccessfulQuote.positive_fuel c he
      change 0 < n at hp
      change n = (n-1)+1
      omega
    let call := codeCall c hcode (n-1)
    obtain ⟨ew,es,hs,_,_⟩ := CallSuccess.codeCall_of_success c hcode (n-1) hf he
    have xl : XiAt q result tree path (call.fuel+1) (rootXiArgs call) call.result := by
      change XiAt q result tree path ((n-1)+1) (a.xiArgs (runtime kind)) (codeCall c hcode (n-1)).result
      rw [←execution_eq_codeCall c hcode (n-1) hf]
      have hf' : n = (n-1)+1 := hf
      rw [←hf']
      exact loc.code_xi hc
    exact ⟨modelKind kind,call,xl,hu,(by cases kind <;> exact hsize),cr,ew,gas,es,out,hs⟩

/-- Distinct surviving submissions own distinct actual marked events, even if
the calldata, sender and output bytes of those invocations are identical. -/
theorem submitted_distinct_events {kind : Contract} {q : Request} {result : q.Outcome} {tree : EventTree}
    (cert : Cert q result tree) (budget : Nat) (hb : budget+tree.count < 2^128)
    (ready : Ready kind budget q) (inputs : NestedProtectedJournal.Inputs q result tree)
    (adequate : FuelAdequacy.Adequate q) {p r : EventTree.Address} {i j : Nat}
    (hp : Submitted kind q result tree p) (hr : Submitted kind q result tree r) (hne : p ≠ r) :
    NestedFrameOwnership.owned p i ≠ NestedFrameOwnership.owned r j :=
  NestedAppendCount.distinct_events (submitted_appendFrame cert budget hb ready inputs adequate hp)
    (submitted_appendFrame cert budget hb ready inputs adequate hr) hne

/-- The finite list is the complete canonical successful-user filter. Its
inclusion in actual append-frame IDs is proved, rather than supplied as a bound. -/
theorem count_le_executed {kind : Contract} {q : Request} {result : q.Outcome} {tree : EventTree}
    (cert : Cert q result tree) (budget : Nat) (hb : budget+tree.count < 2^128)
    (ready : Ready kind budget q) (inputs : NestedProtectedJournal.Inputs q result tree)
    (adequate : FuelAdequacy.Adequate q) :
    count kind q result tree ≤ NestedAppendCount.count q result tree := by
  classical
  have hsub : (submittedList kind q result tree).toFinset ⊆ NestedAppendCount.frames q result tree := by
    intro p hp
    apply NestedAppendCount.mem_frames_iff.mpr
    exact submitted_appendFrame cert budget hb ready inputs adequate
      (mem_submittedList_iff.mp (List.mem_toFinset.mp hp))
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (submittedList_nodup kind q result tree)] at hcard
  exact hcard

theorem count_le_events {kind : Contract} {q : Request} {result : q.Outcome} {tree : EventTree}
    (cert : Cert q result tree) (budget : Nat) (hb : budget+tree.count < 2^128)
    (ready : Ready kind budget q) (inputs : NestedProtectedJournal.Inputs q result tree)
    (adequate : FuelAdequacy.Adequate q) : count kind q result tree ≤ tree.count :=
  (count_le_executed cert budget hb ready inputs adequate).trans (NestedAppendCount.count_le_events q result tree)

/-- Actual reported transaction gas bounds surviving successful user calls.
A failed outer status is allowed; the survival predicate itself filters its
abandoned descendants. Finalization/log provenance is a separate interface. -/
theorem transaction_count_le_used (kind : Contract) (c : RefundAccounting.Context)
    {world : World} {ss : Substate} {z : Bool} {used : UInt256}
    (hr : c.result = .ok (world,ss,z,used)) {tree : EventTree}
    (cert : Cert (TransactionEventBounds.request c) (TransactionEventBounds.request c).eval tree)
    (budget : Nat) (hb : budget+tree.count < 2^128)
    (ready : Ready kind budget (TransactionEventBounds.request c))
    (inputs : NestedProtectedJournal.Inputs (TransactionEventBounds.request c)
      (TransactionEventBounds.request c).eval tree)
    (adequate : FuelAdequacy.Adequate (TransactionEventBounds.request c)) :
    count kind (TransactionEventBounds.request c) (TransactionEventBounds.request c).eval tree ≤ used.toNat := by
  obtain ⟨actual,body,_,hgas,unique⟩ := TransactionEventBounds.transaction_events c hr
  have he := unique tree cert
  subst tree
  exact (count_le_events cert budget hb ready inputs adequate).trans hgas

#print axioms mem_submittedList_iff
#print axioms submittedList_nodup
#print axioms submitted_appendFrame
#print axioms submitted_distinct_events
#print axioms count_le_executed
#print axioms count_le_events
#print axioms transaction_count_le_used
end Eip8282.Audit.Integrator.JournalRetainedWork
