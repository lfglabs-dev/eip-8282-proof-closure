import Eip8282.Audit.Integrator.CallRevert
import Eip8282.Audit.Integrator.CallSuccess
import Eip8282.Audit.Integrator.NestedProtectedJournal
import Eip8282.Audit.Integrator.Topics.ReferenceMeter2
import Eip8282.Audit.Integrator.ReferenceRuntimeCompletion
import Eip8282.Audit.Integrator.ReferenceRuntimeTerminalPayment
import Eip8282.Audit.Integrator.ReferenceRuntimeTransactionPayment
import Eip8282.Audit.Integrator.ReferenceStorageFlow
import Eip8282.Audit.Integrator.WorldNonempty
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceRuntimeEndpoint -/

/-! Source-shaped observations of the very runtime execution published by a
successful message call. Entry and terminal owner preservation discharge the
empty-world settlement fallback. Initial storage bindings and a resource/host
threshold remain explicit; no source interpreter or source gas parity is assumed. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeEndpoint
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Correspondence (runtimeCode)
open ReferenceRuntimeView ReferenceRuntimeCompletion
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private theorem terminal_owner {parent : ReferenceStorageView.Parent} {v : View}
    {post : EVM.State} {out : ByteArray} {op : Operation .EVM}
    (terminal : SuccessEnd parent v post out op) : SystemSpec.HasOwner post.toState := by
  cases terminal with
  | stopped related _ => exact related.owner
  | returned _ related _ => exact related.owner

theorem nonempty {kind : Kind} {parent : ReferenceStorageView.Parent}
    {fuel : Nat} {pre post : EVM.State} {out : ByteArray} {initial : View}
    (observed : Successful (kind := kind) parent fuel pre post out initial) :
    (post.accountMap == ∅) = false := by
  obtain ⟨t,finish,_,_,_,terminal⟩ := observed
  exact WorldNonempty.beq_empty_false_of_hasOwner (terminal_owner terminal)

/-- Recover a complete viewed execution from actual Xi success, preserving
every published field. The memory bound is imposed only on initial resources. -/
theorem xi_success {kind : Kind} (c : XiCall kind)
    {published : Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate}
    {out : ByteArray} (actual : c.result = .ok (.success published out))
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (cap : Nat)
    (cdfit : c.env.calldata.size < UInt256.size)
    (threshold : RuntimeMemoryFunding.energy c.entry < ReferenceMemoryCapacity.cost (cap+1))
    (host : 32*cap < 2^System.Platform.numBits) :
    ∃ post : EVM.State,
      (post.createdAccounts,post.accountMap,post.gasAvailable,post.substate) = published ∧
      Successful (kind := kind) parent c.fuel c.entry post out (initial c tx) ∧
      (post.accountMap == ∅) = false := by
  obtain ⟨post,payload,hx⟩ := SuccessInversion.xi_success_X c actual
  have hj : D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩ = jumpdestsOf kind := by
    cases kind
    · exact deposit_D_J
    · exact exit_D_J
  have hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) c.entry := by
    cases kind
    · exact ⟨c.code_pinned,Or.inl RuntimeExecutionScope.deposit.entry⟩
    · exact ⟨c.code_pinned,Or.inl RuntimeExecutionScope.exit.entry⟩
  rw [← hj] at hx
  have viewed := ReferenceRuntimeCompletion.success hx hat (initial c tx)
    (initial_related c parent tx slots owner) cdfit threshold host
  exact ⟨post,payload,viewed,nonempty viewed⟩

/-- Actual Theta success produces its actual complete viewed code frame. The
published journal equals this frame's final journal: no fallback premise and
no independently selected final state is consumed. -/
theorem theta_success {kind : Kind} (c : MessageCall.Context)
    (codeEq : c.code = runtimeCode kind) (steps : Nat) (hf : c.fuel = steps+1)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (actual : c.result = .ok (created,world,gas,substate,true,out))
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c codeEq steps).entry.toState)
    (owner : SystemSpec.HasOwner (CallBridge.codeCall c codeEq steps).entry.toState)
    (cap : Nat) (cdfit : c.calldata.size < UInt256.size)
    (threshold : RuntimeMemoryFunding.energy (CallBridge.codeCall c codeEq steps).entry <
      ReferenceMemoryCapacity.cost (cap+1))
    (host : 32*cap < 2^System.Platform.numBits) :
    ∃ post : EVM.State,
      (post.createdAccounts,post.accountMap,post.gasAvailable,post.substate) =
        (created,world,gas,substate) ∧
      Successful (kind := kind) parent steps (CallBridge.codeCall c codeEq steps).entry post out
        (initial (CallBridge.codeCall c codeEq steps) tx) := by
  obtain ⟨ew,es,he,hw,hs⟩ := CallSuccess.codeCall_of_success c codeEq steps hf actual
  obtain ⟨post,hp,hview,hne⟩ := xi_success (CallBridge.codeCall c codeEq steps) he
    parent tx slots owner cap cdfit threshold host
  have fields := Prod.mk.inj hp
  have worldEq : post.accountMap = ew := (Prod.mk.inj fields.2).1
  have ne : (ew == ∅) = false := by rw [← worldEq]; exact hne
  simp only [ne,Bool.false_eq_true,ite_false] at hw hs
  rw [hw,hs]
  exact ⟨post,hp,hview⟩

#print axioms nonempty
#print axioms xi_success
#print axioms theta_success
end Eip8282.Audit.Integrator.ReferenceRuntimeEndpoint

end

section

/-! ## ReferenceRuntimeStateBalance -/

/-! Sum state-gas potential over the finite EVM address/word-key space.
No enumeration bound is imposed on execution. The finite sum is mathematical,
not an executable scan of storage or a claim of canonical source reachability.
Actual coupled actions derive all slot changes and their exact total charge. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeStateBalance
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings
open ReferenceRuntimeReadings ReferenceMeterPath ReferenceStorageFlow
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000

abbrev Slot := AccountAddress × Fin UInt256.size

-- Use a symbolic finite enumeration, avoiding reduction of the concrete
-- numeral Fin universes during kernel conversion. Membership remains universal.
noncomputable local instance symbolicSlots : Fintype Slot := Fintype.ofFinite Slot

noncomputable def totalPotential (p : Parent) (tx : Tx) : Int :=
  ∑ q : Slot, slotPotential p tx q.1 (UInt256.mk q.2).toByteArray

private theorem delta_sum {p : Parent} {v next : View} {w : Warm}
    {instr : Instruction} {event : Event} (price : Price p v w next instr.1 event) :
    (∑ q : Slot, keyDelta instr v event q.1 (UInt256.mk q.2).toByteArray) = eventDelta event := by
  classical
  by_cases hs : instr.1 = .SSTORE
  · have same (q : Slot) : keyDelta instr v event q.1 (UInt256.mk q.2).toByteArray =
        if q = (v.env.codeOwner,v.stack[0]!.val) then eventDelta event else 0 := by
      unfold keyDelta
      simp only [hs,true_and,ReferenceStorageView.key_injective.eq_iff]
      have he : (q.1 = v.env.codeOwner ∧ UInt256.mk q.2 = v.stack[0]!) ↔ q = (v.env.codeOwner,v.stack[0]!.val) := by
        constructor
        · rintro ⟨ha,hk⟩
          exact Prod.ext ha (congrArg UInt256.val hk)
        · intro hq
          subst q
          exact ⟨rfl,rfl⟩
      simp only [he]
    calc
      _ = ∑ q : Slot, (if q = (v.env.codeOwner,v.stack[0]!.val) then eventDelta event else 0) :=
        Finset.sum_congr rfl (fun q _ => same q)
      _ = _ := by simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  · simp only [Price,if_neg hs] at price
    obtain ⟨n,hn,rfl⟩ := price
    simp only [keyDelta,hs,false_and,if_false,eventDelta,Finset.sum_const_zero]

theorem action_balance {kind : Kind} {p : Parent} {instr : Instruction} {v next : View}
    {w : Warm} {event : Event} (action : ReferenceRuntimeAction.Action kind p instr v next)
    (price : Price p v w next instr.1 event) :
    eventDelta event = totalPotential p next.storage-totalPotential p v.storage := by
  classical
  calc
    eventDelta event = ∑ q : Slot, keyDelta instr v event q.1 (UInt256.mk q.2).toByteArray := (delta_sum price).symm
    _ = ∑ q : Slot, (slotPotential p next.storage q.1 (UInt256.mk q.2).toByteArray-
        slotPotential p v.storage q.1 (UInt256.mk q.2).toByteArray) := by
      apply Finset.sum_congr rfl
      intro q _
      exact action_delta action price _ _
    _ = _ := Finset.sum_sub_distrib _ _

/-- The actual finite runtime supplies its exact signed state-charge balance.
Readings for an arbitrary unlinked event list would not prove this theorem. -/
theorem of_coupled {kind : Kind} {p : Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post finish finalWarm events) :
    (events.map eventDelta).sum = totalPotential p finish.storage-totalPotential p v.storage := by
  induction h with
  | refl => simp only [List.map_nil,List.sum_nil,sub_self]
  | cons actual decoded related nextRelated warm created action readings price tail ih =>
    simp only [List.map_cons,List.sum_cons,action_balance action price]
    omega

/-- Exact empty storage/created/read projection of a fresh source TransactionState. -/
def emptyTx : Tx := {writes := fun _ _ => none, created := ∅, reads := ∅}

theorem empty_potential (p : Parent) : totalPotential p emptyTx = 0 := by
  classical
  unfold totalPotential
  apply Finset.sum_eq_zero
  intro q _
  simp [slotPotential,emptyTx,original,current,ReferenceStoragePotential.potential]

theorem nonnegative (p : Parent) (tx : Tx) : 0 ≤ totalPotential p tx := by
  classical
  apply Finset.sum_nonneg
  intro q _
  unfold slotPotential ReferenceStoragePotential.potential
  split <;> omega

/-- Fresh-transaction storage is a concrete sufficient initial case. This does
not assert that arbitrary nested frames start with empty transaction overlays. -/
theorem from_empty {kind : Kind} {p : Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post finish finalWarm events)
    (initial : v.storage = emptyTx) : 0 ≤ (events.map eventDelta).sum := by
  rw [of_coupled h,initial,empty_potential,sub_zero]
  exact nonnegative p finish.storage

#print axioms action_balance
#print axioms of_coupled
#print axioms empty_potential
#print axioms nonnegative
#print axioms from_empty
end Eip8282.Audit.Integrator.ReferenceRuntimeStateBalance

end

section

/-! ## ReferenceRuntimeGasBalance -/

/-! Exact successful source-meter accounting on the same actual runtime.
The initial storage potential is retained for nested frames that can refund
state bought earlier. LOG0 occurrences count executed logs, not final retained
queue records. Complete outer rollback/commit selection is still required. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeGasBalance
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings
open ReferenceRuntimeReadings ReferenceMeterPath ReferenceRuntimeStateBalance
open ReferenceMeterConservation
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def logCount : List Labelled → Nat
  | [] => 0
  | label::tail => (if label.2.2.1 = .LOG0 then 1 else 0)+logCount tail

private theorem exec_nonnegative (event : Event) : 0 ≤ actualExec event := by
  cases event <;> simp [actualExec]

theorem log_cost {kind : Kind} {p : Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post finish finalWarm events) :
    (375*logCount trace : Int) ≤ (events.map actualExec).sum := by
  induction h with
  | refl => simp [logCount]
  | @cons fuel gasCost rem pre mid post v next finish w finalWarm trace event events
      actual decoded related nextRelated warm created action readings price tail ih =>
    have nonneg := exec_nonnegative event
    by_cases hl : (decodeAt pre).1 = .LOG0
    · have hn : (decodeAt pre).1 ≠ .SSTORE := by rw [hl]; decide
      simp only [Price,if_neg hn] at price
      obtain ⟨n,hprice,rfl⟩ := price
      rw [hl] at hprice
      simp only [ReferenceCopyLogGas.ordinaryCost,show (Operation.LOG0 : Operation .EVM) ≠ .CALLDATACOPY by decide,
        ↓reduceIte,Option.some.injEq] at hprice
      simp only [List.map_cons,List.sum_cons,actualExec,logCount,hl,↓reduceIte]
      unfold ReferenceCopyLogGas.logCost at hprice
      omega
    · simp only [List.map_cons,List.sum_cons,logCount,if_neg hl,Nat.zero_add]
      omega

/-- Literal pool loss equals exact execution charges plus the derived change
in all slot potentials. A prefunded slot credit is not silently discarded. -/
theorem balance {kind : Kind} {p : Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event} {meter final : ReferenceStorageGas.Meter}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post finish finalWarm events)
    (paid : run events meter = some final) :
    pools meter-pools final = (events.map actualExec).sum+totalPotential p finish.storage-totalPotential p v.storage ∧
    stateBalance final-stateBalance meter = totalPotential p finish.storage-totalPotential p v.storage := by
  have accounting := run_balance paid
  have storage := ReferenceRuntimeStateBalance.of_coupled h
  change (events.map stateDelta).sum = _ at storage
  omega

/-- Include the terminal charge once. The bound holds with the explicit
initial-potential correction; only the fresh-transaction case removes it. -/
theorem through_terminal {kind : Kind} {p : Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event} {meter final : ReferenceStorageGas.Meter}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post finish finalWarm events)
    (amount : Nat) (paid : run (events++[.ordinary amount]) meter = some final) :
    (375*logCount trace : Int) ≤ pools meter-pools final+totalPotential p v.storage := by
  have accounting := (run_balance paid).1
  have storage := ReferenceRuntimeStateBalance.of_coupled h
  change (events.map stateDelta).sum = _ at storage
  have logs := log_cost h
  have finalNonneg := ReferenceRuntimeStateBalance.nonnegative p finish.storage
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    actualExec,stateDelta,add_zero] at accounting
  omega

theorem fresh_transaction {kind : Kind} {p : Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event} {meter final : ReferenceStorageGas.Meter}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post finish finalWarm events)
    (amount : Nat) (paid : run (events++[.ordinary amount]) meter = some final)
    (initial : v.storage = emptyTx) :
    (375*logCount trace : Int) ≤ pools meter-pools final := by
  have bound := through_terminal h amount paid
  rw [initial,empty_potential,add_zero] at bound
  exact bound

#print axioms log_cost
#print axioms balance
#print axioms through_terminal
#print axioms fresh_transaction
end Eip8282.Audit.Integrator.ReferenceRuntimeGasBalance

end

section

/-! ## ReferenceRuntimeGasCertificate -/

/-! The same successful or reverted runtime witness now carries source
allocation, exact terminal payment and an executed-log bound in net pools with
its initial state-credit correction. This does not replace committed occurrence
selection, source nested grant binding or post-transaction refund settlement. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeGasCertificate
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings
open ReferenceRuntimeCompletion ReferenceRuntimePayment ReferenceMeterPath
open ReferenceMemoryCapacity (cost)
open ReferenceRuntimeTerminalPayment ReferenceRuntimeTransactionPayment
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def AllocatedBoundFor (p : ReferenceStorageView.Parent) (v : View)
    (cap : Nat) (trace : List Labelled) (events : List Event) (amount : Nat) : Prop :=
  ∀ txGas intrinsic : Nat,
    intrinsic+baseBound cap*trace.length+cost cap ≤ 16777216 →
    intrinsic+baseBound cap*trace.length+cost cap+97920*storageWrites trace ≤ txGas →
    ∃ final,
      run (events++[.ordinary amount]) (ReferenceTransactionPayment.initialMeter txGas intrinsic) = some final ∧
      (375*ReferenceRuntimeGasBalance.logCount trace : Int) ≤
        ReferenceMeterConservation.pools (ReferenceTransactionPayment.initialMeter txGas intrinsic)-
        ReferenceMeterConservation.pools final+ReferenceRuntimeStateBalance.totalPotential p v.storage

private theorem bounded {kind : Kind} {p : ReferenceStorageView.Parent} {initialCreated : Set AccountAddress}
    {fuel rem cap amount : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post finish finalWarm events)
    (paid : AllocatedPaymentFor cap trace events amount) : AllocatedBoundFor p v cap trace events amount := by
  intro txGas intrinsic execution total
  obtain ⟨final,hpaid⟩ := paid txGas intrinsic execution total
  exact ⟨final,hpaid,ReferenceRuntimeGasBalance.through_terminal h amount hpaid⟩

def SuccessGas (kind : Kind) (parent : ReferenceStorageView.Parent)
    (initialCreated : Set AccountAddress) (fuel cap : Nat) (pre post : EVM.State)
    (out : ByteArray) (v : View) (w : Warm) : Prop :=
  ∃ t : SuccessInversion.SuccessTrace (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre post out,
    ∃ finish finalWarm events,
      Coupled kind parent initialCreated fuel pre v w t.trace (t.rem+1) t.exit finish finalWarm events ∧
      Related parent finish t.exit ∧ WarmRelated finalWarm t.exit ∧
      finish.storage.created = initialCreated ∧
      decodeAt t.exit = (ReferenceDecodeSites.referenceDecode finish.env.code finish.pc).getD (.STOP,none) ∧
      SuccessEnd parent finish post out t.op ∧
      PaymentFor cap t.trace events (terminalCost t.op finish) ∧
      AllocatedBoundFor parent v cap t.trace events (terminalCost t.op finish)

theorem success {kind : Kind} {parent : ReferenceStorageView.Parent}
    {initialCreated : Set AccountAddress} {fuel cap : Nat} {pre post : EVM.State}
    {out : ByteArray} {v : View} {w : Warm}
    (certificate : SuccessPayment kind parent initialCreated fuel cap pre post out v w) :
    SuccessGas kind parent initialCreated fuel cap pre post out v w := by
  obtain ⟨t,finish,finalWarm,events,h,related,warm,created,decoded,terminal,paid,allocated⟩ := certificate
  exact ⟨t,finish,finalWarm,events,h,related,warm,created,decoded,terminal,paid,bounded h allocated⟩

def RevertGas (kind : Kind) (parent : ReferenceStorageView.Parent)
    (initialCreated : Set AccountAddress) (fuel cap : Nat) (pre : EVM.State)
    (gas : UInt256) (out : ByteArray) (v : View) (w : Warm) : Prop :=
  ∃ t : RuntimeRevertTrace.RevertTrace (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre gas out,
    ∃ finish finalWarm events off len rest,
      Coupled kind parent initialCreated fuel pre v w t.trace (t.rem+1) t.exit finish finalWarm events ∧
      Related parent finish t.exit ∧ WarmRelated finalWarm t.exit ∧
      finish.storage.created = initialCreated ∧
      decodeAt t.exit = (ReferenceDecodeSites.referenceDecode finish.env.code finish.pc).getD (.STOP,none) ∧
      finish.stack = off::len::rest ∧ ReferenceReturnView.Result parent finish off len rest t.post ∧
      out = (ReferenceReturnView.returnMemory finish off len).extract off.toNat (off.toNat+len.toNat) ∧
      PaymentFor cap t.trace events (terminalCost .REVERT finish) ∧
      AllocatedBoundFor parent v cap t.trace events (terminalCost .REVERT finish)

theorem revert {kind : Kind} {parent : ReferenceStorageView.Parent}
    {initialCreated : Set AccountAddress} {fuel cap : Nat} {pre : EVM.State}
    {gas : UInt256} {out : ByteArray} {v : View} {w : Warm}
    (certificate : RevertPayment kind parent initialCreated fuel cap pre gas out v w) :
    RevertGas kind parent initialCreated fuel cap pre gas out v w := by
  obtain ⟨t,finish,finalWarm,events,off,len,rest,h,related,warm,created,decoded,shape,result,output,paid,allocated⟩ := certificate
  exact ⟨t,finish,finalWarm,events,off,len,rest,h,related,warm,created,decoded,shape,result,output,paid,bounded h allocated⟩

#print axioms success
#print axioms revert
end Eip8282.Audit.Integrator.ReferenceRuntimeGasCertificate

end

section

/-! ## ReferenceRuntimeReceipt -/

/-! The three guarantee parents and source-shaped observations consume the
same actual message receipt. Successful and REVERT executions carry computed
views; exceptional failures carry the exact restored journal and error. This
does not equate source exceptional gas behaviour or derive canonical admission. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeReceipt
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Correspondence (runtimeCode)
open ReferenceRuntimeView ReferenceRuntimeCompletion
open ReachableCalls (Contract Transition PinnedCall)
open JournalInvariant (Invariant modelKind)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem xi_revert {kind : Kind} (c : XiCall kind) {gas : UInt256} {out : ByteArray}
    (actual : c.result = .ok (.revert gas out))
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (cap : Nat)
    (cdfit : c.env.calldata.size < UInt256.size)
    (threshold : RuntimeMemoryFunding.energy c.entry < ReferenceMemoryCapacity.cost (cap+1))
    (host : 32*cap < 2^System.Platform.numBits) :
    Reverted (kind := kind) parent c.fuel c.entry gas out (initial c tx) := by
  have hx := CallRevert.xi_revert_X c actual
  have hj : D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩ = jumpdestsOf kind := by
    cases kind
    · exact deposit_D_J
    · exact exit_D_J
  have hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) c.entry := by
    cases kind
    · exact ⟨c.code_pinned,Or.inl RuntimeExecutionScope.deposit.entry⟩
    · exact ⟨c.code_pinned,Or.inl RuntimeExecutionScope.exit.entry⟩
  rw [← hj] at hx
  exact ReferenceRuntimeCompletion.revert hx hat (initial c tx)
    (initial_related c parent tx slots owner) cdfit threshold host

def Observed {kind : Kind} (c : MessageCall.Context) (codeEq : c.code = runtimeCode kind)
    (steps : Nat) (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (substate : Substate) (success : Bool) (out : ByteArray) : Prop :=
  let frame := CallBridge.codeCall c codeEq steps
  if success then
    ∃ post : EVM.State,
      (post.createdAccounts,post.accountMap,post.gasAvailable,post.substate) =
        (created,world,gas,substate) ∧
      Successful (kind := kind) parent steps frame.entry post out (initial frame tx)
  else
    world = c.world ∧ substate = c.substate ∧ created = c.created ∧
      ((frame.result = .ok (.revert gas out) ∧
          Reverted (kind := kind) parent steps frame.entry gas out (initial frame tx)) ∨
        ∃ e, frame.result = .error e ∧ (e == ExecutionException.OutOfFuel) = false ∧
          gas = UInt256.ofNat 0 ∧ out = ByteArray.empty)

/-- Source observations of an actual returned message call, including rollback.
The installed target supplies owner existence through the actual value transfer. -/
theorem observe (kind : Contract) (c : MessageCall.Context) (pinned : PinnedCall kind c)
    (codeEq : c.code = runtimeCode (modelKind kind)) (steps : Nat) (hf : c.fuel = steps+1)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (actual : c.result = .ok (created,world,gas,substate,success,out))
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c codeEq steps).entry.toState)
    (cap : Nat) (cdfit : c.calldata.size < UInt256.size)
    (threshold : RuntimeMemoryFunding.energy (CallBridge.codeCall c codeEq steps).entry <
      ReferenceMemoryCapacity.cost (cap+1)) (host : 32*cap < 2^System.Platform.numBits) :
    Observed c codeEq steps parent tx created world gas substate success out := by
  have owner := TransferFrame.pinned_codeCall_hasOwner c pinned codeEq steps
  cases success with
  | true =>
    exact ReferenceRuntimeEndpoint.theta_success c codeEq steps hf actual
      parent tx slots owner cap cdfit threshold host
  | false =>
    obtain ⟨hw,hs,hc,hcase⟩ := CallRevert.false_cases c actual
    refine ⟨hw,hs,hc,?_⟩
    rw [CallBridge.execution_eq_codeCall c codeEq steps hf] at hcase
    rcases hcase with hr | he
    · exact Or.inl ⟨hr,xi_revert (CallBridge.codeCall c codeEq steps) hr
        parent tx slots owner cap cdfit threshold host⟩
    · exact Or.inr he

/-- All three public guarantees and the runtime observations share one complete
receipt. Internal queue/control domains are derived from the history invariant;
its history and funding producers remain required at the protocol boundary. -/
theorem guarantees (kind : Contract) (c : MessageCall.Context) (pinned : PinnedCall kind c)
    (codeEq : c.code = runtimeCode (modelKind kind)) (steps : Nat) (hf : c.fuel = steps+1)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (actual : c.result = .ok (created,world,gas,substate,success,out))
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c codeEq steps).entry.toState)
    (cap : Nat) (cdfit : c.calldata.size < UInt256.size)
    (threshold : RuntimeMemoryFunding.energy (CallBridge.codeCall c codeEq steps).entry <
      ReferenceMemoryCapacity.cost (cap+1)) (host : 32*cap < 2^System.Platform.numBits)
    {budget : Nat} (invariant : Invariant kind budget c.world) (bound : budget < 2^128) :
    NestedProtectedJournal.Observed kind c created world substate success out ∧
      Observed c codeEq steps parent tx created world gas substate success out := by
  let t : Transition kind c.world world :=
    { call := c, pinned := pinned, pre := rfl, created := created, gas := gas,
      substate := substate, success := success, output := out, executed := actual }
  exact ⟨JournalGuarantees.completed t invariant bound cdfit,
    observe kind c pinned codeEq steps hf actual parent tx slots cap cdfit threshold host⟩

#print axioms xi_revert
#print axioms observe
#print axioms guarantees
end Eip8282.Audit.Integrator.ReferenceRuntimeReceipt

end

section

/-! ## ReferenceRuntimeResourceReceipt -/

/-! Resource certificates and all three guarantees share the same actual
returned message receipt. Success/REVERT certificates identify the exact trace
and sufficient initial source-meter grants; exceptional failures retain the
actual error/rollback, without claiming a source exceptional replay. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeResourceReceipt
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Correspondence (runtimeCode)
open ReachableCalls (Contract PinnedCall)
open JournalInvariant (Invariant modelKind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeTerminalPayment
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2400000

def Observed {kind : Kind} (c : MessageCall.Context) (codeEq : c.code = runtimeCode kind)
    (steps cap : Nat) (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx) (w : Warm)
    (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (substate : Substate) (success : Bool) (out : ByteArray) : Prop :=
  let frame := CallBridge.codeCall c codeEq steps
  if success then
    ∃ post : EVM.State,
      (post.createdAccounts,post.accountMap,post.gasAvailable,post.substate) =
        (created,world,gas,substate) ∧
      SuccessCertificate kind parent tx.created steps cap frame.entry post out (initial frame tx) w
  else
    world = c.world ∧ substate = c.substate ∧ created = c.created ∧
      ((frame.result = .ok (.revert gas out) ∧
          RevertCertificate kind parent tx.created steps cap frame.entry gas out (initial frame tx) w) ∨
        ∃ e, frame.result = .error e ∧ (e == ExecutionException.OutOfFuel) = false ∧
          gas = UInt256.ofNat 0 ∧ out = ByteArray.empty)

/-- Attach certificates to the already observed receipt. All runtime witnesses
come from that receipt; only source initial bindings and resources remain inputs. -/
theorem strengthen {kind : Kind} (c : MessageCall.Context) (codeEq : c.code = runtimeCode kind)
    (steps cap : Nat) (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx) (w : Warm)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (observed : ReferenceRuntimeReceipt.Observed c codeEq steps parent tx created world gas substate success out)
    (warm : WarmRelated w (CallBridge.codeCall c codeEq steps).entry)
    (threshold : RuntimeMemoryFunding.energy (CallBridge.codeCall c codeEq steps).entry <
      ReferenceMemoryCapacity.cost (cap+1)) :
    Observed c codeEq steps cap parent tx w created world gas substate success out := by
  let frame := CallBridge.codeCall c codeEq steps
  have hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) frame.entry := by
    cases kind
    · exact ⟨frame.code_pinned,Or.inl RuntimeExecutionScope.deposit.entry⟩
    · exact ⟨frame.code_pinned,Or.inl RuntimeExecutionScope.exit.entry⟩
  cases success with
  | true =>
    obtain ⟨post,payload,viewed⟩ := observed
    exact ⟨post,payload,ReferenceRuntimeTerminalPayment.success viewed hat w warm rfl threshold⟩
  | false =>
    obtain ⟨hw,hs,hc,hcase⟩ := observed
    refine ⟨hw,hs,hc,?_⟩
    rcases hcase with ⟨actual,viewed⟩ | exceptional
    · exact Or.inl ⟨actual,ReferenceRuntimeTerminalPayment.revert viewed hat w warm rfl threshold⟩
    · exact Or.inr exceptional

/-- Same pre-world, full receipt, all three guarantee predicates and complete
source-resource certificates. Canonical history must still produce invariant,
budget and source bindings; PaymentFor gives sufficient grants, not their
protocol admission. -/
theorem guarantees (kind : Contract) (c : MessageCall.Context) (pinned : PinnedCall kind c)
    (codeEq : c.code = runtimeCode (modelKind kind)) (steps : Nat) (hf : c.fuel = steps+1)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (actual : c.result = .ok (created,world,gas,substate,success,out))
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx) (w : Warm)
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c codeEq steps).entry.toState)
    (warm : WarmRelated w (CallBridge.codeCall c codeEq steps).entry)
    (cap : Nat) (cdfit : c.calldata.size < UInt256.size)
    (threshold : RuntimeMemoryFunding.energy (CallBridge.codeCall c codeEq steps).entry <
      ReferenceMemoryCapacity.cost (cap+1)) (host : 32*cap < 2^System.Platform.numBits)
    {budget : Nat} (invariant : Invariant kind budget c.world) (bound : budget < 2^128) :
    NestedProtectedJournal.Observed kind c created world substate success out ∧
      Observed c codeEq steps cap parent tx w created world gas substate success out := by
  obtain ⟨guards,viewed⟩ := ReferenceRuntimeReceipt.guarantees kind c pinned codeEq steps hf actual
    parent tx slots cap cdfit threshold host invariant bound
  exact ⟨guards,strengthen c codeEq steps cap parent tx w viewed warm threshold⟩

#print axioms strengthen
#print axioms guarantees
end Eip8282.Audit.Integrator.ReferenceRuntimeResourceReceipt

end
