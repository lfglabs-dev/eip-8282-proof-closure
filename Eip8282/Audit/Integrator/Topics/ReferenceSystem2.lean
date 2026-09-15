import Eip8282.Audit.Integrator.CallBridge
import Eip8282.Audit.Integrator.EndpointState
import Eip8282.Audit.Integrator.NestedProtectedJournal
import Eip8282.Audit.Integrator.ReferenceCheckedSystemForward
import Eip8282.Audit.Integrator.ReferenceSystemReadingsTrace
import Eip8282.Audit.Integrator.Topics.ReferenceSystem
import Eip8282.Audit.Integrator.SystemJournal
import Eip8282.Audit.Integrator.WorldNonempty

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceSystemEndpoint -/

/-! Exact enclosing endpoints of one completed SYSTEM execution. The same
Completed witness supplies the full Ξ success tuple and actual output. Its
Observed terminal owner excludes Θ's empty-world fallback, so the message-call
result commits that very tuple. No second run, supplied nonempty world, or
assumed reference interpreter execution is used. Initial world/code/context
bindings and construction of Observed remain the caller's producers. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemEndpoint
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Correspondence (runtimeCode)
open SystemExecutionResources ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- Publish all fields of the actual successful Ξ endpoint, not just output. -/
theorem xi_result {kind : Kind} {steps cap outputBytes : Nat} (c : XiCall kind)
    (h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes c.fuel c.entry) :
    c.result = .ok (.success
      (h.finalState.createdAccounts,h.finalState.accountMap,h.finalState.gasAvailable,h.finalState.substate)
      h.output) := by
  apply EndpointState.result_of_X_success c
  have hj : D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩ = jumpdestsOf kind := by
    cases kind
    · exact deposit_D_J
    · exact exit_D_J
  rw [← hj]
  exact h.success

/-- The observed terminal owner is derived along this completed trace; its
account lookup rules out the actual boolean empty-map branch. -/
theorem nonempty {kind : Kind} {parent : ReferenceStorageView.Parent}
    {steps cap outputBytes fuel : Nat} {pre : EVM.State} {initial : View}
    (h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes fuel pre)
    (observed : ReferenceSystemTrace.Observed (parent := parent) h initial) :
    (h.finalState.accountMap == ∅) = false := by
  obtain ⟨_,_,_,_,_,_,_,_,terminal,_⟩ := observed
  exact WorldNonempty.beq_empty_false_of_hasOwner terminal.owner

/-- Bind this same completed code frame to its actual transferred-world Θ
context. Fuel consumes the existing Θ wrapper exactly once. -/
theorem commits {kind : Kind} {parent : ReferenceStorageView.Parent}
    {steps cap outputBytes : Nat} {initial : View}
    (c : MessageCall.Context) (codeEq : c.code = runtimeCode kind)
    (evalFuel : Nat) (hf : c.fuel = evalFuel+1)
    (h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes
      (CallBridge.codeCall c codeEq evalFuel).fuel (CallBridge.codeCall c codeEq evalFuel).entry)
    (observed : ReferenceSystemTrace.Observed (parent := parent) h initial) :
    c.result = .ok
      (h.finalState.createdAccounts,h.finalState.accountMap,h.finalState.gasAvailable,
        h.finalState.substate,true,h.output) := by
  exact CallBridge.commits_endpoint c codeEq evalFuel hf
    h.finalState.createdAccounts h.finalState.accountMap h.finalState.gasAvailable
    h.finalState.substate h.output
    (xi_result (CallBridge.codeCall c codeEq evalFuel) h) (nonempty h observed)

#print axioms xi_result
#print axioms nonempty
#print axioms commits
end Eip8282.Audit.Integrator.ReferenceSystemEndpoint

end

section

/-! ## ReferenceSystemEntry -/

/-! One constructed actual SYSTEM execution carries both its source-shaped
views and its sequential source-formula payment. Empty calldata discharges
the checked-size premise for the proposed mandatory dispatcher. This does not
adopt that dispatcher or identify source storage-gas readings. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemEntry
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView SystemExecutionResources SystemMeterResources
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem attach {kind : Kind} (c : XiCall kind)
    {steps cap outputBytes : Nat}
    (h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes c.fuel c.entry)
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState)
    (permission : c.env.perm = true) (cdfit : c.env.calldata.size < UInt256.size)
    (output_fit : outputBytes ≤ 32*cap) (host : 32*cap < 2^System.Platform.numBits) :
    ReferenceSystemTrace.Observed (parent := parent) h (initial c tx) := by
  have hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) c.entry := by
    cases kind
    · exact ⟨c.code_pinned,Or.inl RuntimeExecutionScope.deposit.entry⟩
    · exact ⟨c.code_pinned,Or.inl RuntimeExecutionScope.exit.entry⟩
  exact ReferenceSystemTrace.attach h hat (initial c tx)
    (initial_related c parent tx slots owner) permission cdfit output_fit host

/-- No independent execution, termination, operand or capacity certificate is
supplied. The one produced execution is used by both view and payment proofs. -/
theorem deposit (inputs : Inputs) (c : XiCall .deposit)
    (system : Deposit.callerWord c = sysW) (permission : c.env.perm = true)
    (gas : c.gas = UInt256.ofNat 30000000) (fuel : 8502 ≤ c.fuel)
    (empty : c.env.calldata = ByteArray.empty)
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) :
    ∃ h : Completed RuntimeExecutionScope.deposit 8500 400 11776 c.fuel c.entry,
      Paid inputs h systemMeter ∧
      ReferenceSystemTrace.Observed (kind := .deposit) (parent := parent) h (initial c tx) := by
  obtain ⟨h,hpaid⟩ := SystemMeterResources.deposit inputs c system permission gas fuel
  refine ⟨h,hpaid,attach c h parent tx slots owner permission ?_ (by decide) ?_⟩
  · rw [empty]; decide
  · rcases System.Platform.numBits_eq with hn | hn <;> rw [hn] <;> decide

theorem exit (inputs : Inputs) (c : XiCall .exit)
    (system : Exit.callerWord c = sysW) (permission : c.env.perm = true)
    (gas : c.gas = UInt256.ofNat 30000000) (fuel : 802 ≤ c.fuel)
    (empty : c.env.calldata = ByteArray.empty)
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) :
    ∃ h : Completed RuntimeExecutionScope.exit 800 40 1088 c.fuel c.entry,
      Paid inputs h systemMeter ∧
      ReferenceSystemTrace.Observed (kind := .exit) (parent := parent) h (initial c tx) := by
  obtain ⟨h,hpaid⟩ := SystemMeterResources.exit inputs c system permission gas fuel
  refine ⟨h,hpaid,attach c h parent tx slots owner permission ?_ (by decide) ?_⟩
  · rw [empty]; decide
  · rcases System.Platform.numBits_eq with hn | hn <;> rw [hn] <;> decide

#print axioms attach
#print axioms deposit
#print axioms exit
end Eip8282.Audit.Integrator.ReferenceSystemEntry

end

section

/-! ## ReferenceSystemGuarantees -/

/-! The source-shaped SYSTEM trace and payment feed the three actual receipt
guarantees through one Completed witness. The initial journal invariant is a
history-producer input here; canonical reachability and source interpretation
are not replaced by assuming that input is protocol-valid. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemGuarantees
open EvmYul EvmYul.EVM
open ReachableCalls (Contract Transition PinnedCall)
open JournalInvariant (Invariant modelKind)
open SystemExecutionResources ReferenceRuntimeView SystemMeterResources
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- The exact successful message receipt is constructed, then consumed by all
three guarantee parents. No independent receipt or poststate is supplied. -/
theorem attach (kind : Contract) (c : MessageCall.Context)
    (pinned : PinnedCall kind c)
    (codeEq : c.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind))
    (evalFuel : Nat) (hf : c.fuel = evalFuel+1)
    {steps cap outputBytes : Nat} {parent : ReferenceStorageView.Parent} {initial : View}
    (h : Completed (ReferenceRuntimeSites.runtime (modelKind kind)) steps cap outputBytes
      (CallBridge.codeCall c codeEq evalFuel).fuel (CallBridge.codeCall c codeEq evalFuel).entry)
    (observed : ReferenceSystemTrace.Observed (parent := parent) h initial)
    {budget : Nat} (invariant : Invariant kind budget c.world)
    (bound : budget < 2^128) (fit : c.calldata.size < UInt256.size) :
    c.result = .ok (h.finalState.createdAccounts,h.finalState.accountMap,
      h.finalState.gasAvailable,h.finalState.substate,true,h.output) ∧
    NestedProtectedJournal.Observed kind c h.finalState.createdAccounts h.finalState.accountMap
      h.finalState.substate true h.output := by
  have hr := ReferenceSystemEndpoint.commits c codeEq evalFuel hf h observed
  let t : Transition kind c.world h.finalState.accountMap :=
    { call := c, pinned := pinned, pre := rfl, created := h.finalState.createdAccounts,
      gas := h.finalState.gasAvailable, substate := h.finalState.substate,
      success := true, output := h.output, executed := hr }
  exact ⟨hr,JournalGuarantees.completed t invariant bound fit⟩

/-- Preserve the SYSTEM journal invariant together with the same actual
receipt, three guarantees, source-shaped trace and paid event sequence. -/
theorem system (kind : Contract) (c : MessageCall.Context)
    (pinned : PinnedCall kind c)
    (codeEq : c.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind))
    (evalFuel : Nat) (hf : c.fuel = evalFuel+1)
    {steps cap outputBytes : Nat} {parent : ReferenceStorageView.Parent} {initial : View}
    (h : Completed (ReferenceRuntimeSites.runtime (modelKind kind)) steps cap outputBytes
      (CallBridge.codeCall c codeEq evalFuel).fuel (CallBridge.codeCall c codeEq evalFuel).entry)
    (observed : ReferenceSystemTrace.Observed (parent := parent) h initial)
    (inputs : Inputs) (meter : ReferenceStorageGas.Meter) (paid : Paid inputs h meter)
    (caller : c.caller = Eip8282.Audit.EvmRunner.sysAddr) (value : c.value = ⟨0⟩)
    {budget : Nat} (invariant : Invariant kind budget c.world)
    (bound : budget < 2^128) (fit : c.calldata.size < UInt256.size) :
    c.result = .ok (h.finalState.createdAccounts,h.finalState.accountMap,
      h.finalState.gasAvailable,h.finalState.substate,true,h.output) ∧
    NestedProtectedJournal.Observed kind c h.finalState.createdAccounts h.finalState.accountMap
      h.finalState.substate true h.output ∧
    Invariant kind budget h.finalState.accountMap ∧
    ReferenceSystemTrace.Observed (parent := parent) h initial ∧ Paid inputs h meter := by
  obtain ⟨hr,hg⟩ := attach kind c pinned codeEq evalFuel hf h observed invariant bound fit
  let t : Transition kind c.world h.finalState.accountMap :=
    { call := c, pinned := pinned, pre := rfl, created := h.finalState.createdAccounts,
      gas := h.finalState.gasAvailable, substate := h.finalState.substate,
      success := true, output := h.output, executed := hr }
  exact ⟨hr,hg,SystemJournal.preserves t caller value fit bound invariant,observed,paid⟩

#print axioms attach
#print axioms system
end Eip8282.Audit.Integrator.ReferenceSystemGuarantees

end

section

/-! ## ReferenceSystemSourcePayment -/

/-! A complete source-formula payment over evolving SYSTEM views, including
RETURN. Each storage event uses the same view's current/original/new values and
pre-access warmth. The literal meter fold, source output and actual receipt
share one completed execution; source interpreter and context bindings remain
separate. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemSourcePayment
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceSystemReadingsTrace
open SystemTraceAnnotations SystemExecutionResources SystemMeterResources ReferenceMeterPath
open ReferenceMemoryCapacity (cost)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def terminalCost (v : View) (off len : UInt256) : Nat :=
  cost ((ReferenceReturnView.returnMemory v off len).size/32)-cost (words v)

def Whole {kind : Kind} (parent : ReferenceStorageView.Parent) (created : Set AccountAddress)
    {steps cap outputBytes fuel : Nat} {pre : EVM.State}
    (h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes fuel pre)
    (v : View) (w : Warm) (meter : ReferenceStorageGas.Meter) : Prop :=
  ∃ prefixEvents events final finish finalWarm off len rest,
    Coupled kind parent created fuel pre v w h.trace (h.rem+2) h.exitState finish finalWarm prefixEvents ∧
    Related parent finish h.exitState ∧ WarmRelated finalWarm h.exitState ∧
    finish.storage.created = created ∧
    ReferenceDecodeSites.referenceDecode finish.env.code finish.pc = some (.RETURN,none) ∧
    finish.stack = off::len::rest ∧
    ReferenceReturnView.Result parent finish off len rest h.finalState ∧
    h.output = (ReferenceReturnView.returnMemory finish off len).extract off.toNat (off.toNat+len.toNat) ∧
    terminalCost finish off len = delta h.exitState h.finalState ∧
    events = prefixEvents++[.ordinary (terminalCost finish off len)] ∧
    run events meter = some final ∧
    meter.execution-(2100*(steps+1)+12100*4+cost cap) ≤ final.execution ∧
    meter.reservoir-97920*4 ≤ final.reservoir ∧ WarmRelated finalWarm h.finalState

/-- Every internal view, access set, reading and payment is constructed from
the actual trace and initial aggregate resources. -/
theorem attach {kind : Kind} {parent : ReferenceStorageView.Parent} {created : Set AccountAddress}
    {steps cap outputBytes fuel : Nat} {pre : EVM.State}
    (h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes fuel pre)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (v : View) (w : Warm) (related : Related parent v pre) (warm : WarmRelated w pre)
    (created_eq : v.storage.created = created)
    (permission : v.env.perm = true) (cdfit : v.env.calldata.size < UInt256.size)
    (output_fit : outputBytes ≤ 32*cap) (host : 32*cap < 2^System.Platform.numBits)
    (meter : ReferenceStorageGas.Meter)
    (execution : 2100*(steps+1)+12100*4+cost cap ≤ meter.execution)
    (reservoir : 97920*4 ≤ meter.reservoir) : Whole parent created h v w meter := by
  obtain ⟨prefixEvents,events,final,hpriced,_,hevents,hpaid,he,hr⟩ :=
    pay_completed (ReferenceSourceReadings.inputs parent created) h hat output_fit meter execution reservoir
  obtain ⟨finish,finalWarm,hcoupled,hrel,hw,hcreated⟩ := from_priced hpriced hat v w related warm created_eq
    (fun op hop => h.allowed op (List.mem_append_left _ hop)) permission cdfit h.exit_capacity host
  obtain ⟨_,_,_,hcap,_⟩ := SystemMemoryResources.attach h hat output_fit
  obtain ⟨off,len,rest,_,hshape,hresult,hout⟩ :=
    ReferenceReturnView.halted h.halt.charge h.terminal hrel hcap host h.returned
  have hcost : terminalCost finish off len = delta h.exitState h.finalState := by
    unfold terminalCost delta
    rw [hresult.memory.size,words_related hrel]
    congr 2
    omega
  have hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
      (decodeAt h.exitState).1 h.exitState =
      .ok (Eip8282.Audit.SymExec.charged h.exitState .RETURN,
        C' (Eip8282.Audit.SymExec.charged h.exitState .RETURN) .RETURN) := by
    rw [h.halt.decode]
    exact h.halt.charge
  have hs : StepOk (h.rem+1)
      (C' (Eip8282.Audit.SymExec.charged h.exitState .RETURN) .RETURN)
      (decodeAt h.exitState) (Eip8282.Audit.SymExec.charged h.exitState .RETURN) h.finalState := by
    rw [h.halt.decode]
    exact h.terminal
  have hwfinal : WarmRelated finalWarm h.finalState := by
    have hh := ReferenceStorageWarmth.accepted_warm h.at_exit hz hs hrel hw
    simpa only [h.halt.decode,warmAfter] using hh
  refine ⟨prefixEvents,events,final,finish,finalWarm,off,len,rest,
    hcoupled,hrel,hw,hcreated,?_,hshape,hresult,?_,hcost,?_,hpaid,he,hr,hwfinal⟩
  · rw [hrel.env,hrel.pc,h.at_exit.1,ReferenceRuntimeSites.code_eq]
    exact ReferenceTerminalDecode.return_decode h.at_exit (congrArg Prod.fst h.halt.decode)
  · exact hout.trans (ReferenceReturnSlice.output_eq_extract hrel off len)
  · rw [hcost]; exact hevents

theorem Whole.observed {kind : Kind} {parent : ReferenceStorageView.Parent} {created : Set AccountAddress}
    {steps cap outputBytes fuel : Nat} {pre : EVM.State}
    {h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes fuel pre}
    {v : View} {w : Warm} {meter : ReferenceStorageGas.Meter}
    (whole : Whole parent created h v w meter) :
    ReferenceSystemTrace.Observed (parent := parent) h v := by
  obtain ⟨_,_,_,finish,_,off,len,rest,hcoupled,hrel,_,_,hdecode,hshape,hresult,hout,_⟩ := whole
  exact ⟨finish,off,len,rest,hcoupled.viewed,hrel,hdecode,hshape,hresult,hout⟩

theorem Whole.paid {kind : Kind} {parent : ReferenceStorageView.Parent} {created : Set AccountAddress}
    {steps cap outputBytes fuel : Nat} {pre : EVM.State}
    {h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes fuel pre}
    {v : View} {w : Warm} {meter : ReferenceStorageGas.Meter}
    (whole : Whole parent created h v w meter) :
    Paid (ReferenceSourceReadings.inputs parent created) h meter := by
  obtain ⟨prefixEvents,events,final,_,_,_,_,_,hc,_,_,_,_,_,_,_,hcost,hevents,hpaid,he,hr,_⟩ := whole
  refine ⟨prefixEvents,events,final,hc.priced,?_,?_,hpaid,he,hr⟩
  · exact ⟨0,rfl,by simp⟩
  · rw [hcost] at hevents; exact hevents

#print axioms attach
#print axioms Whole.observed
#print axioms Whole.paid
end Eip8282.Audit.Integrator.ReferenceSystemSourcePayment

end

section

/-! ## ReferenceSystemSourceEntry -/

/-! Both SYSTEM entries construct their complete source-view payment using
concrete evolving storage readings. Initial layered-storage and warm-set
bindings remain source-context obligations; no execution or reading oracle is
supplied. The proposed grant does not adopt a protocol dispatcher. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemSourceEntry
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSourceReadings SystemExecutionResources SystemMeterResources
open ReferenceSystemSourcePayment
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem attach {kind : Kind} (c : XiCall kind) {steps cap outputBytes : Nat}
    (h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes c.fuel c.entry)
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx) (w : Warm)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warm : WarmRelated w c.entry)
    (permission : c.env.perm = true) (cdfit : c.env.calldata.size < UInt256.size)
    (output_fit : outputBytes ≤ 32*cap) (host : 32*cap < 2^System.Platform.numBits)
    (meter : ReferenceStorageGas.Meter)
    (execution : 2100*(steps+1)+12100*4+ReferenceMemoryCapacity.cost cap ≤ meter.execution)
    (reservoir : 97920*4 ≤ meter.reservoir) :
    Whole parent tx.created h (initial c tx) w meter := by
  have hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) c.entry := by
    cases kind
    · exact ⟨c.code_pinned,Or.inl RuntimeExecutionScope.deposit.entry⟩
    · exact ⟨c.code_pinned,Or.inl RuntimeExecutionScope.exit.entry⟩
  exact ReferenceSystemSourcePayment.attach h hat (initial c tx) w
    (initial_related c parent tx slots owner) warm rfl permission cdfit output_fit host meter execution reservoir

theorem deposit (c : XiCall .deposit)
    (system : Deposit.callerWord c = sysW) (permission : c.env.perm = true)
    (gas : c.gas = UInt256.ofNat 30000000) (fuel : 8502 ≤ c.fuel)
    (empty : c.env.calldata = ByteArray.empty)
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx) (w : Warm)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warm : WarmRelated w c.entry) :
    ∃ h : Completed RuntimeExecutionScope.deposit 8500 400 11776 c.fuel c.entry,
      Whole (kind := .deposit) parent tx.created h (initial c tx) w systemMeter := by
  obtain ⟨h⟩ := SystemExecutionResources.deposit c system permission (by rw [gas]; decide) fuel
  refine ⟨h,attach c h parent tx w slots owner warm permission ?_ (by decide) ?_
    systemMeter (by decide) (by decide)⟩
  · rw [empty]; decide
  · rcases System.Platform.numBits_eq with hn | hn <;> rw [hn] <;> decide

theorem exit (c : XiCall .exit)
    (system : Exit.callerWord c = sysW) (permission : c.env.perm = true)
    (gas : c.gas = UInt256.ofNat 30000000) (fuel : 802 ≤ c.fuel)
    (empty : c.env.calldata = ByteArray.empty)
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx) (w : Warm)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warm : WarmRelated w c.entry) :
    ∃ h : Completed RuntimeExecutionScope.exit 800 40 1088 c.fuel c.entry,
      Whole (kind := .exit) parent tx.created h (initial c tx) w systemMeter := by
  obtain ⟨h⟩ := SystemExecutionResources.exit c system permission (by rw [gas]; decide) fuel
  refine ⟨h,attach c h parent tx w slots owner warm permission ?_ (by decide) ?_
    systemMeter (by decide) (by decide)⟩
  · rw [empty]; decide
  · rcases System.Platform.numBits_eq with hn | hn <;> rw [hn] <;> decide

/-- The three receipt guarantees consume the same source-coupled witness.
The pre-invariant is supplied by the initialized-history producer. -/
theorem guarantees (kind : ReachableCalls.Contract) (c : MessageCall.Context)
    (pinned : ReachableCalls.PinnedCall kind c)
    (codeEq : c.code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind))
    (evalFuel : Nat) (hf : c.fuel = evalFuel+1)
    {steps cap outputBytes : Nat} {parent : ReferenceStorageView.Parent} {created : Set AccountAddress}
    {v : View} {w : Warm} {meter : ReferenceStorageGas.Meter}
    (h : Completed (ReferenceRuntimeSites.runtime (JournalInvariant.modelKind kind)) steps cap outputBytes
      (CallBridge.codeCall c codeEq evalFuel).fuel (CallBridge.codeCall c codeEq evalFuel).entry)
    (whole : Whole parent created h v w meter)
    (caller : c.caller = Eip8282.Audit.EvmRunner.sysAddr) (value : c.value = ⟨0⟩)
    {budget : Nat} (invariant : JournalInvariant.Invariant kind budget c.world)
    (bound : budget < 2^128) (fit : c.calldata.size < UInt256.size) :
    c.result = .ok (h.finalState.createdAccounts,h.finalState.accountMap,
      h.finalState.gasAvailable,h.finalState.substate,true,h.output) ∧
    NestedProtectedJournal.Observed kind c h.finalState.createdAccounts h.finalState.accountMap
      h.finalState.substate true h.output ∧
    JournalInvariant.Invariant kind budget h.finalState.accountMap ∧ Whole parent created h v w meter := by
  obtain ⟨hr,hg,hi,_,_⟩ := ReferenceSystemGuarantees.system kind c pinned codeEq evalFuel hf h
    whole.observed (ReferenceSourceReadings.inputs parent created) meter whole.paid
    caller value invariant bound fit
  exact ⟨hr,hg,hi,whole⟩

#print axioms attach
#print axioms deposit
#print axioms exit
#print axioms guarantees
end Eip8282.Audit.Integrator.ReferenceSystemSourceEntry

end

section

/-! ## ReferenceSystemStackBound -/

/-! Derive the post-stack bound consumed by paid SYSTEM handler acceptance
from the actual old Z delta/alpha guards and the same source action. No output
stack bound is left as a public execution assumption. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemStackBound
open EvmYul EvmYul.EVM ReferenceRuntimeView ReferenceCheckedDispatch
open Eip8282.Audit.Model (Kind)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private theorem stack_cases (s : List UInt256) :
    s = [] ∨ (∃ a, s = [a]) ∨ (∃ a b, s = [a,b]) ∨
    (∃ a b c, s = [a,b,c]) ∨ (∃ a b c d, s = [a,b,c,d]) ∨
    (∃ a b c d e rest, s = a::b::c::d::e::rest) := by
  cases s with
  | nil => exact Or.inl rfl
  | cons a s =>
    right
    cases s with
    | nil => exact Or.inl ⟨a,rfl⟩
    | cons b s =>
      right
      cases s with
      | nil => exact Or.inl ⟨a,b,rfl⟩
      | cons c s =>
        right
        cases s with
        | nil => exact Or.inl ⟨a,b,c,rfl⟩
        | cons d s =>
          right
          cases s with
          | nil => exact Or.inl ⟨a,b,c,d,rfl⟩
          | cons e rest => exact Or.inr ⟨a,b,c,d,e,rest,rfl⟩

theorem handler {kind : Kind} {parent : ReferenceStorageView.Parent} {h : Handler}
    {arg : Option (UInt256 × Nat)} {v next : View}
    (action : ReferenceSystemAction.Action kind parent (opcode h,arg) v next)
    (lower : (δ (opcode h)).getD 0 ≤ v.stack.length)
    (bound : v.stack.length - (δ (opcode h)).getD 0 + (α (opcode h)).getD 0 ≤ 1024) :
    next.stack.length ≤ 1024 := by
  rcases stack_cases v.stack with shape | ⟨a,shape⟩ | ⟨a,b,shape⟩ | ⟨a,b,c,shape⟩ |
    ⟨a,b,c,d,shape⟩ | ⟨a,b,c,d,e,rest,shape⟩
  all_goals cases h
  all_goals try (rename_i selected; cases selected)
  all_goals simp only [opcode,ReferenceWordOps.opcode,ReferenceCheckedEnvironmentStep.opcode,
    ReferenceCheckedStackControlStep.opcode,ReferenceCheckedStackControlStep.family,ReferencePureAction.opcode,
    ReferenceCheckedMemoryStore.opcode,ReferenceCheckedCopyLogStep.opcode,ReferenceCheckedTerminalStep.opcode,
    Bool.false_eq_true,if_false,if_true,δ,α,Option.getD_some,shape,List.length_cons,List.length_nil] at lower bound action
  all_goals cases action
  all_goals try (rename_i pure; simp only [ReferencePureAction.action,ReferencePureAction.classify,
    Option.bind_some,Option.bind_none,ReferencePureAction.familyAction,ReferenceStackOps.dupDepth,
    ReferenceStackOps.swapDepth,shape] at pure)
  all_goals repeat (first | contradiction | split at pure)
  all_goals try (by_cases hj : a.toNat ∈ ReferenceDecodeSites.referenceJumps (ReferenceRuntimeSites.reference kind) <;> simp only [hj,if_pos,if_neg] at pure)
  all_goals try contradiction
  all_goals try (rcases pure with ⟨valid,pure⟩)
  all_goals try cases pure
  all_goals simp_all [ReferencePureAction.advance,stackAction,loadAction,storeAction,memoryAction,
    List.length_take,List.length_drop]
  all_goals omega

#print axioms handler
end Eip8282.Audit.Integrator.ReferenceSystemStackBound

end
