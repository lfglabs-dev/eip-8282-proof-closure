import Eip8282.Audit.Integrator.ReferenceSystemSourcePayment

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
