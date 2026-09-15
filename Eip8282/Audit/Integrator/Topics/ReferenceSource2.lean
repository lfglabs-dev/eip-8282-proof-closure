import Eip8282.Audit.Integrator.Topics.Reference5
import Eip8282.Audit.Integrator.ReferenceSourceReplayTrace
import Eip8282.Audit.Integrator.ReferenceTerminalReplay

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceSourceReplayEntry -/

/-! Build the replay call's gas and fuel from finite source work at an exact
protected entry. Runtime context/world/value are retained; only synthetic
resources change. Source entry/storage/warmth/payment extraction is explicit.
This is an effect-proof call, not a canonical Ethereum transaction receipt. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceReplayEntry
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings
open ReferenceMeterPath ReferenceExecutionLedger ReferenceSourceReplayTrace
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- Extra is the source terminal's execution charge, reserved after the prefix. -/
def call {kind : Kind} (c : XiCall kind) (events : List Event) (extra : Nat) : XiCall kind :=
  {c with gas := UInt256.ofNat (222*(work events+extra)+2301),fuel := events.length+2}

theorem gas_exact {kind : Kind} (c : XiCall kind) (events : List Event) (extra : Nat)
    (bound : work events+extra ≤ 30000000) :
    (call c events extra).entry.gasAvailable.toNat = 222*(work events+extra)+2301 :=
  Eip8282.Audit.EntryReach.toNat_ofNat_lit _ (ReferenceReplayMemoryCost.word_fit bound)

theorem context {kind : Kind} (c : XiCall kind) (events : List Event) (extra : Nat) :
    (call c events extra).env = c.env ∧ (call c events extra).σ = c.σ ∧
    (call c events extra).substate = c.substate ∧ (call c events extra).σ₀ = c.σ₀ :=
  ⟨rfl,rfl,rfl,rfl⟩

/-- No old trace, budget, or initial memory/stack condition is supplied. Empty
runtime entry and the literal finite source work derive those resources. -/
theorem from_entry {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    (extra : Nat)
    (source : Run kind parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState)
    (warmRelated : WarmRelated warm c.entry)
    (bound : work events+extra ≤ 30000000) :
    ∃ post trace,
      Coupled kind parent tx.created (events.length+2) (call c events extra).entry (initial c tx) warm
        trace 2 post finish finalWarm events ∧
      Related parent finish post ∧ RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) post ∧
      WarmRelated finalWarm post ∧ finish.storage.created = tx.created ∧
      222*extra+2301 ≤ post.gasAvailable.toNat ∧
      ReferenceMemoryCapacity.cost (words finish)+extra ≤ 30000000 ∧ finish.stack.length ≤ 1024 := by
  let replay := call c events extra
  have related : Related parent (initial c tx) replay.entry := initial_related replay parent tx slots owner
  have site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) replay.entry := by
    refine ⟨?_,Or.inl ?_⟩
    · change c.env.code = _
      rw [c.code_pinned]
      cases kind <;> rfl
    · exact (ReferenceRuntimeSites.runtime kind).entry
  have emptyCost : ReferenceMemoryCapacity.cost (words (initial c tx)) = 0 := by
    simp [ReferenceMemoryCapacity.cost,words,initial]
  have domain : ReferenceMemoryCapacity.cost (words (initial c tx))+work events ≤ 30000000 := by
    rw [emptyCost]
    omega
  have budget : 222*work events+2301 ≤ replay.entry.gasAvailable.toNat := by
    rw [gas_exact c events extra bound]
    omega
  obtain ⟨post,trace,coupled,finalRelated,finalSite,finalWarmRelated,created,reserve,total⟩ :=
    ReferenceSourceReplayTrace.replay source 1 related site warmRelated rfl domain budget
  have gas : 222*extra+2301 ≤ post.gasAvailable.toNat := by
    rw [gas_exact c events extra bound] at total
    omega
  have memory := source.memory_le
  have finalMemory : ReferenceMemoryCapacity.cost (words finish)+extra ≤ 30000000 := by
    rw [emptyCost] at memory
    omega
  exact ⟨post,trace,coupled,finalRelated,finalSite,finalWarmRelated,created,gas,finalMemory,
    source.stack_bound (by change 0 ≤ 1024; decide)⟩

#print axioms gas_exact
#print axioms context
#print axioms from_entry
end Eip8282.Audit.Integrator.ReferenceSourceReplayEntry

end

section

/-! ## ReferenceSourceReplayCompletion -/

/-! Whole finite protected effect replay, including actual STOP/RETURN/REVERT.
The source-shaped prefix is supplied, never an old execution. Its paid-work
bound builds synthetic gas/fuel and memory bounds. Actual Python source and
outer journal/rollback extraction remain explicit; REVERT's internal view is
not treated as a committed result. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceReplayCompletion
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings
open ReferenceMeterPath ReferenceExecutionLedger ReferenceSourceReplayTrace
open ReferenceSourceReplayEntry
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem decode_view {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v : View} {pre : EVM.State} (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre) :
    decodeAt pre = instruction v := by
  unfold instruction
  rw [related.env,related.pc,site.1,ReferenceRuntimeSites.code_eq]
  exact ReferenceAllDecode.decode_matches site

theorem stop {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    (source : Run kind parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (bound : work events ≤ 30000000) (halt : instruction finish = (.STOP,none)) :
    ∃ middle post trace,
      Coupled kind parent tx.created (events.length+2) (call c events 0).entry (initial c tx) warm
        trace 2 middle finish finalWarm events ∧
      decodeAt middle = (.STOP,none) ∧
      X (events.length+2) (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
        (call c events 0).entry = .ok (.success post ByteArray.empty) ∧ Related parent finish post := by
  obtain ⟨middle,trace,coupled,related,site,_,_,_,_,stack⟩ :=
    from_entry c 0 source slots owner warmRelated (by simpa using bound)
  have decoded := (decode_view related site).trans halt
  obtain ⟨post,terminal,postRelated,_⟩ := ReferenceTerminalReplay.stop 0 related decoded stack
  have same := coupled.viewed.erase.X_eq
  exact ⟨middle,post,trace,coupled,decoded,same.trans terminal,postRelated⟩

theorem returned {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    {off len : UInt256} {rest : Stack UInt256}
    (source : Run kind parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (shape : finish.stack = off::len::rest)
    (bound : work events+ReferenceTerminalReplay.charge finish off len ≤ 30000000)
    (halt : instruction finish = (.RETURN,none)) :
    ∃ middle post trace,
      Coupled kind parent tx.created (events.length+2)
        (call c events (ReferenceTerminalReplay.charge finish off len)).entry (initial c tx) warm
        trace 2 middle finish finalWarm events ∧
      X (events.length+2) (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
        (call c events (ReferenceTerminalReplay.charge finish off len)).entry =
          .ok (.success post (ReferenceReturnView.output finish off len)) ∧
      ReferenceReturnView.Result parent finish off len rest post := by
  obtain ⟨middle,trace,coupled,related,site,_,_,gas,domain,stack⟩ :=
    from_entry c (ReferenceTerminalReplay.charge finish off len) source slots owner warmRelated bound
  have decoded := (decode_view related site).trans halt
  have restBound : rest.length ≤ 1024 := by rw [shape] at stack; simp only [List.length_cons] at stack; omega
  obtain ⟨post,terminal,result,_⟩ := ReferenceTerminalReplay.returned 0 related decoded shape restBound domain (by omega)
  exact ⟨middle,post,trace,coupled,coupled.viewed.erase.X_eq.trans terminal,result⟩

theorem reverted {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    {off len : UInt256} {rest : Stack UInt256}
    (source : Run kind parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (shape : finish.stack = off::len::rest)
    (bound : work events+ReferenceTerminalReplay.charge finish off len ≤ 30000000)
    (halt : instruction finish = (.REVERT,none)) :
    ∃ middle post trace,
      Coupled kind parent tx.created (events.length+2)
        (call c events (ReferenceTerminalReplay.charge finish off len)).entry (initial c tx) warm
        trace 2 middle finish finalWarm events ∧
      X (events.length+2) (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
        (call c events (ReferenceTerminalReplay.charge finish off len)).entry =
          .ok (.revert post.gasAvailable (ReferenceReturnView.output finish off len)) ∧
      ReferenceReturnView.Result parent finish off len rest post := by
  obtain ⟨middle,trace,coupled,related,site,_,_,gas,domain,stack⟩ :=
    from_entry c (ReferenceTerminalReplay.charge finish off len) source slots owner warmRelated bound
  have decoded := (decode_view related site).trans halt
  have restBound : rest.length ≤ 1024 := by rw [shape] at stack; simp only [List.length_cons] at stack; omega
  obtain ⟨post,terminal,result,_⟩ := ReferenceTerminalReplay.reverted 0 related decoded shape restBound domain (by omega)
  exact ⟨middle,post,trace,coupled,coupled.viewed.erase.X_eq.trans terminal,result⟩

#print axioms stop
#print axioms returned
#print axioms reverted
end Eip8282.Audit.Integrator.ReferenceSourceReplayCompletion

end

section

/-! ## ReferenceSourcePaidAppend -/

/-! Produce an existing completed-append resource leaf from a paid source-shaped
run. Old execution success and its complete trace are reconstructed and aligned.
The same event list is used for source effects, prices, payment and leaf work.
Actual source frame identity/extraction and global survivor coverage are still
required; resource threading alone is not an occurrence-completeness proof. -/
namespace Eip8282.Audit.Integrator.ReferenceSourcePaidAppend
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings
open ReferenceMeterPath ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceExecutionLedger ReferenceSourceReplayTrace ReferenceSelectedAppendWork ReferenceTraceAgreement
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem aligned_success {kind : Kind} {parent : ReferenceStorageView.Parent}
    {created : Set AccountAddress} {v finish : View} {warm finalWarm : Warm} {events : List Event}
    {vj : Array UInt256} {fuel rem : Nat} {pre middle post : EVM.State} {trace : List Labelled} {out : ByteArray}
    (tables : vj = D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
    (actual : X fuel vj pre = .ok (.success post out))
    (coupled : Coupled kind parent created fuel pre v warm trace rem middle finish finalWarm events)
    (stopped : decodeAt middle = (.STOP,none)) :
    ∃ t : SuccessInversion.SuccessTrace vj fuel pre post out,
      Coupled kind parent created fuel pre v warm t.trace (t.rem+1) t.exit finish finalWarm events := by
  subst vj
  obtain ⟨t⟩ := SuccessInversion.success_trace actual
  have terminal : Blocked (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (t.rem+1) t.exit := by
    apply blocked_of_terminal
    · rw [t.decode]; exact t.charge
    · rw [t.decode]; simpa only [Nat.add_sub_cancel] using t.step
    · rw [t.decode]; exact t.output
  obtain ⟨sameTrace,sameRem,sameExit⟩ := complete_unique coupled.viewed.erase t.run.toXRuns
    (blocked_of_stop stopped) terminal
  exact ⟨t,by simpa only [sameTrace,sameRem,sameExit] using coupled⟩

private theorem paid_bound {events : List Event} {pre post : Meter}
    (paid : runFull (events++[.ordinary 0]) pre = some post)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000) : work events ≤ 30000000 := by
  have h := ReferenceExecutionLedger.bounded (.paid _ paid)
  simp only [work,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    eventWork,Nat.add_zero] at h
  unfold work
  omega

theorem exit (c : XiCall .exit) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    (source : ReferenceSourceReplayTrace.Run .exit parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (halt : instruction finish = (.STOP,none))
    (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 48)
    {pre post : Meter} (paid : runFull (events++[.ordinary 0]) pre = some post)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000) :
    ProtectedPaid pre post (work events) := by
  have bound := paid_bound paid grant
  obtain ⟨middle,final,trace,coupled,decoded,actual,_⟩ :=
    ReferenceSourceReplayCompletion.stop c source slots owner warmRelated bound halt
  let replay := ReferenceSourceReplayEntry.call c events 0
  have tables : exitJumpdests = D_J (ReferenceRuntimeSites.runtime .exit).code ⟨0⟩ := by
    change exitJumpdests = D_J exitRuntime ⟨0⟩
    rw [exit_D_J]
  have actual' : X (events.length+2) exitJumpdests replay.entry = .ok (.success final ByteArray.empty) := by
    rw [tables]
    exact actual
  obtain ⟨t,priced⟩ := aligned_success tables actual' coupled decoded
  have leaf := ProtectedPaid.exit replay user size actual' t priced 0 paid
  simpa only [work,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    eventWork,Nat.add_zero] using leaf

theorem deposit (c : XiCall .deposit) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    (source : ReferenceSourceReplayTrace.Run .deposit parent (initial c tx) warm finish finalWarm events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (halt : instruction finish = (.STOP,none))
    (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 184)
    {pre post : Meter} (paid : runFull (events++[.ordinary 0]) pre = some post)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000) :
    ProtectedPaid pre post (work events) := by
  have bound := paid_bound paid grant
  obtain ⟨middle,final,trace,coupled,decoded,actual,_⟩ :=
    ReferenceSourceReplayCompletion.stop c source slots owner warmRelated bound halt
  let replay := ReferenceSourceReplayEntry.call c events 0
  have tables : depositJumpdests = D_J (ReferenceRuntimeSites.runtime .deposit).code ⟨0⟩ := by
    change depositJumpdests = D_J depositRuntime ⟨0⟩
    rw [deposit_D_J]
  have actual' : X (events.length+2) depositJumpdests replay.entry = .ok (.success final ByteArray.empty) := by
    rw [tables]
    exact actual
  obtain ⟨t,priced⟩ := aligned_success tables actual' coupled decoded
  have leaf := ProtectedPaid.deposit replay user size actual' t priced 0 paid
  simpa only [work,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    eventWork,Nat.add_zero] using leaf

#print axioms exit
#print axioms deposit
end Eip8282.Audit.Integrator.ReferenceSourcePaidAppend

end
