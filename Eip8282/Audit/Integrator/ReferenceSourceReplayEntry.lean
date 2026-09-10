import Eip8282.Audit.Integrator.ReferenceSourceReplayTrace

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
