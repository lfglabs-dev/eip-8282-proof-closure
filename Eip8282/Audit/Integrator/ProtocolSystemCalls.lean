import Eip8282.Audit.Integrator.SystemJournal
import Eip8282.Audit.Integrator.NestedProtectedJournal

/-! Actual pinned-EVM SYSTEM progress and safety, with explicit counterpart
inputs for proposed Amsterdam. Reference dispatcher: EL
0cc100eb190b64b23baba72dac0165652eaec252, fork.py:729-786,904-923;
audit/receipts/direct-reference-migration-deployment-sources-20260910.json.
OPEN: canonical scheduling/adoption, base-fee word conversion, empty substate
and original-world mapping, installed code/history, and Amsterdam dual-pool
execution/state-gas correspondence. A 30M numeric grant is not that transport.
-/
namespace Eip8282.Audit.Integrator.ProtocolSystemCalls
open EvmYul EvmYul.EVM
open ReachableCalls (Contract Transition address runtime)
open JournalInvariant (modelKind)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def call (kind : Contract) (world : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (gasPrice : UInt256)
    (fuel : Nat) (data : ByteArray) : MessageCall.Context :=
  { fuel := fuel, created := ∅, genesis := genesis, blocks := blocks,
    world := world, originalWorld := world, substate := default,
    caller := Eip8282.Audit.EvmRunner.sysAddr, origin := Eip8282.Audit.EvmRunner.sysAddr,
    target := address kind, code := runtime kind, gas := ⟨30000000⟩,
    gasPrice := gasPrice, value := ⟨0⟩, apparentValue := ⟨0⟩,
    calldata := data, depth := 0, header := header, permission := true, blobHashes := [] }

theorem completes (kind : Contract) (world : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (gasPrice : UInt256)
    (fuel : Nat) (data : ByteArray) (installed : JournalInvariant.CodeAt kind world)
    (resources : 8503 ≤ fuel) :
    ∃ after, ∃ t : Transition kind world after,
      t.call = call kind world genesis blocks header gasPrice fuel data ∧ t.success = true := by
  let c := call kind world genesis blocks header gasPrice fuel data
  have hc : c.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
    cases kind <;> rfl
  obtain ⟨old,ho,hcode⟩ := installed
  obtain ⟨created,after,gas,ss,out,hr⟩ := SystemProgress.pinned (modelKind kind) c hc rfl
    ⟨old,ho⟩ rfl (by change 2500000 ≤ 30000000; decide +kernel) resources
  let t : Transition kind world after :=
    { call := c, pinned := ⟨rfl,rfl,⟨old,ho,hcode⟩,rfl⟩,
      pre := rfl, created := created, gas := gas, substate := ss,
      success := true, output := out, executed := hr }
  exact ⟨after,t,rfl,rfl⟩

theorem guarantees (kind : Contract) (world : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (gasPrice : UInt256)
    (fuel : Nat) (data : ByteArray) {budget : Nat}
    (initial : JournalInvariant.Invariant kind budget world) (bound : budget < 2^128)
    (fit : data.size < UInt256.size) (resources : 8503 ≤ fuel) :
    ∃ after, ∃ t : Transition kind world after,
      t.call = call kind world genesis blocks header gasPrice fuel data ∧ t.success = true ∧
      JournalInvariant.Invariant kind budget after ∧
      NestedProtectedJournal.Observed kind t.call t.created after t.substate t.success t.output := by
  obtain ⟨after,t,hc,hs⟩ := completes kind world genesis blocks header gasPrice fuel data initial.1 resources
  have hcaller : t.call.caller = Eip8282.Audit.EvmRunner.sysAddr := by rw [hc]; rfl
  have hvalue : t.call.value = ⟨0⟩ := by rw [hc]; rfl
  have hfit : t.call.calldata.size < UInt256.size := by rw [hc]; exact fit
  exact ⟨after,t,hc,hs,SystemJournal.preserves t hcaller hvalue hfit bound initial,
    JournalGuarantees.completed t initial bound hfit⟩

/-- Empty calldata covers the normal dispatch/activation shape; actual fork
scheduling and state-gas resources are still separate adapter obligations. -/
theorem empty_guarantees (kind : Contract) (world : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (gasPrice : UInt256)
    (fuel : Nat) {budget : Nat}
    (initial : JournalInvariant.Invariant kind budget world) (bound : budget < 2^128)
    (resources : 8503 ≤ fuel) :
    ∃ after, ∃ t : Transition kind world after,
      t.call = call kind world genesis blocks header gasPrice fuel ByteArray.empty ∧ t.success = true ∧
      JournalInvariant.Invariant kind budget after ∧
      NestedProtectedJournal.Observed kind t.call t.created after t.substate t.success t.output :=
  guarantees kind world genesis blocks header gasPrice fuel ByteArray.empty initial bound
    (by decide +kernel) resources

#print axioms completes
#print axioms guarantees
#print axioms empty_guarantees
end Eip8282.Audit.Integrator.ProtocolSystemCalls
