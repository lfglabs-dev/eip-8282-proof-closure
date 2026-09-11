import Eip8282.Audit.Integrator.ReleaseCandidate

/-! An actual two-call inhibition cycle on either pinned bytecode, after the
same justified finite history. Calls and their success are constructed with
30M pinned scalar gas and sufficient evaluator fuel. This proves reversible
bytecode behavior, not its desirability, permanent inhibition, or adoption of
any Ethereum SYSTEM scheduling policy. Both calls still drain the queue.
-/
namespace Eip8282.Audit.Integrator.ReleaseInhibitionCycle
open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach (INH)
open NestedEvents
open ReachableCalls (Contract Transition address)
open JournalInvariant (Invariant modelKind)
open TransactionAppendBudget (Receipt)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

structure Cycle (kind : Contract) (before after : World) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (gasPrice : UInt256) (fuel : Nat) (data : ByteArray) where
  middle : World
  latch : Transition kind before middle
  unlock : Transition kind middle after
  latchCall : latch.call = ProtocolSystemCalls.call kind before genesis blocks header gasPrice fuel data
  unlockCall : unlock.call = ProtocolSystemCalls.call kind middle genesis blocks header gasPrice fuel ByteArray.empty
  latchSuccess : latch.success = true
  unlockSuccess : unlock.success = true
  latched : SystemSpec.worldSlot middle (address kind) (UInt256.ofNat 0) = INH
  unlocked : SystemSpec.worldSlot after (address kind) (UInt256.ofNat 0) = UInt256.ofNat 0
  latchCount : SystemSpec.worldSlot middle (address kind) (UInt256.ofNat 1) = UInt256.ofNat 0
  unlockCount : SystemSpec.worldSlot after (address kind) (UInt256.ofNat 1) = UInt256.ofNat 0
  latchGuarantees : NestedProtectedJournal.Observed kind latch.call latch.created middle latch.substate latch.success latch.output
  unlockGuarantees : NestedProtectedJournal.Observed kind unlock.call unlock.created after unlock.substate unlock.success unlock.output

private theorem word_eq {a b : UInt256} (h : a.toNat = b.toNat) : a = b := by
  cases a with | mk a =>
  cases b with | mk b =>
  exact congrArg UInt256.mk (Fin.ext h)

private theorem controls {kind : Contract} {before after : World} (t : Transition kind before after)
    {genesis : BlockHeader} {blocks : ProcessedBlocks} {header : BlockHeader}
    {gasPrice : UInt256} {fuel : Nat} {data : ByteArray}
    (hc : t.call = ProtocolSystemCalls.call kind before genesis blocks header gasPrice fuel data)
    (hs : t.success = true)
    (observed : NestedProtectedJournal.Observed kind t.call t.created after t.substate t.success t.output) :
    SystemDataSpec.ControlSlots (modelKind kind) data.size
      (SystemSpec.worldSlot before (address kind)) (SystemSpec.worldSlot after (address kind)) := by
  obtain ⟨_,_,_,control⟩ := observed
  have result := control.2.2 hs
  have sender : t.call.caller = Eip8282.Audit.EvmRunner.sysAddr := by rw [hc]; rfl
  rw [if_pos sender] at result
  simpa only [hc,ProtocolSystemCalls.call] using result

/-- No successful endpoint, inhibited starting state, post-world, queue or
per-call invariant is supplied. The same two actual receipts extend history. -/
theorem after_history {deposit exit : Receipt} {before : World}
    (history : ReleaseCandidate.History deposit exit before) (kind : Contract)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (header : BlockHeader)
    (gasPrice : UInt256) (fuel : Nat) (data : ByteArray)
    (nonempty : data.size ≠ 0) (fit : data.size < UInt256.size) (resources : 8503 ≤ fuel) :
    ∃ after, ∃ _cycle : Cycle kind before after genesis blocks header gasPrice fuel data,
      ActualJournalHistory.Trace exit.world history.receipts history.credits after ∧
      ∀ other, Invariant other (ActualJournalHistory.work history.receipts) after := by
  have initial := (ReleaseCandidate.invariants history).2.2.2
  have bound := (ReleaseCandidate.invariants history).2.2.1
  obtain ⟨middle,latch,lc,ls,_,lg⟩ := ProtocolSystemCalls.guarantees kind before genesis blocks header gasPrice fuel data
    (initial kind) bound fit resources
  have lsender : latch.call.caller = Eip8282.Audit.EvmRunner.sysAddr := by rw [lc]; rfl
  have lvalue : latch.call.value = ⟨0⟩ := by rw [lc]; rfl
  have lfit : latch.call.calldata.size < UInt256.size := by rw [lc]; exact fit
  have middleInv : ∀ other, Invariant other (ActualJournalHistory.work history.receipts) middle :=
    fun other => SystemJournal.preserves latch lsender lvalue lfit bound (initial other)
  have middleHistory := ActualJournalHistory.Trace.system history.actual latch lsender lvalue lfit
  have first := controls latch lc ls lg
  have latched : SystemSpec.worldSlot middle (address kind) (UInt256.ofNat 0) = INH := by
    apply word_eq
    simpa only [if_pos nonempty] using first.1
  obtain ⟨after,unlock,uc,us,_,ug⟩ := ProtocolSystemCalls.empty_guarantees kind middle genesis blocks header gasPrice fuel
    (middleInv kind) bound resources
  have usender : unlock.call.caller = Eip8282.Audit.EvmRunner.sysAddr := by rw [uc]; rfl
  have uvalue : unlock.call.value = ⟨0⟩ := by rw [uc]; rfl
  have ufit : unlock.call.calldata.size < UInt256.size := by rw [uc]; change 0 < UInt256.size; decide +kernel
  have second := controls unlock uc us ug
  have unlocked : SystemSpec.worldSlot after (address kind) (UInt256.ofNat 0) = UInt256.ofNat 0 := by
    apply word_eq
    change (SystemSpec.worldSlot after (address kind) (UInt256.ofNat 0)).toNat = 0
    simpa only [ByteArray.size_empty,ne_eq,not_true_eq_false,if_false,latched,if_true] using second.1
  let cycle : Cycle kind before after genesis blocks header gasPrice fuel data :=
    ⟨middle,latch,unlock,lc,uc,ls,us,latched,unlocked,first.2,second.2,lg,ug⟩
  exact ⟨after,cycle,ActualJournalHistory.Trace.system middleHistory unlock usender uvalue ufit,
    fun other => SystemJournal.preserves unlock usender uvalue ufit bound (middleInv other)⟩

#print axioms after_history
end Eip8282.Audit.Integrator.ReleaseInhibitionCycle
