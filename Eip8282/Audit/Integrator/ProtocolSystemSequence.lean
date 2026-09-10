import Eip8282.Audit.Integrator.ProtocolSystemCalls
import Eip8282.Audit.Integrator.ActualJournalHistory

/-! The proposed empty Deposit-then-Exit SYSTEM sequence runs in one actual
world history. The first call supplies the second call's pre-world and preserves
the other journal. This is a named conditional schedule, not protocol adoption
or an equation with the canonical block processor. -/
namespace Eip8282.Audit.Integrator.ProtocolSystemSequence
open EvmYul EvmYul.EVM
open ReachableCalls (Contract Transition)
open JournalInvariant (Invariant)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

structure EmptyPair (before after : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (gasPrice : UInt256) (fuel : Nat) where
  middle : AccountMap .EVM
  deposit : Transition .deposit before middle
  exit : Transition .exit middle after
  depositCall : deposit.call = ProtocolSystemCalls.call .deposit before genesis blocks header gasPrice fuel ByteArray.empty
  exitCall : exit.call = ProtocolSystemCalls.call .exit middle genesis blocks header gasPrice fuel ByteArray.empty
  depositSuccess : deposit.success = true
  exitSuccess : exit.success = true

/-- The two successful calls are constructed in order, not supplied as desired
endpoints. Both protected invariants are retained after both calls. -/
theorem completes (before : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (gasPrice : UInt256) (fuel : Nat)
    (budgets : Contract → Nat) (initial : ∀ kind, Invariant kind (budgets kind) before)
    (bounds : ∀ kind, budgets kind < 2^128) (resources : 8503 ≤ fuel) :
    ∃ after, ∃ pair : EmptyPair before after genesis blocks header gasPrice fuel,
      (∀ kind, Invariant kind (budgets kind) after) ∧
      NestedProtectedJournal.Observed .deposit pair.deposit.call pair.deposit.created pair.middle
        pair.deposit.substate pair.deposit.success pair.deposit.output ∧
      NestedProtectedJournal.Observed .exit pair.exit.call pair.exit.created after
        pair.exit.substate pair.exit.success pair.exit.output := by
  obtain ⟨middle,dep,depCall,depSuccess,depInv,depGuards⟩ :=
    ProtocolSystemCalls.empty_guarantees .deposit before genesis blocks header gasPrice fuel
      (initial .deposit) (bounds .deposit) resources
  have depSender : dep.call.caller = Eip8282.Audit.EvmRunner.sysAddr := by rw [depCall]; rfl
  have depValue : dep.call.value = ⟨0⟩ := by rw [depCall]; rfl
  have depFit : dep.call.calldata.size < UInt256.size := by rw [depCall]; change 0 < UInt256.size; decide +kernel
  have midInv : ∀ kind, Invariant kind (budgets kind) middle :=
    fun kind => SystemJournal.preserves dep depSender depValue depFit (bounds kind) (initial kind)
  obtain ⟨after,ext,extCall,extSuccess,extInv,extGuards⟩ :=
    ProtocolSystemCalls.empty_guarantees .exit middle genesis blocks header gasPrice fuel
      (midInv .exit) (bounds .exit) resources
  have extSender : ext.call.caller = Eip8282.Audit.EvmRunner.sysAddr := by rw [extCall]; rfl
  have extValue : ext.call.value = ⟨0⟩ := by rw [extCall]; rfl
  have extFit : ext.call.calldata.size < UInt256.size := by rw [extCall]; change 0 < UInt256.size; decide +kernel
  let pair : EmptyPair before after genesis blocks header gasPrice fuel :=
    ⟨middle,dep,ext,depCall,extCall,depSuccess,extSuccess⟩
  exact ⟨after,pair,fun kind => SystemJournal.preserves ext extSender extValue extFit
    (bounds kind) (midInv kind),depGuards,extGuards⟩

/-- Extend the same actual journal history by the ordered pair. SYSTEM does
not add a transaction receipt, external credit or append-work budget. -/
theorem append {before after initial : AccountMap .EVM} {genesis : BlockHeader}
    {blocks : ProcessedBlocks} {header : BlockHeader} {gasPrice : UInt256} {fuel : Nat}
    (pair : EmptyPair before after genesis blocks header gasPrice fuel)
    {receipts : List TransactionAppendBudget.Receipt} {credits : Nat}
    (history : ActualJournalHistory.Trace initial receipts credits before) :
    ActualJournalHistory.Trace initial receipts credits after := by
  have hd := ActualJournalHistory.Trace.system history pair.deposit
    (by rw [pair.depositCall]; rfl) (by rw [pair.depositCall]; rfl)
    (by rw [pair.depositCall]; change 0 < UInt256.size; decide +kernel)
  exact ActualJournalHistory.Trace.system hd pair.exit
    (by rw [pair.exitCall]; rfl) (by rw [pair.exitCall]; rfl)
    (by rw [pair.exitCall]; change 0 < UInt256.size; decide +kernel)

/-- An actual initialized prefix and the constructed ordered SYSTEM calls
remain one history, with the same credits and receipt list. Canonical dispatch
extraction and policy acceptance are still external producers. -/
theorem extends_history {before initial : AccountMap .EVM} (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (gasPrice : UInt256) (fuel : Nat)
    {receipts : List TransactionAppendBudget.Receipt} {credits : Nat}
    (history : ActualJournalHistory.Trace initial receipts credits before)
    (budgets : Contract → Nat) (invariants : ∀ kind, Invariant kind (budgets kind) before)
    (bounds : ∀ kind, budgets kind < 2^128) (resources : 8503 ≤ fuel) :
    ∃ after, ∃ pair : EmptyPair before after genesis blocks header gasPrice fuel,
      ActualJournalHistory.Trace initial receipts credits after ∧
      (∀ kind, Invariant kind (budgets kind) after) ∧
      NestedProtectedJournal.Observed .deposit pair.deposit.call pair.deposit.created pair.middle
        pair.deposit.substate pair.deposit.success pair.deposit.output ∧
      NestedProtectedJournal.Observed .exit pair.exit.call pair.exit.created after
        pair.exit.substate pair.exit.success pair.exit.output := by
  obtain ⟨after,pair,finalInv,dep,ext⟩ := completes before genesis blocks header gasPrice fuel
    budgets invariants bounds resources
  exact ⟨after,pair,append pair history,finalInv,dep,ext⟩

#print axioms completes
#print axioms append
#print axioms extends_history
end Eip8282.Audit.Integrator.ProtocolSystemSequence
