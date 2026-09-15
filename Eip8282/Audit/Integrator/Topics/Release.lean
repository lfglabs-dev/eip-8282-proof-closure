import Eip8282.Audit.Integrator.GetterCall
import Eip8282.Audit.Integrator.ReleaseCandidate
import Eip8282.Audit.Integrator.SubmissionCall

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReleaseGetterProgress -/

/-! A successful mathematical getter after the same initialized/funded history.
Quote completion and safe numerator are derived, not supplied. The 462 bound
is a certified sufficient witness on the safe input interval, not a semantic
iteration limit. Gas below is actual pinned EVMYulLean scalar gas, not the
synthetic replay gas or an established Amsterdam resource bound.
-/
namespace Eip8282.Audit.Integrator.ReleaseGetterProgress
open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open ReachableCalls (Contract PinnedCall)
open JournalInvariant (modelKind)
open TransactionAppendBudget (Receipt)
open MessageCall CallBridge
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- 44,694 scalar gas and 11,171 message-call fuel suffice for either getter
through the whole entry, loop, RETURN and Theta settlement on this domain. -/
theorem after_history {deposit exit : Receipt} {kind : Contract} {c : Context}
    (history : ReleaseCandidate.History deposit exit c.world) (pinned : ReleaseCandidate.CallInput kind c)
    (user : c.caller ≠ EvmRunner.sysAddr)
    (enabled : SystemSpec.worldSlot c.world c.target (UInt256.ofNat 0) ≠ INH)
    (zero : c.value = UInt256.ofNat 0) (empty : c.calldata.size = 0)
    (gas : 44694 ≤ c.gas.toNat) (fuel : 11171 ≤ c.fuel) :
    ∃ (price : UInt256) (world : AccountMap .EVM) (remaining : UInt256) (substate : Substate),
      c.result = .ok (c.created,world,remaining,substate,true,price.toByteArray) ∧
      (∀ address, world.get? address = c.world.get? address) ∧
      substate.logSeries = c.substate.logSeries ∧
      MathFee.MathQuoteCompletes (SuccessfulUser.numerator c (DirectAdmission.target (modelKind kind))) price.toNat ∧
      NestedProtectedJournal.Observed kind c c.created world substate true price.toByteArray := by
  have bound := ReleaseCandidate.enabled_numerator history pinned enabled
  obtain ⟨price,completed,math⟩ := FeeSafeDomain.safe_quote _ bound
  have stepFuel : c.fuel = (c.fuel-1)+1 := by omega
  have gasBound : 87*FeeSafeDomain.certificateBudget+4500 ≤ c.gas.toNat := gas
  have steps : 24*FeeSafeDomain.certificateBudget+82 ≤ c.fuel-1 := by
    change 11170 ≤ c.fuel-1
    omega
  have quoted : GetterCall.ReturnsQuote c price := by
    cases kind with
    | deposit =>
      have code : c.code = Eip8282.Audit.Correspondence.runtimeCode .deposit := pinned.code
      have hen : Deposit.excessWord (codeCall c code (c.fuel-1)) ≠ INH := by
        change slotW (entrySt (codeCall c code (c.fuel-1))) (UInt256.ofNat 0) ≠ INH
        rw [TransferFrame.codeCall_storage]
        exact enabled
      have numerator := SuccessfulUser.deposit_numerator c code (c.fuel-1) bound
      have effective : Deposit.effExcess (codeCall c code (c.fuel-1)) =
          UInt256.ofNat (SuccessfulUser.numerator c 8) :=
        (eq_ofNat_iff_toNat _ _ (lt_of_le_of_lt bound (by decide +kernel))).mpr numerator
      apply GetterCall.deposit_getter c code (c.fuel-1) stepFuel user hen zero pinned.ordinaryValue empty
        (n := FeeSafeDomain.certificateBudget) (price := price) _ gasBound steps
      rw [effective]
      exact completed
    | exit =>
      have code : c.code = Eip8282.Audit.Correspondence.runtimeCode .exit := pinned.code
      have hen : Exit.excessWord (codeCall c code (c.fuel-1)) ≠ INH := by
        change slotW (entrySt (codeCall c code (c.fuel-1))) (UInt256.ofNat 0) ≠ INH
        rw [TransferFrame.codeCall_storage]
        exact enabled
      have numerator := SuccessfulUser.exit_numerator c code (c.fuel-1) bound
      have effective : Exit.effExcess (codeCall c code (c.fuel-1)) =
          UInt256.ofNat (SuccessfulUser.numerator c 2) :=
        (eq_ofNat_iff_toNat _ _ (lt_of_le_of_lt bound (by decide +kernel))).mpr numerator
      apply GetterCall.exit_getter c code (c.fuel-1) stepFuel user hen zero pinned.ordinaryValue empty
        (n := FeeSafeDomain.certificateBudget) (price := price) _ gasBound steps
      rw [effective]
      exact completed
  obtain ⟨world,remaining,substate,actual,lookups,logs⟩ := quoted
  have fit : c.calldata.size < UInt256.size := by rw [empty]; decide +kernel
  exact ⟨price,world,remaining,substate,actual,lookups,logs,math,
    ReleaseCandidate.call history pinned fit actual⟩

#print axioms after_history
end Eip8282.Audit.Integrator.ReleaseGetterProgress

end

section

/-! ## ReleaseInhibitionCycle -/

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

end

section

/-! ## ReleaseSubmitProgress -/

/-! Sufficiency of well-formed mathematical payment in the justified history
domain, at explicit pinned scalar gas/fuel. No completed operational quote,
AppendFits, desired successful receipt or post-invariant is supplied. Funds
are checked against the actual pre-call sender balance; no extra wealth ceiling
is assumed. Ancestor survival is separate from this message's own success.
-/
namespace Eip8282.Audit.Integrator.ReleaseSubmitProgress
open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open ReachableCalls (Contract PinnedCall Transition)
open JournalInvariant (Invariant modelKind)
open TransactionAppendBudget (Receipt)
open MessageCall CallBridge
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- The price predicate is purely mathematical and independent of bytecode
execution. Its existence on this domain is proved, so the universal payment
condition is not used vacuously. Uniform resources cover both contract kinds. -/
theorem after_history {deposit exit : Receipt} {kind : Contract} {c : Context}
    (history : ReleaseCandidate.History deposit exit c.world) (pinned : ReleaseCandidate.CallInput kind c)
    (user : c.caller ≠ EvmRunner.sysAddr)
    (enabled : SystemSpec.worldSlot c.world c.target (UInt256.ofNat 0) ≠ INH)
    (permission : c.permission = true)
    (funded : c.value.toNat ≤ TransferFunding.worldBalance c.world c.caller)
    (paid : ∀ price : Nat,
      MathFee.MathQuoteCompletes (SuccessfulUser.numerator c (DirectAdmission.target (modelKind kind))) price →
      DirectAdmission.PaidInput (modelKind kind) c price)
    (gas : 230194 ≤ c.gas.toNat) (fuel : 11241 ≤ c.fuel) :
    ∃ (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
      (remaining : UInt256) (substate : Substate),
      c.result = .ok (created,world,remaining,substate,true,ByteArray.empty) ∧
      NestedProtectedJournal.Observed kind c created world substate true ByteArray.empty ∧
      Invariant kind (ActualJournalHistory.work history.receipts+1) world := by
  have hInv := (ReleaseCandidate.invariants history).2.2.2 kind
  have hBudget := (ReleaseCandidate.invariants history).2.2.1
  have bound := ReleaseCandidate.enabled_numerator history pinned enabled
  obtain ⟨price,completed,math⟩ := FeeSafeDomain.safe_quote _ bound
  have payment := paid price.toNat math
  have stepFuel : c.fuel = (c.fuel-1)+1 := by omega
  have code : c.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
    cases kind <;> exact pinned.code
  have owner := TransferFrame.pinned_codeCall_hasOwner c (ReleaseCandidate.installed_call history pinned) code (c.fuel-1)
  have bounded : AccountedState.Bounded (ActualJournalHistory.work history.receipts)
      (SystemSpec.worldSlot c.world c.target) := by
    rw [pinned.target]
    cases kind <;> exact hInv.2.1
  have fits := AccountedState.append_fits (codeCall c code (c.fuel-1))
    (TransferFrame.codeCall_storage_invariant c code (c.fuel-1) _ bounded) hBudget
  have receipt : CommittedAppend.AppendResult c (codeCall c code (c.fuel-1))
      (AppendDataSpec.record (modelKind kind) c.calldata c.caller) := by
    cases kind with
    | deposit =>
      have hen : Deposit.excessWord (codeCall c code (c.fuel-1)) ≠ INH := by
        change slotW (entrySt (codeCall c code (c.fuel-1))) (UInt256.ofNat 0) ≠ INH
        rw [TransferFrame.codeCall_storage]
        exact enabled
      have numerator := SuccessfulUser.deposit_numerator c code (c.fuel-1) bound
      have effective : Deposit.effExcess (codeCall c code (c.fuel-1)) =
          UInt256.ofNat (SuccessfulUser.numerator c 8) :=
        (eq_ofNat_iff_toNat _ _ (lt_of_le_of_lt bound (by decide +kernel))).mpr numerator
      apply SubmissionCall.deposit_submission c code (c.fuel-1) stepFuel pinned.ordinaryValue user hen permission
        (n := FeeSafeDomain.certificateBudget) (price := price) _ payment.1 payment.2.1 payment.2.2 _ _ owner fits
      · rw [effective]; exact completed
      · exact gas
      · change 11240 ≤ c.fuel-1; omega
    | exit =>
      have hen : Exit.excessWord (codeCall c code (c.fuel-1)) ≠ INH := by
        change slotW (entrySt (codeCall c code (c.fuel-1))) (UInt256.ofNat 0) ≠ INH
        rw [TransferFrame.codeCall_storage]
        exact enabled
      have numerator := SuccessfulUser.exit_numerator c code (c.fuel-1) bound
      have effective : Exit.effExcess (codeCall c code (c.fuel-1)) =
          UInt256.ofNat (SuccessfulUser.numerator c 2) :=
        (eq_ofNat_iff_toNat _ _ (lt_of_le_of_lt bound (by decide +kernel))).mpr numerator
      apply SubmissionCall.exit_submission c code (c.fuel-1) stepFuel pinned.ordinaryValue user hen permission
        (n := FeeSafeDomain.certificateBudget) (price := price) _ payment.1 payment.2 _ _ owner fits
      · rw [effective]; exact completed
      · change 190194 ≤ c.gas.toNat; omega
      · change 11210 ≤ c.fuel-1; omega
  obtain ⟨created,world,remaining,substate,actual,_⟩ := receipt
  have fit : c.calldata.size < UInt256.size := by
    cases kind <;> rw [payment.1] <;> decide +kernel
  have nonempty : c.calldata.size ≠ 0 := by
    cases kind <;> rw [payment.1] <;> decide +kernel
  have valueBound := FundingHistory.message_value_lt c
    (ProtocolCreditEnvelope.ledger_bound history.ledger).1 funded
    (GenesisWorldFunding.funding_budget history.ledger history.counts).2
  let t : Transition kind c.world world := ⟨c,ReleaseCandidate.installed_call history pinned,rfl,created,remaining,substate,true,ByteArray.empty,actual⟩
  have post := JournalInvariant.protected_call t ⟨fit,fun _ => valueBound⟩ hBudget hInv
  have weight : ConcreteHistory.weight c true = 1 := by
    rw [ConcreteHistory.weight,if_neg user]
    simp only [UserStateInvariant.weight,true_and,if_pos nonempty]
  refine ⟨created,world,remaining,substate,actual,ReleaseCandidate.call history pinned fit actual,?_⟩
  change Invariant kind (ActualJournalHistory.work history.receipts+ConcreteHistory.weight c true) world at post
  simpa only [weight] using post

#print axioms after_history
end Eip8282.Audit.Integrator.ReleaseSubmitProgress

end
