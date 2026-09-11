import Eip8282.Audit.Integrator.ReleaseCandidate
import Eip8282.Audit.Integrator.SubmissionCall

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
