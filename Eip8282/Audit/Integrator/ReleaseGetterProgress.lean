import Eip8282.Audit.Integrator.ReleaseCandidate
import Eip8282.Audit.Integrator.GetterCall

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
