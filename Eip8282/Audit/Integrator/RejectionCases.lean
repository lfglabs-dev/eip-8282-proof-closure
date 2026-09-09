import Eip8282.Audit.Integrator.RejectionSpec

/-!
# Exhaustive input rejection after a completed quote

The predicates describe the pinned word checks. If neither getter nor append
is allowed by those checks, the actual complete call restores the pre-transfer
journal. This covers every input-rejection branch at sufficient resources;
arbitrary-resource success/fee-loop inversion remains a separate obligation.
-/
namespace Eip8282.Audit.Integrator.RejectionCases

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall readWithPadding_size_zero)
open MessageCall CallBridge RejectionSpec
open Eip8282.Audit.Correspondence (runtimeCode)

def RolledBack (c : Context) : Prop :=
  ∃ gas out, c.result = .ok (c.created, c.world, gas, c.substate, false, out) ∧ out.size = 0

def depositAllowed (q : XiCall .deposit) (price : UInt256) : Prop :=
  (Deposit.cdsizeWord q = ⟨0⟩ ∧ Deposit.valueWord q = ⟨0⟩) ∨
  (Deposit.cdsizeWord q = UInt256.ofNat 184 ∧ ¬ Deposit.valueWord q < price ∧
      ¬ Deposit.amountWord q < UInt256.ofNat 1000000000 ∧
      ¬ (Deposit.valueWord q-price) < UInt256.ofNat 1000000000 * Deposit.amountWord q)

theorem deposit_invalid_input (c : Context)
    (hcode : c.code = runtimeCode .deposit) (steps : Nat) (hf : c.fuel = steps+1)
    (huser : Deposit.callerWord (codeCall c hcode steps) ≠ sysW)
    (hen : Deposit.excessWord (codeCall c hcode steps) ≠ INH)
    {n : Nat} {o i : UInt256} (hfee : Deposit.FeeLoopEnds (codeCall c hcode steps) n o i)
    (hinvalid : ¬ depositAllowed (codeCall c hcode steps) (Deposit.feeWord o))
    (hg : 87*n+4600 ≤ c.gas.toNat) (hsteps : 24*n+102 ≤ steps) : RolledBack c := by
  let q := codeCall c hcode steps
  have hgas : 87*n+4500 ≤ q.gas.toNat := by
    change 87*n+4500 ≤ c.gas.toNat
    omega
  have finish {K : Nat} {x : EVM.State} {out : ByteArray}
      (hend : Ends q K x .REVERT out) (hK : K+2 ≤ steps) (hout : out.size = 0) :
      RolledBack c := by
    obtain ⟨gas, hr⟩ := result_of_revert_ends hend hK
    exact ⟨gas, out, rolls_back_endpoint c hcode steps hf gas out hr, hout⟩
  by_cases hs : Deposit.cdsizeWord q = UInt256.ofNat 184
  · by_cases hp : Deposit.valueWord q < Deposit.feeWord o
    · obtain ⟨g, e, hend⟩ := Deposit.user_underpay_reverts q huser hen hfee hs hp hgas
      exact finish hend (by omega) (readWithPadding_size_zero _ _)
    · by_cases ha : Deposit.amountWord q < UInt256.ofNat 1000000000
      · obtain ⟨g, e, hend⟩ := Deposit.user_amountFloor_reverts q huser hen hfee hs hp ha hg
        exact finish hend (by omega) (readWithPadding_size_zero _ _)
      · have hstake : (Deposit.valueWord q-Deposit.feeWord o) <
            UInt256.ofNat 1000000000 * Deposit.amountWord q := by
          by_contra h
          exact hinvalid (Or.inr ⟨hs, hp, ha, h⟩)
        obtain ⟨g, e, hend⟩ := Deposit.user_stake_reverts q huser hen hfee hs hp ha hstake hg
        exact finish hend (by omega) (readWithPadding_size_zero _ _)
  · by_cases hz : Deposit.cdsizeWord q = ⟨0⟩
    · have hv : Deposit.valueWord q ≠ ⟨0⟩ := fun h => hinvalid (Or.inl ⟨hz, h⟩)
      obtain ⟨g, e, hend⟩ := Deposit.user_paidGetter_reverts q huser hen hfee hz hv hgas
      exact finish hend (by omega) (readWithPadding_size_zero _ _)
    · obtain ⟨g, e, hend⟩ := Deposit.user_badsize_reverts q huser hen hfee hs hz hgas
      exact finish hend (by omega) (readWithPadding_size_zero _ _)

#print axioms deposit_invalid_input

def exitAllowed (q : XiCall .exit) (price : UInt256) : Prop :=
  (Exit.cdsizeWord q = ⟨0⟩ ∧ Exit.valueWord q = ⟨0⟩) ∨
  (Exit.cdsizeWord q = UInt256.ofNat 48 ∧ ¬ Exit.valueWord q < price)

theorem exit_invalid_input (c : Context)
    (hcode : c.code = runtimeCode .exit) (steps : Nat) (hf : c.fuel = steps+1)
    (huser : Exit.callerWord (codeCall c hcode steps) ≠ sysW)
    (hen : Exit.excessWord (codeCall c hcode steps) ≠ INH)
    {n : Nat} {o i : UInt256} (hfee : Exit.FeeLoopEnds (codeCall c hcode steps) n o i)
    (hinvalid : ¬ exitAllowed (codeCall c hcode steps) (Exit.feeWord o))
    (hg : 87*n+4600 ≤ c.gas.toNat) (hsteps : 24*n+102 ≤ steps) : RolledBack c := by
  let q := codeCall c hcode steps
  have hgas : 87*n+4500 ≤ q.gas.toNat := by
    change 87*n+4500 ≤ c.gas.toNat
    omega
  have finish {K : Nat} {x : EVM.State} {out : ByteArray}
      (hend : Ends q K x .REVERT out) (hK : K+2 ≤ steps) (hout : out.size = 0) :
      RolledBack c := by
    obtain ⟨gas, hr⟩ := result_of_revert_ends hend hK
    exact ⟨gas, out, rolls_back_endpoint c hcode steps hf gas out hr, hout⟩
  by_cases hs : Exit.cdsizeWord q = UInt256.ofNat 48
  · by_cases hp : Exit.valueWord q < Exit.feeWord o
    · obtain ⟨g, e, hend⟩ := Exit.user_underpay_reverts q huser hen hfee hs hp hgas
      exact finish hend (by omega) (readWithPadding_size_zero _ _)
    · exact False.elim (hinvalid (Or.inr ⟨hs, hp⟩))
  · by_cases hz : Exit.cdsizeWord q = ⟨0⟩
    · have hv : Exit.valueWord q ≠ ⟨0⟩ := fun h => hinvalid (Or.inl ⟨hz, h⟩)
      obtain ⟨g, e, hend⟩ := Exit.user_paidGetter_reverts q huser hen hfee hz hv hgas
      exact finish hend (by omega) (readWithPadding_size_zero _ _)
    · obtain ⟨g, e, hend⟩ := Exit.user_badsize_reverts q huser hen hfee hs hz hgas
      exact finish hend (by omega) (readWithPadding_size_zero _ _)

#print axioms exit_invalid_input

end Eip8282.Audit.Integrator.RejectionCases
