import Eip8282.Audit.Integrator.EndpointState
import Eip8282.Audit.Integrator.CallBridge

/-!
# Rejection paths through actual message-call rollback

These results bind reached bytecode rejections to Θ's complete pre-transfer
journal. The inhibited paths do not run the fee loop and need no completion or
mathematical-price premise. The resource conditions are sufficient bounds from
the existing path proof, not an assertion that all Ethereum calls have them.
-/

namespace Eip8282.Audit.Integrator.RejectionSpec

open EvmYul EvmYul.EVM
open Eip8282.Audit.XiTransport
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Integrator.MessageCall
open Eip8282.Audit.Integrator.CallBridge
open Eip8282.Audit.Correspondence (runtimeCode)

theorem result_of_revert_ends {kind : Model.Kind} {c : XiCall kind}
    {K : Nat} {x : EVM.State} {out : ByteArray}
    (hend : Ends c K x .REVERT out) (hf : K + 2 ≤ c.fuel) :
    ∃ gas, c.result = .ok (.revert gas out) := by
  obtain ⟨w, _, hop, hout⟩ := xiHalts_of_ends hend EntryReach.halting_REVERT hf
  have hr := EndpointState.result_of_halts w
  rw [hop, if_pos rfl, hout] at hr
  exact ⟨_, hr⟩

/-- The deposit inhibitor protects the entire pre-call journal at Θ, including
the balance transfer that preceded code execution. -/
theorem deposit_inhibited_call (c : Context)
    (hcode : c.code = runtimeCode .deposit) (steps : Nat) (hf : c.fuel = steps + 1)
    (huser : Deposit.callerWord (codeCall c hcode steps) ≠ sysW)
    (hinh : Deposit.excessWord (codeCall c hcode steps) = INH)
    (hg : 2200 ≤ c.gas.toNat) (hsteps : 17 ≤ steps) :
    ∃ gas out, c.result = .ok (c.created, c.world, gas, c.substate, false, out) ∧
      out.size = 0 := by
  let q := codeCall c hcode steps
  obtain ⟨g, e, hend⟩ := Deposit.user_inhibited q huser hinh hg
  obtain ⟨gas, hr⟩ := result_of_revert_ends hend hsteps
  exact ⟨gas, _, rolls_back_endpoint c hcode steps hf gas _ hr,
    readWithPadding_size_zero _ _⟩

/-- The same actual rollback theorem for the exit inhibitor. -/
theorem exit_inhibited_call (c : Context)
    (hcode : c.code = runtimeCode .exit) (steps : Nat) (hf : c.fuel = steps + 1)
    (huser : Exit.callerWord (codeCall c hcode steps) ≠ sysW)
    (hinh : Exit.excessWord (codeCall c hcode steps) = INH)
    (hg : 2200 ≤ c.gas.toNat) (hsteps : 17 ≤ steps) :
    ∃ gas out, c.result = .ok (c.created, c.world, gas, c.substate, false, out) ∧
      out.size = 0 := by
  let q := codeCall c hcode steps
  obtain ⟨g, e, hend⟩ := Exit.user_inhibited q huser hinh hg
  obtain ⟨gas, hr⟩ := result_of_revert_ends hend hsteps
  exact ⟨gas, _, rolls_back_endpoint c hcode steps hf gas _ hr,
    readWithPadding_size_zero _ _⟩

#print axioms result_of_revert_ends
#print axioms deposit_inhibited_call
#print axioms exit_inhibited_call

end Eip8282.Audit.Integrator.RejectionSpec
