import Eip8282.Audit.Integrator.AdmissionInversion
import Eip8282.Audit.Integrator.SuccessfulQuote
import Eip8282.Audit.Integrator.GetterCall

/-!
# Read-only getters as a necessary property of actual success

The quote witness, zero value and final state frame are derived from successful
execution at arbitrary resources. The final substate may have additional access
bookkeeping; its logs and the complete account map/created accounts are preserved.
-/
namespace Eip8282.Audit.Integrator.GetterInversion

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall)
open SuccessInversion AdmissionInversion

set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

/-- Actual successful RETURN preserves the entire non-machine state. -/
theorem return_state {fuel : Nat} {vj : Array UInt256}
    {pre final : EVM.State} {out : ByteArray} {off len : UInt256} {stk : Stack UInt256}
    (hd : decodeAt pre = (.RETURN,none)) (hst : pre.stack = off :: len :: stk)
    (h : X fuel vj pre = .ok (.success final out)) : final.toState = pre.toState := by
  obtain ⟨rest, cost, op, arg, mid, post, _, hd', hz, hs, hcase⟩ := success_step h
  have hop := hd.symm.trans hd'
  cases hop
  cases rest with
  | zero => change Except.error ExecutionException.OutOfFuel = Except.ok post at hs; cases hs
  | succ rest =>
      have hmidstack : mid.stack = off :: len :: stk := (Z_ok_stack hz).trans hst
      change EvmYul.EVM.step (rest+1) cost (some (.RETURN,none)) mid = .ok post at hs
      rw [EVM_step_eq_step (by decide : Operation.RETURN ∈ allOps), stepPre_eq_withGE,
        step_withGE (by decide : Operation.RETURN ∈ allOps), step_RETURN hmidstack] at hs
      have he := (Except.ok.inj hs).symm
      rcases hcase with ⟨hn, _⟩ | ⟨_, _, hfinal⟩
      · have hn' := H_eq_none_iff.mp hn
        simp at hn'
      · rw [← hfinal, he]
        change mid.toState = pre.toState
        exact Z_ok_toState hz

/-- The actual deposit getter suffix changes only memory and bookkeeping. -/
theorem deposit_getter_suffix_state (c : XiCall .deposit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {price : UInt256} {final : EVM.State} {out : ByteArray} (henv : st.executionEnv = c.env)
    (h : X fuel depositJumpdests (at_ c st mem aw g 153 [price] e) = .ok (.success final out)) :
    final.toState = st := by
  have hcode := Deposit.hcode_of_env c henv
  obtain ⟨f1, g1, e1, _, hx1⟩ := success_symBlock deposit_b153 deposit_b153_ok hcode rfl
    (deposit_b153_shape c st mem aw g e [price]) h
  rw [withGE_at] at hx1
  obtain ⟨f2, g2, e2, hx2⟩ := success_effect (by decide : Operation.MSTORE ∈ allOps) (by decide)
    (decodeAt_of_code_pc hcode rfl deposit_s154) (step_MSTORE rfl) hx1
  change X f2 depositJumpdests
    (at_ c st (mstoreMem mem (UInt256.ofNat 0) price) (mAfter aw 0 32) g2 155 [] e2) =
      .ok (.success final out) at hx2
  obtain ⟨f3, g3, e3, _, hx3⟩ := success_symBlock (h := hx2) deposit_b155 deposit_b155_ok
    (by exact hcode) rfl (deposit_b155_shape c _ _ _ _ _ [])
  rw [withGE_at] at hx3
  exact return_state
    (decodeAt_of_code_pc (st := at_ c st _ _ g3 158 _ e3) hcode rfl deposit_s158) rfl hx3

theorem exit_getter_suffix_state (c : XiCall .exit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {price : UInt256} {final : EVM.State} {out : ByteArray} (henv : st.executionEnv = c.env)
    (h : X fuel exitJumpdests (at_ c st mem aw g 152 [price] e) = .ok (.success final out)) :
    final.toState = st := by
  have hcode := Exit.hcode_of_env c henv
  obtain ⟨f1, g1, e1, _, hx1⟩ := success_symBlock exit_b152 exit_b152_ok hcode rfl
    (exit_b152_shape c st mem aw g e [price]) h
  rw [withGE_at] at hx1
  obtain ⟨f2, g2, e2, hx2⟩ := success_effect (by decide : Operation.MSTORE ∈ allOps) (by decide)
    (decodeAt_of_code_pc hcode rfl exit_s153) (step_MSTORE rfl) hx1
  change X f2 exitJumpdests
    (at_ c st (mstoreMem mem (UInt256.ofNat 0) price) (mAfter aw 0 32) g2 154 [] e2) =
      .ok (.success final out) at hx2
  obtain ⟨f3, g3, e3, _, hx3⟩ := success_symBlock (h := hx2) exit_b154 exit_b154_ok
    (by exact hcode) rfl (exit_b154_shape c _ _ _ _ _ [])
  rw [withGE_at] at hx3
  exact return_state
    (decodeAt_of_code_pc (st := at_ c st _ _ g3 157 _ e3) hcode rfl exit_s157) rfl hx3

/-- At empty calldata the actual successful post-fee continuation must be
its zero-value getter, and preserves the final non-machine state. -/
theorem deposit_after_fee_state (c : XiCall .deposit)
    {fuel : Nat} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {o i numerator : UInt256} {final : EVM.State} {out : ByteArray}
    (hdata : c.env.calldata.size = 0)
    (h : X fuel depositJumpdests (at_ c (Deposit.st₂ c) mem aw g 127
      [o,⟨0⟩,i,numerator,UInt256.ofNat 17] e) = .ok (.success final out)) :
    c.env.weiValue = ⟨0⟩ ∧ final.toState = Deposit.st₂ c := by
  have hcode := Deposit.hcode_of_env c (st := Deposit.st₂ c) rfl
  obtain ⟨f1, g1, e1, _, hx1⟩ := success_symBlock (h := h) deposit_b127 deposit_b127_ok
    (by exact hcode) rfl (deposit_b127_shape c (Deposit.st₂ c) mem aw g e o ⟨0⟩ i numerator
      (UInt256.ofNat 17) [])
  rw [withGE_at] at hx1
  have hs : Deposit.cdsizeWord c ≠ UInt256.ofNat 184 := by
    change UInt256.ofNat c.env.calldata.size ≠ _
    rw [hdata]
    decide
  obtain ⟨f2, cost2, _, _, hx2⟩ := success_jumpi_untaken
    (decodeAt_of_code_pc
      (st := at_ c (Deposit.st₂ c) mem aw g1 142 _ e1) (by exact hcode) rfl deposit_s142)
    rfl ((eq_eq_zero_iff _ _).mpr (fun he => hs he.symm)) hx1
  rw [jumpi_fallthrough_at, withGE_at] at hx2
  obtain ⟨f3, g3, e3, _, hx3⟩ := success_symBlock (h := hx2) deposit_b143 deposit_b143_ok
    (by exact hcode) rfl (deposit_b143_shape c _ _ _ _ _ _)
  rw [withGE_at] at hx3
  obtain ⟨hsize, f4, g4, e4, hx4⟩ := deposit_guard c rfl deposit_s147 hx3
  obtain ⟨f5, g5, e5, _, hx5⟩ := success_symBlock (h := hx4) deposit_b148 deposit_b148_ok
    (by exact hcode) rfl (deposit_b148_shape c _ _ _ _ _ _)
  rw [withGE_at] at hx5
  obtain ⟨hvalue, _, _, _, hx6⟩ := deposit_guard c rfl deposit_s152 hx5
  exact ⟨hvalue, deposit_getter_suffix_state c rfl hx6⟩

/-- At empty calldata the actual successful post-fee continuation must be
its zero-value getter, and preserves the final non-machine state. -/
theorem exit_after_fee_state (c : XiCall .exit)
    {fuel : Nat} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {o i numerator : UInt256} {final : EVM.State} {out : ByteArray}
    (hdata : c.env.calldata.size = 0)
    (h : X fuel exitJumpdests (at_ c (Exit.st₂ c) mem aw g 126
      [o,⟨0⟩,i,numerator,UInt256.ofNat 17] e) = .ok (.success final out)) :
    c.env.weiValue = ⟨0⟩ ∧ final.toState = Exit.st₂ c := by
  have hcode := Exit.hcode_of_env c (st := Exit.st₂ c) rfl
  obtain ⟨f1, g1, e1, _, hx1⟩ := success_symBlock (h := h) exit_b126 exit_b126_ok
    (by exact hcode) rfl (exit_b126_shape c (Exit.st₂ c) mem aw g e o ⟨0⟩ i numerator
      (UInt256.ofNat 17) [])
  rw [withGE_at] at hx1
  have hs : Exit.cdsizeWord c ≠ UInt256.ofNat 48 := by
    change UInt256.ofNat c.env.calldata.size ≠ _
    rw [hdata]
    decide
  obtain ⟨f2, cost2, _, _, hx2⟩ := success_jumpi_untaken
    (decodeAt_of_code_pc
      (st := at_ c (Exit.st₂ c) mem aw g1 141 _ e1) (by exact hcode) rfl exit_s141)
    rfl ((eq_eq_zero_iff _ _).mpr (fun he => hs he.symm)) hx1
  rw [jumpi_fallthrough_at, withGE_at] at hx2
  obtain ⟨f3, g3, e3, _, hx3⟩ := success_symBlock (h := hx2) exit_b142 exit_b142_ok
    (by exact hcode) rfl (exit_b142_shape c _ _ _ _ _ _)
  rw [withGE_at] at hx3
  obtain ⟨hsize, f4, g4, e4, hx4⟩ := exit_guard c rfl exit_s146 hx3
  obtain ⟨f5, g5, e5, _, hx5⟩ := success_symBlock (h := hx4) exit_b147 exit_b147_ok
    (by exact hcode) rfl (exit_b147_shape c _ _ _ _ _ _)
  rw [withGE_at] at hx5
  obtain ⟨hvalue, _, _, _, hx6⟩ := exit_guard c rfl exit_s151 hx5
  exact ⟨hvalue, exit_getter_suffix_state c rfl hx6⟩

/-- Actual Xi getter observations. Account equality includes balances, code,
storage and transient storage; access bookkeeping is intentionally omitted. -/
def ReadOnlyXi (c : XiCall kind) (created : Std.TreeSet AccountAddress compare)
    (world : AccountMap .EVM) (substate : Substate) : Prop :=
  created = c.createdAccounts ∧ world = c.σ ∧
    substate.logSeries = c.substate.logSeries ∧ c.env.weiValue = ⟨0⟩

private theorem readonly_of_final (c : XiCall kind)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {final : EVM.State}
    (hp : (final.createdAccounts, final.accountMap, final.gasAvailable, final.substate) =
      (created, world, gas, substate))
    (hf : final.toState = touch (touch (entrySt c) (UInt256.ofNat 0)) (UInt256.ofNat 1))
    (hv : c.env.weiValue = ⟨0⟩) : ReadOnlyXi c created world substate := by
  simp only [Prod.mk.injEq] at hp
  obtain ⟨hc, hw, hg, hs⟩ := hp
  have hcreated : final.createdAccounts = c.createdAccounts := by
    rw [hf]
    rfl
  have hworld : final.accountMap = c.σ := by
    rw [hf]
    rfl
  have hlogs : final.substate.logSeries = c.substate.logSeries := by
    rw [hf]
    rfl
  exact ⟨hc.symm.trans hcreated, hw.symm.trans hworld,
    (congrArg Substate.logSeries hs).symm.trans hlogs, hv⟩

/-- Every actually successful empty-calldata user Xi call is read-only,
with zero CALLVALUE, at arbitrary gas and interpreter fuel. -/
theorem deposit_xi_readonly (c : XiCall .deposit)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hdata : c.env.calldata.size = 0)
    (h : c.result = .ok (.success (created, world, gas, substate) out)) :
    ReadOnlyXi c created world substate := by
  obtain ⟨final, hp, hx⟩ := xi_success_X c h
  have hu : Deposit.callerWord c ≠ sysW := by
    intro he
    exact huser ((callerW_eq_sysW_iff c).mp he)
  obtain ⟨_, _, _, _, hhead⟩ := deposit_user_to_fee_head c hu hx
  obtain ⟨_, _, _, _, _, _, _, htail⟩ := deposit_fee_exit c rfl hhead
  obtain ⟨hv, hfinal⟩ := deposit_after_fee_state c hdata htail
  exact readonly_of_final c hp hfinal hv

/-- Every actually successful empty-calldata user Xi call is read-only,
with zero CALLVALUE, at arbitrary gas and interpreter fuel. -/
theorem exit_xi_readonly (c : XiCall .exit)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hdata : c.env.calldata.size = 0)
    (h : c.result = .ok (.success (created, world, gas, substate) out)) :
    ReadOnlyXi c created world substate := by
  obtain ⟨final, hp, hx⟩ := xi_success_X c h
  have hu : Exit.callerWord c ≠ sysW := by
    intro he
    exact huser ((callerW_eq_sysW_iff c).mp he)
  obtain ⟨_, _, _, _, hhead⟩ := exit_user_to_fee_head c hu hx
  obtain ⟨_, _, _, _, _, _, _, htail⟩ := exit_fee_exit c rfl hhead
  obtain ⟨hv, hfinal⟩ := exit_after_fee_state c hdata htail
  exact readonly_of_final c hp hfinal hv

open MessageCall CallBridge CallSuccess
open Eip8282.Audit.Correspondence (runtimeCode)

/-- Observable read-only behavior of the actual complete message call. -/
def ReadOnly (c : Context) (created : Std.TreeSet AccountAddress compare)
    (world : AccountMap .EVM) (substate : Substate) : Prop :=
  created = c.created ∧ (∀ addr, world.get? addr = c.world.get? addr) ∧
    substate.logSeries = c.substate.logSeries ∧ c.value = ⟨0⟩

/-- Actual successful ordinary getters preserve every pre-call account
observation, created accounts and logs through both Θ settlement branches.
Zero actual value is a conclusion, using ordinary CALLVALUE equality. -/
theorem deposit_getter_readonly (c : Context)
    (hcode : c.code = runtimeCode .deposit)
    (huser : c.caller ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hactual : c.apparentValue = c.value) (hdata : c.calldata.size = 0)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    ReadOnly c created world substate := by
  have hf : c.fuel = (c.fuel-1)+1 := by have hp := SuccessfulQuote.positive_fuel c h; omega
  obtain ⟨ew, es, he, hw, hs⟩ := codeCall_of_success c hcode (c.fuel-1) hf h
  obtain ⟨hc, hew, hel, hv⟩ := deposit_xi_readonly (codeCall c hcode (c.fuel-1)) huser hdata he
  have hzero : c.value = (⟨0⟩ : UInt256) := hactual.symm.trans hv
  refine ⟨hc, ?_, ?_, hzero⟩
  · intro addr
    rw [hw, hew]
    split
    · rfl
    · exact GetterCall.entryWorld_zero_lookup c hzero addr
  · rw [hs]
    split
    · rfl
    · exact hel

/-- Actual successful ordinary getters preserve every pre-call account
observation, created accounts and logs through both Θ settlement branches.
Zero actual value is a conclusion, using ordinary CALLVALUE equality. -/
theorem exit_getter_readonly (c : Context)
    (hcode : c.code = runtimeCode .exit)
    (huser : c.caller ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hactual : c.apparentValue = c.value) (hdata : c.calldata.size = 0)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    ReadOnly c created world substate := by
  have hf : c.fuel = (c.fuel-1)+1 := by have hp := SuccessfulQuote.positive_fuel c h; omega
  obtain ⟨ew, es, he, hw, hs⟩ := codeCall_of_success c hcode (c.fuel-1) hf h
  obtain ⟨hc, hew, hel, hv⟩ := exit_xi_readonly (codeCall c hcode (c.fuel-1)) huser hdata he
  have hzero : c.value = (⟨0⟩ : UInt256) := hactual.symm.trans hv
  refine ⟨hc, ?_, ?_, hzero⟩
  · intro addr
    rw [hw, hew]
    split
    · rfl
    · exact GetterCall.entryWorld_zero_lookup c hzero addr
  · rw [hs]
    split
    · rfl
    · exact hel

#print axioms return_state
#print axioms deposit_xi_readonly
#print axioms exit_xi_readonly
#print axioms deposit_getter_readonly
#print axioms exit_getter_readonly

end Eip8282.Audit.Integrator.GetterInversion
