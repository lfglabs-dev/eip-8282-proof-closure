import Eip8282.Audit.Integrator.AdmissionInversion

/-!
# Concrete append states forced by successful execution

Actual execution supplies the accepted gas and effect checks. The concrete
post-state is derived by inverting each instruction, never assumed. Independent
storage-window interpretations retain their explicit owner and fit conditions.
-/
namespace Eip8282.Audit.Integrator.AppendInversion

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall)
open SuccessInversion AdmissionInversion

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- An actual successful storage step determines its stored state. -/
theorem sstore_success {kind : Eip8282.Audit.Model.Kind} {c : XiCall kind}
    {fuel pc : Nat} {vj : Array UInt256} {code : ByteArray}
    {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {key value : UInt256} {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (hop : opcodeAt code pc = some (.SSTORE,none)) (hc : st.executionEnv.code = code)
    (h : X fuel vj (at_ c st mem aw g pc (key::value::stk) e) = .ok (.success final out)) :
    ∃ rest gas count, X rest vj (at_ c (st.sstore key value) mem aw gas (pc+1) stk count) =
      .ok (.success final out) := by
  obtain ⟨rest, gas, count, hx⟩ := success_effect (by decide : Operation.SSTORE ∈ allOps) (by decide)
    (decodeAt_of_code_pc (st := at_ c st mem aw g pc (key::value::stk) e) hc rfl hop)
    (step_SSTORE rfl) h
  rw [toState_replace_at, withGE_at] at hx
  exact ⟨rest, gas, count, hx⟩

theorem mstore_success {kind : Eip8282.Audit.Model.Kind} {c : XiCall kind}
    {fuel pc : Nat} {vj : Array UInt256} {code : ByteArray}
    {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {off value : UInt256} {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (hop : opcodeAt code pc = some (.MSTORE,none)) (hc : st.executionEnv.code = code)
    (h : X fuel vj (at_ c st mem aw g pc (off::value::stk) e) = .ok (.success final out)) :
    ∃ rest gas count, X rest vj (at_ c st (mstoreMem mem off value) (mAfter aw off.toNat 32)
      gas (pc+1) stk count) = .ok (.success final out) := by
  let pre := at_ c st mem aw g pc (off::value::stk) e
  obtain ⟨rest, gas, count, hx⟩ := success_effect (by decide : Operation.MSTORE ∈ allOps) (by decide)
    (decodeAt_of_code_pc (st := pre) hc rfl hop) (step_MSTORE rfl) h
  have he : withGE (({ pre with toMachineState := pre.toMachineState.mstore off value } :
      EVM.State).replaceStackAndIncrPC stk) gas count =
      at_ c st (mstoreMem mem off value) (mAfter aw off.toNat 32) gas (pc+1) stk count :=
    withGE_machine_replace_at c st mem aw g pc (off::value::stk) stk e _ _ _ rfl rfl
  rw [he] at hx
  exact ⟨rest, gas, count, hx⟩

theorem copy_success {kind : Eip8282.Audit.Model.Kind} {c : XiCall kind}
    {fuel pc : Nat} {vj : Array UInt256} {code : ByteArray}
    {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {dst src len : UInt256} {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (hop : opcodeAt code pc = some (.CALLDATACOPY,none)) (hc : st.executionEnv.code = code)
    (h : X fuel vj (at_ c st mem aw g pc (dst::src::len::stk) e) = .ok (.success final out)) :
    ∃ rest gas count, X rest vj (at_ c st (cdcopyMem st mem dst src len)
      (mAfter aw dst.toNat len.toNat) gas (pc+1) stk count) = .ok (.success final out) := by
  let pre := at_ c st mem aw g pc (dst::src::len::stk) e
  obtain ⟨rest, gas, count, hx⟩ := success_effect (by decide : Operation.CALLDATACOPY ∈ allOps) (by decide)
    (decodeAt_of_code_pc (st := pre) hc rfl hop) (step_CALLDATACOPY rfl) h
  have he : withGE (({ pre with toSharedState := pre.toSharedState.calldatacopy dst src len } :
      EVM.State).replaceStackAndIncrPC stk) gas count =
      at_ c st (cdcopyMem st mem dst src len) (mAfter aw dst.toNat len.toNat) gas (pc+1) stk count :=
    withGE_shared_replace_at c st mem aw g pc (dst::src::len::stk) stk e _ _ _ rfl rfl
  rw [he] at hx
  exact ⟨rest, gas, count, hx⟩

theorem log_success {kind : Eip8282.Audit.Model.Kind} {c : XiCall kind}
    {fuel pc : Nat} {vj : Array UInt256} {code : ByteArray}
    {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {off len : UInt256} {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (hop : opcodeAt code pc = some (.LOG0,none)) (hc : st.executionEnv.code = code)
    (h : X fuel vj (at_ c st mem aw g pc (off::len::stk) e) = .ok (.success final out)) :
    ∃ rest gas count, X rest vj (at_ c (logged st (mem.readWithPadding off.toNat len.toNat)) mem
      (mAfter aw off.toNat len.toNat) gas (pc+1) stk count) = .ok (.success final out) := by
  let pre := at_ c st mem aw g pc (off::len::stk) e
  obtain ⟨rest, gas, count, hx⟩ := success_effect (by decide : Operation.LOG0 ∈ allOps) (by decide)
    (decodeAt_of_code_pc (st := pre) hc rfl hop) (step_LOG0 rfl) h
  have he : withGE (({ pre with toSharedState := SharedState.logOp off len #[] pre.toSharedState } :
      EVM.State).replaceStackAndIncrPC stk) gas count =
      at_ c (logged st (mem.readWithPadding off.toNat len.toNat)) mem
        (mAfter aw off.toNat len.toNat) gas (pc+1) stk count :=
    withGE_shared_replace_at c st mem aw g pc (off::len::stk) stk e _ _ _ rfl rfl
  rw [he] at hx
  exact ⟨rest, gas, count, hx⟩

/-- STOP conserves the complete shared state and returns no bytes. -/
theorem stop_success {fuel : Nat} {vj : Array UInt256} {pre final : EVM.State} {out : ByteArray}
    (hd : decodeAt pre = (.STOP,none)) (h : X fuel vj pre = .ok (.success final out)) :
    final.toState = pre.toState ∧ out = .empty := by
  obtain ⟨rest, cost, op, arg, mid, post, _, hd', hz, hs, hcase⟩ := success_step h
  have he := hd.symm.trans hd'
  cases he
  cases rest with
  | zero => change Except.error ExecutionException.OutOfFuel = Except.ok post at hs; cases hs
  | succ rest =>
      change EvmYul.EVM.step (rest+1) cost (some (.STOP,none)) mid = .ok post at hs
      rw [EVM_step_eq_step (by decide : Operation.STOP ∈ allOps), stepPre_eq_withGE,
        step_withGE (by decide : Operation.STOP ∈ allOps), step_STOP] at hs
      have he := (Except.ok.inj hs).symm
      have hstate : post.toState = pre.toState := by
        rw [he]
        change mid.toState = pre.toState
        exact Z_ok_toState hz
      rcases hcase with ⟨hn, _⟩ | ⟨ho, _, hp⟩
      · have hn' := H_eq_none_iff.mp hn
        simp at hn'
      · constructor
        · exact hp ▸ hstate
        · change some ByteArray.empty = some out at ho
          exact (Option.some.inj ho).symm

theorem stop_at_success {kind : Eip8282.Audit.Model.Kind} {c : XiCall kind}
    {fuel pc : Nat} {vj : Array UInt256} {code : ByteArray}
    {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (hop : opcodeAt code pc = some (.STOP,none)) (hc : st.executionEnv.code = code)
    (h : X fuel vj (at_ c st mem aw g pc stk e) = .ok (.success final out)) :
    final.toState = st ∧ out = .empty :=
  stop_success (decodeAt_of_code_pc (st := at_ c st mem aw g pc stk e) hc rfl hop) h

/-- Normalize only environment frames, leaving account-map expressions opaque. -/
macro "append_env" : tactic =>
  `(tactic| simp only [executionEnv_at, Deposit.appendedSt, Deposit.itemStored, Deposit.countStore, Deposit.st₂,
      Exit.appendedSt, Exit.itemStored, Exit.countStore, Exit.st₂,
      executionEnv_touch, executionEnv_sstore, executionEnv_logged, executionEnv_entrySt])

/-- The exit write suffix forces its concrete final shared state and empty
return. Every storage/log/memory effect comes from actual successful execution. -/
theorem exit_suffix (c : XiCall .exit)
    {fuel : Nat} {aw g : UInt256} {e : Nat} {final : EVM.State} {out : ByteArray}
    (h : X fuel exitJumpdests
      (at_ c (Exit.st₂ c) (Exit.mem₀ c) aw g 165 [] e) = .ok (.success final out)) :
    final.toState = Exit.appendedSt c ∧ out = .empty := by
  obtain ⟨f1, g1, e1, _, hx1⟩ := success_symBlock (h := h) exit_b165 exit_b165_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b165_shape c (Exit.st₂ c) _ _ _ _ [])
  rw [withGE_at] at hx1
  simp only [slotW_touch] at hx1
  obtain ⟨f2, g2, e2, hx2⟩ := sstore_success exit_s173 (Exit.hcode_of_env c (by append_env)) hx1
  obtain ⟨f3, g3, e3, _, hx3⟩ := success_symBlock (h := hx2) exit_b174 exit_b174_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b174_shape c (Exit.countStore c) _ _ _ _ [])
  rw [withGE_at] at hx3
  simp only [callerW_touch, callerW_sstore] at hx3
  obtain ⟨f4, g4, e4, hx4⟩ := sstore_success exit_s186 (Exit.hcode_of_env c (by append_env)) hx3
  obtain ⟨f5, g5, e5, _, hx5⟩ := success_symBlock (h := hx4) exit_b187 exit_b187_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b187_shape c _ _ _ _ _ (Exit.slotBase c) [Exit.tailWord c])
  rw [withGE_at] at hx5
  simp only [cdW_touch, cdW_sstore] at hx5
  obtain ⟨f6, g6, e6, hx6⟩ := sstore_success exit_s193 (Exit.hcode_of_env c (by append_env)) hx5
  obtain ⟨f7, g7, e7, _, hx7⟩ := success_symBlock (h := hx6) exit_b194 exit_b194_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b194_shape c _ _ _ _ _ _ [Exit.tailWord c])
  rw [withGE_at] at hx7
  simp only [cdW_touch, cdW_sstore] at hx7
  obtain ⟨f8, g8, e8, hx8⟩ := sstore_success exit_s201 (Exit.hcode_of_env c (by append_env)) hx7
  obtain ⟨f9, g9, e9, _, hx9⟩ := success_symBlock (h := hx8) exit_b202 exit_b202_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b202_shape c (Exit.itemStored c) _ _ _ _ [Exit.tailWord c])
  rw [withGE_at] at hx9
  simp only [callerW_touch, callerW_sstore] at hx9
  obtain ⟨f10, g10, e10, hx10⟩ := mstore_success exit_s207 (Exit.hcode_of_env c (by append_env)) hx9
  obtain ⟨f11, g11, e11, _, hx11⟩ := success_symBlock (h := hx10) exit_b208 exit_b208_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b208_shape c (Exit.itemStored c) _ _ _ _ [Exit.tailWord c])
  rw [withGE_at] at hx11
  obtain ⟨f12, g12, e12, hx12⟩ := copy_success exit_s213 (Exit.hcode_of_env c (by append_env)) hx11
  obtain ⟨f13, g13, e13, _, hx13⟩ := success_symBlock (h := hx12) exit_b214 exit_b214_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b214_shape c (Exit.itemStored c) _ _ _ _ [Exit.tailWord c])
  rw [withGE_at] at hx13
  obtain ⟨f14, g14, e14, hx14⟩ := log_success exit_s217 (Exit.hcode_of_env c (by append_env)) hx13
  obtain ⟨f15, g15, e15, _, hx15⟩ := success_symBlock (h := hx14) exit_b218 exit_b218_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b218_shape c _ _ _ _ _ (Exit.tailWord c) [])
  rw [withGE_at] at hx15
  obtain ⟨f16, g16, e16, hx16⟩ := sstore_success exit_s223 (Exit.hcode_of_env c (by append_env)) hx15
  have hr := stop_at_success exit_s224 (Exit.hcode_of_env c (by append_env)) hx16
  exact hr

/-- Deposit counterpart of the concrete append-suffix necessity theorem. -/
theorem deposit_suffix (c : XiCall .deposit)
    {fuel : Nat} {aw g : UInt256} {e : Nat} {final : EVM.State} {out : ByteArray}
    (h : X fuel depositJumpdests
      (at_ c (Deposit.st₂ c) (Deposit.mem₀ c) aw g 205 [] e) = .ok (.success final out)) :
    final.toState = Deposit.appendedSt c ∧ out = .empty := by
  obtain ⟨f1, g1, e1, _, hx1⟩ := success_symBlock (h := h) deposit_b205 deposit_b205_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b205_shape c (Deposit.st₂ c) _ _ _ _ [])
  rw [withGE_at] at hx1
  simp only [slotW_touch] at hx1
  obtain ⟨f2, g2, e2, hx2⟩ := sstore_success deposit_s213 (Deposit.hcode_of_env c (by append_env)) hx1
  obtain ⟨f3, g3, e3, _, hx3⟩ := success_symBlock (h := hx2) deposit_b214 deposit_b214_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b214_shape c (Deposit.countStore c) _ _ _ _ [])
  rw [withGE_at] at hx3
  simp only [cdW_touch, cdW_sstore] at hx3
  obtain ⟨f4, g4, e4, hx4⟩ := sstore_success deposit_s227 (Deposit.hcode_of_env c (by append_env)) hx3
  obtain ⟨f5, g5, e5, _, hx5⟩ := success_symBlock (h := hx4) deposit_b228 deposit_b228_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b228_shape c _ _ _ _ _ (Deposit.slotBase c) [Deposit.tailWord c])
  rw [withGE_at] at hx5
  simp only [cdW_touch, cdW_sstore] at hx5
  obtain ⟨f6, g6, e6, hx6⟩ := sstore_success deposit_s235 (Deposit.hcode_of_env c (by append_env)) hx5
  obtain ⟨f7, g7, e7, _, hx7⟩ := success_symBlock (h := hx6) deposit_b236 deposit_b236_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b236_shape c _ _ _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx7
  simp only [cdW_touch, cdW_sstore] at hx7
  obtain ⟨f8, g8, e8, hx8⟩ := sstore_success deposit_s243 (Deposit.hcode_of_env c (by append_env)) hx7
  obtain ⟨f9, g9, e9, _, hx9⟩ := success_symBlock (h := hx8) deposit_b244 deposit_b244_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b244_shape c _ _ _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx9
  simp only [cdW_touch, cdW_sstore] at hx9
  obtain ⟨f10, g10, e10, hx10⟩ := sstore_success deposit_s251 (Deposit.hcode_of_env c (by append_env)) hx9
  obtain ⟨f11, g11, e11, _, hx11⟩ := success_symBlock (h := hx10) deposit_b252 deposit_b252_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b252_shape c _ _ _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx11
  simp only [cdW_touch, cdW_sstore] at hx11
  obtain ⟨f12, g12, e12, hx12⟩ := sstore_success deposit_s259 (Deposit.hcode_of_env c (by append_env)) hx11
  obtain ⟨f13, g13, e13, _, hx13⟩ := success_symBlock (h := hx12) deposit_b260 deposit_b260_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b260_shape c _ _ _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx13
  simp only [cdW_touch, cdW_sstore] at hx13
  obtain ⟨f14, g14, e14, hx14⟩ := sstore_success deposit_s267 (Deposit.hcode_of_env c (by append_env)) hx13
  obtain ⟨f15, g15, e15, _, hx15⟩ := success_symBlock (h := hx14) deposit_b268 deposit_b268_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b268_shape c (Deposit.itemStored c) _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx15
  obtain ⟨f16, g16, e16, hx16⟩ := copy_success deposit_s272 (Deposit.hcode_of_env c (by append_env)) hx15
  obtain ⟨f17, g17, e17, _, hx17⟩ := success_symBlock (h := hx16) deposit_b273 deposit_b273_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b273_shape c (Deposit.itemStored c) _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx17
  obtain ⟨f18, g18, e18, hx18⟩ := log_success deposit_s276 (Deposit.hcode_of_env c (by append_env)) hx17
  obtain ⟨f19, g19, e19, _, hx19⟩ := success_symBlock (h := hx18) deposit_b277 deposit_b277_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b277_shape c _ _ _ _ _ (Deposit.tailWord c) [])
  rw [withGE_at] at hx19
  obtain ⟨f20, g20, e20, hx20⟩ := sstore_success deposit_s282 (Deposit.hcode_of_env c (by append_env)) hx19
  have hr := stop_at_success deposit_s283 (Deposit.hcode_of_env c (by append_env)) hx20
  exact hr

/-- Publish a derived shared state without expanding its account-map expression. -/
def ResultAt (c : XiCall kind) (post : EvmYul.State .EVM) : Prop :=
  ∃ gas, c.result = .ok (.success (post.createdAccounts, post.accountMap, gas, post.substate) .empty)

theorem resultAt_of_X {kind : Eip8282.Audit.Model.Kind} (c : XiCall kind)
    {final : EVM.State} {out : ByteArray} {post : EvmYul.State .EVM}
    (hx : X c.fuel (Eip8282.Audit.XiTransport.jumpdestsOf kind) c.entry = .ok (.success final out))
    (hs : final.toState = post) (ho : out = .empty) : ResultAt c post := by
  have hr := EndpointState.result_of_X_success c hx
  rw [ho] at hr
  change c.result = .ok (.success (final.toState.createdAccounts, final.toState.accountMap,
    final.gasAvailable, final.toState.substate) .empty) at hr
  rw [hs] at hr
  exact ⟨final.gasAvailable, hr⟩

/-- Every successful user exit with 48-byte input publishes the concrete append
state. Completion and every effect check are consequences of execution. -/
theorem exit_user_result (c : XiCall .exit)
    {published : Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate}
    {out : ByteArray} (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hsize : c.env.calldata.size = 48) (h : c.result = .ok (.success published out)) :
    ResultAt c (EndpointState.exitAppendState c) := by
  obtain ⟨final, _, hx⟩ := xi_success_X c h
  have hu : Exit.callerWord c ≠ sysW := by
    intro he
    exact huser ((callerW_eq_sysW_iff c).mp he)
  obtain ⟨_, _, _, _, hhead⟩ := exit_user_to_fee_head c hu hx
  obtain ⟨n, output, counter, remaining, gas, count, hloop, htail⟩ := exit_fee_exit c rfl hhead
  have hc := Exit.hcode_of_env c (st := Exit.st₂ c) rfl
  obtain ⟨f1, g1, e1, _, hx1⟩ := success_symBlock (h := htail) exit_b126 exit_b126_ok
    (by exact hc) rfl (exit_b126_shape c _ _ _ _ _ _ _ _ _ _ [])
  rw [withGE_at] at hx1
  have hs : Exit.cdsizeWord c = UInt256.ofNat 48 := by
    change UInt256.ofNat c.env.calldata.size = _
    rw [hsize]
  obtain ⟨f2, cost2, _, _, hx2⟩ := success_jumpi_taken
    (decodeAt_of_code_pc (st := at_ c (Exit.st₂ c) c.entry.memory c.entry.activeWords g1 141 _ e1)
      (by exact hc) rfl exit_s141) rfl ((eq_ne_zero_iff _ _).mpr hs.symm) hx1
  rw [jumpi_taken_at, withGE_at] at hx2
  obtain ⟨f3, g3, e3, _, hx3⟩ := success_symBlock (h := hx2) exit_b158 exit_b158_ok
    (by exact hc) rfl (exit_b158_shape c _ _ _ _ _ _ _)
  rw [withGE_at] at hx3
  obtain ⟨_, _, _, _, hwrite⟩ := exit_guard c rfl exit_s164 hx3
  obtain ⟨hstate, hout⟩ := exit_suffix c hwrite
  have res := resultAt_of_X c (post := Exit.appendedSt c) hx hstate hout
  simpa only [EndpointState.exitAppendState] using res

/-- Every successful user deposit with 184-byte input publishes the concrete append
state. Completion and every effect check are consequences of execution. -/
theorem deposit_user_result (c : XiCall .deposit)
    {published : Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate}
    {out : ByteArray} (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hsize : c.env.calldata.size = 184) (h : c.result = .ok (.success published out)) :
    ResultAt c (EndpointState.depositAppendState c) := by
  obtain ⟨final, _, hx⟩ := xi_success_X c h
  have hu : Deposit.callerWord c ≠ sysW := by
    intro he
    exact huser ((callerW_eq_sysW_iff c).mp he)
  obtain ⟨_, _, _, _, hhead⟩ := deposit_user_to_fee_head c hu hx
  obtain ⟨n, output, counter, remaining, gas, count, hloop, htail⟩ := deposit_fee_exit c rfl hhead
  have hc := Deposit.hcode_of_env c (st := Deposit.st₂ c) rfl
  obtain ⟨f1, g1, e1, _, hx1⟩ := success_symBlock (h := htail) deposit_b127 deposit_b127_ok
    (by exact hc) rfl (deposit_b127_shape c _ _ _ _ _ _ _ _ _ _ [])
  rw [withGE_at] at hx1
  have hs : Deposit.cdsizeWord c = UInt256.ofNat 184 := by
    change UInt256.ofNat c.env.calldata.size = _
    rw [hsize]
  obtain ⟨f2, cost2, _, _, hx2⟩ := success_jumpi_taken
    (decodeAt_of_code_pc (st := at_ c (Deposit.st₂ c) c.entry.memory c.entry.activeWords g1 142 _ e1)
      (by exact hc) rfl deposit_s142) rfl ((eq_ne_zero_iff _ _).mpr hs.symm) hx1
  rw [jumpi_taken_at, withGE_at] at hx2
  obtain ⟨f3, g3, e3, _, hx3⟩ := success_symBlock (h := hx2) deposit_b159 deposit_b159_ok
    (by exact hc) rfl (deposit_b159_shape c _ _ _ _ _ _ _)
  rw [withGE_at] at hx3
  obtain ⟨_, f4, g4, e4, hx4⟩ := deposit_guard c rfl deposit_s166 hx3
  obtain ⟨f5, g5, e5, _, hx5⟩ := success_symBlock (h := hx4) deposit_b167 deposit_b167_ok
    (by exact hc) rfl (deposit_b167_shape c _ _ _ _ _ _)
  rw [withGE_at] at hx5
  obtain ⟨_, f6, g6, e6, hx6⟩ := deposit_guard c rfl deposit_s190 hx5
  obtain ⟨f7, g7, e7, _, hx7⟩ := success_symBlock (h := hx6) deposit_b191 deposit_b191_ok
    (by exact hc) rfl (deposit_b191_shape c _ _ _ _ _ _ _ _)
  rw [withGE_at] at hx7
  obtain ⟨_, _, _, _, hwrite⟩ := deposit_guard c rfl deposit_s204 hx7
  obtain ⟨hstate, hout⟩ := deposit_suffix c hwrite
  have res := resultAt_of_X c (post := Deposit.appendedSt c) hx hstate hout
  simpa only [EndpointState.depositAppendState] using res

open SystemSpec (HasOwner worldSlot worldSlot_state)

/-- The independently observable append consequences in one actual Ξ result. -/
def XiAppendResult (c : XiCall kind) (record : ByteArray) : Prop :=
  ∃ created world gas substate,
    c.result = .ok (.success (created, world, gas, substate) .empty) ∧
    (∃ acc, world.get? c.env.codeOwner = some acc) ∧
    (∀ k, worldSlot world c.env.codeOwner k = AppendStorage.expected c k) ∧
    AppendStorage.StoragePost c world ∧ AppendSpec.AppendedLog c record substate ∧
    AppendSpec.OtherAccountsUnchanged c world

/-- Independent storage and authentic receipt necessity, now at arbitrary
execution resources. Only owner existence and the actual storage-window fits
remain as local premises for interpreting the concrete stored words. -/
theorem exit_user_receipt (c : XiCall .exit)
    {published : Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate}
    {out : ByteArray} (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hsize : c.env.calldata.size = 48) (h : c.result = .ok (.success published out))
    (ho : HasOwner (entrySt c)) (hf : AppendStorage.AppendFits c) :
    XiAppendResult c (ExitRecord.record c.env.source c.env.calldata) := by
  obtain ⟨gas, hr⟩ := exit_user_result c huser hsize h
  have hv := AppendStorage.exit_storage_view c ho
  have he := (AppendSpec.exit_append_frame c).1
  have hw (k : UInt256) : worldSlot (EndpointState.exitAppendState c).accountMap c.env.codeOwner k =
      AppendStorage.expected c k := by
    rw [← he, worldSlot_state]
    exact hv.2 k
  have howner : ∃ acc, (EndpointState.exitAppendState c).accountMap.get? c.env.codeOwner = some acc := by
    simpa only [HasOwner, he] using hv.1
  exact ⟨_, _, gas, _, hr, howner, hw, AppendStorage.storagePost_of_expected c hf _ hw,
    ExitRecord.authentic_log c hsize, AppendSpec.exit_other_accounts c⟩

/-- Independent storage and authentic receipt necessity, now at arbitrary
execution resources. Only owner existence and the actual storage-window fits
remain as local premises for interpreting the concrete stored words. -/
theorem deposit_user_receipt (c : XiCall .deposit)
    {published : Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate}
    {out : ByteArray} (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hsize : c.env.calldata.size = 184) (h : c.result = .ok (.success published out))
    (ho : HasOwner (entrySt c)) (hf : AppendStorage.AppendFits c) :
    XiAppendResult c c.env.calldata := by
  obtain ⟨gas, hr⟩ := deposit_user_result c huser hsize h
  have hv := AppendStorage.deposit_storage_view c ho
  have he := (AppendSpec.deposit_append_frame c).1
  have hw (k : UInt256) : worldSlot (EndpointState.depositAppendState c).accountMap c.env.codeOwner k =
      AppendStorage.expected c k := by
    rw [← he, worldSlot_state]
    exact hv.2 k
  have howner : ∃ acc, (EndpointState.depositAppendState c).accountMap.get? c.env.codeOwner = some acc := by
    simpa only [HasOwner, he] using hv.1
  exact ⟨_, _, gas, _, hr, howner, hw, AppendStorage.storagePost_of_expected c hf _ hw,
    AppendSpec.deposit_authentic_log c hsize, AppendSpec.deposit_other_accounts c⟩

#print axioms sstore_success
#print axioms mstore_success
#print axioms copy_success
#print axioms log_success
#print axioms stop_success
#print axioms deposit_suffix
#print axioms deposit_user_result
#print axioms deposit_user_receipt
#print axioms exit_suffix
#print axioms exit_user_result
#print axioms exit_user_receipt

end Eip8282.Audit.Integrator.AppendInversion
