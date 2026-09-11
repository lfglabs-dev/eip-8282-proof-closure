import Eip8282.Audit.Integrator.AppendInversion
import Eip8282.Audit.Integrator.GetterInversion

/-!
# Actual successful SYSTEM execution determines its drain

The continuation lemmas below invert the executed instructions at arbitrary
resources. They never replace the call by a better-funded execution.
-/
namespace Eip8282.Audit.Integrator.SystemInversion

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall)
open SuccessInversion AdmissionInversion AppendInversion

set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- The real SYSTEM prefix selects the capped word count and touches pointers. -/
theorem exit_prefix (c : XiCall .exit) {fuel : Nat} {final : EVM.State} {out : ByteArray}
    (hsys : Exit.callerWord c = sysW)
    (h : X fuel exitJumpdests c.entry = .ok (.success final out)) :
    ∃ rest gas count, X rest exitJumpdests
      (at_ c (Exit.stP c) (Exit.mem₀ c) (Exit.aw₀ c) gas 247
        [UInt256.ofNat 0, Exit.drainWord c, Exit.headWord₀ c, Exit.tailWord₀ c] count) =
      .ok (.success final out) := by
  rw [entry_eq_at] at h
  have hc := Exit.hcode_of_env c (st := entrySt c) rfl
  obtain ⟨f1,g1,e1,_,hx1⟩ := success_symBlock (h := h) exit_b0 exit_b0_ok (by exact hc) rfl
    (exit_b0_shape c (entrySt c) _ _ c.gas 0 [])
  rw [withGE_at] at hx1
  obtain ⟨f2,cost2,_,_,hx2⟩ := success_jumpi_taken
    (decodeAt_of_code_pc (st := at_ c (entrySt c) _ _ g1 25 _ e1) (by exact hc) rfl exit_s25)
    rfl ((eq_ne_zero_iff _ _).mpr hsys.symm) hx1
  rw [jumpi_taken_at, withGE_at] at hx2
  obtain ⟨f3,g3,e3,_,hx3⟩ := success_symBlock (h := hx2) exit_b225 exit_b225_ok (by exact hc) rfl
    (exit_b225_shape c (entrySt c) _ _ _ _ [])
  rw [withGE_at] at hx3
  simp only [slotW_touch] at hx3
  by_cases hlt : Exit.queueLen c < UInt256.ofNat 16
  · obtain ⟨f4,cost4,_,_,hx4⟩ := success_jumpi_taken
      (decodeAt_of_code_pc (st := at_ c (Exit.stP c) _ _ g3 241 _ e3) (by exact hc) rfl exit_s241)
      rfl ((gt_ne_zero_iff _ _).mpr hlt) hx3
    rw [jumpi_taken_at, withGE_at] at hx4
    obtain ⟨f5,g5,e5,_,hx5⟩ := success_symBlock (h := hx4) exit_b245 exit_b245_ok (by exact hc) rfl
      (exit_b245_shape c (Exit.stP c) _ _ _ _ [Exit.queueLen c, Exit.headWord₀ c, Exit.tailWord₀ c])
    rw [withGE_at] at hx5
    exact ⟨f5,g5,e5, by simpa only [Exit.drainWord, if_pos hlt] using hx5⟩
  · obtain ⟨f4,cost4,_,_,hx4⟩ := success_jumpi_untaken
      (decodeAt_of_code_pc (st := at_ c (Exit.stP c) _ _ g3 241 _ e3) (by exact hc) rfl exit_s241)
      rfl ((gt_eq_zero_iff _ _).mpr hlt) hx3
    rw [jumpi_fallthrough_at, withGE_at] at hx4
    obtain ⟨f5,g5,e5,_,hx5⟩ := success_symBlock (h := hx4) exit_b242 exit_b242_ok (by exact hc) rfl
      (exit_b242_shape c (Exit.stP c) _ _ _ _ (Exit.queueLen c) [Exit.headWord₀ c, Exit.tailWord₀ c])
    rw [withGE_at] at hx5
    obtain ⟨f6,g6,e6,_,hx6⟩ := success_symBlock (h := hx5) exit_b245 exit_b245_ok (by exact hc) rfl
      (exit_b245_shape c (Exit.stP c) _ _ _ _ [UInt256.ofNat 16, Exit.headWord₀ c, Exit.tailWord₀ c])
    rw [withGE_at] at hx6
    exact ⟨f6,g6,e6, by simpa only [Exit.drainWord, if_neg hlt] using hx6⟩

/-- A real nonfinal iteration writes precisely one item and continues with the
same final result. No gas/active-memory bounds are assumed. -/
theorem exit_body (c : XiCall .exit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (i cnt head tail : UInt256) (henv : st.executionEnv = c.env) (hne : i ≠ cnt)
    {final : EVM.State} {out : ByteArray}
    (h : X fuel exitJumpdests (at_ c st mem aw g 247 [i,cnt,head,tail] e) = .ok (.success final out)) :
    ∃ rest aw' gas count, X rest exitJumpdests
      (at_ c (Exit.touchItem st (Exit.base i head))
        (Exit.writeItem st mem (UInt256.ofNat 68*i) (Exit.base i head)) aw' gas 247
        [UInt256.ofNat 1+i,cnt,head,tail] count) = .ok (.success final out) := by
  have hc := Exit.hcode_of_env c henv
  obtain ⟨f1,g1,e1,_,hx1⟩ := success_symBlock (h := h) exit_b247 exit_b247_ok (by exact hc) rfl
    (exit_b247_shape c st mem aw g e i cnt [head,tail])
  rw [withGE_at] at hx1
  obtain ⟨f2,cost2,_,_,hx2⟩ := success_jumpi_untaken
    (decodeAt_of_code_pc (st := at_ c st _ _ g1 254 _ e1) (by exact hc) rfl exit_s254)
    rfl ((eq_eq_zero_iff _ _).mpr hne) hx1
  rw [jumpi_fallthrough_at, withGE_at] at hx2
  obtain ⟨f3,g3,e3,_,hx3⟩ := success_symBlock (h := hx2) exit_b255 exit_b255_ok (by exact hc) rfl
    (exit_b255_shape c st _ _ _ _ i cnt head [tail])
  rw [withGE_at] at hx3
  obtain ⟨f4,g4,e4,hx4⟩ := mstore_success exit_s274 (by simpa only [executionEnv_touch] using hc) hx3
  obtain ⟨f5,g5,e5,_,hx5⟩ := success_symBlock (h := hx4) exit_b275 exit_b275_ok (by exact hc) rfl
    (exit_b275_shape c _ _ _ _ _ _ _ [i,cnt,head,tail])
  rw [withGE_at] at hx5
  simp only [slotW_touch] at hx5
  obtain ⟨f6,g6,e6,hx6⟩ := mstore_success exit_s284 (by simpa only [executionEnv_touch] using hc) hx5
  obtain ⟨f7,g7,e7,_,hx7⟩ := success_symBlock (h := hx6) exit_b285 exit_b285_ok (by exact hc) rfl
    (exit_b285_shape c _ _ _ _ _ _ _ [i,cnt,head,tail])
  rw [withGE_at] at hx7
  simp only [slotW_touch] at hx7
  obtain ⟨f8,g8,e8,hx8⟩ := mstore_success exit_s294 (by simpa only [executionEnv_touch] using hc) hx7
  obtain ⟨f9,g9,e9,_,hx9⟩ := success_symBlock (h := hx8) exit_b295 exit_b295_ok (by exact hc) rfl
    (exit_b295_shape c _ _ _ _ _ i [cnt,head,tail])
  rw [withGE_at] at hx9
  exact ⟨f9,_,g9,e9,hx9⟩

/-- Actual capped-loop execution, with precisely the accumulated bytes and
storage touches. The induction index counts remaining records, not fuel. -/
theorem exit_loop (c : XiCall .exit) (st₀ : EvmYul.State .EVM)
    (henv₀ : st₀.executionEnv = c.env) (head tail cnt : UInt256) (mem₀ : ByteArray)
    (hcnt : cnt.toNat ≤ 16) :
    ∀ (m i : Nat) (st : EvmYul.State .EVM) (aw g : UInt256) (e fuel : Nat)
      (final : EVM.State) (out : ByteArray), i+m=cnt.toNat → Touched st₀ st →
      X fuel exitJumpdests (at_ c st (Exit.drainMem st₀ head mem₀ i) aw g 247
        [UInt256.ofNat i,cnt,head,tail] e) = .ok (.success final out) →
      ∃ st' rest aw' gas count, Touched st₀ st' ∧
        X rest exitJumpdests (at_ c st' (Exit.drainMem st₀ head mem₀ cnt.toNat) aw' gas 301
          [cnt,cnt,head,tail] count) = .ok (.success final out) := by
  intro m
  induction m with
  | zero =>
    intro i st aw g e fuel final out hi ht hx
    have hi' : i = cnt.toNat := by omega
    subst i
    have hc := Exit.hcode_of_env c (ht.executionEnv.trans henv₀)
    obtain ⟨f1,g1,e1,_,hx1⟩ := success_symBlock (h := hx) exit_b247 exit_b247_ok (by exact hc) rfl
      (exit_b247_shape c st _ _ _ _ (UInt256.ofNat cnt.toNat) cnt [head,tail])
    rw [withGE_at] at hx1
    obtain ⟨f2,cost2,_,_,hx2⟩ := success_jumpi_taken
      (decodeAt_of_code_pc (st := at_ c st _ _ g1 254 _ e1) (by exact hc) rfl exit_s254)
      rfl ((eq_ne_zero_iff _ _).mpr (ofNat_toNat' cnt)) hx1
    rw [jumpi_taken_at, withGE_at, ofNat_toNat'] at hx2
    exact ⟨st,f2,_,_,_,ht,hx2⟩
  | succ m ih =>
    intro i st aw g e fuel final out hi ht hx
    have hne : UInt256.ofNat i ≠ cnt := by
      intro he
      have hh := congrArg UInt256.toNat he
      rw [toNat_ofNat_of_lt (by rw [size_eq]; omega)] at hh
      omega
    obtain ⟨f1,aw1,g1,e1,hx1⟩ := exit_body c _ _ _ _ (ht.executionEnv.trans henv₀) hne hx
    rw [Exit.writeItem_of_touched ht, ofNat_add_ofNat, Nat.add_comm 1 i] at hx1
    exact ih (i+1) _ aw1 g1 e1 f1 final out (by omega) (Exit.touched_touchItem ht _) hx1

/-- Actual head-update branches force the exact pointer stores. -/
theorem exit_head (c : XiCall .exit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (cnt : UInt256) (henv : st.executionEnv = c.env) {final : EVM.State} {out : ByteArray}
    (h : X fuel exitJumpdests (at_ c st mem aw g 301
      [cnt,cnt,Exit.headWord₀ c,Exit.tailWord₀ c] e) = .ok (.success final out)) :
    ∃ rest gas count, X rest exitJumpdests (at_ c (Exit.headStore c cnt st) mem aw gas 330
      [cnt] count) = .ok (.success final out) := by
  have hc := Exit.hcode_of_env c henv
  obtain ⟨f1,g1,e1,_,hx1⟩ := success_symBlock (h := h) exit_b301 exit_b301_ok (by exact hc) rfl
    (exit_b301_shape c st mem aw g e cnt cnt (Exit.headWord₀ c) (Exit.tailWord₀ c) [])
  rw [withGE_at] at hx1
  by_cases hfull : Exit.tailWord₀ c = Exit.headWord₀ c+cnt
  · obtain ⟨f2,cost2,_,_,hx2⟩ := success_jumpi_taken
      (decodeAt_of_code_pc (st := at_ c st _ _ g1 310 _ e1) (by exact hc) rfl exit_s310)
      rfl ((eq_ne_zero_iff _ _).mpr hfull) hx1
    rw [jumpi_taken_at, withGE_at] at hx2
    obtain ⟨f3,g3,e3,_,hx3⟩ := success_symBlock (h := hx2) exit_b319 exit_b319_ok (by exact hc) rfl
      (exit_b319_shape c st _ _ _ _ cnt (Exit.headWord₀ c+cnt) [])
    rw [withGE_at] at hx3
    obtain ⟨f4,g4,e4,hx4⟩ := sstore_success exit_s325 hc hx3
    obtain ⟨f5,g5,e5,_,hx5⟩ := success_symBlock (h := hx4) exit_b326 exit_b326_ok
      (by simpa only [executionEnv_at, executionEnv_sstore] using hc) rfl (exit_b326_shape c _ _ _ _ _ [cnt])
    rw [withGE_at] at hx5
    obtain ⟨f6,g6,e6,hx6⟩ := sstore_success exit_s329 (by simpa only [executionEnv_at, executionEnv_sstore] using hc) hx5
    exact ⟨f6,g6,e6,by simpa only [Exit.headStore, if_pos hfull] using hx6⟩
  · obtain ⟨f2,cost2,_,_,hx2⟩ := success_jumpi_untaken
      (decodeAt_of_code_pc (st := at_ c st _ _ g1 310 _ e1) (by exact hc) rfl exit_s310)
      rfl ((eq_eq_zero_iff _ _).mpr hfull) hx1
    rw [jumpi_fallthrough_at, withGE_at] at hx2
    obtain ⟨f3,g3,e3,_,hx3⟩ := success_symBlock (h := hx2) exit_b311 exit_b311_ok (by exact hc) rfl
      (exit_b311_shape c st _ _ _ _ cnt (Exit.headWord₀ c+cnt) [])
    rw [withGE_at] at hx3
    obtain ⟨f4,g4,e4,hx4⟩ := sstore_success exit_s314 hc hx3
    obtain ⟨f5,g5,e5,_,hx5⟩ := success_symBlock (h := hx4) exit_b315 exit_b315_ok
      (by simpa only [executionEnv_at, executionEnv_sstore] using hc) rfl (exit_b315_shape c _ _ _ _ _ [cnt])
    rw [withGE_at] at hx5
    exact ⟨f5,g5,e5,by simpa only [Exit.headStore, if_neg hfull] using hx5⟩

/-- The common executed control-store/RETURN tail. -/
theorem exit_store_return (c : XiCall .exit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (v cnt : UInt256) (henv : st.executionEnv = c.env) {final : EVM.State} {out : ByteArray}
    (h : X fuel exitJumpdests (at_ c st mem aw g 442 [v,cnt] e) = .ok (.success final out)) :
    final.toState = SystemSpec.controlStore st v ∧
      out = mem.readWithPadding 0 (UInt256.ofNat 68*cnt).toNat := by
  have hc := Exit.hcode_of_env c henv
  obtain ⟨f1,g1,e1,_,hx1⟩ := success_symBlock (h := h) exit_b442 exit_b442_ok (by exact hc) rfl
    (exit_b442_shape c st _ _ _ _ [v,cnt])
  rw [withGE_at] at hx1
  obtain ⟨f2,g2,e2,hx2⟩ := sstore_success exit_s444 hc hx1
  obtain ⟨f3,g3,e3,_,hx3⟩ := success_symBlock (h := hx2) exit_b445 exit_b445_ok
    (by simpa only [executionEnv_at, executionEnv_sstore] using hc) rfl (exit_b445_shape c _ _ _ _ _ [cnt])
  rw [withGE_at] at hx3
  obtain ⟨f4,g4,e4,hx4⟩ := sstore_success exit_s448 (by simpa only [executionEnv_at, executionEnv_sstore] using hc) hx3
  obtain ⟨f5,g5,e5,_,hx5⟩ := success_symBlock (h := hx4) exit_b449 exit_b449_ok
    (by simpa only [executionEnv_at, executionEnv_sstore] using hc) rfl (exit_b449_shape c _ _ _ _ _ cnt [])
  rw [withGE_at] at hx5
  have hd := decodeAt_of_code_pc (st := at_ c (SystemSpec.controlStore st v) mem aw g5 453 [UInt256.ofNat 0,UInt256.ofNat 68*cnt] e5)
    (by simpa only [SystemSpec.controlStore, executionEnv_at, executionEnv_sstore] using hc) rfl exit_s453
  exact ⟨GetterInversion.return_state hd rfl hx5, success_return_bytes hd rfl hx5⟩

/-- The actual latch/unlock/fold branches and stores determine the final state. -/
theorem exit_excess (c : XiCall .exit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (cnt : UInt256) (henv : st.executionEnv = c.env) {final : EVM.State} {out : ByteArray}
    (h : X fuel exitJumpdests (at_ c st mem aw g 330 [cnt] e) = .ok (.success final out)) :
    ∃ stX, Touched st stX ∧ final.toState = SystemSpec.controlStore stX (Exit.newExcess c stX) ∧
      out = mem.readWithPadding 0 (UInt256.ofNat 68*cnt).toNat := by
  have hc := Exit.hcode_of_env c henv
  have hcds : cdsizeW st = Exit.cdsizeWord c := by unfold cdsizeW; rw [henv]; rfl
  obtain ⟨f1,g1,e1,_,hx1⟩ := success_symBlock (h := h) exit_b330 exit_b330_ok (by exact hc) rfl
    (exit_b330_shape c st _ _ _ _ [cnt])
  rw [withGE_at] at hx1
  simp only [hcds] at hx1
  by_cases hcd : Exit.cdsizeWord c ≠ ⟨0⟩
  · obtain ⟨f2,cost2,_,_,hx2⟩ := success_jumpi_taken
      (decodeAt_of_code_pc (st := at_ c st _ _ g1 335 _ e1) (by exact hc) rfl exit_s335) rfl hcd hx1
    rw [jumpi_taken_at, withGE_at] at hx2
    obtain ⟨f3,g3,e3,_,hx3⟩ := success_symBlock (h := hx2) exit_b408 exit_b408_ok (by exact hc) rfl
      (exit_b408_shape c st _ _ _ _ [cnt])
    rw [withGE_at] at hx3
    obtain ⟨hs,ho⟩ := exit_store_return c INH cnt henv hx3
    exact ⟨st,Touched.refl _,by simpa only [Exit.newExcess, if_pos hcd] using hs,ho⟩
  · have hzero : Exit.cdsizeWord c = ⟨0⟩ := by simpa using hcd
    obtain ⟨f2,cost2,_,_,hx2⟩ := success_jumpi_untaken
      (decodeAt_of_code_pc (st := at_ c st _ _ g1 335 _ e1) (by exact hc) rfl exit_s335) rfl hzero hx1
    rw [jumpi_fallthrough_at, withGE_at] at hx2
    obtain ⟨f3,g3,e3,_,hx3⟩ := success_symBlock (h := hx2) exit_b336 exit_b336_ok (by exact hc) rfl
      (exit_b336_shape c st _ _ _ _ [cnt])
    rw [withGE_at] at hx3
    simp only [slotW_touch] at hx3
    let stX := touch (touch st (UInt256.ofNat 0)) (UInt256.ofNat 1)
    have ht : Touched st stX := ((Touched.refl st).touch _).touch _
    have hcX := Exit.hcode_of_env c (ht.executionEnv.trans henv)
    by_cases hinh : slotW st (UInt256.ofNat 0) = INH
    · obtain ⟨f4,cost4,_,_,hx4⟩ := success_jumpi_taken
        (decodeAt_of_code_pc (st := at_ c stX _ _ g3 379 _ e3) (by exact hcX) rfl exit_s379)
        rfl ((eq_ne_zero_iff _ _).mpr hinh.symm) hx3
      rw [jumpi_taken_at, withGE_at] at hx4
      obtain ⟨f5,g5,e5,_,hx5⟩ := success_symBlock (h := hx4) exit_b390 exit_b390_ok (by exact hcX) rfl
        (exit_b390_shape c stX _ _ _ _ _ _ [cnt])
      rw [withGE_at] at hx5
      obtain ⟨hs,ho⟩ := exit_store_return c (UInt256.ofNat 0) cnt (ht.executionEnv.trans henv) hx5
      exact ⟨stX,ht,by simpa only [Exit.newExcess, if_neg hcd, stX, slotW_touch, if_pos hinh] using hs,ho⟩
    · obtain ⟨f4,cost4,_,_,hx4⟩ := success_jumpi_untaken
        (decodeAt_of_code_pc (st := at_ c stX _ _ g3 379 _ e3) (by exact hcX) rfl exit_s379)
        rfl ((eq_eq_zero_iff _ _).mpr (fun he => hinh he.symm)) hx3
      rw [jumpi_fallthrough_at, withGE_at] at hx4
      obtain ⟨f5,g5,e5,_,hx5⟩ := success_symBlock (h := hx4) exit_b380 exit_b380_ok (by exact hcX) rfl
        (exit_b380_shape c stX _ _ _ _ _ _ [cnt])
      rw [withGE_at] at hx5
      by_cases hgt : UInt256.ofNat 2 < slotW st (UInt256.ofNat 1)+slotW st (UInt256.ofNat 0)
      · obtain ⟨f6,cost6,_,_,hx6⟩ := success_jumpi_taken
          (decodeAt_of_code_pc (st := at_ c stX _ _ g5 389 _ e5) (by exact hcX) rfl exit_s389)
          rfl ((gt_ne_zero_iff _ _).mpr hgt) hx5
        rw [jumpi_taken_at, withGE_at] at hx6
        obtain ⟨f7,g7,e7,_,hx7⟩ := success_symBlock (h := hx6) exit_b398 exit_b398_ok (by exact hcX) rfl
          (exit_b398_shape c stX _ _ _ _ _ _ [cnt])
        rw [withGE_at] at hx7
        obtain ⟨hs,ho⟩ := exit_store_return c _ cnt (ht.executionEnv.trans henv) hx7
        exact ⟨stX,ht,by simpa only [Exit.newExcess, if_neg hcd, stX, slotW_touch, if_neg hinh, if_pos hgt] using hs,ho⟩
      · obtain ⟨f6,cost6,_,_,hx6⟩ := success_jumpi_untaken
          (decodeAt_of_code_pc (st := at_ c stX _ _ g5 389 _ e5) (by exact hcX) rfl exit_s389)
          rfl ((gt_eq_zero_iff _ _).mpr hgt) hx5
        rw [jumpi_fallthrough_at, withGE_at] at hx6
        obtain ⟨f7,g7,e7,_,hx7⟩ := success_symBlock (h := hx6) exit_b390 exit_b390_ok (by exact hcX) rfl
          (exit_b390_shape c stX _ _ _ _ _ _ [cnt])
        rw [withGE_at] at hx7
        obtain ⟨hs,ho⟩ := exit_store_return c (UInt256.ofNat 0) cnt (ht.executionEnv.trans henv) hx7
        exact ⟨stX,ht,by simpa only [Exit.newExcess, if_neg hcd, stX, slotW_touch, if_neg hinh, if_neg hgt] using hs,ho⟩

/-- Full executed SYSTEM path: final state and buffer, with no resource or
post-state premise. Intermediate witnesses carry only actual read touches. -/
theorem exit_final (c : XiCall .exit) {fuel : Nat} {final : EVM.State} {out : ByteArray}
    (hsys : Exit.callerWord c = sysW)
    (h : X fuel exitJumpdests c.entry = .ok (.success final out)) :
    ∃ st' stX, Touched (entrySt c) st' ∧
      Touched (Exit.headStore c (Exit.drainWord c) st') stX ∧
      final.toState = SystemSpec.controlStore stX (Exit.newExcess c stX) ∧
      out = (Exit.drainMem (entrySt c) (Exit.headWord₀ c) (Exit.mem₀ c)
        (Exit.drainWord c).toNat).readWithPadding 0 (UInt256.ofNat 68*Exit.drainWord c).toNat := by
  obtain ⟨f1,g1,e1,hx1⟩ := exit_prefix c hsys h
  obtain ⟨st',f2,aw2,g2,e2,ht,hx2⟩ := exit_loop c (entrySt c) rfl
    (Exit.headWord₀ c) (Exit.tailWord₀ c) (Exit.drainWord c) (Exit.mem₀ c)
    (Exit.drainWord_le c) (Exit.drainWord c).toNat 0 (Exit.stP c) (Exit.aw₀ c) g1 e1 f1 final out
    (by omega) (Exit.touched_stP c) hx1
  obtain ⟨f3,g3,e3,hx3⟩ := exit_head c _ ht.executionEnv hx2
  have henvH : (Exit.headStore c (Exit.drainWord c) st').executionEnv = c.env := by
    unfold Exit.headStore
    split <;> simp only [executionEnv_sstore] <;> exact ht.executionEnv
  obtain ⟨stX,hxt,hs,ho⟩ := exit_excess c _ henvH hx3
  exact ⟨st',stX,ht,hxt,hs,ho⟩

/-- Actual successful Ξ publishes that exact concrete state and return buffer.
The owner account need not be assumed for this operational statement. -/
theorem exit_system_result (c : XiCall .exit)
    {published : Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate}
    {out : ByteArray} (hsys : c.env.source = Eip8282.Audit.EvmRunner.sysAddr)
    (h : c.result = .ok (.success published out)) :
    ∃ st' stX gas, Touched (entrySt c) st' ∧
      Touched (Exit.headStore c (Exit.drainWord c) st') stX ∧
      published = ((SystemSpec.controlStore stX (Exit.newExcess c stX)).createdAccounts,
        (SystemSpec.controlStore stX (Exit.newExcess c stX)).accountMap, gas,
        (SystemSpec.controlStore stX (Exit.newExcess c stX)).substate) ∧
      out = (Exit.drainMem (entrySt c) (Exit.headWord₀ c) (Exit.mem₀ c)
        (Exit.drainWord c).toNat).readWithPadding 0 (UInt256.ofNat 68*Exit.drainWord c).toNat := by
  obtain ⟨final,hpub,hx⟩ := xi_success_X c h
  have hw : Exit.callerWord c = sysW := (callerW_eq_sysW_iff c).mpr hsys
  obtain ⟨st',stX,ht,hxt,hs,ho⟩ := exit_final c hw hx
  refine ⟨st',stX,final.gasAvailable,ht,hxt,?_,ho⟩
  rw [← hpub]
  rw [hs]

/-- Every successful SYSTEM Ξ call has the independent all-slot storage result
and exact staged output. Only actual owner existence is needed to interpret
upstream SSTORE as storage updates; no gas/fuel/permission condition is assumed. -/
theorem exit_system_storage (c : XiCall .exit)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hsys : c.env.source = Eip8282.Audit.EvmRunner.sysAddr)
    (h : c.result = .ok (.success (created,world,gas,substate) out))
    (howner : SystemSpec.HasOwner (entrySt c)) :
    (∀ k, SystemSpec.worldSlot world c.env.codeOwner k = SystemSpec.expectedSlot (entrySt c)
      (UInt256.ofNat 2) (Exit.drainWord c) (Exit.cdsizeWord c) k) ∧
    out = (Exit.drainMem (entrySt c) (Exit.headWord₀ c) (Exit.mem₀ c)
      (Exit.drainWord c).toNat).readWithPadding 0 (UInt256.ofNat 68*Exit.drainWord c).toNat := by
  obtain ⟨st',stX,g,ht,hxt,hpub,hout⟩ := exit_system_result c hsys h
  have hw : world = (SystemSpec.controlStore stX (Exit.newExcess c stX)).accountMap :=
    congrArg (fun p => p.2.1) hpub
  have henv := SystemSpec.system_environment ht (Exit.drainWord c) hxt (Exit.newExcess c stX)
  refine ⟨?_,hout⟩
  intro k
  rw [hw, ← congrArg ExecutionEnv.codeOwner henv, SystemSpec.worldSlot_state]
  rw [← ControlSpec.exit_systemExcess c stX]
  exact SystemSpec.system_storage howner ht (UInt256.ofNat 2) (Exit.drainWord c)
    (Exit.cdsizeWord c) hxt k

/-- Actual successful MSTORE8, including its one-byte memory expansion. -/
theorem mstore8_success {kind : Eip8282.Audit.Model.Kind} {c : XiCall kind}
    {fuel pc : Nat} {vj : Array UInt256} {code : ByteArray}
    {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {off value : UInt256} {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (hop : opcodeAt code pc = some (.MSTORE8,none)) (hc : st.executionEnv.code = code)
    (h : X fuel vj (at_ c st mem aw g pc (off::value::stk) e) = .ok (.success final out)) :
    ∃ rest gas count, X rest vj (at_ c st (mstore8Mem mem off value) (mAfter aw off.toNat 1)
      gas (pc+1) stk count) = .ok (.success final out) := by
  let pre := at_ c st mem aw g pc (off::value::stk) e
  obtain ⟨rest, gas, count, hx⟩ := success_effect (by decide : Operation.MSTORE8 ∈ allOps) (by decide)
    (decodeAt_of_code_pc (st := pre) hc rfl hop) (step_MSTORE8 rfl) h
  have he : withGE (({ pre with toMachineState := pre.toMachineState.mstore8 off value } :
      EVM.State).replaceStackAndIncrPC stk) gas count =
      at_ c st (mstore8Mem mem off value) (mAfter aw off.toNat 1) gas (pc+1) stk count :=
    withGE_machine_replace_at c st mem aw g pc (off::value::stk) stk e _ _ _ rfl rfl
  rw [he] at hx
  exact ⟨rest, gas, count, hx⟩

theorem deposit_prefix (c : XiCall .deposit) {fuel : Nat} {final : EVM.State} {out : ByteArray}
    (hsys : Deposit.callerWord c = sysW)
    (h : X fuel depositJumpdests c.entry = .ok (.success final out)) :
    ∃ rest gas count, X rest depositJumpdests
      (at_ c (Deposit.stP c) (Deposit.mem₀ c) (Deposit.aw₀ c) gas 307
        [UInt256.ofNat 0, Deposit.drainWord c, Deposit.headWord₀ c, Deposit.tailWord₀ c] count) =
      .ok (.success final out) := by
  rw [entry_eq_at] at h
  have hc := Deposit.hcode_of_env c (st := entrySt c) rfl
  obtain ⟨f1,g1,e1,_,hx1⟩ := success_symBlock (h := h) deposit_b0 deposit_b0_ok (by exact hc) rfl
    (deposit_b0_shape c (entrySt c) _ _ c.gas 0 [])
  rw [withGE_at] at hx1
  obtain ⟨f2,cost2,_,_,hx2⟩ := success_jumpi_taken
    (decodeAt_of_code_pc (st := at_ c (entrySt c) _ _ g1 26 _ e1) (by exact hc) rfl deposit_s26)
    rfl ((eq_ne_zero_iff _ _).mpr hsys.symm) hx1
  rw [jumpi_taken_at, withGE_at] at hx2
  obtain ⟨f3,g3,e3,_,hx3⟩ := success_symBlock (h := hx2) deposit_b284 deposit_b284_ok (by exact hc) rfl
    (deposit_b284_shape c (entrySt c) _ _ _ _ [])
  rw [withGE_at] at hx3
  simp only [slotW_touch] at hx3
  by_cases hlt : Deposit.queueLen c < UInt256.ofNat 64
  · obtain ⟨f4,cost4,_,_,hx4⟩ := success_jumpi_taken
      (decodeAt_of_code_pc (st := at_ c (Deposit.stP c) _ _ g3 301 _ e3) (by exact hc) rfl deposit_s301)
      rfl ((gt_ne_zero_iff _ _).mpr hlt) hx3
    rw [jumpi_taken_at, withGE_at] at hx4
    obtain ⟨f5,g5,e5,_,hx5⟩ := success_symBlock (h := hx4) deposit_b305 deposit_b305_ok (by exact hc) rfl
      (deposit_b305_shape c (Deposit.stP c) _ _ _ _ [Deposit.queueLen c, Deposit.headWord₀ c, Deposit.tailWord₀ c])
    rw [withGE_at] at hx5
    exact ⟨f5,g5,e5, by simpa only [Deposit.drainWord, if_pos hlt] using hx5⟩
  · obtain ⟨f4,cost4,_,_,hx4⟩ := success_jumpi_untaken
      (decodeAt_of_code_pc (st := at_ c (Deposit.stP c) _ _ g3 301 _ e3) (by exact hc) rfl deposit_s301)
      rfl ((gt_eq_zero_iff _ _).mpr hlt) hx3
    rw [jumpi_fallthrough_at, withGE_at] at hx4
    obtain ⟨f5,g5,e5,_,hx5⟩ := success_symBlock (h := hx4) deposit_b302 deposit_b302_ok (by exact hc) rfl
      (deposit_b302_shape c (Deposit.stP c) _ _ _ _ (Deposit.queueLen c) [Deposit.headWord₀ c, Deposit.tailWord₀ c])
    rw [withGE_at] at hx5
    obtain ⟨f6,g6,e6,_,hx6⟩ := success_symBlock (h := hx5) deposit_b305 deposit_b305_ok (by exact hc) rfl
      (deposit_b305_shape c (Deposit.stP c) _ _ _ _ [UInt256.ofNat 64, Deposit.headWord₀ c, Deposit.tailWord₀ c])
    rw [withGE_at] at hx6
    exact ⟨f6,g6,e6, by simpa only [Deposit.drainWord, if_neg hlt] using hx6⟩

theorem deposit_body (c : XiCall .deposit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (i cnt head tail : UInt256) (henv : st.executionEnv = c.env) (hne : i ≠ cnt)
    {final : EVM.State} {out : ByteArray}
    (h : X fuel depositJumpdests (at_ c st mem aw g 307 [i,cnt,head,tail] e) = .ok (.success final out)) :
    ∃ rest aw' gas count, X rest depositJumpdests
      (at_ c (Deposit.touchItem st (Deposit.base i head))
        (Deposit.writeItem st mem (UInt256.ofNat 184*i) (Deposit.base i head)) aw' gas 307
        [UInt256.ofNat 1+i,cnt,head,tail] count) = .ok (.success final out) := by
  have hc := Deposit.hcode_of_env c henv
  obtain ⟨f1,g1,e1,_,hx1⟩ := success_symBlock (h := h) deposit_b307 deposit_b307_ok (by exact hc) rfl
    (deposit_b307_shape c st mem aw g e i cnt [head,tail])
  rw [withGE_at] at hx1
  obtain ⟨f2,cost2,_,_,hx2⟩ := success_jumpi_untaken
    (decodeAt_of_code_pc (st := at_ c st _ _ g1 314 _ e1) (by exact hc) rfl deposit_s314)
    rfl ((eq_eq_zero_iff _ _).mpr hne) hx1
  rw [jumpi_fallthrough_at, withGE_at] at hx2
  obtain ⟨f3,g3,e3,_,hx3⟩ := success_symBlock (h := hx2) deposit_b315 deposit_b315_ok (by exact hc) rfl
    (deposit_b315_shape c _ _ _ _ _ i cnt head [tail])
  rw [withGE_at] at hx3
  obtain ⟨f4,g4,e4,hx4⟩ := mstore_success deposit_s331 (by simpa only [executionEnv_touch] using hc) hx3
  obtain ⟨f5,g5,e5,_,hx5⟩ := success_symBlock (h := hx4) deposit_b332 deposit_b332_ok (by exact hc) rfl
    (deposit_b332_shape c _ _ _ _ _ _ _ [i,cnt,head,tail])
  rw [withGE_at] at hx5
  simp only [slotW_touch] at hx5
  obtain ⟨f6,g6,e6,hx6⟩ := mstore_success deposit_s341 (by simpa only [executionEnv_touch] using hc) hx5
  obtain ⟨f7,g7,e7,_,hx7⟩ := success_symBlock (h := hx6) deposit_b342 deposit_b342_ok (by exact hc) rfl
    (deposit_b342_shape c _ _ _ _ _ _ _ [i,cnt,head,tail])
  rw [withGE_at] at hx7
  simp only [slotW_touch] at hx7
  obtain ⟨f8,g8,e8,hx8⟩ := mstore_success deposit_s352 (by simpa only [executionEnv_touch] using hc) hx7
  obtain ⟨f9,g9,e9,_,hx9⟩ := success_symBlock (h := hx8) deposit_b353 deposit_b353_ok (by exact hc) rfl
    (deposit_b353_shape c _ _ _ _ _ _ _ [_,i,cnt,head,tail])
  rw [withGE_at] at hx9
  obtain ⟨f10,g10,e10,hx10⟩ := mstore8_success deposit_s378 (by simpa only [executionEnv_touch] using hc) hx9
  obtain ⟨f11,g11,e11,_,hx11⟩ := success_symBlock (h := hx10) deposit_b379 deposit_b379_ok (by exact hc) rfl
    (deposit_b379_shape c _ _ _ _ _ _ _ [_,_,i,cnt,head,tail])
  rw [withGE_at] at hx11
  obtain ⟨f12,g12,e12,hx12⟩ := mstore8_success deposit_s387 (by simpa only [executionEnv_touch] using hc) hx11
  obtain ⟨f13,g13,e13,_,hx13⟩ := success_symBlock (h := hx12) deposit_b388 deposit_b388_ok (by exact hc) rfl
    (deposit_b388_shape c _ _ _ _ _ _ _ [_,_,i,cnt,head,tail])
  rw [withGE_at] at hx13
  obtain ⟨f14,g14,e14,hx14⟩ := mstore8_success deposit_s396 (by simpa only [executionEnv_touch] using hc) hx13
  obtain ⟨f15,g15,e15,_,hx15⟩ := success_symBlock (h := hx14) deposit_b397 deposit_b397_ok (by exact hc) rfl
    (deposit_b397_shape c _ _ _ _ _ _ _ [_,_,i,cnt,head,tail])
  rw [withGE_at] at hx15
  obtain ⟨f16,g16,e16,hx16⟩ := mstore8_success deposit_s405 (by simpa only [executionEnv_touch] using hc) hx15
  obtain ⟨f17,g17,e17,_,hx17⟩ := success_symBlock (h := hx16) deposit_b406 deposit_b406_ok (by exact hc) rfl
    (deposit_b406_shape c _ _ _ _ _ _ _ [_,_,i,cnt,head,tail])
  rw [withGE_at] at hx17
  obtain ⟨f18,g18,e18,hx18⟩ := mstore8_success deposit_s414 (by simpa only [executionEnv_touch] using hc) hx17
  obtain ⟨f19,g19,e19,_,hx19⟩ := success_symBlock (h := hx18) deposit_b415 deposit_b415_ok (by exact hc) rfl
    (deposit_b415_shape c _ _ _ _ _ _ _ [_,_,i,cnt,head,tail])
  rw [withGE_at] at hx19
  obtain ⟨f20,g20,e20,hx20⟩ := mstore8_success deposit_s423 (by simpa only [executionEnv_touch] using hc) hx19
  obtain ⟨f21,g21,e21,_,hx21⟩ := success_symBlock (h := hx20) deposit_b424 deposit_b424_ok (by exact hc) rfl
    (deposit_b424_shape c _ _ _ _ _ _ _ [_,_,i,cnt,head,tail])
  rw [withGE_at] at hx21
  obtain ⟨f22,g22,e22,hx22⟩ := mstore8_success deposit_s432 (by simpa only [executionEnv_touch] using hc) hx21
  obtain ⟨f23,g23,e23,hx23⟩ := mstore8_success deposit_s433 (by simpa only [executionEnv_touch] using hc) hx22
  obtain ⟨f24,g24,e24,_,hx24⟩ := success_symBlock (h := hx23) deposit_b434 deposit_b434_ok (by exact hc) rfl
    (deposit_b434_shape c _ _ _ _ _ _ _ [i,cnt,head,tail])
  rw [withGE_at] at hx24
  simp only [slotW_touch] at hx24
  obtain ⟨f25,g25,e25,hx25⟩ := mstore_success deposit_s443 (by simpa only [executionEnv_touch] using hc) hx24
  obtain ⟨f26,g26,e26,_,hx26⟩ := success_symBlock (h := hx25) deposit_b444 deposit_b444_ok (by exact hc) rfl
    (deposit_b444_shape c _ _ _ _ _ _ _ [i,cnt,head,tail])
  rw [withGE_at] at hx26
  simp only [slotW_touch] at hx26
  obtain ⟨f27,g27,e27,hx27⟩ := mstore_success deposit_s453 (by simpa only [executionEnv_touch] using hc) hx26
  obtain ⟨f28,g28,e28,_,hx28⟩ := success_symBlock (h := hx27) deposit_b454 deposit_b454_ok (by exact hc) rfl
    (deposit_b454_shape c _ _ _ _ _ _ _ [i,cnt,head,tail])
  rw [withGE_at] at hx28
  simp only [slotW_touch] at hx28
  obtain ⟨f29,g29,e29,hx29⟩ := mstore_success deposit_s463 (by simpa only [executionEnv_touch] using hc) hx28
  obtain ⟨f30,g30,e30,_,hx30⟩ := success_symBlock (h := hx29) deposit_b464 deposit_b464_ok (by exact hc) rfl
    (deposit_b464_shape c _ _ _ _ _ i [cnt,head,tail])
  rw [withGE_at] at hx30
  exact ⟨f30,_,g30,e30,hx30⟩

theorem deposit_loop (c : XiCall .deposit) (st₀ : EvmYul.State .EVM)
    (henv₀ : st₀.executionEnv = c.env) (head tail cnt : UInt256) (mem₀ : ByteArray)
    (hcnt : cnt.toNat ≤ 64) :
    ∀ (m i : Nat) (st : EvmYul.State .EVM) (aw g : UInt256) (e fuel : Nat)
      (final : EVM.State) (out : ByteArray), i+m=cnt.toNat → Touched st₀ st →
      X fuel depositJumpdests (at_ c st (Deposit.drainMem st₀ head mem₀ i) aw g 307
        [UInt256.ofNat i,cnt,head,tail] e) = .ok (.success final out) →
      ∃ st' rest aw' gas count, Touched st₀ st' ∧
        X rest depositJumpdests (at_ c st' (Deposit.drainMem st₀ head mem₀ cnt.toNat) aw' gas 471
          [cnt,cnt,head,tail] count) = .ok (.success final out) := by
  intro m
  induction m with
  | zero =>
    intro i st aw g e fuel final out hi ht hx
    have hi' : i = cnt.toNat := by omega
    subst i
    have hc := Deposit.hcode_of_env c (ht.executionEnv.trans henv₀)
    obtain ⟨f1,g1,e1,_,hx1⟩ := success_symBlock (h := hx) deposit_b307 deposit_b307_ok (by exact hc) rfl
      (deposit_b307_shape c st _ _ _ _ (UInt256.ofNat cnt.toNat) cnt [head,tail])
    rw [withGE_at] at hx1
    obtain ⟨f2,cost2,_,_,hx2⟩ := success_jumpi_taken
      (decodeAt_of_code_pc (st := at_ c st _ _ g1 314 _ e1) (by exact hc) rfl deposit_s314)
      rfl ((eq_ne_zero_iff _ _).mpr (ofNat_toNat' cnt)) hx1
    rw [jumpi_taken_at, withGE_at, ofNat_toNat'] at hx2
    exact ⟨st,f2,_,_,_,ht,hx2⟩
  | succ m ih =>
    intro i st aw g e fuel final out hi ht hx
    have hne : UInt256.ofNat i ≠ cnt := by
      intro he
      have hh := congrArg UInt256.toNat he
      rw [toNat_ofNat_of_lt (by rw [size_eq]; omega)] at hh
      omega
    obtain ⟨f1,aw1,g1,e1,hx1⟩ := deposit_body c _ _ _ _ (ht.executionEnv.trans henv₀) hne hx
    rw [Deposit.writeItem_of_touched ht, ofNat_add_ofNat, Nat.add_comm 1 i] at hx1
    exact ih (i+1) _ aw1 g1 e1 f1 final out (by omega) (Deposit.touched_touchItem ht _) hx1

theorem deposit_head (c : XiCall .deposit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (cnt : UInt256) (henv : st.executionEnv = c.env) {final : EVM.State} {out : ByteArray}
    (h : X fuel depositJumpdests (at_ c st mem aw g 471
      [cnt,cnt,Deposit.headWord₀ c,Deposit.tailWord₀ c] e) = .ok (.success final out)) :
    ∃ rest gas count, X rest depositJumpdests (at_ c (Deposit.headStore c cnt st) mem aw gas 500
      [cnt] count) = .ok (.success final out) := by
  have hc := Deposit.hcode_of_env c henv
  obtain ⟨f1,g1,e1,_,hx1⟩ := success_symBlock (h := h) deposit_b471 deposit_b471_ok (by exact hc) rfl
    (deposit_b471_shape c st mem aw g e cnt cnt (Deposit.headWord₀ c) (Deposit.tailWord₀ c) [])
  rw [withGE_at] at hx1
  by_cases hfull : Deposit.tailWord₀ c = Deposit.headWord₀ c+cnt
  · obtain ⟨f2,cost2,_,_,hx2⟩ := success_jumpi_taken
      (decodeAt_of_code_pc (st := at_ c st _ _ g1 480 _ e1) (by exact hc) rfl deposit_s480)
      rfl ((eq_ne_zero_iff _ _).mpr hfull) hx1
    rw [jumpi_taken_at, withGE_at] at hx2
    obtain ⟨f3,g3,e3,_,hx3⟩ := success_symBlock (h := hx2) deposit_b489 deposit_b489_ok (by exact hc) rfl
      (deposit_b489_shape c st _ _ _ _ cnt (Deposit.headWord₀ c+cnt) [])
    rw [withGE_at] at hx3
    obtain ⟨f4,g4,e4,hx4⟩ := sstore_success deposit_s495 hc hx3
    obtain ⟨f5,g5,e5,_,hx5⟩ := success_symBlock (h := hx4) deposit_b496 deposit_b496_ok
      (by simpa only [executionEnv_at, executionEnv_sstore] using hc) rfl (deposit_b496_shape c _ _ _ _ _ [cnt])
    rw [withGE_at] at hx5
    obtain ⟨f6,g6,e6,hx6⟩ := sstore_success deposit_s499 (by simpa only [executionEnv_at, executionEnv_sstore] using hc) hx5
    exact ⟨f6,g6,e6,by simpa only [Deposit.headStore, if_pos hfull] using hx6⟩
  · obtain ⟨f2,cost2,_,_,hx2⟩ := success_jumpi_untaken
      (decodeAt_of_code_pc (st := at_ c st _ _ g1 480 _ e1) (by exact hc) rfl deposit_s480)
      rfl ((eq_eq_zero_iff _ _).mpr hfull) hx1
    rw [jumpi_fallthrough_at, withGE_at] at hx2
    obtain ⟨f3,g3,e3,_,hx3⟩ := success_symBlock (h := hx2) deposit_b481 deposit_b481_ok (by exact hc) rfl
      (deposit_b481_shape c st _ _ _ _ cnt (Deposit.headWord₀ c+cnt) [])
    rw [withGE_at] at hx3
    obtain ⟨f4,g4,e4,hx4⟩ := sstore_success deposit_s484 hc hx3
    obtain ⟨f5,g5,e5,_,hx5⟩ := success_symBlock (h := hx4) deposit_b485 deposit_b485_ok
      (by simpa only [executionEnv_at, executionEnv_sstore] using hc) rfl (deposit_b485_shape c _ _ _ _ _ [cnt])
    rw [withGE_at] at hx5
    exact ⟨f5,g5,e5,by simpa only [Deposit.headStore, if_neg hfull] using hx5⟩

theorem deposit_store_return (c : XiCall .deposit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (v cnt : UInt256) (henv : st.executionEnv = c.env) {final : EVM.State} {out : ByteArray}
    (h : X fuel depositJumpdests (at_ c st mem aw g 612 [v,cnt] e) = .ok (.success final out)) :
    final.toState = SystemSpec.controlStore st v ∧
      out = mem.readWithPadding 0 (UInt256.ofNat 184*cnt).toNat := by
  have hc := Deposit.hcode_of_env c henv
  obtain ⟨f1,g1,e1,_,hx1⟩ := success_symBlock (h := h) deposit_b612 deposit_b612_ok (by exact hc) rfl
    (deposit_b612_shape c st _ _ _ _ [v,cnt])
  rw [withGE_at] at hx1
  obtain ⟨f2,g2,e2,hx2⟩ := sstore_success deposit_s614 hc hx1
  obtain ⟨f3,g3,e3,_,hx3⟩ := success_symBlock (h := hx2) deposit_b615 deposit_b615_ok
    (by simpa only [executionEnv_at, executionEnv_sstore] using hc) rfl (deposit_b615_shape c _ _ _ _ _ [cnt])
  rw [withGE_at] at hx3
  obtain ⟨f4,g4,e4,hx4⟩ := sstore_success deposit_s618 (by simpa only [executionEnv_at, executionEnv_sstore] using hc) hx3
  obtain ⟨f5,g5,e5,_,hx5⟩ := success_symBlock (h := hx4) deposit_b619 deposit_b619_ok
    (by simpa only [executionEnv_at, executionEnv_sstore] using hc) rfl (deposit_b619_shape c _ _ _ _ _ cnt [])
  rw [withGE_at] at hx5
  have hd := decodeAt_of_code_pc (st := at_ c (SystemSpec.controlStore st v) mem aw g5 623 [UInt256.ofNat 0,UInt256.ofNat 184*cnt] e5)
    (by simpa only [SystemSpec.controlStore, executionEnv_at, executionEnv_sstore] using hc) rfl deposit_s623
  exact ⟨GetterInversion.return_state hd rfl hx5, success_return_bytes hd rfl hx5⟩

theorem deposit_excess (c : XiCall .deposit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (cnt : UInt256) (henv : st.executionEnv = c.env) {final : EVM.State} {out : ByteArray}
    (h : X fuel depositJumpdests (at_ c st mem aw g 500 [cnt] e) = .ok (.success final out)) :
    ∃ stX, Touched st stX ∧ final.toState = SystemSpec.controlStore stX (Deposit.newExcess c stX) ∧
      out = mem.readWithPadding 0 (UInt256.ofNat 184*cnt).toNat := by
  have hc := Deposit.hcode_of_env c henv
  have hcds : cdsizeW st = Deposit.cdsizeWord c := by unfold cdsizeW; rw [henv]; rfl
  obtain ⟨f1,g1,e1,_,hx1⟩ := success_symBlock (h := h) deposit_b500 deposit_b500_ok (by exact hc) rfl
    (deposit_b500_shape c st _ _ _ _ [cnt])
  rw [withGE_at] at hx1
  simp only [hcds] at hx1
  by_cases hcd : Deposit.cdsizeWord c ≠ ⟨0⟩
  · obtain ⟨f2,cost2,_,_,hx2⟩ := success_jumpi_taken
      (decodeAt_of_code_pc (st := at_ c st _ _ g1 505 _ e1) (by exact hc) rfl deposit_s505) rfl hcd hx1
    rw [jumpi_taken_at, withGE_at] at hx2
    obtain ⟨f3,g3,e3,_,hx3⟩ := success_symBlock (h := hx2) deposit_b578 deposit_b578_ok (by exact hc) rfl
      (deposit_b578_shape c st _ _ _ _ [cnt])
    rw [withGE_at] at hx3
    obtain ⟨hs,ho⟩ := deposit_store_return c INH cnt henv hx3
    exact ⟨st,Touched.refl _,by simpa only [Deposit.newExcess, if_pos hcd] using hs,ho⟩
  · have hzero : Deposit.cdsizeWord c = ⟨0⟩ := by simpa using hcd
    obtain ⟨f2,cost2,_,_,hx2⟩ := success_jumpi_untaken
      (decodeAt_of_code_pc (st := at_ c st _ _ g1 505 _ e1) (by exact hc) rfl deposit_s505) rfl hzero hx1
    rw [jumpi_fallthrough_at, withGE_at] at hx2
    obtain ⟨f3,g3,e3,_,hx3⟩ := success_symBlock (h := hx2) deposit_b506 deposit_b506_ok (by exact hc) rfl
      (deposit_b506_shape c st _ _ _ _ [cnt])
    rw [withGE_at] at hx3
    simp only [slotW_touch] at hx3
    let stX := touch (touch st (UInt256.ofNat 0)) (UInt256.ofNat 1)
    have ht : Touched st stX := ((Touched.refl st).touch _).touch _
    have hcX := Deposit.hcode_of_env c (ht.executionEnv.trans henv)
    by_cases hinh : slotW st (UInt256.ofNat 0) = INH
    · obtain ⟨f4,cost4,_,_,hx4⟩ := success_jumpi_taken
        (decodeAt_of_code_pc (st := at_ c stX _ _ g3 549 _ e3) (by exact hcX) rfl deposit_s549)
        rfl ((eq_ne_zero_iff _ _).mpr hinh.symm) hx3
      rw [jumpi_taken_at, withGE_at] at hx4
      obtain ⟨f5,g5,e5,_,hx5⟩ := success_symBlock (h := hx4) deposit_b560 deposit_b560_ok (by exact hcX) rfl
        (deposit_b560_shape c stX _ _ _ _ _ _ [cnt])
      rw [withGE_at] at hx5
      obtain ⟨hs,ho⟩ := deposit_store_return c (UInt256.ofNat 0) cnt (ht.executionEnv.trans henv) hx5
      exact ⟨stX,ht,by simpa only [Deposit.newExcess, if_neg hcd, stX, slotW_touch, if_pos hinh] using hs,ho⟩
    · obtain ⟨f4,cost4,_,_,hx4⟩ := success_jumpi_untaken
        (decodeAt_of_code_pc (st := at_ c stX _ _ g3 549 _ e3) (by exact hcX) rfl deposit_s549)
        rfl ((eq_eq_zero_iff _ _).mpr (fun he => hinh he.symm)) hx3
      rw [jumpi_fallthrough_at, withGE_at] at hx4
      obtain ⟨f5,g5,e5,_,hx5⟩ := success_symBlock (h := hx4) deposit_b550 deposit_b550_ok (by exact hcX) rfl
        (deposit_b550_shape c stX _ _ _ _ _ _ [cnt])
      rw [withGE_at] at hx5
      by_cases hgt : UInt256.ofNat 8 < slotW st (UInt256.ofNat 1)+slotW st (UInt256.ofNat 0)
      · obtain ⟨f6,cost6,_,_,hx6⟩ := success_jumpi_taken
          (decodeAt_of_code_pc (st := at_ c stX _ _ g5 559 _ e5) (by exact hcX) rfl deposit_s559)
          rfl ((gt_ne_zero_iff _ _).mpr hgt) hx5
        rw [jumpi_taken_at, withGE_at] at hx6
        obtain ⟨f7,g7,e7,_,hx7⟩ := success_symBlock (h := hx6) deposit_b568 deposit_b568_ok (by exact hcX) rfl
          (deposit_b568_shape c stX _ _ _ _ _ _ [cnt])
        rw [withGE_at] at hx7
        obtain ⟨hs,ho⟩ := deposit_store_return c _ cnt (ht.executionEnv.trans henv) hx7
        exact ⟨stX,ht,by simpa only [Deposit.newExcess, if_neg hcd, stX, slotW_touch, if_neg hinh, if_pos hgt] using hs,ho⟩
      · obtain ⟨f6,cost6,_,_,hx6⟩ := success_jumpi_untaken
          (decodeAt_of_code_pc (st := at_ c stX _ _ g5 559 _ e5) (by exact hcX) rfl deposit_s559)
          rfl ((gt_eq_zero_iff _ _).mpr hgt) hx5
        rw [jumpi_fallthrough_at, withGE_at] at hx6
        obtain ⟨f7,g7,e7,_,hx7⟩ := success_symBlock (h := hx6) deposit_b560 deposit_b560_ok (by exact hcX) rfl
          (deposit_b560_shape c stX _ _ _ _ _ _ [cnt])
        rw [withGE_at] at hx7
        obtain ⟨hs,ho⟩ := deposit_store_return c (UInt256.ofNat 0) cnt (ht.executionEnv.trans henv) hx7
        exact ⟨stX,ht,by simpa only [Deposit.newExcess, if_neg hcd, stX, slotW_touch, if_neg hinh, if_neg hgt] using hs,ho⟩

theorem deposit_final (c : XiCall .deposit) {fuel : Nat} {final : EVM.State} {out : ByteArray}
    (hsys : Deposit.callerWord c = sysW)
    (h : X fuel depositJumpdests c.entry = .ok (.success final out)) :
    ∃ st' stX, Touched (entrySt c) st' ∧
      Touched (Deposit.headStore c (Deposit.drainWord c) st') stX ∧
      final.toState = SystemSpec.controlStore stX (Deposit.newExcess c stX) ∧
      out = (Deposit.drainMem (entrySt c) (Deposit.headWord₀ c) (Deposit.mem₀ c)
        (Deposit.drainWord c).toNat).readWithPadding 0 (UInt256.ofNat 184*Deposit.drainWord c).toNat := by
  obtain ⟨f1,g1,e1,hx1⟩ := deposit_prefix c hsys h
  obtain ⟨st',f2,aw2,g2,e2,ht,hx2⟩ := deposit_loop c (entrySt c) rfl
    (Deposit.headWord₀ c) (Deposit.tailWord₀ c) (Deposit.drainWord c) (Deposit.mem₀ c)
    (Deposit.drainWord_le c) (Deposit.drainWord c).toNat 0 (Deposit.stP c) (Deposit.aw₀ c) g1 e1 f1 final out
    (by omega) (Deposit.touched_stP c) hx1
  obtain ⟨f3,g3,e3,hx3⟩ := deposit_head c _ ht.executionEnv hx2
  have henvH : (Deposit.headStore c (Deposit.drainWord c) st').executionEnv = c.env := by
    unfold Deposit.headStore
    split <;> simp only [executionEnv_sstore] <;> exact ht.executionEnv
  obtain ⟨stX,hxt,hs,ho⟩ := deposit_excess c _ henvH hx3
  exact ⟨st',stX,ht,hxt,hs,ho⟩

theorem deposit_system_result (c : XiCall .deposit)
    {published : Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate}
    {out : ByteArray} (hsys : c.env.source = Eip8282.Audit.EvmRunner.sysAddr)
    (h : c.result = .ok (.success published out)) :
    ∃ st' stX gas, Touched (entrySt c) st' ∧
      Touched (Deposit.headStore c (Deposit.drainWord c) st') stX ∧
      published = ((SystemSpec.controlStore stX (Deposit.newExcess c stX)).createdAccounts,
        (SystemSpec.controlStore stX (Deposit.newExcess c stX)).accountMap, gas,
        (SystemSpec.controlStore stX (Deposit.newExcess c stX)).substate) ∧
      out = (Deposit.drainMem (entrySt c) (Deposit.headWord₀ c) (Deposit.mem₀ c)
        (Deposit.drainWord c).toNat).readWithPadding 0 (UInt256.ofNat 184*Deposit.drainWord c).toNat := by
  obtain ⟨final,hpub,hx⟩ := xi_success_X c h
  have hw : Deposit.callerWord c = sysW := (callerW_eq_sysW_iff c).mpr hsys
  obtain ⟨st',stX,ht,hxt,hs,ho⟩ := deposit_final c hw hx
  refine ⟨st',stX,final.gasAvailable,ht,hxt,?_,ho⟩
  rw [← hpub]
  rw [hs]

theorem deposit_system_storage (c : XiCall .deposit)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hsys : c.env.source = Eip8282.Audit.EvmRunner.sysAddr)
    (h : c.result = .ok (.success (created,world,gas,substate) out))
    (howner : SystemSpec.HasOwner (entrySt c)) :
    (∀ k, SystemSpec.worldSlot world c.env.codeOwner k = SystemSpec.expectedSlot (entrySt c)
      (UInt256.ofNat 8) (Deposit.drainWord c) (Deposit.cdsizeWord c) k) ∧
    out = (Deposit.drainMem (entrySt c) (Deposit.headWord₀ c) (Deposit.mem₀ c)
      (Deposit.drainWord c).toNat).readWithPadding 0 (UInt256.ofNat 184*Deposit.drainWord c).toNat := by
  obtain ⟨st',stX,g,ht,hxt,hpub,hout⟩ := deposit_system_result c hsys h
  have hw : world = (SystemSpec.controlStore stX (Deposit.newExcess c stX)).accountMap :=
    congrArg (fun p => p.2.1) hpub
  have henv := SystemSpec.system_environment ht (Deposit.drainWord c) hxt (Deposit.newExcess c stX)
  refine ⟨?_,hout⟩
  intro k
  rw [hw, ← congrArg ExecutionEnv.codeOwner henv, SystemSpec.worldSlot_state]
  rw [← ControlSpec.deposit_systemExcess c stX]
  exact SystemSpec.system_storage howner ht (UInt256.ofNat 8) (Deposit.drainWord c)
    (Deposit.cdsizeWord c) hxt k



#print axioms exit_prefix
#print axioms exit_body
#print axioms exit_loop
#print axioms exit_head
#print axioms exit_store_return
#print axioms exit_excess
#print axioms exit_final
#print axioms exit_system_result
#print axioms exit_system_storage


#print axioms mstore8_success
#print axioms deposit_prefix
#print axioms deposit_body
#print axioms deposit_loop
#print axioms deposit_head
#print axioms deposit_store_return
#print axioms deposit_excess
#print axioms deposit_final
#print axioms deposit_system_result
#print axioms deposit_system_storage

end Eip8282.Audit.Integrator.SystemInversion
