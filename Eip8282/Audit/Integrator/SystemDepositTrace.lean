import Eip8282.Audit.EntryReach.Deposit
import Eip8282.Audit.Integrator.SystemPathBudget

/-! Annotated companions of the actual Deposit SYSTEM construction. The same
symbolic blocks and literal one-step proofs produce endpoints and gas witnesses,
with exact operation lists retained and at most four SSTORE occurrences.
Reference execution/resource refinement is not asserted; terminal Halt is separate. -/
namespace Eip8282.Audit.Integrator.SystemDepositTrace
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall jumpdestsOf)
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.EntryReach Eip8282.Audit.EntryReach.Deposit
open SystemPathBudget (Reach Allowed storeWeight)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private abbrev le_of_exact {α : Sort _} (x : α) : α := x

private theorem budget_mono {vj : Array UInt256} {K L stores more : Nat} {s t : EVM.State}
    (h : Reach vj K stores s t) (hk : K ≤ L) (hs : stores ≤ more := by omega) :
    Reach vj L more s t := h.mono hk hs

private abbrev chain := @SystemPathBudget.chain
private abbrev chainLe := @SystemPathBudget.chain

private theorem reach_jumpi_taken {kind : Kind} {vj : Array UInt256} {code : ByteArray}
    {c : XiCall kind} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc d : Nat} {cond : UInt256} {r : Stack UInt256} {e : Nat}
    (hsite : opcodeAt code pc = some (.JUMPI, none)) (hcode : st.executionEnv.code = code)
    (hc : cond ≠ ⟨0⟩) (hdest : vj.contains (UInt256.ofNat d) = true)
    (hgas : 10 ≤ g.toNat) (hlen : r.length ≤ 1024) :
    ∃ g' e', g.toNat - 10 ≤ g'.toNat ∧
      Reach vj 1 0 (at_ c st mem aw g pc (UInt256.ofNat d :: cond :: r) e)
        (at_ c st mem aw g' d r e') := by
  apply SystemPathBudget.singleton_result (op := .JUMPI) (Eip8282.Audit.EntryReach.reach_jumpi_taken hsite hcode hc hdest hgas hlen)
  · exact congrArg Prod.fst (decodeAt_of_code_pc (by simpa using hcode) rfl hsite)
  · decide +kernel

private theorem reach_jumpi_fallthrough {kind : Kind} {vj : Array UInt256} {code : ByteArray}
    {c : XiCall kind} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc : Nat} {d cond : UInt256} {r : Stack UInt256} {e : Nat}
    (hsite : opcodeAt code pc = some (.JUMPI, none)) (hcode : st.executionEnv.code = code)
    (hc : cond = ⟨0⟩) (hgas : 10 ≤ g.toNat) (hlen : r.length ≤ 1024) :
    ∃ g' e', g.toNat - 10 ≤ g'.toNat ∧
      Reach vj 1 0 (at_ c st mem aw g pc (d :: cond :: r) e) (at_ c st mem aw g' (pc + 1) r e') := by
  apply SystemPathBudget.singleton_result (op := .JUMPI) (Eip8282.Audit.EntryReach.reach_jumpi_fallthrough hsite hcode hc hgas hlen)
  · exact congrArg Prod.fst (decodeAt_of_code_pc (by simpa using hcode) rfl hsite)
  · decide +kernel

private theorem reach_sstore {kind : Kind} {vj : Array UInt256} {code : ByteArray}
    {c : XiCall kind} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc : Nat} {k v : UInt256} {r : Stack UInt256} {e : Nat}
    (hsite : opcodeAt code pc = some (.SSTORE, none)) (hcode : st.executionEnv.code = code)
    (hperm : st.executionEnv.perm = true)
    (hgas : 22100 ≤ g.toNat) (hlen : r.length ≤ 1024) :
    ∃ g' e', g.toNat - 22100 ≤ g'.toNat ∧
      Reach vj 1 1 (at_ c st mem aw g pc (k :: v :: r) e)
        (at_ c (st.sstore k v) mem aw g' (pc + 1) r e') := by
  apply SystemPathBudget.singleton_result (op := .SSTORE) (Eip8282.Audit.EntryReach.reach_sstore hsite hcode hperm hgas hlen)
  · exact congrArg Prod.fst (decodeAt_of_code_pc (by simpa using hcode) rfl hsite)
  · decide +kernel

private theorem reach_mstore {kind : Kind} {vj : Array UInt256} {code : ByteArray}
    {c : XiCall kind} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc : Nat} {off v : UInt256} {r : Stack UInt256} {e : Nat} {B : Nat}
    (hsite : opcodeAt code pc = some (.MSTORE, none)) (hcode : st.executionEnv.code = code)
    (haw : aw.toNat ≤ B) (hspan : (off.toNat + 32 + 31) / 32 ≤ B) (hB : B < UInt256.size)
    {M : Nat} (hM : memBound B + GasConstants.Gverylow = M)
    (hgas : M ≤ g.toNat) (hlen : r.length ≤ 1024) :
    ∃ g' e', g.toNat - M ≤ g'.toNat ∧
      Reach vj 1 0 (at_ c st mem aw g pc (off :: v :: r) e)
        (at_ c st (mstoreMem mem off v) (mAfter aw off.toNat 32) g' (pc + 1) r e') := by
  apply SystemPathBudget.singleton_result (op := .MSTORE) (Eip8282.Audit.EntryReach.reach_mstore hsite hcode haw hspan hB hM hgas hlen)
  · exact congrArg Prod.fst (decodeAt_of_code_pc (by simpa using hcode) rfl hsite)
  · decide +kernel

private theorem reach_mstore8 {kind : Kind} {vj : Array UInt256} {code : ByteArray}
    {c : XiCall kind} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc : Nat} {off v : UInt256} {r : Stack UInt256} {e : Nat} {B : Nat}
    (hsite : opcodeAt code pc = some (.MSTORE8, none)) (hcode : st.executionEnv.code = code)
    (haw : aw.toNat ≤ B) (hspan : (off.toNat + 1 + 31) / 32 ≤ B) (hB : B < UInt256.size)
    {M : Nat} (hM : memBound B + GasConstants.Gverylow = M)
    (hgas : M ≤ g.toNat) (hlen : r.length ≤ 1024) :
    ∃ g' e', g.toNat - M ≤ g'.toNat ∧
      Reach vj 1 0 (at_ c st mem aw g pc (off :: v :: r) e)
        (at_ c st (mstore8Mem mem off v) (mAfter aw off.toNat 1) g' (pc + 1) r e') := by
  apply SystemPathBudget.singleton_result (op := .MSTORE8) (Eip8282.Audit.EntryReach.reach_mstore8 hsite hcode haw hspan hB hM hgas hlen)
  · exact congrArg Prod.fst (decodeAt_of_code_pc (by simpa using hcode) rfl hsite)
  · decide +kernel

private theorem block_step {kind : Kind} {vj : Array UInt256} {vjNats : List Nat}
    (hvj : ∀ n ∈ vjNats, vj.contains (UInt256.ofNat n) = true)
    {code : ByteArray} (sites : List Site) (hsites : sitesOk code sites = true)
    {K n : Nat} (hK : blockBound sites = K) (hn : sites.length = n)
    {c : XiCall kind} {st st' : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc pc' : Nat} {stk stk' : Stack UInt256} {e : Nat}
    (hshape : symBlock vjNats (sites.map Prod.snd) (at_ c st mem aw g pc stk e)
      = some (at_ c st' mem aw g pc' stk' e))
    (hcode : st.executionEnv.code = code) (hpc : pc = headPc sites)
    (hgas : K ≤ g.toNat) (hlen : stk.length + n ≤ 1024)
    (hallowed : (sites.map (fun site => site.2.1)).all (fun op => decide (Allowed op)) = true := by decide +kernel)
    (hstores : SystemTraceAnnotations.weight storeWeight (sites.map (fun site => site.2.1)) ≤ 0 := by decide +kernel) :
    ∃ g' e', g.toNat - K ≤ g'.toNat ∧
      Reach vj n 0 (at_ c st mem aw g pc stk e) (at_ c st' mem aw g' pc' stk' e') := by
  apply SystemPathBudget.block_step hvj sites hsites hK hn hshape hcode hpc hgas hlen
  · intro site hs
    exact of_decide_eq_true (List.all_eq_true.mp hallowed _ (List.mem_map.mpr ⟨site,hs,rfl⟩))
  · exact hstores

private abbrev chainAt := @SystemPathBudget.chainAt
private abbrev liftAt := @SystemPathBudget.liftAt

variable (c : XiCall .deposit)

theorem gate (hg : 11 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat), c.gas.toNat - 11 ≤ g.toNat ∧
      Reach depositJumpdests 4 0 c.entry
        (at_ c (entrySt c) c.entry.memory c.entry.activeWords g 26
          (UInt256.ofNat 284 :: UInt256.eq sysW (callerWord c) :: []) e) := by
  change ∃ (g : UInt256) (e : Nat), c.gas.toNat - 11 ≤ g.toNat ∧
    Reach depositJumpdests 4 0 (at_ c (entrySt c) c.entry.memory c.entry.activeWords c.gas 0 [] 0) _
  exact block_step hvj_deposit deposit_b0 deposit_b0_ok (n := 4) deposit_b0_bound rfl
    (deposit_b0_shape c (entrySt c) _ _ c.gas 0 []) (hcode_of_env c rfl) rfl hg (by simp)


theorem system_prefix (hsys : callerWord c = sysW) (hg : 4300 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat), c.gas.toNat - 4300 ≤ g.toNat ∧
      Reach depositJumpdests 25 0 c.entry
        (at_ c (stP c) (mem₀ c) (aw₀ c) g 307
          (UInt256.ofNat 0 :: drainWord c :: headWord₀ c :: tailWord₀ c :: []) e) := by
  have h1 := le_of_exact (gate c (by gas_omega))
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s26 (hcode_of_env c rfl) ((eq_ne_zero_iff _ _).mpr hsys.symm)
      (hvj_deposit 284 (by decide)) (by gas_omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b284 deposit_b284_ok (n := 12) deposit_b284_bound rfl
      (deposit_b284_shape c (entrySt c) _ _ g₁ e₁ []) (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
  clear h2
  simp only [slotW_touch] at h3
  by_cases hlt : queueLen c < UInt256.ofNat 64
  · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_taken deposit_s301 (hcode_of_env c rfl) ((gt_ne_zero_iff _ _).mpr hlt)
        (hvj_deposit 305 (by decide)) (by gas_omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b305 deposit_b305_ok (n := 2) deposit_b305_bound rfl
        (deposit_b305_shape c (stP c) _ _ g₁ e₁ [queueLen c, headWord₀ c, tailWord₀ c])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h4
    simp only [drainWord, if_pos hlt]
    obtain ⟨g, e, hg', hr⟩ := h5
    exact ⟨g, e, by gas_omega, budget_mono hr (by gas_omega)⟩
  · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_fallthrough deposit_s301 (hcode_of_env c rfl) ((gt_eq_zero_iff _ _).mpr hlt)
        (by gas_omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b302 deposit_b302_ok (n := 2) deposit_b302_bound rfl
        (deposit_b302_shape c (stP c) _ _ g₁ e₁ (queueLen c) [headWord₀ c, tailWord₀ c])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h4
    have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b305 deposit_b305_ok (n := 2) deposit_b305_bound rfl
        (deposit_b305_shape c (stP c) _ _ g₁ e₁ [UInt256.ofNat 64, headWord₀ c, tailWord₀ c])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h5
    simp only [drainWord, if_neg hlt]
    obtain ⟨g, e, hg', hr⟩ := h6
    exact ⟨g, e, by gas_omega, budget_mono hr (by gas_omega)⟩


theorem drain_body {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (iW cnt head tail : UInt256) (henv : st.executionEnv = c.env) (hi : iW.toNat ≤ 63)
    (hne : iW ≠ cnt) (haw : aw.toNat ≤ 400) (hg : 36000 ≤ g.toNat) :
    ∃ (aw' g' : UInt256) (e' : Nat), aw'.toNat ≤ 400 ∧ g.toNat - 36000 ≤ g'.toNat ∧
      Reach depositJumpdests 130 0
        (at_ c st mem aw g 307 (iW :: cnt :: head :: tail :: []) e)
        (at_ c (touchItem st (base iW head))
          (writeItem st mem (UInt256.ofNat 184 * iW) (base iW head)) aw' g' 307
          ((UInt256.ofNat 1 + iW) :: cnt :: head :: tail :: []) e') := by
  obtain ⟨h0, h32, h64, h80, h96, h128, h160, h87, h86, h85, h84, h83, h82, h81⟩ := item_offsets hi
  have hcode : st.executionEnv.code = depositRuntime := hcode_of_env c henv
  have hcodeT : ∀ b, (touchItem st b).executionEnv.code = depositRuntime := fun _ => hcode
  -- 307..313 and the untaken exit test
  have h1 : ∃ (aw' g' : UInt256) (e' : Nat), aw'.toNat ≤ 400 ∧ g.toNat - 13 ≤ g'.toNat ∧
      Reach depositJumpdests 5 0 (at_ c st mem aw g 307 (iW :: cnt :: head :: tail :: []) e)
        (at_ c st mem aw' g' 314
          (UInt256.ofNat 471 :: UInt256.eq iW cnt :: iW :: cnt :: head :: tail :: []) e') :=
    liftAt (block_step hvj_deposit deposit_b307 deposit_b307_ok (n := 5)
      deposit_b307_bound rfl (deposit_b307_shape c st mem aw g e iW cnt [head, tail]) hcode rfl
      (by gas_omega) (by simp)) haw
  have h2 := chainAt h1 fun aw g₁ e₁ haw hg₁ => liftAt
    (reach_jumpi_fallthrough deposit_s314 hcode ((eq_eq_zero_iff _ _).mpr hne) (by gas_omega) (by simp))
    haw
  clear h1
  -- 315..330: base slot, first word
  have h3 := chainAt h2 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b315 deposit_b315_ok (n := 13) deposit_b315_bound rfl
      (deposit_b315_shape c st mem aw g₁ e₁ iW cnt head [tail]) hcode rfl (by gas_omega) (by simp))
    haw
  clear h2
  have h4 := chainAt h3 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore deposit_s331 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h0]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h0]; omega) (by decide)
  clear h3
  -- 332..340: second word
  have h5 := chainAt h4 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b332 deposit_b332_ok (n := 7) deposit_b332_bound rfl
      (deposit_b332_shape c _ _ aw g₁ e₁ _ _ [iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h4
  simp only [slotW_touch] at h5
  have h6 := chainAt h5 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore deposit_s341 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h32]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h32]; omega) (by decide)
  clear h5
  -- 342..351: third word, kept for the amount
  have h7 := chainAt h6 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b342 deposit_b342_ok (n := 8) deposit_b342_bound rfl
      (deposit_b342_shape c _ _ aw g₁ e₁ _ _ [iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h6
  simp only [slotW_touch] at h7
  have h8 := chainAt h7 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore deposit_s352 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h64]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h64]; omega) (by decide)
  clear h7
  -- 353..377 and the eight little-endian amount bytes
  have h9 := chainAt h8 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b353 deposit_b353_ok (n := 13) deposit_b353_bound rfl
      (deposit_b353_shape c _ _ aw g₁ e₁ _ _ [_, iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega)
      (by simp))
    haw
  clear h8
  have h10 := chainAt h9 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore8 deposit_s378 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h87]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h87]; omega) (by decide)
  clear h9
  have h11 := chainAt h10 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b379 deposit_b379_ok (n := 6) deposit_b379_bound rfl
      (deposit_b379_shape c _ _ aw g₁ e₁ _ _ [_, _, iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega)
      (by simp))
    haw
  clear h10
  have h12 := chainAt h11 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore8 deposit_s387 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h86]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h86]; omega) (by decide)
  clear h11
  have h13 := chainAt h12 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b388 deposit_b388_ok (n := 6) deposit_b388_bound rfl
      (deposit_b388_shape c _ _ aw g₁ e₁ _ _ [_, _, iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega)
      (by simp))
    haw
  clear h12
  have h14 := chainAt h13 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore8 deposit_s396 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h85]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h85]; omega) (by decide)
  clear h13
  have h15 := chainAt h14 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b397 deposit_b397_ok (n := 6) deposit_b397_bound rfl
      (deposit_b397_shape c _ _ aw g₁ e₁ _ _ [_, _, iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega)
      (by simp))
    haw
  clear h14
  have h16 := chainAt h15 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore8 deposit_s405 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h84]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h84]; omega) (by decide)
  clear h15
  have h17 := chainAt h16 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b406 deposit_b406_ok (n := 6) deposit_b406_bound rfl
      (deposit_b406_shape c _ _ aw g₁ e₁ _ _ [_, _, iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega)
      (by simp))
    haw
  clear h16
  have h18 := chainAt h17 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore8 deposit_s414 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h83]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h83]; omega) (by decide)
  clear h17
  have h19 := chainAt h18 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b415 deposit_b415_ok (n := 6) deposit_b415_bound rfl
      (deposit_b415_shape c _ _ aw g₁ e₁ _ _ [_, _, iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega)
      (by simp))
    haw
  clear h18
  have h20 := chainAt h19 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore8 deposit_s423 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h82]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h82]; omega) (by decide)
  clear h19
  have h21 := chainAt h20 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b424 deposit_b424_ok (n := 6) deposit_b424_bound rfl
      (deposit_b424_shape c _ _ aw g₁ e₁ _ _ [_, _, iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega)
      (by simp))
    haw
  clear h20
  have h22 := chainAt h21 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore8 deposit_s432 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h81]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h81]; omega) (by decide)
  clear h21
  have h23 := chainAt h22 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore8 deposit_s433 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h80]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h80]; omega) (by decide)
  clear h22
  -- 434..462: the last three words
  have h24 := chainAt h23 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b434 deposit_b434_ok (n := 7) deposit_b434_bound rfl
      (deposit_b434_shape c _ _ aw g₁ e₁ _ _ [iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h23
  simp only [slotW_touch] at h24
  have h25 := chainAt h24 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore deposit_s443 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h96]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h96]; omega) (by decide)
  clear h24
  have h26 := chainAt h25 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b444 deposit_b444_ok (n := 7) deposit_b444_bound rfl
      (deposit_b444_shape c _ _ aw g₁ e₁ _ _ [iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h25
  simp only [slotW_touch] at h26
  have h27 := chainAt h26 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore deposit_s453 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h128]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h128]; omega) (by decide)
  clear h26
  have h28 := chainAt h27 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b454 deposit_b454_ok (n := 7) deposit_b454_bound rfl
      (deposit_b454_shape c _ _ aw g₁ e₁ _ _ [iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h27
  simp only [slotW_touch] at h28
  have h29 := chainAt h28 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore deposit_s463 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h160]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h160]; omega) (by decide)
  clear h28
  -- 464..470: bump the counter and jump back
  have h30 := chainAt h29 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b464 deposit_b464_ok (n := 4) deposit_b464_bound rfl
      (deposit_b464_shape c _ _ aw g₁ e₁ iW [cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h29
  obtain ⟨aw', g', e', haw', hg', hr⟩ := h30
  exact ⟨aw', g', e', haw', by gas_omega, budget_mono hr (by gas_omega)⟩



theorem drain_loop (st₀ : EvmYul.State .EVM) (henv₀ : st₀.executionEnv = c.env)
    (head tail cnt : UInt256) (mem₀ : ByteArray) (hcnt : cnt.toNat ≤ 64) :
    ∀ (m i : Nat) (st : EvmYul.State .EVM) (aw g : UInt256) (e : Nat), i + m = cnt.toNat →
      Touched st₀ st → aw.toNat ≤ 400 → 36000 * m + 25 ≤ g.toNat →
      ∃ (st' : EvmYul.State .EVM) (aw' g' : UInt256) (e' : Nat), Touched st₀ st' ∧
        aw'.toNat ≤ 400 ∧ g.toNat - (36000 * m + 25) ≤ g'.toNat ∧
        Reach depositJumpdests (130 * m + 6) 0
          (at_ c st (drainMem st₀ head mem₀ i) aw g 307
            (UInt256.ofNat i :: cnt :: head :: tail :: []) e)
          (at_ c st' (drainMem st₀ head mem₀ cnt.toNat) aw' g' 471
            (cnt :: cnt :: head :: tail :: []) e') := by
  intro m
  induction m with
  | zero =>
    intro i st aw g e hi hst haw hg
    have hi' : i = cnt.toNat := by gas_omega
    subst hi'
    have henv : st.executionEnv = c.env := hst.executionEnv.trans henv₀
    have hcode := hcode_of_env c henv
    have hcnt' : UInt256.ofNat cnt.toNat = cnt := ofNat_toNat' cnt
    have h1 := block_step hvj_deposit deposit_b307 deposit_b307_ok (n := 5) deposit_b307_bound rfl
      (deposit_b307_shape c st (drainMem st₀ head mem₀ cnt.toNat) aw g e (UInt256.ofNat cnt.toNat)
        cnt [head, tail]) hcode rfl (by gas_omega) (by simp)
    have h2 := chain h1 fun g₁ e₁ hg₁ =>
      reach_jumpi_taken deposit_s314 hcode ((eq_ne_zero_iff _ _).mpr hcnt')
        (hvj_deposit 471 (by decide)) (by gas_omega) (by simp)
    obtain ⟨g', e', hg', hr⟩ := h2
    rw [hcnt'] at hr ⊢
    exact ⟨st, aw, g', e', hst, haw, by gas_omega, budget_mono hr (by gas_omega)⟩
  | succ m ih =>
    intro i st aw g e hi hst haw hg
    have henv : st.executionEnv = c.env := hst.executionEnv.trans henv₀
    have hi63 : (UInt256.ofNat i).toNat ≤ 63 := by
      rw [toNat_ofNat_of_lt (by rw [size_eq]; omega)]; omega
    have hne : UInt256.ofNat i ≠ cnt := by
      intro h
      have := congrArg UInt256.toNat h
      rw [toNat_ofNat_of_lt (by rw [size_eq]; omega)] at this
      omega
    obtain ⟨aw₁, g₁, e₁, haw₁, hg₁, hr₁⟩ :=
      drain_body c (mem := drainMem st₀ head mem₀ i) (g := g) (e := e) (UInt256.ofNat i) cnt head
        tail henv hi63 hne haw (by gas_omega)
    rw [writeItem_of_touched hst, ofNat_add_ofNat, Nat.add_comm 1 i] at hr₁
    obtain ⟨st', aw', g', e', hst', haw', hg', hr'⟩ :=
      ih (i + 1) (touchItem st (base (UInt256.ofNat i) head)) aw₁ g₁ e₁ (by gas_omega)
        (touched_touchItem hst _) haw₁ (by gas_omega)
    refine ⟨st', aw', g', e', hst', haw', by gas_omega, ?_⟩
    exact budget_mono (hr₁.trans hr') (by gas_omega)


theorem update_head {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (henv : st.executionEnv = c.env) (hperm : c.env.perm = true) (cnt : UInt256)
    (hg : 44500 ≤ g.toNat) :
    ∃ (g' : UInt256) (e' : Nat), g.toNat - 44500 ≤ g'.toNat ∧
      Reach depositJumpdests 20 2
        (at_ c st mem aw g 471 (cnt :: cnt :: headWord₀ c :: tailWord₀ c :: []) e)
        (at_ c (headStore c cnt st) mem aw g' 500 (cnt :: []) e') := by
  have hcode := hcode_of_env c henv
  have h1 := le_of_exact <| block_step hvj_deposit deposit_b471 deposit_b471_ok (n := 7)
    deposit_b471_bound rfl (deposit_b471_shape c st mem aw g e cnt cnt (headWord₀ c) (tailWord₀ c) [])
    hcode rfl (by gas_omega) (by simp)
  by_cases hfull : tailWord₀ c = headWord₀ c + cnt
  · have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_taken deposit_s480 hcode ((eq_ne_zero_iff _ _).mpr hfull)
        (hvj_deposit 489 (by decide)) (by gas_omega) (by simp)
    clear h1
    have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b489 deposit_b489_ok (n := 5) deposit_b489_bound rfl
        (deposit_b489_shape c st mem aw g₁ e₁ cnt (headWord₀ c + cnt) []) hcode rfl (by gas_omega) (by simp)
    clear h2
    have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_sstore deposit_s495 hcode (perm_of_env c henv hperm) (by gas_omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b496 deposit_b496_ok (n := 2) deposit_b496_bound rfl
        (deposit_b496_shape c _ mem aw g₁ e₁ [cnt]) (hcode_of_env c (by env_simp; exact henv)) rfl
        (by gas_omega) (by simp)
    clear h4
    have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_sstore deposit_s499 (hcode_of_env c (by env_simp; exact henv))
        (perm_of_env c (by env_simp; exact henv) hperm) (by gas_omega) (by simp)
    clear h5
    obtain ⟨g', e', hg', hr⟩ := h6
    simp only [headStore, if_pos hfull]
    exact ⟨g', e', by gas_omega, budget_mono hr (by gas_omega)⟩
  · have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_fallthrough deposit_s480 hcode ((eq_eq_zero_iff _ _).mpr hfull) (by gas_omega) (by simp)
    clear h1
    have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b481 deposit_b481_ok (n := 2) deposit_b481_bound rfl
        (deposit_b481_shape c st mem aw g₁ e₁ cnt (headWord₀ c + cnt) []) hcode rfl (by gas_omega) (by simp)
    clear h2
    have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_sstore deposit_s484 hcode (perm_of_env c henv hperm) (by gas_omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b485 deposit_b485_ok (n := 2) deposit_b485_bound rfl
        (deposit_b485_shape c _ mem aw g₁ e₁ [cnt]) (hcode_of_env c (by env_simp; exact henv)) rfl
        (by gas_omega) (by simp)
    clear h4
    obtain ⟨g', e', hg', hr⟩ := h5
    simp only [headStore, if_neg hfull]
    exact ⟨g', e', by gas_omega, budget_mono hr (by gas_omega)⟩


theorem update_excess {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (henv : st.executionEnv = c.env) (hperm : c.env.perm = true) (cnt : UInt256)
    (hg : 50000 ≤ g.toNat) :
    ∃ (stX : EvmYul.State .EVM) (g' : UInt256) (e' : Nat), Touched st stX ∧
      g.toNat - 50000 ≤ g'.toNat ∧
      Reach depositJumpdests 36 2 (at_ c st mem aw g 500 (cnt :: []) e)
        (at_ c ((stX.sstore (UInt256.ofNat 0) (newExcess c stX)).sstore (UInt256.ofNat 1)
          (UInt256.ofNat 0)) mem aw g' 623 (UInt256.ofNat 0 :: (UInt256.ofNat 184 * cnt) :: []) e') := by
  have hcode := hcode_of_env c henv
  have hcds : cdsizeW st = cdsizeWord c := by unfold cdsizeW; rw [henv]; rfl
  have h1 := le_of_exact <| block_step hvj_deposit deposit_b500 deposit_b500_ok (n := 3)
    deposit_b500_bound rfl (deposit_b500_shape c st mem aw g e [cnt]) hcode rfl (by gas_omega) (by simp)
  simp only [hcds] at h1
  -- the tail from `store_excess` (612), shared by every branch
  have tail : ∀ (stX : EvmYul.State .EVM) (v g₁ : UInt256) (e₁ : Nat), Touched st stX →
      g₁.toNat ≥ g.toNat - 5000 →
      ∃ (g' : UInt256) (e' : Nat), g₁.toNat - 44300 ≤ g'.toNat ∧
        Reach depositJumpdests 9 2 (at_ c stX mem aw g₁ 612 (v :: cnt :: []) e₁)
          (at_ c ((stX.sstore (UInt256.ofNat 0) v).sstore (UInt256.ofNat 1) (UInt256.ofNat 0)) mem aw
            g' 623 (UInt256.ofNat 0 :: (UInt256.ofNat 184 * cnt) :: []) e') := by
    intro stX v g₁ e₁ hstX hg₁
    have henvX : stX.executionEnv = c.env := hstX.executionEnv.trans henv
    have hcodeX := hcode_of_env c henvX
    have t1 := le_of_exact <| block_step hvj_deposit deposit_b612 deposit_b612_ok (n := 2)
      deposit_b612_bound rfl (deposit_b612_shape c stX mem aw g₁ e₁ [v, cnt]) hcodeX rfl (by gas_omega)
      (by simp)
    have t2 := chainLe t1 fun g₂ e₂ hg₂ => le_of_exact <|
      reach_sstore deposit_s614 hcodeX (perm_of_env c henvX hperm) (by gas_omega) (by simp)
    clear t1
    have t3 := chainLe t2 fun g₂ e₂ hg₂ => le_of_exact <|
      block_step hvj_deposit deposit_b615 deposit_b615_ok (n := 2) deposit_b615_bound rfl
        (deposit_b615_shape c _ mem aw g₂ e₂ [cnt]) (hcode_of_env c (by env_simp; exact henvX)) rfl
        (by gas_omega) (by simp)
    clear t2
    have t4 := chainLe t3 fun g₂ e₂ hg₂ => le_of_exact <|
      reach_sstore deposit_s618 (hcode_of_env c (by env_simp; exact henvX))
        (perm_of_env c (by env_simp; exact henvX) hperm) (by gas_omega) (by simp)
    clear t3
    have t5 := chainLe t4 fun g₂ e₂ hg₂ => le_of_exact <|
      block_step hvj_deposit deposit_b619 deposit_b619_ok (n := 3) deposit_b619_bound rfl
        (deposit_b619_shape c _ mem aw g₂ e₂ cnt []) (hcode_of_env c (by env_simp; exact henvX)) rfl
        (by gas_omega) (by simp)
    clear t4
    obtain ⟨g', e', hg', hr⟩ := t5
    exact ⟨g', e', by gas_omega, budget_mono hr (by gas_omega)⟩
  by_cases hcd : cdsizeWord c ≠ ⟨0⟩
  · -- nonempty calldata: latch the inhibitor
    have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_taken deposit_s505 hcode hcd (hvj_deposit 578 (by decide)) (by gas_omega) (by simp)
    clear h1
    have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b578 deposit_b578_ok (n := 2) deposit_b578_bound rfl
        (deposit_b578_shape c st mem aw g₁ e₁ [cnt]) hcode rfl (by gas_omega) (by simp)
    clear h2
    obtain ⟨g₁, e₁, hg₁, hr₁⟩ := h3
    obtain ⟨g', e', hg', hr'⟩ := tail st INH g₁ e₁ (Touched.refl st) (by gas_omega)
    refine ⟨st, g', e', Touched.refl st, by gas_omega, ?_⟩
    simp only [newExcess, if_pos hcd]
    exact budget_mono (hr₁.trans hr') (by gas_omega)
  · have hcd' : cdsizeWord c = ⟨0⟩ := by
      by_contra h; exact hcd h
    have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_fallthrough deposit_s505 hcode hcd' (by gas_omega) (by simp)
    clear h1
    have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b506 deposit_b506_ok (n := 8) deposit_b506_bound rfl
        (deposit_b506_shape c st mem aw g₁ e₁ [cnt]) hcode rfl (by gas_omega) (by simp)
    clear h2
    simp only [slotW_touch] at h3
    have hstX : Touched st (touch (touch st (UInt256.ofNat 0)) (UInt256.ofNat 1)) :=
      ((Touched.refl st).touch _).touch _
    have hcodeX : (touch (touch st (UInt256.ofNat 0)) (UInt256.ofNat 1)).executionEnv.code
        = depositRuntime := hcode
    by_cases hinh : slotW st (UInt256.ofNat 0) = INH
    · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
        reach_jumpi_taken deposit_s549 hcodeX ((eq_ne_zero_iff _ _).mpr hinh.symm)
          (hvj_deposit 560 (by decide)) (by gas_omega) (by simp)
      clear h3
      have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
        block_step hvj_deposit deposit_b560 deposit_b560_ok (n := 6) deposit_b560_bound rfl
          (deposit_b560_shape c _ mem aw g₁ e₁ _ _ [cnt]) hcodeX rfl (by gas_omega) (by simp)
      clear h4
      obtain ⟨g₁, e₁, hg₁, hr₁⟩ := h5
      obtain ⟨g', e', hg', hr'⟩ := tail _ (UInt256.ofNat 0) g₁ e₁ hstX (by gas_omega)
      refine ⟨_, g', e', hstX, by gas_omega, ?_⟩
      simp only [newExcess, if_neg hcd, slotW_touch, if_pos hinh]
      exact budget_mono (hr₁.trans hr') (by gas_omega)
    · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
        reach_jumpi_fallthrough deposit_s549 hcodeX ((eq_eq_zero_iff _ _).mpr (fun h => hinh h.symm))
          (by gas_omega) (by simp)
      clear h3
      have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
        block_step hvj_deposit deposit_b550 deposit_b550_ok (n := 6) deposit_b550_bound rfl
          (deposit_b550_shape c _ mem aw g₁ e₁ _ _ [cnt]) hcodeX rfl (by gas_omega) (by simp)
      clear h4
      by_cases hgt : UInt256.ofNat 8 < slotW st (UInt256.ofNat 1) + slotW st (UInt256.ofNat 0)
      · have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
          reach_jumpi_taken deposit_s559 hcodeX ((gt_ne_zero_iff _ _).mpr hgt)
            (hvj_deposit 568 (by decide)) (by gas_omega) (by simp)
        clear h5
        have h7 := chainLe h6 fun g₁ e₁ hg₁ => le_of_exact <|
          block_step hvj_deposit deposit_b568 deposit_b568_ok (n := 7) deposit_b568_bound rfl
            (deposit_b568_shape c _ mem aw g₁ e₁ _ _ [cnt]) hcodeX rfl (by gas_omega) (by simp)
        clear h6
        obtain ⟨g₁, e₁, hg₁, hr₁⟩ := h7
        obtain ⟨g', e', hg', hr'⟩ := tail _ _ g₁ e₁ hstX (by gas_omega)
        refine ⟨_, g', e', hstX, by gas_omega, ?_⟩
        simp only [newExcess, if_neg hcd, slotW_touch, if_neg hinh, if_pos hgt]
        exact budget_mono (hr₁.trans hr') (by gas_omega)
      · have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
          reach_jumpi_fallthrough deposit_s559 hcodeX ((gt_eq_zero_iff _ _).mpr hgt) (by gas_omega)
            (by simp)
        clear h5
        have h7 := chainLe h6 fun g₁ e₁ hg₁ => le_of_exact <|
          block_step hvj_deposit deposit_b560 deposit_b560_ok (n := 6) deposit_b560_bound rfl
            (deposit_b560_shape c _ mem aw g₁ e₁ _ _ [cnt]) hcodeX rfl (by gas_omega) (by simp)
        clear h6
        obtain ⟨g₁, e₁, hg₁, hr₁⟩ := h7
        obtain ⟨g', e', hg', hr'⟩ := tail _ (UInt256.ofNat 0) g₁ e₁ hstX (by gas_omega)
        refine ⟨_, g', e', hstX, by gas_omega, ?_⟩
        simp only [newExcess, if_neg hcd, slotW_touch, if_neg hinh, if_neg hgt]
        exact budget_mono (hr₁.trans hr') (by gas_omega)


theorem system_returns (hsys : callerWord c = sysW) (hperm : c.env.perm = true)
    (hg : 2500000 ≤ c.gas.toNat) :
    ∃ (st' stX : EvmYul.State .EVM) (aw g : UInt256) (e : Nat),
      Touched (entrySt c) st' ∧ Touched (headStore c (drainWord c) st') stX ∧
      aw.toNat ≤ 400 ∧ (Reach depositJumpdests 8500 4 c.entry
        (at_ c ((stX.sstore (UInt256.ofNat 0) (newExcess c stX)).sstore (UInt256.ofNat 1)
            (UInt256.ofNat 0))
          (drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) aw g 623
          (UInt256.ofNat 0 :: (UInt256.ofNat 184 * drainWord c) :: []) e) ∧ Halt depositJumpdests
        (at_ c ((stX.sstore (UInt256.ofNat 0) (newExcess c stX)).sstore (UInt256.ofNat 1)
            (UInt256.ofNat 0))
          (drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) aw g 623
          (UInt256.ofNat 0 :: (UInt256.ofNat 184 * drainWord c) :: []) e) .RETURN
        ((drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat).readWithPadding 0
          (UInt256.ofNat 184 * drainWord c).toNat)) := by
  obtain ⟨g₀, e₀, hg₀, hpre⟩ := system_prefix c hsys (by gas_omega)
  have hcnt := drainWord_le c
  obtain ⟨st', aw', g₁, e₁, hst', haw', hg₁, hloop⟩ := drain_loop c (entrySt c) rfl (headWord₀ c)
    (tailWord₀ c) (drainWord c) (mem₀ c) hcnt (drainWord c).toNat 0 (stP c) (aw₀ c) g₀ e₀
    (by gas_omega) (touched_stP c) (by rw [activeWords_entry]; omega) (by gas_omega)
  have h1 : ∃ (g : UInt256) (e : Nat), c.gas.toNat - 2308400 ≤ g.toNat ∧
      Reach depositJumpdests 8351 0 c.entry
        (at_ c st' (drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) aw' g 471
          (drainWord c :: drainWord c :: headWord₀ c :: tailWord₀ c :: []) e) :=
    ⟨g₁, e₁, by gas_omega, budget_mono (hpre.trans hloop) (by gas_omega)⟩
  have henv' : st'.executionEnv = c.env := hst'.executionEnv
  have h2 := chainLe h1 fun g e hg => update_head c henv' hperm (drainWord c) (by gas_omega)
  clear h1
  have henvH : (headStore c (drainWord c) st').executionEnv = c.env := by
    unfold headStore; split <;> (env_simp; exact henv')
  have h3 : ∃ (stX : EvmYul.State .EVM) (g : UInt256) (e : Nat),
      Touched (headStore c (drainWord c) st') stX ∧ c.gas.toNat - 2402900 ≤ g.toNat ∧
      Reach depositJumpdests (8351 + 20 + 36) 4 c.entry
        (at_ c ((stX.sstore (UInt256.ofNat 0) (newExcess c stX)).sstore (UInt256.ofNat 1)
            (UInt256.ofNat 0))
          (drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) aw' g 623
          (UInt256.ofNat 0 :: (UInt256.ofNat 184 * drainWord c) :: []) e) := by
    obtain ⟨g₂, e₂, hg₂, hr₂⟩ := h2
    obtain ⟨stX, g₃, e₃, hstX, hg₃, hr₃⟩ := update_excess c
      (mem := drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) (aw := aw')
      (g := g₂) (e := e₂) henvH hperm (drainWord c) (by gas_omega)
    exact ⟨stX, g₃, e₃, hstX, by gas_omega, hr₂.trans hr₃⟩
  clear h2
  obtain ⟨stX, g, e, hstX, hgX, hr⟩ := h3
  have henvX : stX.executionEnv = c.env := hstX.executionEnv.trans henvH
  refine ⟨st', stX, aw', g, e, hst', hstX, haw', budget_mono hr (by gas_omega), ?_⟩
  have hlen : (UInt256.ofNat 184 * drainWord c).toNat = 184 * (drainWord c).toNat :=
    toNat_ofNat_mul_of_lt 184 _ (by rw [size_eq]; omega)
  refine halt_RETURN deposit_s623 (hcode_of_env c (by env_simp; exact henvX)) (B := 400) (M := 1512)
    (g := g) haw' ?_ (by decide) (by decide) ?_ (by simp)
  · rw [hlen]; show (0 + 184 * (drainWord c).toNat + 31) / 32 ≤ 400; omega
  · omega


#print axioms gate
#print axioms system_prefix
#print axioms drain_body
#print axioms drain_loop
#print axioms update_head
#print axioms update_excess
#print axioms system_returns
end Eip8282.Audit.Integrator.SystemDepositTrace
