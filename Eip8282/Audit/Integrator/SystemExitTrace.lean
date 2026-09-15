import Eip8282.Audit.Execution.Exit
import Eip8282.Audit.Integrator.SystemPathBudget

/-! Annotated companions of the actual Exit SYSTEM construction. The same
symbolic blocks and literal one-step proofs produce endpoints and gas witnesses,
with exact operation lists retained and at most four SSTORE occurrences.
Reference execution/resource refinement is not asserted; terminal Halt is separate. -/
namespace Eip8282.Audit.Integrator.SystemExitTrace
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall jumpdestsOf)
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.EntryReach Eip8282.Audit.EntryReach.Exit
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

private theorem chainAt {kind : Kind} {c : XiCall kind} {vj : Array UInt256} {k k' K K' B stores more : Nat}
    {s : EVM.State} {st st' : EvmYul.State .EVM} {mem mem' : ByteArray} {pc pc' : Nat}
    {stk stk' : Stack UInt256} {g₀ : UInt256}
    (h₁ : ∃ (aw g : UInt256) (e : Nat), aw.toNat ≤ B ∧ g₀.toNat - K ≤ g.toNat ∧
      Reach vj k stores s (at_ c st mem aw g pc stk e))
    (h₂ : ∀ (aw g : UInt256) (e : Nat), aw.toNat ≤ B → g₀.toNat - K ≤ g.toNat →
      ∃ (aw' g' : UInt256) (e' : Nat), aw'.toNat ≤ B ∧ g.toNat - K' ≤ g'.toNat ∧
        Reach vj k' more (at_ c st mem aw g pc stk e) (at_ c st' mem' aw' g' pc' stk' e')) :
    ∃ (aw' g' : UInt256) (e' : Nat), aw'.toNat ≤ B ∧ g₀.toNat - (K + K') ≤ g'.toNat ∧
      Reach vj (k + k') (stores+more) s (at_ c st' mem' aw' g' pc' stk' e') := by
  obtain ⟨aw, g, e, haw, hg, hr⟩ := h₁
  obtain ⟨aw', g', e', haw', hg', hr'⟩ := h₂ aw g e haw hg
  exact ⟨aw', g', e', haw', by omega, hr.trans hr'⟩

/-- Lift an exact step into the threaded form: `haw` bounds the active-word
count of the machine the step lands on. Stated on `at_` so that its implicit
arguments are fixed by the expected type before the step's side goals run. -/
private theorem liftAt {kind : Kind} {c : XiCall kind} {vj : Array UInt256} {k K B stores : Nat} {s : EVM.State}
    {st' : EvmYul.State .EVM} {mem' : ByteArray} {pc' : Nat} {stk' : Stack UInt256}
    {g₀ aw' : UInt256}
    (h : ∃ (g' : UInt256) (e' : Nat), g₀.toNat - K ≤ g'.toNat ∧
      Reach vj k stores s (at_ c st' mem' aw' g' pc' stk' e'))
    (haw : aw'.toNat ≤ B) :
    ∃ (aw'' g' : UInt256) (e' : Nat), aw''.toNat ≤ B ∧ g₀.toNat - K ≤ g'.toNat ∧
      Reach vj k stores s (at_ c st' mem' aw'' g' pc' stk' e') := by
  obtain ⟨g', e', hg, hr⟩ := h
  exact ⟨aw', g', e', haw, hg, hr⟩


variable (c : XiCall .exit)

theorem gate (hg : 11 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat), c.gas.toNat - 11 ≤ g.toNat ∧
      Reach exitJumpdests 4 0 c.entry
        (at_ c (entrySt c) c.entry.memory c.entry.activeWords g 25
          (UInt256.ofNat 225 :: UInt256.eq sysW (callerWord c) :: []) e) := by
  change ∃ (g : UInt256) (e : Nat), c.gas.toNat - 11 ≤ g.toNat ∧
    Reach exitJumpdests 4 0 (at_ c (entrySt c) c.entry.memory c.entry.activeWords c.gas 0 [] 0) _
  exact block_step hvj_exit exit_b0 exit_b0_ok (n := 4) exit_b0_bound rfl
    (exit_b0_shape c (entrySt c) _ _ c.gas 0 []) (hcode_of_env c rfl) rfl hg (by simp)

theorem system_prefix (hsys : callerWord c = sysW) (hg : 4300 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat), c.gas.toNat - 4300 ≤ g.toNat ∧
      Reach exitJumpdests 25 0 c.entry
        (at_ c (stP c) (mem₀ c) (aw₀ c) g 247
          (UInt256.ofNat 0 :: drainWord c :: headWord₀ c :: tailWord₀ c :: []) e) := by
  have h1 := le_of_exact (gate c (by gas_omega))
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken exit_s25 (hcode_of_env c rfl) ((eq_ne_zero_iff _ _).mpr hsys.symm)
      (hvj_exit 225 (by decide)) (by gas_omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b225 exit_b225_ok (n := 12) exit_b225_bound rfl
      (exit_b225_shape c (entrySt c) _ _ g₁ e₁ []) (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
  clear h2
  simp only [slotW_touch] at h3
  by_cases hlt : queueLen c < UInt256.ofNat 16
  · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_taken exit_s241 (hcode_of_env c rfl) ((gt_ne_zero_iff _ _).mpr hlt)
        (hvj_exit 245 (by decide)) (by gas_omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b245 exit_b245_ok (n := 2) exit_b245_bound rfl
        (exit_b245_shape c (stP c) _ _ g₁ e₁ [queueLen c, headWord₀ c, tailWord₀ c])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h4
    simp only [drainWord, if_pos hlt]
    obtain ⟨g, e, hg', hr⟩ := h5
    exact ⟨g, e, by gas_omega, budget_mono hr (by gas_omega)⟩
  · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_fallthrough exit_s241 (hcode_of_env c rfl) ((gt_eq_zero_iff _ _).mpr hlt)
        (by gas_omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b242 exit_b242_ok (n := 2) exit_b242_bound rfl
        (exit_b242_shape c (stP c) _ _ g₁ e₁ (queueLen c) [headWord₀ c, tailWord₀ c])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h4
    have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b245 exit_b245_ok (n := 2) exit_b245_bound rfl
        (exit_b245_shape c (stP c) _ _ g₁ e₁ [UInt256.ofNat 16, headWord₀ c, tailWord₀ c])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h5
    simp only [drainWord, if_neg hlt]
    obtain ⟨g, e, hg', hr⟩ := h6
    exact ⟨g, e, by gas_omega, budget_mono hr (by gas_omega)⟩

theorem drain_body {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (iW cnt head tail : UInt256) (henv : st.executionEnv = c.env) (hi : iW.toNat ≤ 15)
    (hne : iW ≠ cnt) (haw : aw.toNat ≤ 40) (hg : 7000 ≤ g.toNat) :
    ∃ (aw' g' : UInt256) (e' : Nat), aw'.toNat ≤ 40 ∧ g.toNat - 7000 ≤ g'.toNat ∧
      Reach exitJumpdests 42 0
        (at_ c st mem aw g 247 (iW :: cnt :: head :: tail :: []) e)
        (at_ c (touchItem st (base iW head))
          (writeItem st mem (UInt256.ofNat 68 * iW) (base iW head)) aw' g' 247
          ((UInt256.ofNat 1 + iW) :: cnt :: head :: tail :: []) e') := by
  obtain ⟨h0, h20, h52⟩ := item_offsets hi
  have hcode : st.executionEnv.code = exitRuntime := hcode_of_env c henv
  -- 247..253 and the untaken exit test
  have h1 : ∃ (aw' g' : UInt256) (e' : Nat), aw'.toNat ≤ 40 ∧ g.toNat - 13 ≤ g'.toNat ∧
      Reach exitJumpdests 5 0 (at_ c st mem aw g 247 (iW :: cnt :: head :: tail :: []) e)
        (at_ c st mem aw' g' 254
          (UInt256.ofNat 301 :: UInt256.eq iW cnt :: iW :: cnt :: head :: tail :: []) e') :=
    liftAt (block_step hvj_exit exit_b247 exit_b247_ok (n := 5)
      exit_b247_bound rfl (exit_b247_shape c st mem aw g e iW cnt [head, tail]) hcode rfl
      (by gas_omega) (by simp)) haw
  have h2 := chainAt h1 fun aw g₁ e₁ haw hg₁ => liftAt
    (reach_jumpi_fallthrough exit_s254 hcode ((eq_eq_zero_iff _ _).mpr hne) (by gas_omega)
      (by simp))
    haw
  clear h1
  -- 255..273: base slot, the caller word
  have h3 := chainAt h2 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_exit exit_b255 exit_b255_ok (n := 15) exit_b255_bound rfl
      (exit_b255_shape c st mem aw g₁ e₁ iW cnt head [tail]) hcode rfl (by gas_omega) (by simp))
    haw
  clear h2
  have h4 := chainAt h3 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore exit_s274 (hcode_of_env c (by env_simp; exact henv)) (B := 40)
        haw ?_ (by decide) (M := 126) (by decide) ?_ ?_) ?_
      · rw [h0]; omega
      · gas_omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h0]; omega) (by decide)
  clear h3
  -- 275..283: first request word
  have h5 := chainAt h4 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_exit exit_b275 exit_b275_ok (n := 7) exit_b275_bound rfl
      (exit_b275_shape c _ _ aw g₁ e₁ _ _ [iW, cnt, head, tail])
      (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h4
  simp only [slotW_touch] at h5
  have h6 := chainAt h5 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore exit_s284 (hcode_of_env c (by env_simp; exact henv)) (B := 40)
        haw ?_ (by decide) (M := 126) (by decide) ?_ ?_) ?_
      · rw [h20]; omega
      · gas_omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h20]; omega) (by decide)
  clear h5
  -- 285..293: second request word
  have h7 := chainAt h6 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_exit exit_b285 exit_b285_ok (n := 7) exit_b285_bound rfl
      (exit_b285_shape c _ _ aw g₁ e₁ _ _ [iW, cnt, head, tail])
      (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h6
  simp only [slotW_touch] at h7
  have h8 := chainAt h7 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore exit_s294 (hcode_of_env c (by env_simp; exact henv)) (B := 40)
        haw ?_ (by decide) (M := 126) (by decide) ?_ ?_) ?_
      · rw [h52]; omega
      · gas_omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h52]; omega) (by decide)
  clear h7
  -- 295..300: bump the counter, back to the head
  have h9 := chainAt h8 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_exit exit_b295 exit_b295_ok (n := 4) exit_b295_bound rfl
      (exit_b295_shape c _ _ aw g₁ e₁ iW [cnt, head, tail])
      (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h8
  obtain ⟨aw', g', e', haw', hg', hr⟩ := h9
  exact ⟨aw', g', e', haw', by gas_omega, budget_mono hr (by gas_omega)⟩

theorem drain_loop (st₀ : EvmYul.State .EVM) (henv₀ : st₀.executionEnv = c.env)
    (head tail cnt : UInt256) (mem₀ : ByteArray) (hcnt : cnt.toNat ≤ 16) :
    ∀ (m i : Nat) (st : EvmYul.State .EVM) (aw g : UInt256) (e : Nat), i + m = cnt.toNat →
      Touched st₀ st → aw.toNat ≤ 40 → 7000 * m + 25 ≤ g.toNat →
      ∃ (st' : EvmYul.State .EVM) (aw' g' : UInt256) (e' : Nat), Touched st₀ st' ∧
        aw'.toNat ≤ 40 ∧ g.toNat - (7000 * m + 25) ≤ g'.toNat ∧
        Reach exitJumpdests (42 * m + 6) 0
          (at_ c st (drainMem st₀ head mem₀ i) aw g 247
            (UInt256.ofNat i :: cnt :: head :: tail :: []) e)
          (at_ c st' (drainMem st₀ head mem₀ cnt.toNat) aw' g' 301
            (cnt :: cnt :: head :: tail :: []) e') := by
  intro m
  induction m with
  | zero =>
    intro i st aw g e hi hst haw hg
    have hi' : i = cnt.toNat := by omega
    subst hi'
    have henv : st.executionEnv = c.env := hst.executionEnv.trans henv₀
    have hcode := hcode_of_env c henv
    have hcnt' : UInt256.ofNat cnt.toNat = cnt := ofNat_toNat' cnt
    have h1 := block_step hvj_exit exit_b247 exit_b247_ok (n := 5) exit_b247_bound rfl
      (exit_b247_shape c st (drainMem st₀ head mem₀ cnt.toNat) aw g e (UInt256.ofNat cnt.toNat)
        cnt [head, tail]) hcode rfl (by gas_omega) (by simp)
    have h2 := chain h1 fun g₁ e₁ hg₁ =>
      reach_jumpi_taken exit_s254 hcode ((eq_ne_zero_iff _ _).mpr hcnt')
        (hvj_exit 301 (by decide)) (by gas_omega) (by simp)
    obtain ⟨g', e', hg', hr⟩ := h2
    rw [hcnt'] at hr ⊢
    exact ⟨st, aw, g', e', hst, haw, by gas_omega, budget_mono hr (by gas_omega)⟩
  | succ m ih =>
    intro i st aw g e hi hst haw hg
    have henv : st.executionEnv = c.env := hst.executionEnv.trans henv₀
    have hi15 : (UInt256.ofNat i).toNat ≤ 15 := by
      rw [toNat_ofNat_of_lt (by rw [size_eq]; omega)]; omega
    have hne : UInt256.ofNat i ≠ cnt := by
      intro h
      have := congrArg UInt256.toNat h
      rw [toNat_ofNat_of_lt (by rw [size_eq]; omega)] at this
      omega
    obtain ⟨aw₁, g₁, e₁, haw₁, hg₁, hr₁⟩ :=
      drain_body c (mem := drainMem st₀ head mem₀ i) (g := g) (e := e) (UInt256.ofNat i) cnt head
        tail henv hi15 hne haw (by gas_omega)
    rw [writeItem_of_touched hst, ofNat_add_ofNat, Nat.add_comm 1 i] at hr₁
    obtain ⟨st', aw', g', e', hst', haw', hg', hr'⟩ :=
      ih (i + 1) (touchItem st (base (UInt256.ofNat i) head)) aw₁ g₁ e₁ (by omega)
        (touched_touchItem hst _) haw₁ (by gas_omega)
    refine ⟨st', aw', g', e', hst', haw', by gas_omega, ?_⟩
    exact budget_mono (hr₁.trans hr') (by gas_omega)

theorem update_head {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (henv : st.executionEnv = c.env) (hperm : c.env.perm = true) (cnt : UInt256)
    (hg : 44500 ≤ g.toNat) :
    ∃ (g' : UInt256) (e' : Nat), g.toNat - 44500 ≤ g'.toNat ∧
      Reach exitJumpdests 20 2
        (at_ c st mem aw g 301 (cnt :: cnt :: headWord₀ c :: tailWord₀ c :: []) e)
        (at_ c (headStore c cnt st) mem aw g' 330 (cnt :: []) e') := by
  have hcode := hcode_of_env c henv
  have h1 := le_of_exact <| block_step hvj_exit exit_b301 exit_b301_ok (n := 7)
    exit_b301_bound rfl (exit_b301_shape c st mem aw g e cnt cnt (headWord₀ c) (tailWord₀ c) [])
    hcode rfl (by gas_omega) (by simp)
  by_cases hfull : tailWord₀ c = headWord₀ c + cnt
  · have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_taken exit_s310 hcode ((eq_ne_zero_iff _ _).mpr hfull)
        (hvj_exit 319 (by decide)) (by gas_omega) (by simp)
    clear h1
    have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b319 exit_b319_ok (n := 5) exit_b319_bound rfl
        (exit_b319_shape c st mem aw g₁ e₁ cnt (headWord₀ c + cnt) []) hcode rfl (by gas_omega)
        (by simp)
    clear h2
    have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_sstore exit_s325 hcode (perm_of_env c henv hperm) (by gas_omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b326 exit_b326_ok (n := 2) exit_b326_bound rfl
        (exit_b326_shape c _ mem aw g₁ e₁ [cnt]) (hcode_of_env c (by env_simp; exact henv)) rfl
        (by gas_omega) (by simp)
    clear h4
    have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_sstore exit_s329 (hcode_of_env c (by env_simp; exact henv))
        (perm_of_env c (by env_simp; exact henv) hperm) (by gas_omega) (by simp)
    clear h5
    obtain ⟨g', e', hg', hr⟩ := h6
    simp only [headStore, if_pos hfull]
    exact ⟨g', e', by gas_omega, budget_mono hr (by gas_omega)⟩
  · have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_fallthrough exit_s310 hcode ((eq_eq_zero_iff _ _).mpr hfull) (by gas_omega)
        (by simp)
    clear h1
    have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b311 exit_b311_ok (n := 2) exit_b311_bound rfl
        (exit_b311_shape c st mem aw g₁ e₁ cnt (headWord₀ c + cnt) []) hcode rfl (by gas_omega)
        (by simp)
    clear h2
    have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_sstore exit_s314 hcode (perm_of_env c henv hperm) (by gas_omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b315 exit_b315_ok (n := 2) exit_b315_bound rfl
        (exit_b315_shape c _ mem aw g₁ e₁ [cnt]) (hcode_of_env c (by env_simp; exact henv)) rfl
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
      Reach exitJumpdests 36 2 (at_ c st mem aw g 330 (cnt :: []) e)
        (at_ c ((stX.sstore (UInt256.ofNat 0) (newExcess c stX)).sstore (UInt256.ofNat 1)
          (UInt256.ofNat 0)) mem aw g' 453 (UInt256.ofNat 0 :: (UInt256.ofNat 68 * cnt) :: []) e') := by
  have hcode := hcode_of_env c henv
  have hcds : cdsizeW st = cdsizeWord c := by unfold cdsizeW; rw [henv]; rfl
  have h1 := le_of_exact <| block_step hvj_exit exit_b330 exit_b330_ok (n := 3)
    exit_b330_bound rfl (exit_b330_shape c st mem aw g e [cnt]) hcode rfl (by gas_omega) (by simp)
  simp only [hcds] at h1
  -- the tail from `store_excess` (442), shared by every branch
  have tail : ∀ (stX : EvmYul.State .EVM) (v g₁ : UInt256) (e₁ : Nat), Touched st stX →
      g₁.toNat ≥ g.toNat - 5000 →
      ∃ (g' : UInt256) (e' : Nat), g₁.toNat - 44300 ≤ g'.toNat ∧
        Reach exitJumpdests 9 2 (at_ c stX mem aw g₁ 442 (v :: cnt :: []) e₁)
          (at_ c ((stX.sstore (UInt256.ofNat 0) v).sstore (UInt256.ofNat 1) (UInt256.ofNat 0)) mem aw
            g' 453 (UInt256.ofNat 0 :: (UInt256.ofNat 68 * cnt) :: []) e') := by
    intro stX v g₁ e₁ hstX hg₁
    have henvX : stX.executionEnv = c.env := hstX.executionEnv.trans henv
    have hcodeX := hcode_of_env c henvX
    have t1 := le_of_exact <| block_step hvj_exit exit_b442 exit_b442_ok (n := 2)
      exit_b442_bound rfl (exit_b442_shape c stX mem aw g₁ e₁ [v, cnt]) hcodeX rfl (by gas_omega)
      (by simp)
    have t2 := chainLe t1 fun g₂ e₂ hg₂ => le_of_exact <|
      reach_sstore exit_s444 hcodeX (perm_of_env c henvX hperm) (by gas_omega) (by simp)
    clear t1
    have t3 := chainLe t2 fun g₂ e₂ hg₂ => le_of_exact <|
      block_step hvj_exit exit_b445 exit_b445_ok (n := 2) exit_b445_bound rfl
        (exit_b445_shape c _ mem aw g₂ e₂ [cnt]) (hcode_of_env c (by env_simp; exact henvX)) rfl
        (by gas_omega) (by simp)
    clear t2
    have t4 := chainLe t3 fun g₂ e₂ hg₂ => le_of_exact <|
      reach_sstore exit_s448 (hcode_of_env c (by env_simp; exact henvX))
        (perm_of_env c (by env_simp; exact henvX) hperm) (by gas_omega) (by simp)
    clear t3
    have t5 := chainLe t4 fun g₂ e₂ hg₂ => le_of_exact <|
      block_step hvj_exit exit_b449 exit_b449_ok (n := 3) exit_b449_bound rfl
        (exit_b449_shape c _ mem aw g₂ e₂ cnt []) (hcode_of_env c (by env_simp; exact henvX)) rfl
        (by gas_omega) (by simp)
    clear t4
    obtain ⟨g', e', hg', hr⟩ := t5
    exact ⟨g', e', by gas_omega, budget_mono hr (by gas_omega)⟩
  by_cases hcd : cdsizeWord c ≠ ⟨0⟩
  · -- nonempty calldata: latch the inhibitor
    have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_taken exit_s335 hcode hcd (hvj_exit 408 (by decide)) (by gas_omega) (by simp)
    clear h1
    have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b408 exit_b408_ok (n := 2) exit_b408_bound rfl
        (exit_b408_shape c st mem aw g₁ e₁ [cnt]) hcode rfl (by gas_omega) (by simp)
    clear h2
    obtain ⟨g₁, e₁, hg₁, hr₁⟩ := h3
    obtain ⟨g', e', hg', hr'⟩ := tail st INH g₁ e₁ (Touched.refl st) (by gas_omega)
    refine ⟨st, g', e', Touched.refl st, by gas_omega, ?_⟩
    simp only [newExcess, if_pos hcd]
    exact budget_mono (hr₁.trans hr') (by gas_omega)
  · have hcd' : cdsizeWord c = ⟨0⟩ := by
      by_contra h; exact hcd h
    have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_fallthrough exit_s335 hcode hcd' (by gas_omega) (by simp)
    clear h1
    have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b336 exit_b336_ok (n := 8) exit_b336_bound rfl
        (exit_b336_shape c st mem aw g₁ e₁ [cnt]) hcode rfl (by gas_omega) (by simp)
    clear h2
    simp only [slotW_touch] at h3
    have hstX : Touched st (touch (touch st (UInt256.ofNat 0)) (UInt256.ofNat 1)) :=
      ((Touched.refl st).touch _).touch _
    have hcodeX : (touch (touch st (UInt256.ofNat 0)) (UInt256.ofNat 1)).executionEnv.code
        = exitRuntime := hcode
    by_cases hinh : slotW st (UInt256.ofNat 0) = INH
    · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
        reach_jumpi_taken exit_s379 hcodeX ((eq_ne_zero_iff _ _).mpr hinh.symm)
          (hvj_exit 390 (by decide)) (by gas_omega) (by simp)
      clear h3
      have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
        block_step hvj_exit exit_b390 exit_b390_ok (n := 6) exit_b390_bound rfl
          (exit_b390_shape c _ mem aw g₁ e₁ _ _ [cnt]) hcodeX rfl (by gas_omega) (by simp)
      clear h4
      obtain ⟨g₁, e₁, hg₁, hr₁⟩ := h5
      obtain ⟨g', e', hg', hr'⟩ := tail _ (UInt256.ofNat 0) g₁ e₁ hstX (by gas_omega)
      refine ⟨_, g', e', hstX, by gas_omega, ?_⟩
      simp only [newExcess, if_neg hcd, slotW_touch, if_pos hinh]
      exact budget_mono (hr₁.trans hr') (by gas_omega)
    · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
        reach_jumpi_fallthrough exit_s379 hcodeX ((eq_eq_zero_iff _ _).mpr (fun h => hinh h.symm))
          (by gas_omega) (by simp)
      clear h3
      have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
        block_step hvj_exit exit_b380 exit_b380_ok (n := 6) exit_b380_bound rfl
          (exit_b380_shape c _ mem aw g₁ e₁ _ _ [cnt]) hcodeX rfl (by gas_omega) (by simp)
      clear h4
      by_cases hgt : UInt256.ofNat 2 < slotW st (UInt256.ofNat 1) + slotW st (UInt256.ofNat 0)
      · have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
          reach_jumpi_taken exit_s389 hcodeX ((gt_ne_zero_iff _ _).mpr hgt)
            (hvj_exit 398 (by decide)) (by gas_omega) (by simp)
        clear h5
        have h7 := chainLe h6 fun g₁ e₁ hg₁ => le_of_exact <|
          block_step hvj_exit exit_b398 exit_b398_ok (n := 7) exit_b398_bound rfl
            (exit_b398_shape c _ mem aw g₁ e₁ _ _ [cnt]) hcodeX rfl (by gas_omega) (by simp)
        clear h6
        obtain ⟨g₁, e₁, hg₁, hr₁⟩ := h7
        obtain ⟨g', e', hg', hr'⟩ := tail _ _ g₁ e₁ hstX (by gas_omega)
        refine ⟨_, g', e', hstX, by gas_omega, ?_⟩
        simp only [newExcess, if_neg hcd, slotW_touch, if_neg hinh, if_pos hgt]
        exact budget_mono (hr₁.trans hr') (by gas_omega)
      · have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
          reach_jumpi_fallthrough exit_s389 hcodeX ((gt_eq_zero_iff _ _).mpr hgt) (by gas_omega)
            (by simp)
        clear h5
        have h7 := chainLe h6 fun g₁ e₁ hg₁ => le_of_exact <|
          block_step hvj_exit exit_b390 exit_b390_ok (n := 6) exit_b390_bound rfl
            (exit_b390_shape c _ mem aw g₁ e₁ _ _ [cnt]) hcodeX rfl (by gas_omega) (by simp)
        clear h6
        obtain ⟨g₁, e₁, hg₁, hr₁⟩ := h7
        obtain ⟨g', e', hg', hr'⟩ := tail _ (UInt256.ofNat 0) g₁ e₁ hstX (by gas_omega)
        refine ⟨_, g', e', hstX, by gas_omega, ?_⟩
        simp only [newExcess, if_neg hcd, slotW_touch, if_neg hinh, if_neg hgt]
        exact budget_mono (hr₁.trans hr') (by gas_omega)

theorem system_returns (hsys : callerWord c = sysW) (hperm : c.env.perm = true)
    (hg : 250000 ≤ c.gas.toNat) :
    ∃ (st' stX : EvmYul.State .EVM) (aw g : UInt256) (e : Nat),
      Touched (entrySt c) st' ∧ Touched (headStore c (drainWord c) st') stX ∧
      aw.toNat ≤ 40 ∧ (Reach exitJumpdests 800 4 c.entry
        (at_ c ((stX.sstore (UInt256.ofNat 0) (newExcess c stX)).sstore (UInt256.ofNat 1)
            (UInt256.ofNat 0))
          (drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) aw g 453
          (UInt256.ofNat 0 :: (UInt256.ofNat 68 * drainWord c) :: []) e) ∧ Halt exitJumpdests
        (at_ c ((stX.sstore (UInt256.ofNat 0) (newExcess c stX)).sstore (UInt256.ofNat 1)
            (UInt256.ofNat 0))
          (drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) aw g 453
          (UInt256.ofNat 0 :: (UInt256.ofNat 68 * drainWord c) :: []) e) .RETURN
        ((drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat).readWithPadding 0
          (UInt256.ofNat 68 * drainWord c).toNat)) := by
  obtain ⟨g₀, e₀, hg₀, hpre⟩ := system_prefix c hsys (by gas_omega)
  have hcnt := drainWord_le c
  obtain ⟨st', aw', g₁, e₁, hst', haw', hg₁, hloop⟩ := drain_loop c (entrySt c) rfl (headWord₀ c)
    (tailWord₀ c) (drainWord c) (mem₀ c) hcnt (drainWord c).toNat 0 (stP c) (aw₀ c) g₀ e₀
    (by omega) (touched_stP c) (by rw [activeWords_entry]; omega) (by gas_omega)
  have h1 : ∃ (g : UInt256) (e : Nat), c.gas.toNat - 116400 ≤ g.toNat ∧
      Reach exitJumpdests 703 0 c.entry
        (at_ c st' (drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) aw' g 301
          (drainWord c :: drainWord c :: headWord₀ c :: tailWord₀ c :: []) e) :=
    ⟨g₁, e₁, by gas_omega, budget_mono (hpre.trans hloop) (by gas_omega)⟩
  have henv' : st'.executionEnv = c.env := hst'.executionEnv
  have h2 := chainLe h1 fun g e hg => update_head c henv' hperm (drainWord c) (by gas_omega)
  clear h1
  have henvH : (headStore c (drainWord c) st').executionEnv = c.env := by
    unfold headStore; split <;> (env_simp; exact henv')
  have h3 : ∃ (stX : EvmYul.State .EVM) (g : UInt256) (e : Nat),
      Touched (headStore c (drainWord c) st') stX ∧ c.gas.toNat - 210900 ≤ g.toNat ∧
      Reach exitJumpdests (703 + 20 + 36) 4 c.entry
        (at_ c ((stX.sstore (UInt256.ofNat 0) (newExcess c stX)).sstore (UInt256.ofNat 1)
            (UInt256.ofNat 0))
          (drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) aw' g 453
          (UInt256.ofNat 0 :: (UInt256.ofNat 68 * drainWord c) :: []) e) := by
    obtain ⟨g₂, e₂, hg₂, hr₂⟩ := h2
    obtain ⟨stX, g₃, e₃, hstX, hg₃, hr₃⟩ := update_excess c
      (mem := drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) (aw := aw')
      (g := g₂) (e := e₂) henvH hperm (drainWord c) (by gas_omega)
    exact ⟨stX, g₃, e₃, hstX, by gas_omega, hr₂.trans hr₃⟩
  clear h2
  obtain ⟨stX, g, e, hstX, hgX, hr⟩ := h3
  have henvX : stX.executionEnv = c.env := hstX.executionEnv.trans henvH
  refine ⟨st', stX, aw', g, e, hst', hstX, haw', budget_mono hr (by gas_omega), ?_⟩
  have hlen : (UInt256.ofNat 68 * drainWord c).toNat = 68 * (drainWord c).toNat :=
    toNat_ofNat_mul_of_lt 68 _ (by rw [size_eq]; omega)
  refine halt_RETURN exit_s453 (hcode_of_env c (by env_simp; exact henvX)) (B := 40) (M := 123)
    (g := g) haw' ?_ (by decide) (by decide) ?_ (by simp)
  · rw [hlen]; show (0 + 68 * (drainWord c).toNat + 31) / 32 ≤ 40; omega
  · gas_omega

#print axioms gate
#print axioms system_prefix
#print axioms drain_body
#print axioms drain_loop
#print axioms update_head
#print axioms update_excess
#print axioms system_returns
end Eip8282.Audit.Integrator.SystemExitTrace
