import Eip8282.Audit.Integrator.ActualAppendGas

/-!
# Actual append paths and opcode gas debits

All supported XRuns segments are extracted from actual successful evaluation.
The fee loop is followed by induction on actual interpreter fuel, without a
completion witness, fixed iteration cutoff or sufficient-resource premise.
Generated instruction shapes locate the real LOG0 and its length; the path
continues to the final STOP. ActualAppendGas then accounts for the opcode and
memory debits, including the halting step and Theta's returned gas.

The final bounds need no owner, storage fit, mathematical fee domain or funding
premise. Transaction-wide, nested-frame and refund accounting remain separate.
-/
namespace Eip8282.Audit.Integrator.AppendGasPath
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall)
open SuccessInversion ActualAppendGas
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- Packaging of the evaluator's existing supported run relation. -/
def Segment (vj : Array UInt256) (fuel : Nat) (pre : EVM.State)
    (rest : Nat) (post : EVM.State) : Prop :=
  ∃ trace, XRuns vj fuel pre trace rest post ∧ Supported trace

theorem Segment.refl (vj : Array UInt256) (fuel : Nat) (pre : EVM.State) :
    Segment vj fuel pre fuel pre := ⟨[], .refl _ _, by simp [Supported]⟩

theorem Segment.single {vj : Array UInt256} {fuel cost : Nat} {pre post : EVM.State}
    (hop : (decodeAt pre).1 ∈ allOps) (h : XStepAt vj fuel cost pre post) :
    Segment vj (fuel+1) pre fuel post := by
  refine ⟨[(fuel,cost,decodeAt pre)], .cons h (.refl _ _), ?_⟩
  intro s hs
  have he := List.mem_singleton.mp hs
  subst s
  exact hop

theorem Segment.trans {vj : Array UInt256} {f g r : Nat} {pre mid post : EVM.State}
    (h₁ : Segment vj f pre g mid) (h₂ : Segment vj g mid r post) :
    Segment vj f pre r post := by
  obtain ⟨t₁, hr₁, hs₁⟩ := h₁
  obtain ⟨t₂, hr₂, hs₂⟩ := h₂
  refine ⟨t₁++t₂, hr₁.trans hr₂, ?_⟩
  intro s hs
  exact (List.mem_append.mp hs).elim (hs₁ s) (hs₂ s)

/-- Retain the actual supported step behind a checked symbolic instruction. -/
theorem traced_symStep {fuel : Nat} {vj : Array UInt256} {vjNats : List Nat}
    {pre shaped final : EVM.State} {out : ByteArray} {inst : Instruction}
    (hdec : decodeAt pre = inst) (hshape : symStep vjNats inst pre = some shaped)
    (h : X fuel vj pre = .ok (.success final out)) :
    ∃ rest cost, fuel = rest + 1 ∧ Z vj inst.1 pre = .ok (pre, cost) ∧
      X rest vj (withGE shaped (pre.gasAvailable - UInt256.ofNat cost)
        (pre.execLength + 1)) = .ok (.success final out) ∧
      Segment vj fuel pre rest (withGE shaped (pre.gasAvailable - UInt256.ofNat cost)
        (pre.execLength+1)) := by
  obtain ⟨hguard, hstep⟩ := guardOk_of_symStep hshape
  have hm := mem_blockOps_of_guardOk hguard
  obtain ⟨rest, cost, mid, post, hf, hz, hs, hactual, htail⟩ :=
    success_continue hdec (not_halting_block hm) h
  have hmid : mid = pre := by
    rw [Z_ok_state hz]
    exact charged_eq_self (memcost_zero hm pre)
  subst mid
  cases rest with
  | zero => simp only [X_zero] at htail; contradiction
  | succ rest =>
      have he : post = withGE shaped (pre.gasAvailable - UInt256.ofNat cost)
          (pre.execLength + 1) := by
        change EvmYul.EVM.step (rest + 1) cost (some (inst.1, inst.2)) pre = .ok post at hs
        rw [EVM_step_eq_step (List.mem_append_left _ hm), stepPre_eq_withGE,
          step_withGE (List.mem_append_left _ hm), hstep] at hs
        exact (Except.ok.inj hs).symm
      refine ⟨rest + 1, cost, hf, hz, he ▸ htail, ?_⟩
      rw [hf, ← he]
      exact Segment.single (by rw [hdec]; exact List.mem_append_left _ hm) hactual

/-- Retain a real supported segment for every checked straight-line block. -/
theorem traced_symBlock {fuel : Nat} {vj : Array UInt256} {vjNats : List Nat}
    {code : ByteArray} (sites : List Site) (hsites : sitesOk code sites = true)
    {pre shaped final : EVM.State} {out : ByteArray}
    (hcode : pre.executionEnv.code = code)
    (hpc : pre.pc = UInt256.ofNat (headPc sites))
    (hshape : symBlock vjNats (sites.map Prod.snd) pre = some shaped)
    (h : X fuel vj pre = .ok (.success final out)) :
    ∃ rest gas count, fuel = rest + sites.length ∧
      X rest vj (withGE shaped gas count) = .ok (.success final out) ∧
      Segment vj fuel pre rest (withGE shaped gas count) := by
  induction sites generalizing fuel pre shaped with
  | nil =>
      simp only [List.map_nil, symBlock, Option.some.injEq] at hshape
      subst shaped
      exact ⟨fuel, pre.gasAvailable, pre.execLength, rfl, h, Segment.refl _ _ _⟩
  | cons site tail ih =>
      obtain ⟨pc, inst⟩ := site
      change pre.pc = UInt256.ofNat pc at hpc
      obtain ⟨hop, hsitesTail⟩ := sitesOk_cons hsites
      rw [List.map_cons, symBlock_cons] at hshape
      cases hfirst : symStep vjNats inst pre with
      | none => rw [hfirst] at hshape; contradiction
      | some first =>
          rw [hfirst] at hshape
          change symBlock vjNats (tail.map Prod.snd) first = some shaped at hshape
          obtain ⟨hguard, hstep⟩ := guardOk_of_symStep hfirst
          have hm := mem_blockOps_of_guardOk hguard
          obtain ⟨rest, cost, hf, hz, hnext, hpnext⟩ := traced_symStep
            (decodeAt_of_code_pc hcode hpc hop) hfirst h
          rcases hsitesTail with rfl | ⟨hhead, hne, hsitesTail⟩
          · change some first = some shaped at hshape
            obtain rfl := Option.some.inj hshape
            exact ⟨rest, _, _, hf, hnext, hpnext⟩
          · have hcodeNext : (withGE first (pre.gasAvailable - UInt256.ofNat cost)
                (pre.execLength + 1)).executionEnv.code = code := by
              rw [executionEnv_withGE, executionEnv_step (List.mem_append_left _ hm) hstep, hcode]
            have hpcNext : (withGE first (pre.gasAvailable - UInt256.ofNat cost)
                (pre.execLength + 1)).pc = UInt256.ofNat (headPc tail) := by
              rw [pc_withGE, pc_step hm hne (arg_width_of_opcodeAt hop) hstep,
                hpc, ofNat_add_ofNat, hhead]
              change UInt256.ofNat (pc + (argOnNBytesOfInstr inst.1 + 1)) =
                UInt256.ofNat (pc + 1 + argOnNBytesOfInstr inst.1)
              congr 1
              omega
            have hshapeNext : symBlock vjNats (tail.map Prod.snd)
                (withGE first (pre.gasAvailable - UInt256.ofNat cost) (pre.execLength + 1)) =
                some (withGE shaped (pre.gasAvailable - UInt256.ofNat cost) (pre.execLength + 1)) := by
              rw [symBlock_withGE, hshape]
              rfl
            obtain ⟨remaining, gas, count, hremaining, hresult, hpresult⟩ :=
              ih hsitesTail hcodeNext hpcNext hshapeNext hnext
            rw [withGE_withGE] at hresult hpresult
            exact ⟨remaining, gas, count, by simp only [List.length_cons]; omega, hresult, hpnext.trans hpresult⟩

theorem traced_jumpi_untaken {fuel : Nat} {vj : Array UInt256}
    {pre final : EVM.State} {out : ByteArray} {dest cond : UInt256} {stk : Stack UInt256}
    (hdec : decodeAt pre = (.JUMPI, none)) (hstack : pre.stack = dest :: cond :: stk)
    (hcond : cond = ⟨0⟩) (h : X fuel vj pre = .ok (.success final out)) :
    ∃ rest cost, fuel = rest+1 ∧ Z vj .JUMPI pre = .ok (pre, cost) ∧
      X rest vj (withGE { pre with pc := pre.pc + ⟨1⟩, stack := stk }
        (pre.gasAvailable - UInt256.ofNat cost) (pre.execLength+1)) =
          .ok (.success final out) ∧
      Segment vj fuel pre rest (withGE { pre with pc := pre.pc + ⟨1⟩, stack := stk }
        (pre.gasAvailable - UInt256.ofNat cost) (pre.execLength+1)) := by
  obtain ⟨rest, cost, mid, post, hf, hz, hs, hactual, htail⟩ :=
    success_continue hdec (by decide) h
  have hmid : mid = pre := by
    rw [Z_ok_state hz]
    exact charged_eq_self (memcost_JUMPI pre)
  subst mid
  cases rest with
  | zero => simp only [X_zero] at htail; contradiction
  | succ rest =>
      have he : post = withGE { pre with pc := pre.pc + ⟨1⟩, stack := stk }
          (pre.gasAvailable - UInt256.ofNat cost) (pre.execLength+1) := by
        change EvmYul.EVM.step (rest+1) cost (some (.JUMPI, none)) pre = .ok post at hs
        rw [EVM_step_eq_step (by decide : Operation.JUMPI ∈ allOps), stepPre_eq_withGE,
          step_withGE (by decide : Operation.JUMPI ∈ allOps),
          step_JUMPI_untaken hstack hcond] at hs
        exact (Except.ok.inj hs).symm
      refine ⟨rest+1, cost, hf, hz, he ▸ htail, ?_⟩
      rw [hf, ← he]
      exact Segment.single (by rw [hdec]; decide) hactual

theorem traced_jumpi_taken {fuel : Nat} {vj : Array UInt256}
    {pre final : EVM.State} {out : ByteArray} {dest cond : UInt256} {stk : Stack UInt256}
    (hdec : decodeAt pre = (.JUMPI, none)) (hstack : pre.stack = dest :: cond :: stk)
    (hcond : cond ≠ ⟨0⟩) (h : X fuel vj pre = .ok (.success final out)) :
    ∃ rest cost, fuel = rest+1 ∧ Z vj .JUMPI pre = .ok (pre, cost) ∧
      X rest vj (withGE { pre with pc := dest, stack := stk }
        (pre.gasAvailable - UInt256.ofNat cost) (pre.execLength+1)) =
          .ok (.success final out) ∧
      Segment vj fuel pre rest (withGE { pre with pc := dest, stack := stk }
        (pre.gasAvailable - UInt256.ofNat cost) (pre.execLength+1)) := by
  obtain ⟨rest, cost, mid, post, hf, hz, hs, hactual, htail⟩ :=
    success_continue hdec (by decide) h
  have hmid : mid = pre := by
    rw [Z_ok_state hz]
    exact charged_eq_self (memcost_JUMPI pre)
  subst mid
  cases rest with
  | zero => simp only [X_zero] at htail; contradiction
  | succ rest =>
      have he : post = withGE { pre with pc := dest, stack := stk }
          (pre.gasAvailable - UInt256.ofNat cost) (pre.execLength+1) := by
        change EvmYul.EVM.step (rest+1) cost (some (.JUMPI, none)) pre = .ok post at hs
        rw [EVM_step_eq_step (by decide : Operation.JUMPI ∈ allOps), stepPre_eq_withGE,
          step_withGE (by decide : Operation.JUMPI ∈ allOps),
          step_JUMPI_taken hstack hcond] at hs
        exact (Except.ok.inj hs).symm
      refine ⟨rest+1, cost, hf, hz, he ▸ htail, ?_⟩
      rw [hf, ← he]
      exact Segment.single (by rw [hdec]; decide) hactual


theorem traced_effect {fuel : Nat} {vj : Array UInt256}
    {pre shaped final : EVM.State} {out : ByteArray} {op : Operation .EVM}
    {arg : Option (UInt256 × Nat)} (hm : op ∈ allOps) (hn : Halting op = false)
    (hd : decodeAt pre = (op,arg)) (hstep : EvmYul.step op arg pre = .ok shaped)
    (h : X fuel vj pre = .ok (.success final out)) :
    ∃ rest gas count, X rest vj (withGE shaped gas count) = .ok (.success final out) ∧
      Segment vj fuel pre rest (withGE shaped gas count) := by
  obtain ⟨rest, cost, mid, post, hf, hz, hs, hactual, htail⟩ := success_continue hd hn h
  cases rest with
  | zero => simp only [X_zero] at htail; contradiction
  | succ rest =>
      have hmid : mid = withGE pre mid.gasAvailable pre.execLength := by
        rw [Z_ok_state hz]
        rfl
      have he : post = withGE shaped (mid.gasAvailable - UInt256.ofNat cost) (pre.execLength+1) := by
        change EvmYul.EVM.step (rest+1) cost (some (op,arg)) mid = .ok post at hs
        rw [EVM_step_eq_step hm, stepPre_eq_withGE, hmid, withGE_withGE,
          step_withGE hm, hstep] at hs
        exact (Except.ok.inj hs).symm
      refine ⟨rest+1, _, _, he ▸ htail, ?_⟩
      rw [hf, ← he]
      exact Segment.single (by rw [hd]; exact hm) hactual


/-- Actual nonzero exit fee iteration, with its complete supported segment. -/
theorem traced_exit_cycle (c : XiCall .exit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {o a i numerator : UInt256} {final : EVM.State} {out : ByteArray}
    (henv : st.executionEnv = c.env) (ha : a ≠ ⟨0⟩)
    (h : X fuel exitJumpdests
      (at_ c st mem aw g 99 [o,a,i,numerator,UInt256.ofNat 17] e) =
        .ok (.success final out)) :
    ∃ rest gas count, fuel = rest+24 ∧
      X rest exitJumpdests (at_ c st mem aw gas 99
        [a+o, (numerator*a)/(i*UInt256.ofNat 17), UInt256.ofNat 1+i,
          numerator, UInt256.ofNat 17] count) = .ok (.success final out) ∧
      Segment exitJumpdests fuel (at_ c st mem aw g 99
        [o,a,i,numerator,UInt256.ofNat 17] e) rest (at_ c st mem aw gas 99
        [a+o, (numerator*a)/(i*UInt256.ofNat 17), UInt256.ofNat 1+i,
          numerator, UInt256.ofNat 17] count) := by
  have hcode := Exit.hcode_of_env c henv
  obtain ⟨f1, g1, e1, hf1, hx1, hp1⟩ := traced_symBlock exit_b99 exit_b99_ok
    hcode rfl (exit_b99_shape c st mem aw g e o a [i,numerator,UInt256.ofNat 17]) h
  rw [withGE_at] at hx1 hp1
  obtain ⟨f2, cost, hf2, _, hx2, hp2⟩ := traced_jumpi_untaken
    (decodeAt_of_code_pc hcode rfl exit_s106) rfl ((feeLoop_continue_iff a).mpr ha) hx1
  rw [jumpi_fallthrough_at, withGE_at] at hx2 hp2
  obtain ⟨f3, g3, e3, hf3, hx3, hp3⟩ := traced_symBlock exit_b107 exit_b107_ok
    hcode rfl (exit_b107_shape c st mem aw _ _ o a i numerator (UInt256.ofNat 17) []) hx2
  rw [withGE_at] at hx3 hp3
  exact ⟨f3, g3, e3, by
    change fuel = f1+6 at hf1
    change f2 = f3+17 at hf3
    omega, hx3, hp1.trans (hp2.trans hp3)⟩

/-- Induct over actual successful fuel to retain the complete exit fee-loop path. -/
theorem traced_exit_fee (c : XiCall .exit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {o a i numerator : UInt256} {final : EVM.State} {out : ByteArray}
    (henv : st.executionEnv = c.env)
    (h : X fuel exitJumpdests
      (at_ c st mem aw g 99 [o,a,i,numerator,UInt256.ofNat 17] e) =
        .ok (.success final out)) :
    ∃ n output counter rest gas count,
      feeExit numerator n o a i = some (output,counter) ∧
      X rest exitJumpdests (at_ c st mem aw gas 126
        [output,⟨0⟩,counter,numerator,UInt256.ofNat 17] count) = .ok (.success final out) ∧
      Segment exitJumpdests fuel (at_ c st mem aw g 99
        [o,a,i,numerator,UInt256.ofNat 17] e) rest (at_ c st mem aw gas 126
        [output,⟨0⟩,counter,numerator,UInt256.ofNat 17] count) := by
  induction fuel using Nat.strong_induction_on generalizing o a i g e with
  | h fuel ih =>
      by_cases ha : a = ⟨0⟩
      · subst a
        have hcode := Exit.hcode_of_env c henv
        obtain ⟨f1, g1, e1, _, hx1, hp1⟩ := traced_symBlock exit_b99 exit_b99_ok hcode rfl
          (exit_b99_shape c st mem aw g e o ⟨0⟩ [i,numerator,UInt256.ofNat 17]) h
        rw [withGE_at] at hx1 hp1
        obtain ⟨f2, cost, _, _, hx2, hp2⟩ := traced_jumpi_taken
          (decodeAt_of_code_pc hcode rfl exit_s106) rfl ((feeLoop_exit_iff _).mpr rfl) hx1
        rw [jumpi_taken_at, withGE_at] at hx2 hp2
        exact ⟨0, o, i, f2, _, _, by simp [feeExit], hx2, hp1.trans hp2⟩
      · obtain ⟨rest, gas, count, hf, hnext, hpnext⟩ := traced_exit_cycle c henv ha h
        obtain ⟨n, output, counter, remaining, gas', count', hloop, htail, hptail⟩ :=
          ih rest (by omega) hnext
        exact ⟨n+1, output, counter, remaining, gas', count',
          by simpa only [feeExit, if_neg ha] using hloop, htail, hpnext.trans hptail⟩

/-- Recover the actual user entry prefix and its supported instructions. -/
theorem traced_exit_entry (c : XiCall .exit) {fuel : Nat}
    {final : EVM.State} {out : ByteArray}
    (huser : Exit.callerWord c ≠ sysW)
    (h : X fuel exitJumpdests c.entry = .ok (.success final out)) :
    Exit.excessWord c ≠ INH ∧ ∃ rest gas count,
      X rest exitJumpdests (at_ c (Exit.st₂ c) c.entry.memory c.entry.activeWords gas 99
        [⟨0⟩, UInt256.ofNat 17, UInt256.ofNat 1, Exit.effExcess c, UInt256.ofNat 17] count) =
          .ok (.success final out) ∧
      Segment exitJumpdests fuel c.entry rest
        (at_ c (Exit.st₂ c) c.entry.memory c.entry.activeWords gas 99
          [⟨0⟩, UInt256.ofNat 17, UInt256.ofNat 1, Exit.effExcess c, UInt256.ofNat 17] count) := by
  have hen := (SuccessInversion.exit_user_to_fee_head c huser h).1
  rw [entry_eq_at] at h
  have hcode := Exit.hcode_of_env c (st := entrySt c) rfl
  obtain ⟨f1, g1, e1, _, hx1, hp1⟩ := traced_symBlock (h := h) exit_b0 exit_b0_ok (by exact hcode) rfl
    (exit_b0_shape c (entrySt c) _ _ c.gas 0 [])
  rw [withGE_at] at hx1 hp1
  rw [← entry_eq_at] at hp1
  obtain ⟨f2, cost2, _, _, hx2, hp2⟩ := traced_jumpi_untaken (h := hx1)
    (decodeAt_of_code_pc (st := at_ c (entrySt c) c.entry.memory c.entry.activeWords g1 25 _ e1) (by exact hcode) rfl exit_s25) rfl
    ((eq_eq_zero_iff _ _).mpr (fun he => huser he.symm))
  rw [jumpi_fallthrough_at, withGE_at] at hx2 hp2
  obtain ⟨f3, g3, e3, _, hx3, hp3⟩ := traced_symBlock (h := hx2) exit_b26 exit_b26_ok (by exact hcode) rfl
    (exit_b26_shape c (entrySt c) _ _ _ _ [])
  rw [withGE_at] at hx3 hp3
  refine ⟨hen, ?_⟩
  obtain ⟨f4, cost4, _, _, hx4, hp4⟩ := traced_jumpi_untaken (h := hx3)
    (decodeAt_of_code_pc (st := at_ c (touch (entrySt c) (UInt256.ofNat 0)) c.entry.memory c.entry.activeWords g3 66 _ e3) (by exact hcode) rfl exit_s66) rfl
    ((eq_eq_zero_iff _ _).mpr (fun he => hen he.symm))
  rw [jumpi_fallthrough_at, withGE_at] at hx4 hp4
  obtain ⟨f5, g5, e5, _, hx5, hp5⟩ := traced_symBlock (h := hx4) exit_b67 exit_b67_ok (by exact hcode) rfl
    (exit_b67_shape c _ _ _ _ _ _)
  rw [withGE_at] at hx5 hp5
  simp only [slotW_touch] at hx5 hp5
  by_cases hcount : 2 < (Exit.countWord c).toNat
  · obtain ⟨f6, cost6, _, _, hx6, hp6⟩ := traced_jumpi_taken (h := hx5)
      (decodeAt_of_code_pc (st := at_ c (Exit.st₂ c) c.entry.memory c.entry.activeWords g5 76 _ e5) (by exact hcode) rfl exit_s76) rfl
      ((gt_ne_zero_iff _ _).mpr ((ofNat_lt_iff (by decide) _).mpr hcount))
    rw [jumpi_taken_at, withGE_at] at hx6 hp6
    obtain ⟨f7, g7, e7, _, hx7, hp7⟩ := traced_symBlock (h := hx6) exit_b81 exit_b81_ok (by exact hcode) rfl
      (exit_b81_shape c _ _ _ _ _ _ _ _)
    rw [withGE_at] at hx7 hp7
    obtain ⟨f8, g8, e8, _, hx8, hp8⟩ := traced_symBlock (h := hx7) exit_b87 exit_b87_ok (by exact hcode) rfl
      (exit_b87_shape c _ _ _ _ _ _ _)
    rw [withGE_at] at hx8 hp8
    exact ⟨f8, g8, e8, by simpa only [Exit.effExcess, if_pos hcount, Exit.countWord, Exit.excessWord,
      (show UInt256.ofNat 17 * UInt256.ofNat 1 = UInt256.ofNat 17 from rfl),
      (show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl)] using And.intro hx8 (hp1.trans (hp2.trans (hp3.trans (hp4.trans (hp5.trans (hp6.trans (hp7.trans hp8)))))))⟩
  · obtain ⟨f6, cost6, _, _, hx6, hp6⟩ := traced_jumpi_untaken (h := hx5)
      (decodeAt_of_code_pc (st := at_ c (Exit.st₂ c) c.entry.memory c.entry.activeWords g5 76 _ e5) (by exact hcode) rfl exit_s76) rfl
      ((gt_eq_zero_iff _ _).mpr (fun hh => hcount ((ofNat_lt_iff (by decide) _).mp hh)))
    rw [jumpi_fallthrough_at, withGE_at] at hx6 hp6
    obtain ⟨f7, g7, e7, _, hx7, hp7⟩ := traced_symBlock (h := hx6) exit_b77 exit_b77_ok (by exact hcode) rfl
      (exit_b77_shape c _ _ _ _ _ _ _)
    rw [withGE_at] at hx7 hp7
    obtain ⟨f8, g8, e8, _, hx8, hp8⟩ := traced_symBlock (h := hx7) exit_b87 exit_b87_ok (by exact hcode) rfl
      (exit_b87_shape c _ _ _ _ _ _ _)
    rw [withGE_at] at hx8 hp8
    exact ⟨f8, g8, e8, by simpa only [Exit.effExcess, if_neg hcount, Exit.countWord, Exit.excessWord,
      (show UInt256.ofNat 17 * UInt256.ofNat 1 = UInt256.ofNat 17 from rfl),
      (show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl)] using And.intro hx8 (hp1.trans (hp2.trans (hp3.trans (hp4.trans (hp5.trans (hp6.trans (hp7.trans hp8)))))))⟩


theorem effect_one {fuel : Nat} {vj : Array UInt256}
    {pre shaped final : EVM.State} {out : ByteArray} {op : Operation .EVM}
    {arg : Option (UInt256 × Nat)} (hm : op ∈ allOps) (hn : Halting op = false)
    (hd : decodeAt pre = (op,arg)) (hstep : EvmYul.step op arg pre = .ok shaped)
    (h : X fuel vj pre = .ok (.success final out)) :
    ∃ rest gas count cost, fuel = rest+1 ∧
      XStepAt vj rest cost pre (withGE shaped gas count) ∧
      X rest vj (withGE shaped gas count) = .ok (.success final out) := by
  obtain ⟨rest, cost, mid, post, hf, hz, hs, hactual, htail⟩ := success_continue hd hn h
  cases rest with
  | zero => simp only [X_zero] at htail; contradiction
  | succ rest =>
      have hmid : mid = withGE pre mid.gasAvailable pre.execLength := by
        rw [Z_ok_state hz]
        rfl
      have he : post = withGE shaped (mid.gasAvailable - UInt256.ofNat cost) (pre.execLength+1) := by
        change EvmYul.EVM.step (rest+1) cost (some (op,arg)) mid = .ok post at hs
        rw [EVM_step_eq_step hm, stepPre_eq_withGE, hmid, withGE_withGE,
          step_withGE hm, hstep] at hs
        exact (Except.ok.inj hs).symm
      exact ⟨rest+1, _, _, cost, hf, he ▸ hactual, he ▸ htail⟩

theorem traced_sstore_success {kind : Eip8282.Audit.Model.Kind} {c : XiCall kind}
    {fuel pc : Nat} {vj : Array UInt256} {code : ByteArray}
    {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {key value : UInt256} {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (hop : opcodeAt code pc = some (.SSTORE,none)) (hc : st.executionEnv.code = code)
    (h : X fuel vj (at_ c st mem aw g pc (key::value::stk) e) = .ok (.success final out)) :
    ∃ rest gas count, X rest vj (at_ c (st.sstore key value) mem aw gas (pc+1) stk count) =
      .ok (.success final out) ∧
      Segment vj fuel (at_ c st mem aw g pc (key::value::stk) e) rest (at_ c (st.sstore key value) mem aw gas (pc+1) stk count) := by
  obtain ⟨rest, gas, count, hx, hp⟩ := traced_effect (by decide : Operation.SSTORE ∈ allOps) (by decide)
    (decodeAt_of_code_pc (st := at_ c st mem aw g pc (key::value::stk) e) hc rfl hop)
    (step_SSTORE rfl) h
  rw [toState_replace_at, withGE_at] at hx hp
  exact ⟨rest, gas, count, hx, hp⟩

theorem traced_mstore_success {kind : Eip8282.Audit.Model.Kind} {c : XiCall kind}
    {fuel pc : Nat} {vj : Array UInt256} {code : ByteArray}
    {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {off value : UInt256} {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (hop : opcodeAt code pc = some (.MSTORE,none)) (hc : st.executionEnv.code = code)
    (h : X fuel vj (at_ c st mem aw g pc (off::value::stk) e) = .ok (.success final out)) :
    ∃ rest gas count, X rest vj (at_ c st (mstoreMem mem off value) (mAfter aw off.toNat 32)
      gas (pc+1) stk count) = .ok (.success final out) ∧
      Segment vj fuel (at_ c st mem aw g pc (off::value::stk) e) rest (at_ c st (mstoreMem mem off value) (mAfter aw off.toNat 32)
      gas (pc+1) stk count) := by
  let pre := at_ c st mem aw g pc (off::value::stk) e
  obtain ⟨rest, gas, count, hx, hp⟩ := traced_effect (by decide : Operation.MSTORE ∈ allOps) (by decide)
    (decodeAt_of_code_pc (st := pre) hc rfl hop) (step_MSTORE rfl) h
  have he : withGE (({ pre with toMachineState := pre.toMachineState.mstore off value } :
      EVM.State).replaceStackAndIncrPC stk) gas count =
      at_ c st (mstoreMem mem off value) (mAfter aw off.toNat 32) gas (pc+1) stk count :=
    withGE_machine_replace_at c st mem aw g pc (off::value::stk) stk e _ _ _ rfl rfl
  rw [he] at hx hp
  exact ⟨rest, gas, count, hx, hp⟩

theorem traced_copy_success {kind : Eip8282.Audit.Model.Kind} {c : XiCall kind}
    {fuel pc : Nat} {vj : Array UInt256} {code : ByteArray}
    {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {dst src len : UInt256} {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (hop : opcodeAt code pc = some (.CALLDATACOPY,none)) (hc : st.executionEnv.code = code)
    (h : X fuel vj (at_ c st mem aw g pc (dst::src::len::stk) e) = .ok (.success final out)) :
    ∃ rest gas count, X rest vj (at_ c st (cdcopyMem st mem dst src len)
      (mAfter aw dst.toNat len.toNat) gas (pc+1) stk count) = .ok (.success final out) ∧
      Segment vj fuel (at_ c st mem aw g pc (dst::src::len::stk) e) rest (at_ c st (cdcopyMem st mem dst src len)
      (mAfter aw dst.toNat len.toNat) gas (pc+1) stk count) := by
  let pre := at_ c st mem aw g pc (dst::src::len::stk) e
  obtain ⟨rest, gas, count, hx, hp⟩ := traced_effect (by decide : Operation.CALLDATACOPY ∈ allOps) (by decide)
    (decodeAt_of_code_pc (st := pre) hc rfl hop) (step_CALLDATACOPY rfl) h
  have he : withGE (({ pre with toSharedState := pre.toSharedState.calldatacopy dst src len } :
      EVM.State).replaceStackAndIncrPC stk) gas count =
      at_ c st (cdcopyMem st mem dst src len) (mAfter aw dst.toNat len.toNat) gas (pc+1) stk count :=
    withGE_shared_replace_at c st mem aw g pc (dst::src::len::stk) stk e _ _ _ rfl rfl
  rw [he] at hx hp
  exact ⟨rest, gas, count, hx, hp⟩

theorem log_one {kind : Eip8282.Audit.Model.Kind} {c : XiCall kind}
    {fuel pc : Nat} {vj : Array UInt256} {code : ByteArray}
    {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {off len : UInt256} {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (hop : opcodeAt code pc = some (.LOG0,none)) (hc : st.executionEnv.code = code)
    (h : X fuel vj (at_ c st mem aw g pc (off::len::stk) e) = .ok (.success final out)) :
    ∃ rest gas count cost, fuel = rest+1 ∧
      XStepAt vj rest cost (at_ c st mem aw g pc (off::len::stk) e) (at_ c (logged st (mem.readWithPadding off.toNat len.toNat)) mem
      (mAfter aw off.toNat len.toNat) gas (pc+1) stk count) ∧
      X rest vj (at_ c (logged st (mem.readWithPadding off.toNat len.toNat)) mem
      (mAfter aw off.toNat len.toNat) gas (pc+1) stk count) = .ok (.success final out) := by
  let pre := at_ c st mem aw g pc (off::len::stk) e
  obtain ⟨rest, gas, count, cost, hf, hp, hx⟩ := effect_one (by decide : Operation.LOG0 ∈ allOps) (by decide)
    (decodeAt_of_code_pc (st := pre) hc rfl hop) (step_LOG0 rfl) h
  have he : withGE (({ pre with toSharedState := SharedState.logOp off len #[] pre.toSharedState } :
      EVM.State).replaceStackAndIncrPC stk) gas count =
      at_ c (logged st (mem.readWithPadding off.toNat len.toNat)) mem
        (mAfter aw off.toNat len.toNat) gas (pc+1) stk count :=
    withGE_shared_replace_at c st mem aw g pc (off::len::stk) stk e _ _ _ rfl rfl
  rw [he] at hx hp
  exact ⟨rest, gas, count, cost, hf, hp, hx⟩

/-- A LOG0 inside an actual supported path, using the evaluator's relations. -/
def ThroughLog (vj : Array UInt256) (fuel : Nat) (start : EVM.State) (len : UInt256) : Prop :=
  ∃ atLog afterLog finish fLog fFinish cost off stk,
    Segment vj fuel start (fLog+1) atLog ∧ decodeAt atLog = (.LOG0,none) ∧
    atLog.stack = off :: len :: stk ∧ XStepAt vj fLog cost atLog afterLog ∧
    Segment vj fLog afterLog fFinish finish ∧ (decodeAt finish).1 ∈ allOps ∧
    Halting (decodeAt finish).1 = true

theorem ThroughLog.prepend {vj : Array UInt256} {fuel rest : Nat} {pre mid : EVM.State}
    {len : UInt256} (hp : Segment vj fuel pre rest mid) (hl : ThroughLog vj rest mid len) :
    ThroughLog vj fuel pre len := by
  obtain ⟨atLog, afterLog, finish, fLog, fFinish, cost, off, stk, hb, hd, hs, hm, ha, ho, hh⟩ := hl
  exact ⟨atLog, afterLog, finish, fLog, fFinish, cost, off, stk, hp.trans hb, hd, hs, hm, ha, ho, hh⟩

theorem ThroughLog.toLogPath {kind : Eip8282.Audit.Model.Kind} (q : XiCall kind) (len : UInt256)
    (h : ThroughLog (Eip8282.Audit.XiTransport.jumpdestsOf kind) q.fuel q.entry len) : LogPath q len := by
  obtain ⟨atLog, afterLog, finish, fLog, fFinish, cost, off, stk, ⟨bt,hb,hsb⟩, hd, hs, hm,
    ⟨aft,ha,hsa⟩, ho, hh⟩ := h
  exact ⟨atLog,afterLog,finish,fLog,fFinish,cost,bt,aft,off,stk,hb,hsb,hd,hs,hm,ha,hsa,ho,hh⟩


/-- Locate the actual 68-byte LOG0 and follow its continuation to STOP. -/
theorem exit_suffix_path (c : XiCall .exit)
    {fuel : Nat} {aw g : UInt256} {e : Nat} {final : EVM.State} {out : ByteArray}
    (h : X fuel exitJumpdests
      (at_ c (Exit.st₂ c) (Exit.mem₀ c) aw g 165 [] e) = .ok (.success final out)) :
    ThroughLog exitJumpdests fuel (at_ c (Exit.st₂ c) (Exit.mem₀ c) aw g 165 [] e)
      (UInt256.ofNat 68) := by
  obtain ⟨f1, g1, e1, _, hx1, hp1⟩ := traced_symBlock (h := h) exit_b165 exit_b165_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b165_shape c (Exit.st₂ c) _ _ _ _ [])
  rw [withGE_at] at hx1 hp1
  simp only [slotW_touch] at hx1 hp1
  obtain ⟨f2, g2, e2, hx2, hp2⟩ := traced_sstore_success exit_s173 (Exit.hcode_of_env c (by append_env)) hx1
  obtain ⟨f3, g3, e3, _, hx3, hp3⟩ := traced_symBlock (h := hx2) exit_b174 exit_b174_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b174_shape c (Exit.countStore c) _ _ _ _ [])
  rw [withGE_at] at hx3 hp3
  simp only [callerW_touch, callerW_sstore] at hx3 hp3
  obtain ⟨f4, g4, e4, hx4, hp4⟩ := traced_sstore_success exit_s186 (Exit.hcode_of_env c (by append_env)) hx3
  obtain ⟨f5, g5, e5, _, hx5, hp5⟩ := traced_symBlock (h := hx4) exit_b187 exit_b187_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b187_shape c _ _ _ _ _ (Exit.slotBase c) [Exit.tailWord c])
  rw [withGE_at] at hx5 hp5
  simp only [cdW_touch, cdW_sstore] at hx5 hp5
  obtain ⟨f6, g6, e6, hx6, hp6⟩ := traced_sstore_success exit_s193 (Exit.hcode_of_env c (by append_env)) hx5
  obtain ⟨f7, g7, e7, _, hx7, hp7⟩ := traced_symBlock (h := hx6) exit_b194 exit_b194_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b194_shape c _ _ _ _ _ _ [Exit.tailWord c])
  rw [withGE_at] at hx7 hp7
  simp only [cdW_touch, cdW_sstore] at hx7 hp7
  obtain ⟨f8, g8, e8, hx8, hp8⟩ := traced_sstore_success exit_s201 (Exit.hcode_of_env c (by append_env)) hx7
  obtain ⟨f9, g9, e9, _, hx9, hp9⟩ := traced_symBlock (h := hx8) exit_b202 exit_b202_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b202_shape c (Exit.itemStored c) _ _ _ _ [Exit.tailWord c])
  rw [withGE_at] at hx9 hp9
  simp only [callerW_touch, callerW_sstore] at hx9 hp9
  obtain ⟨f10, g10, e10, hx10, hp10⟩ := traced_mstore_success exit_s207 (Exit.hcode_of_env c (by append_env)) hx9
  obtain ⟨f11, g11, e11, _, hx11, hp11⟩ := traced_symBlock (h := hx10) exit_b208 exit_b208_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b208_shape c (Exit.itemStored c) _ _ _ _ [Exit.tailWord c])
  rw [withGE_at] at hx11 hp11
  obtain ⟨f12, g12, e12, hx12, hp12⟩ := traced_copy_success exit_s213 (Exit.hcode_of_env c (by append_env)) hx11
  obtain ⟨f13, g13, e13, _, hx13, hp13⟩ := traced_symBlock (h := hx12) exit_b214 exit_b214_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b214_shape c (Exit.itemStored c) _ _ _ _ [Exit.tailWord c])
  rw [withGE_at] at hx13 hp13
  obtain ⟨f14, g14, e14, cost14, hf14, hstep14, hx14⟩ := log_one exit_s217 (Exit.hcode_of_env c (by append_env)) hx13
  obtain ⟨f15, g15, e15, _, hx15, hp15⟩ := traced_symBlock (h := hx14) exit_b218 exit_b218_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b218_shape c _ _ _ _ _ (Exit.tailWord c) [])
  rw [withGE_at] at hx15 hp15
  obtain ⟨f16, g16, e16, hx16, hp16⟩ := traced_sstore_success exit_s223 (Exit.hcode_of_env c (by append_env)) hx15
  refine ⟨_, _, _, f14, f16, cost14, _, _, ?_, ?_, rfl, hstep14,
    hp15.trans hp16, ?_, ?_⟩
  · have hp := hp1.trans (hp2.trans (hp3.trans (hp4.trans (hp5.trans (hp6.trans
      (hp7.trans (hp8.trans (hp9.trans (hp10.trans (hp11.trans (hp12.trans hp13)))))))))))
    rw [hf14] at hp
    exact hp
  · exact decodeAt_of_code_pc (Exit.hcode_of_env c (by append_env)) rfl exit_s217
  · rw [decodeAt_of_code_pc (Exit.hcode_of_env c (by append_env)) rfl exit_s224]
    decide
  · rw [decodeAt_of_code_pc (Exit.hcode_of_env c (by append_env)) rfl exit_s224]
    decide


theorem traced_exit_guard (c : XiCall .exit)
    {fuel pc : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {cond : UInt256} {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (henv : st.executionEnv = c.env)
    (hop : opcodeAt exitRuntime pc = some (.JUMPI, none))
    (h : X fuel exitJumpdests
      (at_ c st mem aw g pc (UInt256.ofNat 454 :: cond :: stk) e) = .ok (.success final out)) :
    cond = ⟨0⟩ ∧ ∃ rest gas count,
      X rest exitJumpdests (at_ c st mem aw gas (pc+1) stk count) = .ok (.success final out) ∧
      Segment exitJumpdests fuel
        (at_ c st mem aw g pc (UInt256.ofNat 454 :: cond :: stk) e)
        rest (at_ c st mem aw gas (pc+1) stk count) := by
  have hc := (AdmissionInversion.exit_guard c henv hop h).1
  have hd := decodeAt_of_code_pc
    (st := at_ c st mem aw g pc (UInt256.ofNat 454 :: cond :: stk) e)
    (Exit.hcode_of_env c henv) rfl hop
  obtain ⟨rest, cost, _, _, hx, hp⟩ := traced_jumpi_untaken hd rfl hc h
  rw [jumpi_fallthrough_at, withGE_at] at hx hp
  exact ⟨hc, rest, _, _, hx, hp⟩


theorem exit_user_path (c : XiCall .exit)
    {fuel : Nat} {final : EVM.State} {out : ByteArray}
    (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hsize : c.env.calldata.size = 48)
    (hx : X fuel exitJumpdests c.entry = .ok (.success final out)) :
    ThroughLog exitJumpdests fuel c.entry (UInt256.ofNat 68) := by
  have hu : Exit.callerWord c ≠ sysW := by
    intro he
    exact huser ((callerW_eq_sysW_iff c).mp he)
  obtain ⟨_, _, _, _, hhead, phead⟩ := traced_exit_entry c hu hx
  obtain ⟨n, output, counter, remaining, gas, count, hloop, htail, ptail⟩ := traced_exit_fee c rfl hhead
  have hc := Exit.hcode_of_env c (st := Exit.st₂ c) rfl
  obtain ⟨f1, g1, e1, _, hx1, hp1⟩ := traced_symBlock (h := htail) exit_b126 exit_b126_ok
    (by exact hc) rfl (exit_b126_shape c _ _ _ _ _ _ _ _ _ _ [])
  rw [withGE_at] at hx1 hp1
  have hs : Exit.cdsizeWord c = UInt256.ofNat 48 := by
    change UInt256.ofNat c.env.calldata.size = _
    rw [hsize]
  obtain ⟨f2, cost2, _, _, hx2, hp2⟩ := traced_jumpi_taken
    (decodeAt_of_code_pc (st := at_ c (Exit.st₂ c) c.entry.memory c.entry.activeWords g1 141 _ e1)
      (by exact hc) rfl exit_s141) rfl ((eq_ne_zero_iff _ _).mpr hs.symm) hx1
  rw [jumpi_taken_at, withGE_at] at hx2 hp2
  obtain ⟨f3, g3, e3, _, hx3, hp3⟩ := traced_symBlock (h := hx2) exit_b158 exit_b158_ok
    (by exact hc) rfl (exit_b158_shape c _ _ _ _ _ _ _)
  rw [withGE_at] at hx3 hp3
  obtain ⟨_, _, _, _, hwrite, pwrite⟩ := traced_exit_guard c rfl exit_s164 hx3
  exact (exit_suffix_path c hwrite).prepend
    (phead.trans (ptail.trans (hp1.trans (hp2.trans (hp3.trans pwrite)))))


/-- Every successful user exit append has a genuine supported LOG0 path. -/
theorem exit_log_path (q : XiCall .exit)
    (huser : q.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hsize : q.env.calldata.size = 48)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : q.result = .ok (.success (created,world,gas,substate) out)) :
    LogPath q (UInt256.ofNat 68) := by
  obtain ⟨final, _, hx⟩ := xi_success_X q h
  exact ThroughLog.toLogPath q _ (exit_user_path q huser hsize hx)

/-- Actual Theta exit append debit, with no supplied path or resource bound. -/
theorem exit_theta_debit (c : MessageCall.Context)
    (hcode : c.code = Eip8282.Audit.Correspondence.runtimeCode .exit)
    (huser : c.caller ≠ Eip8282.Audit.EvmRunner.sysAddr) (hsize : c.calldata.size = 48)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,true,out)) :
    gas.toNat + 919 ≤ c.gas.toNat := by
  have hf : c.fuel = (c.fuel-1)+1 := by
    have hp := SuccessfulQuote.positive_fuel c h
    omega
  obtain ⟨ew, es, he, _, _⟩ := CallSuccess.codeCall_of_success c hcode (c.fuel-1) hf h
  have hp := exit_log_path (CallBridge.codeCall c hcode (c.fuel-1)) huser hsize he
  exact theta_log_debit c hcode (UInt256.ofNat 68) hp h

#print axioms traced_symBlock
#print axioms traced_exit_fee
#print axioms traced_exit_entry
#print axioms exit_suffix_path
#print axioms exit_log_path
#print axioms exit_theta_debit




/-- Actual nonzero deposit fee iteration, with its complete supported segment. -/
theorem traced_deposit_cycle (c : XiCall .deposit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {o a i numerator : UInt256} {final : EVM.State} {out : ByteArray}
    (henv : st.executionEnv = c.env) (ha : a ≠ ⟨0⟩)
    (h : X fuel depositJumpdests
      (at_ c st mem aw g 100 [o,a,i,numerator,UInt256.ofNat 17] e) =
        .ok (.success final out)) :
    ∃ rest gas count, fuel = rest+24 ∧
      X rest depositJumpdests (at_ c st mem aw gas 100
        [a+o, (numerator*a)/(i*UInt256.ofNat 17), UInt256.ofNat 1+i,
          numerator, UInt256.ofNat 17] count) = .ok (.success final out) ∧
      Segment depositJumpdests fuel (at_ c st mem aw g 100
        [o,a,i,numerator,UInt256.ofNat 17] e) rest (at_ c st mem aw gas 100
        [a+o, (numerator*a)/(i*UInt256.ofNat 17), UInt256.ofNat 1+i,
          numerator, UInt256.ofNat 17] count) := by
  have hcode := Deposit.hcode_of_env c henv
  obtain ⟨f1, g1, e1, hf1, hx1, hp1⟩ := traced_symBlock deposit_b100 deposit_b100_ok
    hcode rfl (deposit_b100_shape c st mem aw g e o a [i,numerator,UInt256.ofNat 17]) h
  rw [withGE_at] at hx1 hp1
  obtain ⟨f2, cost, hf2, _, hx2, hp2⟩ := traced_jumpi_untaken
    (decodeAt_of_code_pc hcode rfl deposit_s107) rfl ((feeLoop_continue_iff a).mpr ha) hx1
  rw [jumpi_fallthrough_at, withGE_at] at hx2 hp2
  obtain ⟨f3, g3, e3, hf3, hx3, hp3⟩ := traced_symBlock deposit_b108 deposit_b108_ok
    hcode rfl (deposit_b108_shape c st mem aw _ _ o a i numerator (UInt256.ofNat 17) []) hx2
  rw [withGE_at] at hx3 hp3
  exact ⟨f3, g3, e3, by
    change fuel = f1+6 at hf1
    change f2 = f3+17 at hf3
    omega, hx3, hp1.trans (hp2.trans hp3)⟩

/-- Actual-fuel induction retains the deposit fee-loop path without a cutoff. -/
theorem traced_deposit_fee (c : XiCall .deposit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {o a i numerator : UInt256} {final : EVM.State} {out : ByteArray}
    (henv : st.executionEnv = c.env)
    (h : X fuel depositJumpdests
      (at_ c st mem aw g 100 [o,a,i,numerator,UInt256.ofNat 17] e) =
        .ok (.success final out)) :
    ∃ n output counter rest gas count,
      feeExit numerator n o a i = some (output,counter) ∧
      X rest depositJumpdests (at_ c st mem aw gas 127
        [output,⟨0⟩,counter,numerator,UInt256.ofNat 17] count) = .ok (.success final out) ∧
      Segment depositJumpdests fuel (at_ c st mem aw g 100
        [o,a,i,numerator,UInt256.ofNat 17] e) rest (at_ c st mem aw gas 127
        [output,⟨0⟩,counter,numerator,UInt256.ofNat 17] count) := by
  induction fuel using Nat.strong_induction_on generalizing o a i g e with
  | h fuel ih =>
      by_cases ha : a = ⟨0⟩
      · subst a
        have hcode := Deposit.hcode_of_env c henv
        obtain ⟨f1, g1, e1, _, hx1, hp1⟩ := traced_symBlock deposit_b100 deposit_b100_ok hcode rfl
          (deposit_b100_shape c st mem aw g e o ⟨0⟩ [i,numerator,UInt256.ofNat 17]) h
        rw [withGE_at] at hx1 hp1
        obtain ⟨f2, cost, _, _, hx2, hp2⟩ := traced_jumpi_taken
          (decodeAt_of_code_pc hcode rfl deposit_s107) rfl ((feeLoop_exit_iff _).mpr rfl) hx1
        rw [jumpi_taken_at, withGE_at] at hx2 hp2
        exact ⟨0, o, i, f2, _, _, by simp [feeExit], hx2, hp1.trans hp2⟩
      · obtain ⟨rest, gas, count, hf, hnext, hpnext⟩ := traced_deposit_cycle c henv ha h
        obtain ⟨n, output, counter, remaining, gas', count', hloop, htail, hptail⟩ :=
          ih rest (by omega) hnext
        exact ⟨n+1, output, counter, remaining, gas', count',
          by simpa only [feeExit, if_neg ha] using hloop, htail, hpnext.trans hptail⟩

/-- Recover the actual deposit user entry prefix and supported instructions. -/
theorem traced_deposit_entry (c : XiCall .deposit) {fuel : Nat}
    {final : EVM.State} {out : ByteArray}
    (huser : Deposit.callerWord c ≠ sysW)
    (h : X fuel depositJumpdests c.entry = .ok (.success final out)) :
    Deposit.excessWord c ≠ INH ∧ ∃ rest gas count,
      X rest depositJumpdests (at_ c (Deposit.st₂ c) c.entry.memory c.entry.activeWords gas 100
        [⟨0⟩, UInt256.ofNat 17, UInt256.ofNat 1, Deposit.effExcess c, UInt256.ofNat 17] count) =
          .ok (.success final out) ∧
      Segment depositJumpdests fuel c.entry rest
        (at_ c (Deposit.st₂ c) c.entry.memory c.entry.activeWords gas 100
          [⟨0⟩, UInt256.ofNat 17, UInt256.ofNat 1, Deposit.effExcess c, UInt256.ofNat 17] count) := by
  have hen := (SuccessInversion.deposit_user_to_fee_head c huser h).1
  rw [entry_eq_at] at h
  have hcode := Deposit.hcode_of_env c (st := entrySt c) rfl
  obtain ⟨f1, g1, e1, _, hx1, hp1⟩ := traced_symBlock (h := h) deposit_b0 deposit_b0_ok (by exact hcode) rfl
    (deposit_b0_shape c (entrySt c) _ _ c.gas 0 [])
  rw [withGE_at] at hx1 hp1
  rw [← entry_eq_at] at hp1
  obtain ⟨f2, cost2, _, _, hx2, hp2⟩ := traced_jumpi_untaken (h := hx1)
    (decodeAt_of_code_pc (st := at_ c (entrySt c) c.entry.memory c.entry.activeWords g1 26 _ e1) (by exact hcode) rfl deposit_s26) rfl
    ((eq_eq_zero_iff _ _).mpr (fun he => huser he.symm))
  rw [jumpi_fallthrough_at, withGE_at] at hx2 hp2
  obtain ⟨f3, g3, e3, _, hx3, hp3⟩ := traced_symBlock (h := hx2) deposit_b27 deposit_b27_ok (by exact hcode) rfl
    (deposit_b27_shape c (entrySt c) _ _ _ _ [])
  rw [withGE_at] at hx3 hp3
  refine ⟨hen, ?_⟩
  obtain ⟨f4, cost4, _, _, hx4, hp4⟩ := traced_jumpi_untaken (h := hx3)
    (decodeAt_of_code_pc (st := at_ c (touch (entrySt c) (UInt256.ofNat 0)) c.entry.memory c.entry.activeWords g3 67 _ e3) (by exact hcode) rfl deposit_s67) rfl
    ((eq_eq_zero_iff _ _).mpr (fun he => hen he.symm))
  rw [jumpi_fallthrough_at, withGE_at] at hx4 hp4
  obtain ⟨f5, g5, e5, _, hx5, hp5⟩ := traced_symBlock (h := hx4) deposit_b68 deposit_b68_ok (by exact hcode) rfl
    (deposit_b68_shape c _ _ _ _ _ _)
  rw [withGE_at] at hx5 hp5
  simp only [slotW_touch] at hx5 hp5
  by_cases hcount : 8 < (Deposit.countWord c).toNat
  · obtain ⟨f6, cost6, _, _, hx6, hp6⟩ := traced_jumpi_taken (h := hx5)
      (decodeAt_of_code_pc (st := at_ c (Deposit.st₂ c) c.entry.memory c.entry.activeWords g5 77 _ e5) (by exact hcode) rfl deposit_s77) rfl
      ((gt_ne_zero_iff _ _).mpr ((ofNat_lt_iff (by decide) _).mpr hcount))
    rw [jumpi_taken_at, withGE_at] at hx6 hp6
    obtain ⟨f7, g7, e7, _, hx7, hp7⟩ := traced_symBlock (h := hx6) deposit_b82 deposit_b82_ok (by exact hcode) rfl
      (deposit_b82_shape c _ _ _ _ _ _ _ _)
    rw [withGE_at] at hx7 hp7
    obtain ⟨f8, g8, e8, _, hx8, hp8⟩ := traced_symBlock (h := hx7) deposit_b88 deposit_b88_ok (by exact hcode) rfl
      (deposit_b88_shape c _ _ _ _ _ _ _)
    rw [withGE_at] at hx8 hp8
    exact ⟨f8, g8, e8, by simpa only [Deposit.effExcess, if_pos hcount, Deposit.countWord, Deposit.excessWord,
      (show UInt256.ofNat 17 * UInt256.ofNat 1 = UInt256.ofNat 17 from rfl),
      (show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl)] using And.intro hx8 (hp1.trans (hp2.trans (hp3.trans (hp4.trans (hp5.trans (hp6.trans (hp7.trans hp8)))))))⟩
  · obtain ⟨f6, cost6, _, _, hx6, hp6⟩ := traced_jumpi_untaken (h := hx5)
      (decodeAt_of_code_pc (st := at_ c (Deposit.st₂ c) c.entry.memory c.entry.activeWords g5 77 _ e5) (by exact hcode) rfl deposit_s77) rfl
      ((gt_eq_zero_iff _ _).mpr (fun hh => hcount ((ofNat_lt_iff (by decide) _).mp hh)))
    rw [jumpi_fallthrough_at, withGE_at] at hx6 hp6
    obtain ⟨f7, g7, e7, _, hx7, hp7⟩ := traced_symBlock (h := hx6) deposit_b78 deposit_b78_ok (by exact hcode) rfl
      (deposit_b78_shape c _ _ _ _ _ _ _)
    rw [withGE_at] at hx7 hp7
    obtain ⟨f8, g8, e8, _, hx8, hp8⟩ := traced_symBlock (h := hx7) deposit_b88 deposit_b88_ok (by exact hcode) rfl
      (deposit_b88_shape c _ _ _ _ _ _ _)
    rw [withGE_at] at hx8 hp8
    exact ⟨f8, g8, e8, by simpa only [Deposit.effExcess, if_neg hcount, Deposit.countWord, Deposit.excessWord,
      (show UInt256.ofNat 17 * UInt256.ofNat 1 = UInt256.ofNat 17 from rfl),
      (show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl)] using And.intro hx8 (hp1.trans (hp2.trans (hp3.trans (hp4.trans (hp5.trans (hp6.trans (hp7.trans hp8)))))))⟩

/-- Locate the actual 184-byte LOG0 and follow its continuation to STOP. -/
theorem deposit_suffix_path (c : XiCall .deposit)
    {fuel : Nat} {aw g : UInt256} {e : Nat} {final : EVM.State} {out : ByteArray}
    (h : X fuel depositJumpdests
      (at_ c (Deposit.st₂ c) (Deposit.mem₀ c) aw g 205 [] e) = .ok (.success final out)) :
    ThroughLog depositJumpdests fuel (at_ c (Deposit.st₂ c) (Deposit.mem₀ c) aw g 205 [] e)
      (UInt256.ofNat 184) := by
  obtain ⟨f1, g1, e1, _, hx1, hp1⟩ := traced_symBlock (h := h) deposit_b205 deposit_b205_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b205_shape c (Deposit.st₂ c) _ _ _ _ [])
  rw [withGE_at] at hx1 hp1
  simp only [slotW_touch] at hx1 hp1
  obtain ⟨f2, g2, e2, hx2, hp2⟩ := traced_sstore_success deposit_s213 (Deposit.hcode_of_env c (by append_env)) hx1
  obtain ⟨f3, g3, e3, _, hx3, hp3⟩ := traced_symBlock (h := hx2) deposit_b214 deposit_b214_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b214_shape c (Deposit.countStore c) _ _ _ _ [])
  rw [withGE_at] at hx3 hp3
  simp only [cdW_touch, cdW_sstore] at hx3 hp3
  obtain ⟨f4, g4, e4, hx4, hp4⟩ := traced_sstore_success deposit_s227 (Deposit.hcode_of_env c (by append_env)) hx3
  obtain ⟨f5, g5, e5, _, hx5, hp5⟩ := traced_symBlock (h := hx4) deposit_b228 deposit_b228_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b228_shape c _ _ _ _ _ (Deposit.slotBase c) [Deposit.tailWord c])
  rw [withGE_at] at hx5 hp5
  simp only [cdW_touch, cdW_sstore] at hx5 hp5
  obtain ⟨f6, g6, e6, hx6, hp6⟩ := traced_sstore_success deposit_s235 (Deposit.hcode_of_env c (by append_env)) hx5
  obtain ⟨f7, g7, e7, _, hx7, hp7⟩ := traced_symBlock (h := hx6) deposit_b236 deposit_b236_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b236_shape c _ _ _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx7 hp7
  simp only [cdW_touch, cdW_sstore] at hx7 hp7
  obtain ⟨f8, g8, e8, hx8, hp8⟩ := traced_sstore_success deposit_s243 (Deposit.hcode_of_env c (by append_env)) hx7
  obtain ⟨f9, g9, e9, _, hx9, hp9⟩ := traced_symBlock (h := hx8) deposit_b244 deposit_b244_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b244_shape c _ _ _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx9 hp9
  simp only [cdW_touch, cdW_sstore] at hx9 hp9
  obtain ⟨f10, g10, e10, hx10, hp10⟩ := traced_sstore_success deposit_s251 (Deposit.hcode_of_env c (by append_env)) hx9
  obtain ⟨f11, g11, e11, _, hx11, hp11⟩ := traced_symBlock (h := hx10) deposit_b252 deposit_b252_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b252_shape c _ _ _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx11 hp11
  simp only [cdW_touch, cdW_sstore] at hx11 hp11
  obtain ⟨f12, g12, e12, hx12, hp12⟩ := traced_sstore_success deposit_s259 (Deposit.hcode_of_env c (by append_env)) hx11
  obtain ⟨f13, g13, e13, _, hx13, hp13⟩ := traced_symBlock (h := hx12) deposit_b260 deposit_b260_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b260_shape c _ _ _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx13 hp13
  simp only [cdW_touch, cdW_sstore] at hx13 hp13
  obtain ⟨f14, g14, e14, hx14, hp14⟩ := traced_sstore_success deposit_s267 (Deposit.hcode_of_env c (by append_env)) hx13
  obtain ⟨f15, g15, e15, _, hx15, hp15⟩ := traced_symBlock (h := hx14) deposit_b268 deposit_b268_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b268_shape c (Deposit.itemStored c) _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx15 hp15
  obtain ⟨f16, g16, e16, hx16, hp16⟩ := traced_copy_success deposit_s272 (Deposit.hcode_of_env c (by append_env)) hx15
  obtain ⟨f17, g17, e17, _, hx17, hp17⟩ := traced_symBlock (h := hx16) deposit_b273 deposit_b273_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b273_shape c (Deposit.itemStored c) _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx17 hp17
  obtain ⟨f18, g18, e18, cost18, hf18, hstep18, hx18⟩ := log_one deposit_s276 (Deposit.hcode_of_env c (by append_env)) hx17
  obtain ⟨f19, g19, e19, _, hx19, hp19⟩ := traced_symBlock (h := hx18) deposit_b277 deposit_b277_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b277_shape c _ _ _ _ _ (Deposit.tailWord c) [])
  rw [withGE_at] at hx19 hp19
  obtain ⟨f20, g20, e20, hx20, hp20⟩ := traced_sstore_success deposit_s282 (Deposit.hcode_of_env c (by append_env)) hx19
  refine ⟨_, _, _, f18, f20, cost18, _, _, ?_, ?_, rfl, hstep18,
    hp19.trans hp20, ?_, ?_⟩
  · have hp := hp1.trans (hp2.trans (hp3.trans (hp4.trans (hp5.trans (hp6.trans (hp7.trans (hp8.trans (hp9.trans (hp10.trans (hp11.trans (hp12.trans (hp13.trans (hp14.trans (hp15.trans (hp16.trans (hp17))))))))))))))))
    rw [hf18] at hp
    exact hp
  · exact decodeAt_of_code_pc (Deposit.hcode_of_env c (by append_env)) rfl deposit_s276
  · rw [decodeAt_of_code_pc (Deposit.hcode_of_env c (by append_env)) rfl deposit_s283]
    decide
  · rw [decodeAt_of_code_pc (Deposit.hcode_of_env c (by append_env)) rfl deposit_s283]
    decide


theorem traced_deposit_guard (c : XiCall .deposit)
    {fuel pc : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {cond : UInt256} {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (henv : st.executionEnv = c.env)
    (hop : opcodeAt depositRuntime pc = some (.JUMPI, none))
    (h : X fuel depositJumpdests
      (at_ c st mem aw g pc (UInt256.ofNat 624 :: cond :: stk) e) = .ok (.success final out)) :
    cond = ⟨0⟩ ∧ ∃ rest gas count,
      X rest depositJumpdests (at_ c st mem aw gas (pc+1) stk count) = .ok (.success final out) ∧
      Segment depositJumpdests fuel
        (at_ c st mem aw g pc (UInt256.ofNat 624 :: cond :: stk) e)
        rest (at_ c st mem aw gas (pc+1) stk count) := by
  have hc := (AdmissionInversion.deposit_guard c henv hop h).1
  have hd := decodeAt_of_code_pc
    (st := at_ c st mem aw g pc (UInt256.ofNat 624 :: cond :: stk) e)
    (Deposit.hcode_of_env c henv) rfl hop
  obtain ⟨rest, cost, _, _, hx, hp⟩ := traced_jumpi_untaken hd rfl hc h
  rw [jumpi_fallthrough_at, withGE_at] at hx hp
  exact ⟨hc, rest, _, _, hx, hp⟩

theorem deposit_user_path (c : XiCall .deposit)
    {fuel : Nat} {final : EVM.State} {out : ByteArray}
    (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hsize : c.env.calldata.size = 184)
    (hx : X fuel depositJumpdests c.entry = .ok (.success final out)) :
    ThroughLog depositJumpdests fuel c.entry (UInt256.ofNat 184) := by
  have hu : Deposit.callerWord c ≠ sysW := by
    intro he
    exact huser ((callerW_eq_sysW_iff c).mp he)
  obtain ⟨_, _, _, _, hhead, phead⟩ := traced_deposit_entry c hu hx
  obtain ⟨n, output, counter, remaining, gas, count, hloop, htail, ptail⟩ := traced_deposit_fee c rfl hhead
  have hc := Deposit.hcode_of_env c (st := Deposit.st₂ c) rfl
  obtain ⟨f1, g1, e1, _, hx1, hp1⟩ := traced_symBlock (h := htail) deposit_b127 deposit_b127_ok
    (by exact hc) rfl (deposit_b127_shape c _ _ _ _ _ _ _ _ _ _ [])
  rw [withGE_at] at hx1 hp1
  have hs : Deposit.cdsizeWord c = UInt256.ofNat 184 := by
    change UInt256.ofNat c.env.calldata.size = _
    rw [hsize]
  obtain ⟨f2, cost2, _, _, hx2, hp2⟩ := traced_jumpi_taken
    (decodeAt_of_code_pc (st := at_ c (Deposit.st₂ c) c.entry.memory c.entry.activeWords g1 142 _ e1)
      (by exact hc) rfl deposit_s142) rfl ((eq_ne_zero_iff _ _).mpr hs.symm) hx1
  rw [jumpi_taken_at, withGE_at] at hx2 hp2
  obtain ⟨f3, g3, e3, _, hx3, hp3⟩ := traced_symBlock (h := hx2) deposit_b159 deposit_b159_ok
    (by exact hc) rfl (deposit_b159_shape c _ _ _ _ _ _ _)
  rw [withGE_at] at hx3 hp3
  obtain ⟨_, f4, g4, e4, hx4, hp4⟩ := traced_deposit_guard c rfl deposit_s166 hx3
  obtain ⟨f5, g5, e5, _, hx5, hp5⟩ := traced_symBlock (h := hx4) deposit_b167 deposit_b167_ok
    (by exact hc) rfl (deposit_b167_shape c _ _ _ _ _ _)
  rw [withGE_at] at hx5 hp5
  obtain ⟨_, f6, g6, e6, hx6, hp6⟩ := traced_deposit_guard c rfl deposit_s190 hx5
  obtain ⟨f7, g7, e7, _, hx7, hp7⟩ := traced_symBlock (h := hx6) deposit_b191 deposit_b191_ok
    (by exact hc) rfl (deposit_b191_shape c _ _ _ _ _ _ _ _)
  rw [withGE_at] at hx7 hp7
  obtain ⟨_, _, _, _, hwrite, pwrite⟩ := traced_deposit_guard c rfl deposit_s204 hx7
  exact (deposit_suffix_path c hwrite).prepend
    (phead.trans (ptail.trans (hp1.trans (hp2.trans (hp3.trans
      (hp4.trans (hp5.trans (hp6.trans (hp7.trans pwrite)))))))))


/-- Every successful user deposit append supplies its actual supported LOG0 path. -/
theorem deposit_log_path (q : XiCall .deposit)
    (huser : q.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hsize : q.env.calldata.size = 184)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : q.result = .ok (.success (created,world,gas,substate) out)) :
    LogPath q (UInt256.ofNat 184) := by
  obtain ⟨final, _, hx⟩ := xi_success_X q h
  exact ThroughLog.toLogPath q _ (deposit_user_path q huser hsize hx)

/-- Actual Theta deposit debit, without a supplied path or resource lower bound. -/
theorem deposit_theta_debit (c : MessageCall.Context)
    (hcode : c.code = Eip8282.Audit.Correspondence.runtimeCode .deposit)
    (huser : c.caller ≠ Eip8282.Audit.EvmRunner.sysAddr) (hsize : c.calldata.size = 184)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,true,out)) :
    gas.toNat + 1847 ≤ c.gas.toNat := by
  have hf : c.fuel = (c.fuel-1)+1 := by
    have hp := SuccessfulQuote.positive_fuel c h
    omega
  obtain ⟨ew, es, he, _, _⟩ := CallSuccess.codeCall_of_success c hcode (c.fuel-1) hf h
  have hp := deposit_log_path (CallBridge.codeCall c hcode (c.fuel-1)) huser hsize he
  exact theta_log_debit c hcode (UInt256.ofNat 184) hp h

#print axioms traced_deposit_fee
#print axioms traced_deposit_entry
#print axioms deposit_suffix_path
#print axioms deposit_log_path
#print axioms deposit_theta_debit

end Eip8282.Audit.Integrator.AppendGasPath
