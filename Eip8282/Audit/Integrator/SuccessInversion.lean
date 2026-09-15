import Eip8282.Audit.Execution.State
import Eip8282.Audit.Execution.Deposit
import Eip8282.Audit.Execution.Exit
import Eip8282.Audit.Execution.Words

/-!
# Inverting actual successful execution

The input here is an actual successful `X` evaluation, at arbitrary resources.
The accepted gas check, executed step and remaining successful evaluation are
conclusions. No sufficient-gas bound, fee completion, or post-state agreement
is assumed. The fee-specific inversions identify the 24-instruction cycle and derive
word-recurrence completion from actual success. For either pinned runtime,
every successful non-SYSTEM Ξ call is uninhibited and has a completed
operational quote. Identifying returned bytes or append admission from arbitrary
success, and natural-tariff correspondence, remain separate obligations.
-/

namespace Eip8282.Audit.Integrator.SuccessInversion

set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

open EvmYul EvmYul.EVM EvmYul.EVM.Proof

/-- A successful evaluation has positive fuel, accepts the actual decoded
instruction, and either continues successfully or halts with this exact result.
Exceptional halts and REVERT cannot be hidden in either alternative. -/
theorem success_step {fuel : Nat} {vj : Array UInt256} {pre final : EVM.State}
    {out : ByteArray} (h : X fuel vj pre = .ok (.success final out)) :
    ∃ (rest cost : Nat) (op : Operation .EVM) (arg : Option (UInt256 × Nat))
      (mid post : EVM.State),
      fuel = rest + 1 ∧ decodeAt pre = (op, arg) ∧
      Z vj op pre = .ok (mid, cost) ∧ StepOk rest cost (op, arg) mid post ∧
      ((H post.toMachineState op = none ∧ X rest vj post = .ok (.success final out)) ∨
       (H post.toMachineState op = some out ∧ op ≠ .REVERT ∧ post = final)) := by
  cases fuel with
  | zero => simp only [X_zero] at h; contradiction
  | succ rest =>
      rcases hdec : decodeAt pre with ⟨op, arg⟩
      cases hz : Z vj op pre with
      | error err =>
          rw [X_succ_of_Z_error hdec hz] at h
          contradiction
      | ok charged =>
          obtain ⟨mid, cost⟩ := charged
          cases hs : EvmYul.EVM.step rest cost (some (op, arg)) mid with
          | error err =>
              rw [X_succ_of_step_error hdec hz hs] at h
              contradiction
          | ok post =>
              refine ⟨rest, cost, op, arg, mid, post, rfl, rfl, hz, hs, ?_⟩
              cases hh : H post.toMachineState op with
              | none =>
                  exact Or.inl ⟨rfl, (X_succ_of_continue hdec hz hs hh).symm.trans h⟩
              | some data =>
                  by_cases hr : op = .REVERT
                  · rw [X_succ_of_revert hdec hz hs hh hr] at h
                    cases h
                  · rw [X_succ_of_halt hdec hz hs hh hr] at h
                    have heq := Except.ok.inj h
                    cases heq
                    exact Or.inr ⟨rfl, hr, rfl⟩

/-- At a nonhalting opcode, actual success forces an actual next step and the
same final result at strictly smaller fuel. Every gas condition is derived
through the returned `Z` acceptance rather than supplied by the consumer. -/
theorem success_continue {fuel : Nat} {vj : Array UInt256} {pre final : EVM.State}
    {out : ByteArray} {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    (hdec : decodeAt pre = (op, arg)) (hnh : Halting op = false)
    (h : X fuel vj pre = .ok (.success final out)) :
    ∃ (rest cost : Nat) (mid post : EVM.State), fuel = rest + 1 ∧
      Z vj op pre = .ok (mid, cost) ∧ StepOk rest cost (op, arg) mid post ∧
      XStepAt vj rest cost pre post ∧ X rest vj post = .ok (.success final out) := by
  obtain ⟨rest, cost, w, a, mid, post, hf, hd, hz, hs, hcase⟩ := success_step h
  have heq := hdec.symm.trans hd
  cases heq
  have hh : H post.toMachineState op = none := H_eq_none_of_not_halting hnh
  rcases hcase with ⟨_, htail⟩ | ⟨hstop, _, _⟩
  · refine ⟨rest, cost, mid, post, hf, hz, hs, ?_, htail⟩
    exact ⟨mid, by simpa only [hdec] using hz, by simpa only [hdec] using hs,
      by simpa only [hdec] using hh⟩
  · rw [hh] at hstop
    contradiction

open Eip8282.Audit.SymExec

/-- A symbolic shape identifies the actual next state of a successful step.
The actual gas charge is recovered from Z; neither gas sufficiency nor a
predicted post-state of the complete call is an assumption. -/
theorem success_symStep {fuel : Nat} {vj : Array UInt256} {vjNats : List Nat}
    {pre shaped final : EVM.State} {out : ByteArray} {inst : Instruction}
    (hdec : decodeAt pre = inst) (hshape : symStep vjNats inst pre = some shaped)
    (h : X fuel vj pre = .ok (.success final out)) :
    ∃ rest cost, fuel = rest + 1 ∧ Z vj inst.1 pre = .ok (pre, cost) ∧
      X rest vj (withGE shaped (pre.gasAvailable - UInt256.ofNat cost)
        (pre.execLength + 1)) = .ok (.success final out) := by
  obtain ⟨hguard, hstep⟩ := guardOk_of_symStep hshape
  have hm := mem_blockOps_of_guardOk hguard
  obtain ⟨rest, cost, mid, post, hf, hz, hs, _, htail⟩ :=
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
      exact ⟨rest + 1, cost, hf, hz, he ▸ htail⟩


/-- Invert a checked straight-line block along an actual successful execution.
Every instruction consumes one unit of fuel. Gas and instruction count are
those of the actual continuation; no block gas bound is imposed. -/
theorem success_symBlock {fuel : Nat} {vj : Array UInt256} {vjNats : List Nat}
    {code : ByteArray} (sites : List Site) (hsites : sitesOk code sites = true)
    {pre shaped final : EVM.State} {out : ByteArray}
    (hcode : pre.executionEnv.code = code)
    (hpc : pre.pc = UInt256.ofNat (headPc sites))
    (hshape : symBlock vjNats (sites.map Prod.snd) pre = some shaped)
    (h : X fuel vj pre = .ok (.success final out)) :
    ∃ rest gas count, fuel = rest + sites.length ∧
      X rest vj (withGE shaped gas count) = .ok (.success final out) := by
  induction sites generalizing fuel pre shaped with
  | nil =>
      simp only [List.map_nil, symBlock, Option.some.injEq] at hshape
      subst shaped
      exact ⟨fuel, pre.gasAvailable, pre.execLength, rfl, h⟩
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
          obtain ⟨rest, cost, hf, hz, hnext⟩ := success_symStep
            (decodeAt_of_code_pc hcode hpc hop) hfirst h
          rcases hsitesTail with rfl | ⟨hhead, hne, hsitesTail⟩
          · change some first = some shaped at hshape
            obtain rfl := Option.some.inj hshape
            exact ⟨rest, _, _, hf, hnext⟩
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
            obtain ⟨remaining, gas, count, hremaining, hresult⟩ :=
              ih hsitesTail hcodeNext hpcNext hshapeNext hnext
            rw [withGE_withGE] at hresult
            exact ⟨remaining, gas, count, by simp only [List.length_cons]; omega, hresult⟩

/-- An actually successful untaken JUMPI has the expected continuation,
with its accepted gas charge obtained from execution. -/
theorem success_jumpi_untaken {fuel : Nat} {vj : Array UInt256}
    {pre final : EVM.State} {out : ByteArray} {dest cond : UInt256} {stk : Stack UInt256}
    (hdec : decodeAt pre = (.JUMPI, none)) (hstack : pre.stack = dest :: cond :: stk)
    (hcond : cond = ⟨0⟩) (h : X fuel vj pre = .ok (.success final out)) :
    ∃ rest cost, fuel = rest+1 ∧ Z vj .JUMPI pre = .ok (pre, cost) ∧
      X rest vj (withGE { pre with pc := pre.pc + ⟨1⟩, stack := stk }
        (pre.gasAvailable - UInt256.ofNat cost) (pre.execLength+1)) =
          .ok (.success final out) := by
  obtain ⟨rest, cost, mid, post, hf, hz, hs, _, htail⟩ :=
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
      exact ⟨rest+1, cost, hf, hz, he ▸ htail⟩

/-- An actually successful taken JUMPI has the expected continuation,
with its accepted gas charge obtained from execution. -/
theorem success_jumpi_taken {fuel : Nat} {vj : Array UInt256}
    {pre final : EVM.State} {out : ByteArray} {dest cond : UInt256} {stk : Stack UInt256}
    (hdec : decodeAt pre = (.JUMPI, none)) (hstack : pre.stack = dest :: cond :: stk)
    (hcond : cond ≠ ⟨0⟩) (h : X fuel vj pre = .ok (.success final out)) :
    ∃ rest cost, fuel = rest+1 ∧ Z vj .JUMPI pre = .ok (pre, cost) ∧
      X rest vj (withGE { pre with pc := dest, stack := stk }
        (pre.gasAvailable - UInt256.ofNat cost) (pre.execLength+1)) =
          .ok (.success final out) := by
  obtain ⟨rest, cost, mid, post, hf, hz, hs, _, htail⟩ :=
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
      exact ⟨rest+1, cost, hf, hz, he ▸ htail⟩

open Eip8282.Audit.EntryReach Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall)

/-- Actual success at a nonzero deposit fee-loop head forces exactly the
24-instruction recurrence cycle and the same successful continuation.
All gas checks are derived from success; word arithmetic remains exact. -/
theorem deposit_fee_cycle (c : XiCall .deposit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {o a i numerator : UInt256} {final : EVM.State} {out : ByteArray}
    (henv : st.executionEnv = c.env) (ha : a ≠ ⟨0⟩)
    (h : X fuel depositJumpdests
      (at_ c st mem aw g 100 [o,a,i,numerator,UInt256.ofNat 17] e) =
        .ok (.success final out)) :
    ∃ rest gas count, fuel = rest+24 ∧
      X rest depositJumpdests (at_ c st mem aw gas 100
        [a+o, (numerator*a)/(i*UInt256.ofNat 17), UInt256.ofNat 1+i,
          numerator, UInt256.ofNat 17] count) = .ok (.success final out) := by
  have hcode := Deposit.hcode_of_env c henv
  obtain ⟨f1, g1, e1, hf1, hx1⟩ := success_symBlock deposit_b100 deposit_b100_ok
    hcode rfl (deposit_b100_shape c st mem aw g e o a [i,numerator,UInt256.ofNat 17]) h
  rw [withGE_at] at hx1
  obtain ⟨f2, cost, hf2, _, hx2⟩ := success_jumpi_untaken
    (decodeAt_of_code_pc hcode rfl deposit_s107) rfl ((feeLoop_continue_iff a).mpr ha) hx1
  rw [jumpi_fallthrough_at, withGE_at] at hx2
  obtain ⟨f3, g3, e3, hf3, hx3⟩ := success_symBlock deposit_b108 deposit_b108_ok
    hcode rfl (deposit_b108_shape c st mem aw _ _ o a i numerator (UInt256.ofNat 17) []) hx2
  rw [withGE_at] at hx3
  exact ⟨f3, g3, e3, by
    change fuel = f1+6 at hf1
    change f2 = f3+17 at hf3
    omega, hx3⟩

/-- Actual success at a nonzero exit fee-loop head forces exactly the
24-instruction recurrence cycle and the same successful continuation.
All gas checks are derived from success; word arithmetic remains exact. -/
theorem exit_fee_cycle (c : XiCall .exit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {o a i numerator : UInt256} {final : EVM.State} {out : ByteArray}
    (henv : st.executionEnv = c.env) (ha : a ≠ ⟨0⟩)
    (h : X fuel exitJumpdests
      (at_ c st mem aw g 99 [o,a,i,numerator,UInt256.ofNat 17] e) =
        .ok (.success final out)) :
    ∃ rest gas count, fuel = rest+24 ∧
      X rest exitJumpdests (at_ c st mem aw gas 99
        [a+o, (numerator*a)/(i*UInt256.ofNat 17), UInt256.ofNat 1+i,
          numerator, UInt256.ofNat 17] count) = .ok (.success final out) := by
  have hcode := Exit.hcode_of_env c henv
  obtain ⟨f1, g1, e1, hf1, hx1⟩ := success_symBlock exit_b99 exit_b99_ok
    hcode rfl (exit_b99_shape c st mem aw g e o a [i,numerator,UInt256.ofNat 17]) h
  rw [withGE_at] at hx1
  obtain ⟨f2, cost, hf2, _, hx2⟩ := success_jumpi_untaken
    (decodeAt_of_code_pc hcode rfl exit_s106) rfl ((feeLoop_continue_iff a).mpr ha) hx1
  rw [jumpi_fallthrough_at, withGE_at] at hx2
  obtain ⟨f3, g3, e3, hf3, hx3⟩ := success_symBlock exit_b107 exit_b107_ok
    hcode rfl (exit_b107_shape c st mem aw _ _ o a i numerator (UInt256.ofNat 17) []) hx2
  rw [withGE_at] at hx3
  exact ⟨f3, g3, e3, by
    change fuel = f1+6 at hf1
    change f2 = f3+17 at hf3
    omega, hx3⟩

/-- Successful execution from the deposit fee-loop head proves that the word
recurrence completes. The witness is derived by descent on actual interpreter
fuel, with no fixed cutoff, termination premise, or sufficient gas bound. -/
theorem deposit_fee_completes (c : XiCall .deposit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {o a i numerator : UInt256} {final : EVM.State} {out : ByteArray}
    (henv : st.executionEnv = c.env)
    (h : X fuel depositJumpdests
      (at_ c st mem aw g 100 [o,a,i,numerator,UInt256.ofNat 17] e) =
        .ok (.success final out)) :
    ∃ n output counter, 24*n ≤ fuel ∧ feeExit numerator n o a i = some (output,counter) := by
  induction fuel using Nat.strong_induction_on generalizing o a i g e with
  | h fuel ih =>
      by_cases ha : a = ⟨0⟩
      · subst a
        exact ⟨0, o, i, by omega, by simp [feeExit]⟩
      · obtain ⟨rest, gas, count, hf, hnext⟩ := deposit_fee_cycle c henv ha h
        obtain ⟨n, output, counter, hn, hloop⟩ := ih rest (by omega) hnext
        refine ⟨n+1, output, counter, by omega, ?_⟩
        simpa only [feeExit, if_neg ha] using hloop

/-- Successful execution from the exit fee-loop head proves that the word
recurrence completes. The witness is derived by descent on actual interpreter
fuel, with no fixed cutoff, termination premise, or sufficient gas bound. -/
theorem exit_fee_completes (c : XiCall .exit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {o a i numerator : UInt256} {final : EVM.State} {out : ByteArray}
    (henv : st.executionEnv = c.env)
    (h : X fuel exitJumpdests
      (at_ c st mem aw g 99 [o,a,i,numerator,UInt256.ofNat 17] e) =
        .ok (.success final out)) :
    ∃ n output counter, 24*n ≤ fuel ∧ feeExit numerator n o a i = some (output,counter) := by
  induction fuel using Nat.strong_induction_on generalizing o a i g e with
  | h fuel ih =>
      by_cases ha : a = ⟨0⟩
      · subst a
        exact ⟨0, o, i, by omega, by simp [feeExit]⟩
      · obtain ⟨rest, gas, count, hf, hnext⟩ := exit_fee_cycle c henv ha h
        obtain ⟨n, output, counter, hn, hloop⟩ := ih rest (by omega) hnext
        refine ⟨n+1, output, counter, by omega, ?_⟩
        simpa only [feeExit, if_neg ha] using hloop

/-- The opcode of an actual successful first step is never REVERT. This also
applies when success will occur later in the execution. -/
theorem success_not_revert {fuel : Nat} {vj : Array UInt256} {pre final : EVM.State}
    {out : ByteArray} (h : X fuel vj pre = .ok (.success final out)) :
    (decodeAt pre).1 ≠ .REVERT := by
  obtain ⟨rest, cost, op, arg, mid, post, hf, hd, hz, hs, hcase⟩ := success_step h
  rw [hd]
  intro hr
  change op = .REVERT at hr
  rcases hcase with ⟨hh, _⟩ | ⟨_, hn, _⟩
  · have hnh := H_eq_none_iff.mp hh
    rw [hr] at hnh
    simp at hnh
  · exact hn hr

/-- Any successful ordinary deposit execution reaches the fee-loop head.
The inhibitor exclusion follows from actual execution of the rejection branch;
all intervening gas checks and branch choices are recovered from success. -/
theorem deposit_user_to_fee_head (c : XiCall .deposit) {fuel : Nat}
    {final : EVM.State} {out : ByteArray}
    (huser : Deposit.callerWord c ≠ sysW)
    (h : X fuel depositJumpdests c.entry = .ok (.success final out)) :
    Deposit.excessWord c ≠ INH ∧ ∃ rest gas count,
      X rest depositJumpdests (at_ c (Deposit.st₂ c) c.entry.memory c.entry.activeWords gas 100
        [⟨0⟩, UInt256.ofNat 17, UInt256.ofNat 1, Deposit.effExcess c, UInt256.ofNat 17] count) =
          .ok (.success final out) := by
  rw [entry_eq_at] at h
  have hcode := Deposit.hcode_of_env c (st := entrySt c) rfl
  obtain ⟨f1, g1, e1, _, hx1⟩ := success_symBlock (h := h) deposit_b0 deposit_b0_ok (by exact hcode) rfl
    (deposit_b0_shape c (entrySt c) _ _ c.gas 0 [])
  rw [withGE_at] at hx1
  obtain ⟨f2, cost2, _, _, hx2⟩ := success_jumpi_untaken (h := hx1)
    (decodeAt_of_code_pc (st := at_ c (entrySt c) c.entry.memory c.entry.activeWords g1 26 _ e1) (by exact hcode) rfl deposit_s26) rfl
    ((eq_eq_zero_iff _ _).mpr (fun he => huser he.symm))
  rw [jumpi_fallthrough_at, withGE_at] at hx2
  obtain ⟨f3, g3, e3, _, hx3⟩ := success_symBlock (h := hx2) deposit_b27 deposit_b27_ok (by exact hcode) rfl
    (deposit_b27_shape c (entrySt c) _ _ _ _ [])
  rw [withGE_at] at hx3
  have hen : Deposit.excessWord c ≠ INH := by
    intro hin
    obtain ⟨f4, cost4, _, _, hx4⟩ := success_jumpi_taken (h := hx3)
      (decodeAt_of_code_pc (st := at_ c (touch (entrySt c) (UInt256.ofNat 0)) c.entry.memory c.entry.activeWords g3 67 _ e3) (by exact hcode) rfl deposit_s67) rfl
      ((eq_ne_zero_iff _ _).mpr hin.symm)
    rw [jumpi_taken_at, withGE_at] at hx4
    obtain ⟨f5, g5, e5, _, hx5⟩ := success_symBlock (h := hx4) deposit_b624 deposit_b624_ok (by exact hcode) rfl
      (deposit_b624_shape c _ _ _ _ _ _)
    rw [withGE_at] at hx5
    have hn := success_not_revert hx5
    apply hn
    exact congrArg Prod.fst (decodeAt_of_code_pc
      (st := at_ c (touch (entrySt c) (UInt256.ofNat 0)) c.entry.memory c.entry.activeWords g5 627
        [UInt256.ofNat 0, UInt256.ofNat 0, Deposit.excessWord c] e5)
      (by exact hcode) rfl deposit_s627)
  refine ⟨hen, ?_⟩
  obtain ⟨f4, cost4, _, _, hx4⟩ := success_jumpi_untaken (h := hx3)
    (decodeAt_of_code_pc (st := at_ c (touch (entrySt c) (UInt256.ofNat 0)) c.entry.memory c.entry.activeWords g3 67 _ e3) (by exact hcode) rfl deposit_s67) rfl
    ((eq_eq_zero_iff _ _).mpr (fun he => hen he.symm))
  rw [jumpi_fallthrough_at, withGE_at] at hx4
  obtain ⟨f5, g5, e5, _, hx5⟩ := success_symBlock (h := hx4) deposit_b68 deposit_b68_ok (by exact hcode) rfl
    (deposit_b68_shape c _ _ _ _ _ _)
  rw [withGE_at] at hx5
  simp only [slotW_touch] at hx5
  by_cases hcount : 8 < (Deposit.countWord c).toNat
  · obtain ⟨f6, cost6, _, _, hx6⟩ := success_jumpi_taken (h := hx5)
      (decodeAt_of_code_pc (st := at_ c (Deposit.st₂ c) c.entry.memory c.entry.activeWords g5 77 _ e5) (by exact hcode) rfl deposit_s77) rfl
      ((gt_ne_zero_iff _ _).mpr ((ofNat_lt_iff (by decide) _).mpr hcount))
    rw [jumpi_taken_at, withGE_at] at hx6
    obtain ⟨f7, g7, e7, _, hx7⟩ := success_symBlock (h := hx6) deposit_b82 deposit_b82_ok (by exact hcode) rfl
      (deposit_b82_shape c _ _ _ _ _ _ _ _)
    rw [withGE_at] at hx7
    obtain ⟨f8, g8, e8, _, hx8⟩ := success_symBlock (h := hx7) deposit_b88 deposit_b88_ok (by exact hcode) rfl
      (deposit_b88_shape c _ _ _ _ _ _ _)
    rw [withGE_at] at hx8
    exact ⟨f8, g8, e8, by simpa only [Deposit.effExcess, if_pos hcount, Deposit.countWord, Deposit.excessWord,
      (show UInt256.ofNat 17 * UInt256.ofNat 1 = UInt256.ofNat 17 from rfl),
      (show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl)] using hx8⟩
  · obtain ⟨f6, cost6, _, _, hx6⟩ := success_jumpi_untaken (h := hx5)
      (decodeAt_of_code_pc (st := at_ c (Deposit.st₂ c) c.entry.memory c.entry.activeWords g5 77 _ e5) (by exact hcode) rfl deposit_s77) rfl
      ((gt_eq_zero_iff _ _).mpr (fun hh => hcount ((ofNat_lt_iff (by decide) _).mp hh)))
    rw [jumpi_fallthrough_at, withGE_at] at hx6
    obtain ⟨f7, g7, e7, _, hx7⟩ := success_symBlock (h := hx6) deposit_b78 deposit_b78_ok (by exact hcode) rfl
      (deposit_b78_shape c _ _ _ _ _ _ _)
    rw [withGE_at] at hx7
    obtain ⟨f8, g8, e8, _, hx8⟩ := success_symBlock (h := hx7) deposit_b88 deposit_b88_ok (by exact hcode) rfl
      (deposit_b88_shape c _ _ _ _ _ _ _)
    rw [withGE_at] at hx8
    exact ⟨f8, g8, e8, by simpa only [Deposit.effExcess, if_neg hcount, Deposit.countWord, Deposit.excessWord,
      (show UInt256.ofNat 17 * UInt256.ofNat 1 = UInt256.ofNat 17 from rfl),
      (show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl)] using hx8⟩

/-- Any successful ordinary exit execution reaches the fee-loop head.
The inhibitor exclusion follows from actual execution of the rejection branch;
all intervening gas checks and branch choices are recovered from success. -/
theorem exit_user_to_fee_head (c : XiCall .exit) {fuel : Nat}
    {final : EVM.State} {out : ByteArray}
    (huser : Exit.callerWord c ≠ sysW)
    (h : X fuel exitJumpdests c.entry = .ok (.success final out)) :
    Exit.excessWord c ≠ INH ∧ ∃ rest gas count,
      X rest exitJumpdests (at_ c (Exit.st₂ c) c.entry.memory c.entry.activeWords gas 99
        [⟨0⟩, UInt256.ofNat 17, UInt256.ofNat 1, Exit.effExcess c, UInt256.ofNat 17] count) =
          .ok (.success final out) := by
  rw [entry_eq_at] at h
  have hcode := Exit.hcode_of_env c (st := entrySt c) rfl
  obtain ⟨f1, g1, e1, _, hx1⟩ := success_symBlock (h := h) exit_b0 exit_b0_ok (by exact hcode) rfl
    (exit_b0_shape c (entrySt c) _ _ c.gas 0 [])
  rw [withGE_at] at hx1
  obtain ⟨f2, cost2, _, _, hx2⟩ := success_jumpi_untaken (h := hx1)
    (decodeAt_of_code_pc (st := at_ c (entrySt c) c.entry.memory c.entry.activeWords g1 25 _ e1) (by exact hcode) rfl exit_s25) rfl
    ((eq_eq_zero_iff _ _).mpr (fun he => huser he.symm))
  rw [jumpi_fallthrough_at, withGE_at] at hx2
  obtain ⟨f3, g3, e3, _, hx3⟩ := success_symBlock (h := hx2) exit_b26 exit_b26_ok (by exact hcode) rfl
    (exit_b26_shape c (entrySt c) _ _ _ _ [])
  rw [withGE_at] at hx3
  have hen : Exit.excessWord c ≠ INH := by
    intro hin
    obtain ⟨f4, cost4, _, _, hx4⟩ := success_jumpi_taken (h := hx3)
      (decodeAt_of_code_pc (st := at_ c (touch (entrySt c) (UInt256.ofNat 0)) c.entry.memory c.entry.activeWords g3 66 _ e3) (by exact hcode) rfl exit_s66) rfl
      ((eq_ne_zero_iff _ _).mpr hin.symm)
    rw [jumpi_taken_at, withGE_at] at hx4
    obtain ⟨f5, g5, e5, _, hx5⟩ := success_symBlock (h := hx4) exit_b454 exit_b454_ok (by exact hcode) rfl
      (exit_b454_shape c _ _ _ _ _ _)
    rw [withGE_at] at hx5
    have hn := success_not_revert hx5
    apply hn
    exact congrArg Prod.fst (decodeAt_of_code_pc
      (st := at_ c (touch (entrySt c) (UInt256.ofNat 0)) c.entry.memory c.entry.activeWords g5 457
        [UInt256.ofNat 0, UInt256.ofNat 0, Exit.excessWord c] e5)
      (by exact hcode) rfl exit_s457)
  refine ⟨hen, ?_⟩
  obtain ⟨f4, cost4, _, _, hx4⟩ := success_jumpi_untaken (h := hx3)
    (decodeAt_of_code_pc (st := at_ c (touch (entrySt c) (UInt256.ofNat 0)) c.entry.memory c.entry.activeWords g3 66 _ e3) (by exact hcode) rfl exit_s66) rfl
    ((eq_eq_zero_iff _ _).mpr (fun he => hen he.symm))
  rw [jumpi_fallthrough_at, withGE_at] at hx4
  obtain ⟨f5, g5, e5, _, hx5⟩ := success_symBlock (h := hx4) exit_b67 exit_b67_ok (by exact hcode) rfl
    (exit_b67_shape c _ _ _ _ _ _)
  rw [withGE_at] at hx5
  simp only [slotW_touch] at hx5
  by_cases hcount : 2 < (Exit.countWord c).toNat
  · obtain ⟨f6, cost6, _, _, hx6⟩ := success_jumpi_taken (h := hx5)
      (decodeAt_of_code_pc (st := at_ c (Exit.st₂ c) c.entry.memory c.entry.activeWords g5 76 _ e5) (by exact hcode) rfl exit_s76) rfl
      ((gt_ne_zero_iff _ _).mpr ((ofNat_lt_iff (by decide) _).mpr hcount))
    rw [jumpi_taken_at, withGE_at] at hx6
    obtain ⟨f7, g7, e7, _, hx7⟩ := success_symBlock (h := hx6) exit_b81 exit_b81_ok (by exact hcode) rfl
      (exit_b81_shape c _ _ _ _ _ _ _ _)
    rw [withGE_at] at hx7
    obtain ⟨f8, g8, e8, _, hx8⟩ := success_symBlock (h := hx7) exit_b87 exit_b87_ok (by exact hcode) rfl
      (exit_b87_shape c _ _ _ _ _ _ _)
    rw [withGE_at] at hx8
    exact ⟨f8, g8, e8, by simpa only [Exit.effExcess, if_pos hcount, Exit.countWord, Exit.excessWord,
      (show UInt256.ofNat 17 * UInt256.ofNat 1 = UInt256.ofNat 17 from rfl),
      (show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl)] using hx8⟩
  · obtain ⟨f6, cost6, _, _, hx6⟩ := success_jumpi_untaken (h := hx5)
      (decodeAt_of_code_pc (st := at_ c (Exit.st₂ c) c.entry.memory c.entry.activeWords g5 76 _ e5) (by exact hcode) rfl exit_s76) rfl
      ((gt_eq_zero_iff _ _).mpr (fun hh => hcount ((ofNat_lt_iff (by decide) _).mp hh)))
    rw [jumpi_fallthrough_at, withGE_at] at hx6
    obtain ⟨f7, g7, e7, _, hx7⟩ := success_symBlock (h := hx6) exit_b77 exit_b77_ok (by exact hcode) rfl
      (exit_b77_shape c _ _ _ _ _ _ _)
    rw [withGE_at] at hx7
    obtain ⟨f8, g8, e8, _, hx8⟩ := success_symBlock (h := hx7) exit_b87 exit_b87_ok (by exact hcode) rfl
      (exit_b87_shape c _ _ _ _ _ _ _)
    rw [withGE_at] at hx8
    exact ⟨f8, g8, e8, by simpa only [Exit.effExcess, if_neg hcount, Exit.countWord, Exit.excessWord,
      (show UInt256.ofNat 17 * UInt256.ofNat 1 = UInt256.ofNat 17 from rfl),
      (show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl)] using hx8⟩

/-- A trace certificate tied to the exact successful final state and bytes.
Every stored state belongs to the execution; none is a freely assumed result. -/
structure SuccessTrace (vj : Array UInt256) (fuel : Nat)
    (pre final : EVM.State) (out : ByteArray) where
  rem : Nat
  cost : Nat
  trace : List Labelled
  exit : EVM.State
  mid : EVM.State
  op : Operation .EVM
  arg : Option (UInt256 × Nat)
  run : RunUntil Halting vj fuel pre trace (rem + 1) exit
  decode : decodeAt exit = (op, arg)
  charge : Z vj op exit = .ok (mid, cost)
  step : StepOk rem cost (op, arg) mid final
  output : H final.toMachineState op = some out
  not_revert : op ≠ .REVERT

/-- Every actual success supplies its finite trace and halting certificate.
This is a necessity theorem at arbitrary gas and fuel, not an assumption that
the evaluator will succeed or that a particular fee loop terminates. -/
theorem success_trace {fuel : Nat} {vj : Array UInt256} {pre final : EVM.State}
    {out : ByteArray} (h : X fuel vj pre = .ok (.success final out)) :
    Nonempty (SuccessTrace vj fuel pre final out) := by
  induction fuel generalizing pre with
  | zero => simp only [X_zero] at h; contradiction
  | succ fuel ih =>
      obtain ⟨rest, cost, op, arg, mid, post, hf, hd, hz, hs, hcase⟩ := success_step h
      have he : rest = fuel := by omega
      subst rest
      rcases hcase with ⟨hh, htail⟩ | ⟨hh, hn, hpost⟩
      · obtain ⟨t⟩ := ih htail
        have hnh := H_eq_none_iff.mp hh
        have hstep : XStepAt vj fuel cost pre post :=
          ⟨mid, by simpa only [hd] using hz, by simpa only [hd] using hs,
            by simpa only [hd] using hh⟩
        exact ⟨{
          rem := t.rem, cost := t.cost, trace := (fuel, cost, decodeAt pre) :: t.trace,
          exit := t.exit, mid := t.mid, op := t.op, arg := t.arg,
          run := RunUntil.step (by simp only [hd, stopOrHalting, hnh, Bool.false_or])
            hstep t.run,
          decode := t.decode, charge := t.charge, step := t.step,
          output := t.output, not_revert := t.not_revert }⟩
      · subst post
        have hhalt := halting_of_H_eq_some hh
        exact ⟨{
          rem := fuel, cost := cost, trace := [], exit := pre, mid := mid,
          op := op, arg := arg,
          run := RunUntil.stop (by simp only [hd, stopOrHalting, hhalt, Bool.true_or]),
          decode := hd, charge := hz, step := hs, output := hh, not_revert := hn }⟩

/-- Recover the actual X success from Ξ. The final state has exactly
the published world, gas, created accounts, substate and bytes. -/
theorem xi_success_X {kind : Eip8282.Audit.Model.Kind}
    (c : Eip8282.Audit.XiTransport.XiCall kind)
    {published : Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate}
    {out : ByteArray} (h : c.result = .ok (.success published out)) :
    ∃ final : EVM.State,
      (final.createdAccounts, final.accountMap, final.gasAvailable, final.substate) = published ∧
      X c.fuel (Eip8282.Audit.XiTransport.jumpdestsOf kind) c.entry =
        .ok (.success final out) := by
  open Eip8282.Audit.XiTransport in
    unfold XiCall.result Ξ at h
    change (do
      let r ← X c.fuel (D_J c.env.code ⟨0⟩) c.entry
      match r with
      | .success st o => Except.ok (ExecutionResult.success
          (st.createdAccounts, st.accountMap, st.gasAvailable, st.substate) o)
      | .revert g o => Except.ok (ExecutionResult.revert g o)) = _ at h
    rw [Xi_validJumps_eq c.code_pinned] at h
    cases hx : X c.fuel (jumpdestsOf kind) c.entry with
    | error err =>
        simp only [hx, Bind.bind, Except.bind] at h
        cases h
    | ok result =>
        cases result with
        | revert gas data =>
            simp only [hx, Bind.bind, Except.bind] at h
            cases h
        | success final data =>
            simp only [hx, Bind.bind, Except.bind, Except.ok.injEq,
              ExecutionResult.success.injEq] at h
            obtain ⟨hworld, hdata⟩ := h
            subst data
            exact ⟨final, hworld, rfl⟩

/-- Invert Ξ's result wrapper as well. The recovered X final state has exactly
the published world, gas, created accounts, substate and bytes. -/
theorem xi_success_trace {kind : Eip8282.Audit.Model.Kind}
    (c : Eip8282.Audit.XiTransport.XiCall kind)
    {published : Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate}
    {out : ByteArray} (h : c.result = .ok (.success published out)) :
    ∃ final : EVM.State,
      (final.createdAccounts, final.accountMap, final.gasAvailable, final.substate) = published ∧
      Nonempty (SuccessTrace (Eip8282.Audit.XiTransport.jumpdestsOf kind)
        c.fuel c.entry final out) := by
  obtain ⟨final, hp, hx⟩ := xi_success_X c h
  exact ⟨final, hp, success_trace hx⟩

/-- Every actually successful non-SYSTEM deposit Ξ call is uninhibited and
has a completed operational quote. This is necessity at arbitrary resources;
no fee-loop completion, natural-fit or protocol-history premise is supplied. -/
theorem deposit_user_success_quote (c : XiCall .deposit)
    {published : Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate}
    {out : ByteArray} (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (h : c.result = .ok (.success published out)) :
    Deposit.excessWord c ≠ INH ∧ ∃ n price,
      quoteWithin (Deposit.effExcess c) n = some price := by
  obtain ⟨final, _, hx⟩ := xi_success_X c h
  have hu : Deposit.callerWord c ≠ sysW := by
    intro he
    exact huser ((callerW_eq_sysW_iff c).mp he)
  obtain ⟨hen, rest, gas, count, hhead⟩ := deposit_user_to_fee_head c hu hx
  obtain ⟨n, output, counter, _, hloop⟩ := deposit_fee_completes c rfl hhead
  exact ⟨hen, n, output / UInt256.ofNat 17, quoteWithin_some_of_feeExit hloop⟩

/-- Every actually successful non-SYSTEM exit Ξ call is uninhibited and
has a completed operational quote. This is necessity at arbitrary resources;
no fee-loop completion, natural-fit or protocol-history premise is supplied. -/
theorem exit_user_success_quote (c : XiCall .exit)
    {published : Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate}
    {out : ByteArray} (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (h : c.result = .ok (.success published out)) :
    Exit.excessWord c ≠ INH ∧ ∃ n price,
      quoteWithin (Exit.effExcess c) n = some price := by
  obtain ⟨final, _, hx⟩ := xi_success_X c h
  have hu : Exit.callerWord c ≠ sysW := by
    intro he
    exact huser ((callerW_eq_sysW_iff c).mp he)
  obtain ⟨hen, rest, gas, count, hhead⟩ := exit_user_to_fee_head c hu hx
  obtain ⟨n, output, counter, _, hloop⟩ := exit_fee_completes c rfl hhead
  exact ⟨hen, n, output / UInt256.ofNat 17, quoteWithin_some_of_feeExit hloop⟩

#print axioms xi_success_X
#print axioms deposit_user_success_quote
#print axioms exit_user_success_quote
#print axioms exit_user_to_fee_head
#print axioms success_jumpi_taken
#print axioms deposit_user_to_fee_head
#print axioms deposit_fee_completes
#print axioms exit_fee_completes
#print axioms success_jumpi_untaken
#print axioms deposit_fee_cycle
#print axioms exit_fee_cycle
#print axioms success_symStep
#print axioms success_symBlock
#print axioms success_step
#print axioms success_continue
#print axioms success_not_revert
#print axioms success_trace
#print axioms xi_success_trace

end Eip8282.Audit.Integrator.SuccessInversion
