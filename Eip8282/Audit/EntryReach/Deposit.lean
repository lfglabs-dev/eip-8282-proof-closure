import Eip8282.Audit.EntryReach.Path

/-!
# Entry reachability of the builder-deposits runtime

Every complete `Ξ` message call into the pinned `builder_deposits` runtime is
followed here from the entry machine to the halting instruction it reaches,
along every path the code has: the eight user endpoints and the system drain.
Each theorem is a chain of the generated block lemmas
(`Eip8282.Audit.EntryReach.Blocks`) and the step lemmas
(`Eip8282.Audit.EntryReach.Steps`), so it rests on `SymExec.pureStep_sound`,
the kernel-checked decodes of the pinned image, and EVMYulLean's own `Z` and
`EvmYul.step` — no trace, no `native_decide`, no premise about the model.

The branch conditions are the words the code tests, read off the entry state by
`Eip8282.Audit.EntryReach.Machine`'s readers; relating them to `Model.userCall`
is the next slice (OPERANDS), not this one.
-/

namespace Eip8282.Audit.EntryReach.Deposit

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall jumpdestsOf)
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.EntryReach

set_option maxRecDepth 100000

/-- `SYSTEM_ADDR` as the word `PUSH20` pushes. -/
abbrev sysW : UInt256 := UInt256.ofNat 1461501637330902918203684832716283019655932542974
/-- `INHIBITOR`. -/
abbrev INH : UInt256 :=
  UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935

variable (c : XiCall .deposit)

/-- The words the user path reads off the entry state. -/
abbrev callerWord : UInt256 := callerW (entrySt c)
abbrev excessWord : UInt256 := slotW (entrySt c) (UInt256.ofNat 0)
abbrev countWord : UInt256 := slotW (entrySt c) (UInt256.ofNat 1)
abbrev valueWord : UInt256 := valueW (entrySt c)
abbrev cdsizeWord : UInt256 := cdsizeW (entrySt c)

/-- The state after the user path's two control reads. -/
abbrev st₂ : EvmYul.State .EVM := touch (touch (entrySt c) (UInt256.ofNat 0)) (UInt256.ofNat 1)

theorem executionEnv_st₂ : (st₂ c).executionEnv = c.env := rfl

theorem hcode_of_env {st : EvmYul.State .EVM} (h : st.executionEnv = c.env) :
    st.executionEnv.code = depositRuntime := by
  rw [h]; exact c.code_pinned

/-! ## The opening gate -/

/-- `CALLER; PUSH20 SYSTEM_ADDR; EQ; PUSH2 @read_requests` from the entry machine. -/
theorem gate (hg : 11 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat), c.gas.toNat - 11 ≤ g.toNat ∧
      Reaches depositJumpdests 4 c.entry
        (at_ c (entrySt c) c.entry.memory c.entry.activeWords g 26
          (UInt256.ofNat 284 :: UInt256.eq sysW (callerWord c) :: []) e) := by
  change ∃ (g : UInt256) (e : Nat), c.gas.toNat - 11 ≤ g.toNat ∧
    Reaches depositJumpdests 4 (at_ c (entrySt c) c.entry.memory c.entry.activeWords c.gas 0 [] 0) _
  exact block_step hvj_deposit deposit_b0 deposit_b0_ok (n := 4) deposit_b0_bound rfl
    (deposit_b0_shape c (entrySt c) _ _ c.gas 0 []) (hcode_of_env c rfl) rfl hg (by simp)

/-! ## The user path up to the fee loop -/

/-- `bump_excess`: the excess the fee loop is quoted at. -/
def effExcess : UInt256 :=
  if 8 < (countWord c).toNat then (countWord c - UInt256.ofNat 8) + excessWord c
  else excessWord c

theorem ofNat_lt_iff {n : Nat} (hn : n < UInt256.size) (a : UInt256) :
    UInt256.ofNat n < a ↔ n < a.toNat := by
  show (UInt256.ofNat n).toNat < a.toNat ↔ n < a.toNat
  rw [toNat_ofNat_of_lt hn]

/-- From the fall-through of the gate (`pc = 27`) to the fee loop head, on an
uninhibited image: the excess and count are read, `bump_excess` is resolved, and
the loop is entered with output `0`, accumulator `17 · 1` and counter `1`. -/
theorem to_fee_loop {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (hen : excessWord c ≠ INH) (hg : 4300 ≤ g.toNat) :
    ∃ (g' : UInt256) (e' : Nat), g.toNat - 4300 ≤ g'.toNat ∧
      ReachesLe depositJumpdests 29 (at_ c (entrySt c) mem aw g 27 [] e)
        (at_ c (st₂ c) mem aw g' 100
          (UInt256.ofNat 0 :: (UInt256.ofNat 17 * UInt256.ofNat 1) :: UInt256.ofNat 1 ::
            effExcess c :: UInt256.ofNat 17 :: []) e') := by
  -- 27..64: the inhibitor test
  have h1 := block_step hvj_deposit deposit_b27 deposit_b27_ok (n := 6) deposit_b27_bound rfl
    (deposit_b27_shape c (entrySt c) mem aw g e []) (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
  -- 67: not taken
  have h2 := chain h1 fun g₁ e₁ hg₁ =>
    reach_jumpi_fallthrough deposit_s67 (hcode_of_env c rfl)
      ((eq_eq_zero_iff _ _).mpr (fun h => hen h.symm)) (by gas_omega)
      (by simp)
  clear h1
  -- 68..75: the count test
  have h3 := chain h2 fun g₁ e₁ hg₁ =>
    block_step hvj_deposit deposit_b68 deposit_b68_ok (n := 6) deposit_b68_bound rfl
      (deposit_b68_shape c _ mem aw g₁ e₁ [excessWord c]) (hcode_of_env c rfl) rfl
      (by gas_omega) (by simp)
  clear h2
  simp only [slotW_touch] at h3
  by_cases hcnt : 8 < (countWord c).toNat
  · -- bump_excess taken
    have h4 := chain h3 fun g₁ e₁ hg₁ =>
      reach_jumpi_taken deposit_s77 (hcode_of_env c rfl)
        ((gt_ne_zero_iff _ _).mpr ((ofNat_lt_iff (by decide) _).mpr hcnt))
        (hvj_deposit 82 (by decide)) (by gas_omega) (by simp)
    clear h3
    have h5 := chain h4 fun g₁ e₁ hg₁ =>
      block_step hvj_deposit deposit_b82 deposit_b82_ok (n := 5) deposit_b82_bound rfl
        (deposit_b82_shape c _ mem aw g₁ e₁ (countWord c) (excessWord c) [])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h4
    have h6 := chain h5 fun g₁ e₁ hg₁ =>
      block_step hvj_deposit deposit_b88 deposit_b88_ok (n := 9) deposit_b88_bound rfl
        (deposit_b88_shape c _ mem aw g₁ e₁ _ []) (hcode_of_env c rfl) rfl (by omega)
        (by simp)
    clear h5
    simp only [effExcess, if_pos hcnt]
    obtain ⟨g', e', hg', hr⟩ := h6
    exact ⟨g', e', by omega, Reaches.le hr (by decide)⟩
  · -- bump_excess not taken
    have h4 := chain h3 fun g₁ e₁ hg₁ =>
      reach_jumpi_fallthrough deposit_s77 (hcode_of_env c rfl)
        ((gt_eq_zero_iff _ _).mpr (fun h => hcnt ((ofNat_lt_iff (by decide) _).mp h)))
        (by gas_omega) (by simp)
    clear h3
    have h5 := chain h4 fun g₁ e₁ hg₁ =>
      block_step hvj_deposit deposit_b78 deposit_b78_ok (n := 3) deposit_b78_bound rfl
        (deposit_b78_shape c _ mem aw g₁ e₁ (countWord c) [excessWord c])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h4
    have h6 := chain h5 fun g₁ e₁ hg₁ =>
      block_step hvj_deposit deposit_b88 deposit_b88_ok (n := 9) deposit_b88_bound rfl
        (deposit_b88_shape c _ mem aw g₁ e₁ _ []) (hcode_of_env c rfl) rfl (by omega)
        (by simp)
    clear h5
    simp only [effExcess, if_neg hcnt]
    obtain ⟨g', e', hg', hr⟩ := h6
    exact ⟨g', e', by omega, Reaches.le hr (by decide)⟩


/-! ## The fee loop

`fake_expo` runs `[out, acc, i, X, 17] ↦ [acc + out, X·acc / (i·17), 1 + i, X, 17]`
until `acc = 0`. `feeExit` is that recurrence on words, returning the output and
counter it holds when it stops, provided it stops within the given number of
iterations. Relating it to `Model.fakeExponential.go` is the OPERANDS slice. -/

def feeExit (X : UInt256) : Nat → UInt256 → UInt256 → UInt256 → Option (UInt256 × UInt256)
  | 0, o, a, i => if a = ⟨0⟩ then some (o, i) else none
  | n + 1, o, a, i =>
      if a = ⟨0⟩ then some (o, i)
      else feeExit X n (a + o) ((X * a) / (i * UInt256.ofNat 17)) (UInt256.ofNat 1 + i)

/-- One pass of the loop head onto the taken exit branch, at `acc = 0`. -/
theorem fee_head_exit {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (henv : st.executionEnv = c.env) (o i X : UInt256) (hg : 25 ≤ g.toNat) :
    ∃ (g' : UInt256) (e' : Nat), g.toNat - 25 ≤ g'.toNat ∧
      Reaches depositJumpdests 7
        (at_ c st mem aw g 100 (o :: ⟨0⟩ :: i :: X :: UInt256.ofNat 17 :: []) e)
        (at_ c st mem aw g' 127 (o :: ⟨0⟩ :: i :: X :: UInt256.ofNat 17 :: []) e') := by
  have h1 := block_step hvj_deposit deposit_b100 deposit_b100_ok (n := 6) deposit_b100_bound rfl
    (deposit_b100_shape c st mem aw g e o ⟨0⟩ [i, X, UInt256.ofNat 17]) (hcode_of_env c henv) rfl
    (by omega) (by simp)
  exact chain h1 fun g₁ e₁ hg₁ =>
    reach_jumpi_taken deposit_s107 (hcode_of_env c henv) ((feeLoop_exit_iff _).mpr rfl)
      (hvj_deposit 127 (by decide)) (by omega) (by simp)

/-- One full iteration of the loop, at `acc ≠ 0`. -/
theorem fee_iteration {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (henv : st.executionEnv = c.env) (o a i X : UInt256) (ha : a ≠ ⟨0⟩) (hg : 87 ≤ g.toNat) :
    ∃ (g' : UInt256) (e' : Nat), g.toNat - 87 ≤ g'.toNat ∧
      Reaches depositJumpdests 24
        (at_ c st mem aw g 100 (o :: a :: i :: X :: UInt256.ofNat 17 :: []) e)
        (at_ c st mem aw g' 100
          ((a + o) :: ((X * a) / (i * UInt256.ofNat 17)) :: (UInt256.ofNat 1 + i) :: X ::
            UInt256.ofNat 17 :: []) e') := by
  have h1 := block_step hvj_deposit deposit_b100 deposit_b100_ok (n := 6) deposit_b100_bound rfl
    (deposit_b100_shape c st mem aw g e o a [i, X, UInt256.ofNat 17]) (hcode_of_env c henv) rfl
    (by omega) (by simp)
  have h2 := chain h1 fun g₁ e₁ hg₁ =>
    reach_jumpi_fallthrough deposit_s107 (hcode_of_env c henv) ((feeLoop_continue_iff _).mpr ha)
      (by omega) (by simp)
  clear h1
  exact chain h2 fun g₁ e₁ hg₁ =>
    block_step hvj_deposit deposit_b108 deposit_b108_ok (n := 17) deposit_b108_bound rfl
      (deposit_b108_shape c st mem aw g₁ e₁ o a i X (UInt256.ofNat 17) []) (hcode_of_env c henv) rfl
      (by omega) (by simp)

/-- **The fee loop terminates where `feeExit` says it does.** From the loop head
with `n` iterations of budget left, the run lands on the exit block with the
output and counter `feeExit` computes, in at most `24 · n + 7` iterations of `X`. -/
theorem fee_loop {st : EvmYul.State .EVM} {mem : ByteArray} {aw : UInt256} (X : UInt256)
    (henv : st.executionEnv = c.env) :
    ∀ (n : Nat) (o a i g : UInt256) (e : Nat) (o' i' : UInt256),
      feeExit X n o a i = some (o', i') → 87 * n + 25 ≤ g.toNat →
      ∃ (g' : UInt256) (e' : Nat), g.toNat - (87 * n + 25) ≤ g'.toNat ∧
        ReachesLe depositJumpdests (24 * n + 7)
          (at_ c st mem aw g 100 (o :: a :: i :: X :: UInt256.ofNat 17 :: []) e)
          (at_ c st mem aw g' 127 (o' :: ⟨0⟩ :: i' :: X :: UInt256.ofNat 17 :: []) e') := by
  intro n
  induction n with
  | zero =>
    intro o a i g e o' i' hexit hg
    simp only [feeExit] at hexit
    split at hexit
    · rename_i ha
      simp only [Option.some.injEq, Prod.mk.injEq] at hexit
      obtain ⟨rfl, rfl⟩ := hexit
      subst ha
      obtain ⟨g', e', hg', hr⟩ := fee_head_exit c (mem := mem) (aw := aw) (g := g) (e := e) henv o i X
        (by omega)
      exact ⟨g', e', by omega, Reaches.le hr (by omega)⟩
    · exact absurd hexit (by simp)
  | succ n ih =>
    intro o a i g e o' i' hexit hg
    simp only [feeExit] at hexit
    split at hexit
    · rename_i ha
      simp only [Option.some.injEq, Prod.mk.injEq] at hexit
      obtain ⟨rfl, rfl⟩ := hexit
      subst ha
      obtain ⟨g', e', hg', hr⟩ := fee_head_exit c (mem := mem) (aw := aw) (g := g) (e := e) henv o i X
        (by omega)
      exact ⟨g', e', by omega, Reaches.le hr (by omega)⟩
    · rename_i ha
      obtain ⟨g₁, e₁, hg₁, hr₁⟩ := fee_iteration c (mem := mem) (aw := aw) (g := g) (e := e) henv
        o a i X ha (by omega)
      obtain ⟨g', e', hg', hr'⟩ := ih (a + o) ((X * a) / (i * UInt256.ofNat 17))
        (UInt256.ofNat 1 + i) g₁ e₁ o' i' hexit (by omega)
      exact ⟨g', e', by omega, (Reaches.le hr₁ le_rfl).trans hr' |>.mono (by omega)⟩

/-! ## The user path onto the dispatch -/

/-- The fee word the getter returns and the write path compares against. -/
abbrev feeWord (o : UInt256) : UInt256 := o / UInt256.ofNat 17

/-- **From the entry machine to the calldata-size dispatch**, for a user caller
on an uninhibited image whose fee loop terminates within `n` iterations. The
machine stands on the `JUMPI @handle_input` with the fee quoted. -/
theorem user_prefix (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256}
    (hfee : feeExit (effExcess c) n (UInt256.ofNat 0) (UInt256.ofNat 17 * UInt256.ofNat 1)
      (UInt256.ofNat 1) = some (o', i'))
    (hg : 87 * n + 4400 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat), c.gas.toNat - (87 * n + 4400) ≤ g.toNat ∧
      ReachesLe depositJumpdests (24 * n + 60) c.entry
        (at_ c (st₂ c) c.entry.memory c.entry.activeWords g 142
          (UInt256.ofNat 159 :: UInt256.eq (UInt256.ofNat 184) (cdsizeWord c) ::
            feeWord o' :: []) e) := by
  have h1 := le_of_exact (gate c (by omega))
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s26 (hcode_of_env c rfl)
      ((eq_eq_zero_iff _ _).mpr (fun h => huser h.symm)) (by omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => to_fee_loop c hen (by omega)
  clear h2
  have h4 := chainLe h3 fun g₁ e₁ hg₁ =>
    fee_loop c (effExcess c) rfl n _ _ _ g₁ e₁ o' i' hfee (by omega)
  clear h3
  have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b127 deposit_b127_ok (n := 13) deposit_b127_bound rfl
      (deposit_b127_shape c (st₂ c) _ _ g₁ e₁ o' ⟨0⟩ i' (effExcess c) (UInt256.ofNat 17) [])
      (hcode_of_env c rfl) rfl (by omega) (by simp)
  clear h4
  simp only [cdsizeW_touch] at h5
  obtain ⟨g, e, hg', hr⟩ := h5
  exact ⟨g, e, by omega, ReachesLe.mono hr (by omega)⟩


/-! ## The `revert:` subroutine -/

/-- Entering `revert:` (`pc = 624`) with any stack: three instructions later the
machine stands on the `REVERT` with two zero operands pushed, and that `REVERT`
halts publishing the empty slice. -/
theorem revert_tail {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (henv : st.executionEnv = c.env) (r : Stack UInt256) (haw : aw.toNat = 0)
    (hg : 5 ≤ g.toNat) (hr : r.length + 3 ≤ 1024) :
    ∃ (g' : UInt256) (e' : Nat), g.toNat - 5 ≤ g'.toNat ∧
      Reaches depositJumpdests 3 (at_ c st mem aw g 624 r e)
        (at_ c st mem aw g' 627 (UInt256.ofNat 0 :: UInt256.ofNat 0 :: r) e') ∧
      Halt depositJumpdests (at_ c st mem aw g' 627 (UInt256.ofNat 0 :: UInt256.ofNat 0 :: r) e')
        .REVERT (mem.readWithPadding 0 0) := by
  obtain ⟨g', e', hg', hr'⟩ := block_step hvj_deposit deposit_b624 deposit_b624_ok (n := 3)
    deposit_b624_bound rfl (deposit_b624_shape c st mem aw g e r) (hcode_of_env c henv) rfl hg
    (by simpa using hr)
  refine ⟨g', e', hg', hr', ?_⟩
  exact halt_REVERT deposit_s627 (hcode_of_env c henv) (B := 0) (by omega) (by decide) (by decide)
    rfl (Nat.zero_le _) (by omega)

/-! ## The user endpoints

Each theorem names the branch words that select the endpoint, and delivers the
completed path: the halting machine, its opcode, and the bytes it publishes.
`mem₀`/`aw₀` are the entry memory (empty) and active-word count (zero). -/

abbrev mem₀ : ByteArray := c.entry.memory
abbrev aw₀ : UInt256 := c.entry.activeWords

/-- The fee-loop hypothesis every uninhibited user endpoint carries. -/
abbrev FeeLoopEnds (n : Nat) (o' i' : UInt256) : Prop :=
  feeExit (effExcess c) n (UInt256.ofNat 0) (UInt256.ofNat 17 * UInt256.ofNat 1)
    (UInt256.ofNat 1) = some (o', i')

/-- **Inhibited.** `SLOT_EXCESS = INHIBITOR`: the user path reverts at once. -/
theorem user_inhibited (huser : callerWord c ≠ sysW) (hinh : excessWord c = INH)
    (hg : 2200 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c 15 (at_ c (touch (entrySt c) (UInt256.ofNat 0)) (mem₀ c) (aw₀ c) g 627
        (UInt256.ofNat 0 :: UInt256.ofNat 0 :: excessWord c :: []) e) .REVERT
        ((mem₀ c).readWithPadding 0 0) := by
  have h1 := le_of_exact (gate c (by omega))
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s26 (hcode_of_env c rfl)
      ((eq_eq_zero_iff _ _).mpr (fun h => huser h.symm)) (by omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b27 deposit_b27_ok (n := 6) deposit_b27_bound rfl
      (deposit_b27_shape c (entrySt c) _ _ g₁ e₁ []) (hcode_of_env c rfl) rfl (by omega) (by simp)
  clear h2
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s67 (hcode_of_env c rfl)
      ((eq_ne_zero_iff _ _).mpr hinh.symm) (hvj_deposit 624 (by decide)) (by omega) (by simp)
  clear h3
  obtain ⟨g₄, e₄, hg₄, hr₄⟩ := h4
  obtain ⟨g', e', _, hr', hhalt⟩ := revert_tail c (st := touch (entrySt c) (UInt256.ofNat 0))
    (mem := mem₀ c) (aw := aw₀ c) (g := g₄) (e := e₄) rfl [excessWord c] (activeWords_entry c)
    (by omega) (by simp)
  exact ⟨g', e', ReachesLe.mono (hr₄.trans (Reaches.le hr' le_rfl)) (by decide), hhalt⟩

/-- **Bad calldata size.** Uninhibited, `|I_d| ∉ {0, 184}`: revert after the fee
quote. -/
theorem user_badsize_reverts (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hne184 : cdsizeWord c ≠ UInt256.ofNat 184) (hne0 : cdsizeWord c ≠ ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 70) (at_ c (st₂ c) (mem₀ c) (aw₀ c) g 627
        (UInt256.ofNat 0 :: UInt256.ofNat 0 :: feeWord o' :: []) e) .REVERT
        ((mem₀ c).readWithPadding 0 0) := by
  have h1 := user_prefix c huser hen hfee (by omega)
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s142 (hcode_of_env c rfl)
      ((eq_eq_zero_iff _ _).mpr (fun h => hne184 h.symm)) (by omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b143 deposit_b143_ok (n := 2) deposit_b143_bound rfl
      (deposit_b143_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by omega)
      (by simp)
  clear h2
  simp only [cdsizeW_touch] at h3
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s147 (hcode_of_env c rfl) hne0 (hvj_deposit 624 (by decide))
      (by omega) (by simp)
  clear h3
  obtain ⟨g₄, e₄, hg₄, hr₄⟩ := h4
  obtain ⟨g', e', _, hr', hhalt⟩ := revert_tail c (st := st₂ c) (mem := mem₀ c) (aw := aw₀ c) (g := g₄) (e := e₄)
    rfl [feeWord o'] (activeWords_entry c) (by omega) (by simp)
  exact ⟨g', e', ReachesLe.mono (hr₄.trans (Reaches.le hr' le_rfl)) (by omega), hhalt⟩

/-- **Paid getter.** Empty calldata with nonzero value: revert. -/
theorem user_paidGetter_reverts (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = ⟨0⟩) (hval : valueWord c ≠ ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 70) (at_ c (st₂ c) (mem₀ c) (aw₀ c) g 627
        (UInt256.ofNat 0 :: UInt256.ofNat 0 :: feeWord o' :: []) e) .REVERT
        ((mem₀ c).readWithPadding 0 0) := by
  have h1 := user_prefix c huser hen hfee (by omega)
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s142 (hcode_of_env c rfl)
      ((eq_eq_zero_iff _ _).mpr (fun h => by rw [hsize] at h; exact absurd h (by decide)))
      (by omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b143 deposit_b143_ok (n := 2) deposit_b143_bound rfl
      (deposit_b143_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by omega)
      (by simp)
  clear h2
  simp only [cdsizeW_touch] at h3
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s147 (hcode_of_env c rfl) hsize (by omega) (by simp)
  clear h3
  have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b148 deposit_b148_ok (n := 2) deposit_b148_bound rfl
      (deposit_b148_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by omega)
      (by simp)
  clear h4
  simp only [valueW_touch] at h5
  have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s152 (hcode_of_env c rfl) hval (hvj_deposit 624 (by decide))
      (by omega) (by simp)
  clear h5
  obtain ⟨g₆, e₆, hg₆, hr₆⟩ := h6
  obtain ⟨g', e', _, hr', hhalt⟩ := revert_tail c (st := st₂ c) (mem := mem₀ c) (aw := aw₀ c) (g := g₆) (e := e₆)
    rfl [feeWord o'] (activeWords_entry c) (by omega) (by simp)
  exact ⟨g', e', ReachesLe.mono (hr₆.trans (Reaches.le hr' le_rfl)) (by omega), hhalt⟩

/-- **Fee getter.** Empty calldata, zero value: the fee word is stored at memory
`0` and the 32-byte slice is returned. -/
theorem user_getter_returns (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = ⟨0⟩) (hval : valueWord c = ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 80)
        (at_ c (st₂ c) (mstoreMem (mem₀ c) (UInt256.ofNat 0) (feeWord o'))
          (mAfter (aw₀ c) 0 32) g 158 (UInt256.ofNat 0 :: UInt256.ofNat 32 :: []) e) .RETURN
        ((mstoreMem (mem₀ c) (UInt256.ofNat 0) (feeWord o')).readWithPadding 0 32) := by
  have h1 := user_prefix c huser hen hfee (by omega)
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s142 (hcode_of_env c rfl)
      ((eq_eq_zero_iff _ _).mpr (fun h => by rw [hsize] at h; exact absurd h (by decide)))
      (by omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b143 deposit_b143_ok (n := 2) deposit_b143_bound rfl
      (deposit_b143_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by omega)
      (by simp)
  clear h2
  simp only [cdsizeW_touch] at h3
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s147 (hcode_of_env c rfl) hsize (by omega) (by simp)
  clear h3
  have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b148 deposit_b148_ok (n := 2) deposit_b148_bound rfl
      (deposit_b148_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by omega)
      (by simp)
  clear h4
  simp only [valueW_touch] at h5
  have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s152 (hcode_of_env c rfl) hval (by omega) (by simp)
  clear h5
  have h7 := chainLe h6 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b153 deposit_b153_ok (n := 1) deposit_b153_bound rfl
      (deposit_b153_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by omega)
      (by simp)
  clear h6
  have h8 := chainLe h7 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_mstore deposit_s154 (hcode_of_env c rfl) (B := 1) (by rw [activeWords_entry]; omega)
      (by decide) (by decide) (M := 6) (by decide) (by omega) (by simp)
  clear h7
  have h9 := chainLe h8 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b155 deposit_b155_ok (n := 2) deposit_b155_bound rfl
      (deposit_b155_shape c (st₂ c) _ _ g₁ e₁ []) (hcode_of_env c rfl) rfl (by omega) (by simp)
  clear h8
  obtain ⟨g', e', hg', hr'⟩ := h9
  refine ⟨g', e', ReachesLe.mono hr' (by omega), ?_⟩
  refine halt_RETURN deposit_s158 (hcode_of_env c rfl) (B := 1) (M := 3) (g := g') ?_ ?_ ?_ ?_ ?_ ?_
  · exact toNat_mAfter_le (by rw [activeWords_entry]; omega) (by decide) (by decide)
  · decide
  · decide
  · decide
  · omega
  · simp

/-- **Underpaid submission.** 184-byte calldata with `Iᵥ < fee`: revert. -/
theorem user_underpay_reverts (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = UInt256.ofNat 184) (hlt : valueWord c < feeWord o')
    (hg : 87 * n + 4500 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 80) (at_ c (st₂ c) (mem₀ c) (aw₀ c) g 627
        (UInt256.ofNat 0 :: UInt256.ofNat 0 :: feeWord o' :: []) e) .REVERT
        ((mem₀ c).readWithPadding 0 0) := by
  have h1 := user_prefix c huser hen hfee (by omega)
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s142 (hcode_of_env c rfl) ((eq_ne_zero_iff _ _).mpr hsize.symm)
      (hvj_deposit 159 (by decide)) (by omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b159 deposit_b159_ok (n := 5) deposit_b159_bound rfl
      (deposit_b159_shape c (st₂ c) _ _ g₁ e₁ (feeWord o') []) (hcode_of_env c rfl) rfl (by omega)
      (by simp)
  clear h2
  simp only [valueW_touch] at h3
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s166 (hcode_of_env c rfl) ((lt_ne_zero_iff _ _).mpr hlt)
      (hvj_deposit 624 (by decide)) (by omega) (by simp)
  clear h3
  obtain ⟨g₄, e₄, hg₄, hr₄⟩ := h4
  obtain ⟨g', e', _, hr', hhalt⟩ := revert_tail c (st := st₂ c) (mem := mem₀ c) (aw := aw₀ c) (g := g₄) (e := e₄)
    rfl [feeWord o'] (activeWords_entry c) (by omega) (by simp)
  exact ⟨g', e', ReachesLe.mono (hr₄.trans (Reaches.le hr' le_rfl)) (by omega), hhalt⟩

/-- The masked `uint64` amount word `handle_input` extracts from calldata bytes
`80..88`. -/
abbrev amountWord : UInt256 :=
  UInt256.land (UInt256.ofNat 18446744073709551615) (cdW (entrySt c) (UInt256.ofNat 56))

/-- **Amount below the floor.** Paid 184-byte calldata whose amount is under one
gwei's worth: revert. -/
theorem user_amountFloor_reverts (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = UInt256.ofNat 184) (hpaid : ¬ valueWord c < feeWord o')
    (hfloor : amountWord c < UInt256.ofNat 1000000000)
    (hg : 87 * n + 4600 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 90) (at_ c (st₂ c) (mem₀ c) (aw₀ c) g 627
        (UInt256.ofNat 0 :: UInt256.ofNat 0 :: amountWord c :: feeWord o' :: []) e) .REVERT
        ((mem₀ c).readWithPadding 0 0) := by
  have h1 := user_prefix c huser hen hfee (by omega)
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s142 (hcode_of_env c rfl) ((eq_ne_zero_iff _ _).mpr hsize.symm)
      (hvj_deposit 159 (by decide)) (by omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b159 deposit_b159_ok (n := 5) deposit_b159_bound rfl
      (deposit_b159_shape c (st₂ c) _ _ g₁ e₁ (feeWord o') []) (hcode_of_env c rfl) rfl (by omega)
      (by simp)
  clear h2
  simp only [valueW_touch] at h3
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s166 (hcode_of_env c rfl) ((lt_eq_zero_iff _ _).mpr hpaid)
      (by omega) (by simp)
  clear h3
  have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b167 deposit_b167_ok (n := 8) deposit_b167_bound rfl
      (deposit_b167_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by omega)
      (by simp)
  clear h4
  simp only [cdW_touch] at h5
  have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s190 (hcode_of_env c rfl) ((gt_ne_zero_iff _ _).mpr hfloor)
      (hvj_deposit 624 (by decide)) (by omega) (by simp)
  clear h5
  obtain ⟨g₆, e₆, hg₆, hr₆⟩ := h6
  obtain ⟨g', e', _, hr', hhalt⟩ := revert_tail c (st := st₂ c) (mem := mem₀ c) (aw := aw₀ c) (g := g₆) (e := e₆)
    rfl [amountWord c, feeWord o'] (activeWords_entry c) (by omega) (by simp)
  exact ⟨g', e', ReachesLe.mono (hr₆.trans (Reaches.le hr' le_rfl)) (by omega), hhalt⟩

/-- **Stake not covered.** The value left after the fee is below the amount in
wei: revert. -/
theorem user_stake_reverts (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = UInt256.ofNat 184) (hpaid : ¬ valueWord c < feeWord o')
    (hfloor : ¬ amountWord c < UInt256.ofNat 1000000000)
    (hstake : (valueWord c - feeWord o') < UInt256.ofNat 1000000000 * amountWord c)
    (hg : 87 * n + 4600 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 100) (at_ c (st₂ c) (mem₀ c) (aw₀ c) g 627
        (UInt256.ofNat 0 :: UInt256.ofNat 0 :: []) e) .REVERT
        ((mem₀ c).readWithPadding 0 0) := by
  have h1 := user_prefix c huser hen hfee (by omega)
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s142 (hcode_of_env c rfl) ((eq_ne_zero_iff _ _).mpr hsize.symm)
      (hvj_deposit 159 (by decide)) (by omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b159 deposit_b159_ok (n := 5) deposit_b159_bound rfl
      (deposit_b159_shape c (st₂ c) _ _ g₁ e₁ (feeWord o') []) (hcode_of_env c rfl) rfl (by omega)
      (by simp)
  clear h2
  simp only [valueW_touch] at h3
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s166 (hcode_of_env c rfl) ((lt_eq_zero_iff _ _).mpr hpaid)
      (by omega) (by simp)
  clear h3
  have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b167 deposit_b167_ok (n := 8) deposit_b167_bound rfl
      (deposit_b167_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by omega)
      (by simp)
  clear h4
  simp only [cdW_touch] at h5
  have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s190 (hcode_of_env c rfl) ((gt_eq_zero_iff _ _).mpr hfloor)
      (by omega) (by simp)
  clear h5
  have h7 := chainLe h6 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b191 deposit_b191_ok (n := 7) deposit_b191_bound rfl
      (deposit_b191_shape c (st₂ c) _ _ g₁ e₁ (amountWord c) (feeWord o') [])
      (hcode_of_env c rfl) rfl (by omega) (by simp)
  clear h6
  simp only [valueW_touch] at h7
  have h8 := chainLe h7 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s204 (hcode_of_env c rfl) ((lt_ne_zero_iff _ _).mpr hstake)
      (hvj_deposit 624 (by decide)) (by omega) (by simp)
  clear h7
  obtain ⟨g₈, e₈, hg₈, hr₈⟩ := h8
  obtain ⟨g', e', _, hr', hhalt⟩ := revert_tail c (st := st₂ c) (mem := mem₀ c) (aw := aw₀ c) (g := g₈) (e := e₈)
    rfl [] (activeWords_entry c) (by omega) (by simp)
  exact ⟨g', e', ReachesLe.mono (hr₈.trans (Reaches.le hr' le_rfl)) (by omega), hhalt⟩


/-! ## The accepted deposit

The write path: eight `SSTORE`s, the `CALLDATACOPY` that stages the record, its
`LOG0`, and `STOP`. The pieces of the final state are named so the theorem can be
read: `countStore` is the state after `SLOT_COUNT` is bumped, `tailWord` the
`QUEUE_TAIL` it then reads, `slotBase` the base slot of the appended item, and
`dw off` the calldata word at `off`. -/

abbrev countStore : EvmYul.State .EVM :=
  (touch (st₂ c) (UInt256.ofNat 1)).sstore (UInt256.ofNat 1) (UInt256.ofNat 1 + countWord c)
abbrev tailWord : UInt256 := slotW (countStore c) (UInt256.ofNat 3)
abbrev slotBase : UInt256 := UInt256.ofNat 4 + (UInt256.ofNat 6 * tailWord c)
abbrev dw (off : Nat) : UInt256 := cdW (entrySt c) (UInt256.ofNat off)

/-- The six item words stored, slot by slot. -/
abbrev itemStored : EvmYul.State .EVM :=
  (((((((touch (countStore c) (UInt256.ofNat 3)).sstore (slotBase c) (dw c 0)).sstore
    (UInt256.ofNat 1 + slotBase c) (dw c 32)).sstore
    (UInt256.ofNat 1 + (UInt256.ofNat 1 + slotBase c)) (dw c 64)).sstore
    (UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 + slotBase c))) (dw c 96)).sstore
    (UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 + slotBase c))))
    (dw c 128)).sstore
    (UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 +
      (UInt256.ofNat 1 + slotBase c))))) (dw c 160))

/-- Memory after the record is staged: the 184 calldata bytes at offset `0`. -/
abbrev stagedMem : ByteArray :=
  cdcopyMem (itemStored c) (mem₀ c) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 184)

/-- The final state: item stored, receipt logged, `QUEUE_TAIL` advanced. -/
abbrev appendedSt : EvmYul.State .EVM :=
  (logged (itemStored c) ((stagedMem c).readWithPadding 0 184)).sstore (UInt256.ofNat 3)
    (UInt256.ofNat 1 + tailWord c)

/-- **Accepted submission.** 184-byte calldata, the fee paid, the amount at or
above the floor and the stake covered: the record is stored and logged and the
run halts on `STOP`. Write permission is required, exactly as `Z` demands at the
first `SSTORE`. -/
theorem user_append_stops (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    (hperm : c.env.perm = true)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = UInt256.ofNat 184) (hpaid : ¬ valueWord c < feeWord o')
    (hfloor : ¬ amountWord c < UInt256.ofNat 1000000000)
    (hstake : ¬ (valueWord c - feeWord o') < UInt256.ofNat 1000000000 * amountWord c)
    (hg : 87 * n + 190000 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 150)
        (at_ c (appendedSt c) (stagedMem c) (mAfter (mAfter (aw₀ c) 0 184) 0 184) g 283 [] e)
        .STOP .empty := by
  have h1 := user_prefix c huser hen hfee (by omega)
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s142 (hcode_of_env c rfl) ((eq_ne_zero_iff _ _).mpr hsize.symm)
      (hvj_deposit 159 (by decide)) (by omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b159 deposit_b159_ok (n := 5) deposit_b159_bound rfl
      (deposit_b159_shape c (st₂ c) _ _ g₁ e₁ (feeWord o') []) (hcode_of_env c rfl) rfl (by omega)
      (by simp)
  clear h2
  simp only [valueW_touch] at h3
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s166 (hcode_of_env c rfl) ((lt_eq_zero_iff _ _).mpr hpaid)
      (by omega) (by simp)
  clear h3
  have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b167 deposit_b167_ok (n := 8) deposit_b167_bound rfl
      (deposit_b167_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by omega)
      (by simp)
  clear h4
  simp only [cdW_touch] at h5
  have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s190 (hcode_of_env c rfl) ((gt_eq_zero_iff _ _).mpr hfloor)
      (by omega) (by simp)
  clear h5
  have h7 := chainLe h6 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b191 deposit_b191_ok (n := 7) deposit_b191_bound rfl
      (deposit_b191_shape c (st₂ c) _ _ g₁ e₁ (amountWord c) (feeWord o') [])
      (hcode_of_env c rfl) rfl (by omega) (by simp)
  clear h6
  simp only [valueW_touch] at h7
  have h8 := chainLe h7 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s204 (hcode_of_env c rfl) ((lt_eq_zero_iff _ _).mpr hstake)
      (by omega) (by simp)
  clear h7
  -- 205..212: bump the count
  have h9 := chainLe h8 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b205 deposit_b205_ok (n := 5) deposit_b205_bound rfl
      (deposit_b205_shape c (st₂ c) _ _ g₁ e₁ []) (hcode_of_env c rfl) rfl (by omega) (by simp)
  clear h8
  simp only [slotW_touch] at h9
  have h10 := chainLe h9 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore deposit_s213 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by omega) (by simp)
  clear h9
  -- 214..226: base slot and the first item word
  have h11 := chainLe h10 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b214 deposit_b214_ok (n := 10) deposit_b214_bound rfl
      (deposit_b214_shape c (countStore c) _ _ g₁ e₁ []) (hcode_of_env c (by env_simp)) rfl
      (by omega) (by simp)
  clear h10
  simp only [cdW_touch, cdW_sstore] at h11
  have h12 := chainLe h11 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore deposit_s227 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by omega) (by simp)
  clear h11
  have h13 := chainLe h12 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b228 deposit_b228_ok (n := 5) deposit_b228_bound rfl
      (deposit_b228_shape c _ _ _ g₁ e₁ (slotBase c) [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by omega) (by simp)
  clear h12
  simp only [cdW_touch, cdW_sstore] at h13
  have h14 := chainLe h13 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore deposit_s235 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by omega) (by simp)
  clear h13
  have h15 := chainLe h14 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b236 deposit_b236_ok (n := 5) deposit_b236_bound rfl
      (deposit_b236_shape c _ _ _ g₁ e₁ _ [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by omega) (by simp)
  clear h14
  simp only [cdW_touch, cdW_sstore] at h15
  have h16 := chainLe h15 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore deposit_s243 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by omega) (by simp)
  clear h15
  have h17 := chainLe h16 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b244 deposit_b244_ok (n := 5) deposit_b244_bound rfl
      (deposit_b244_shape c _ _ _ g₁ e₁ _ [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by omega) (by simp)
  clear h16
  simp only [cdW_touch, cdW_sstore] at h17
  have h18 := chainLe h17 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore deposit_s251 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by omega) (by simp)
  clear h17
  have h19 := chainLe h18 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b252 deposit_b252_ok (n := 5) deposit_b252_bound rfl
      (deposit_b252_shape c _ _ _ g₁ e₁ _ [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by omega) (by simp)
  clear h18
  simp only [cdW_touch, cdW_sstore] at h19
  have h20 := chainLe h19 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore deposit_s259 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by omega) (by simp)
  clear h19
  have h21 := chainLe h20 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b260 deposit_b260_ok (n := 5) deposit_b260_bound rfl
      (deposit_b260_shape c _ _ _ g₁ e₁ _ [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by omega) (by simp)
  clear h20
  simp only [cdW_touch, cdW_sstore] at h21
  have h22 := chainLe h21 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore deposit_s267 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by omega) (by simp)
  clear h21
  -- 268..276: stage and log the record
  have h23 := chainLe h22 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b268 deposit_b268_ok (n := 3) deposit_b268_bound rfl
      (deposit_b268_shape c (itemStored c) _ _ g₁ e₁ [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by omega) (by simp)
  clear h22
  have h24 := chainLe h23 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_calldatacopy deposit_s272 (hcode_of_env c (by env_simp)) (B := 6)
      (by rw [activeWords_entry]; omega) (by decide) (by decide) (M := 39) (by decide) (by omega)
      (by simp)
  clear h23
  have h25 := chainLe h24 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b273 deposit_b273_ok (n := 2) deposit_b273_bound rfl
      (deposit_b273_shape c (itemStored c) _ _ g₁ e₁ [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by omega) (by simp)
  clear h24
  have h26 := chainLe h25 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_log0 deposit_s276 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (B := 6) (toNat_mAfter_le (by rw [activeWords_entry]; omega) (by decide) (by decide))
      (by decide) (by decide) (M := 1865) (by decide) (by omega) (by simp)
  clear h25
  -- 277..282: advance the tail
  have h27 := chainLe h26 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b277 deposit_b277_ok (n := 3) deposit_b277_bound rfl
      (deposit_b277_shape c _ _ _ g₁ e₁ (tailWord c) []) (hcode_of_env c (by env_simp))
      rfl (by omega) (by simp)
  clear h26
  have h28 := chainLe h27 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore deposit_s282 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by omega) (by simp)
  clear h27
  obtain ⟨g', e', _, hr'⟩ := h28
  refine ⟨g', e', ReachesLe.mono hr' (by omega), ?_⟩
  exact halt_STOP deposit_s283 (hcode_of_env c (by env_simp)) (by simp)


/-! ## The system path

`read_requests` reads the queue pointers, clamps the count at `MAX_PER_BLOCK`,
runs `accum_loop` once per drained item, updates the pointers, folds the excess
and returns the staged records. -/

abbrev tailWord₀ : UInt256 := slotW (entrySt c) (UInt256.ofNat 3)
abbrev headWord₀ : UInt256 := slotW (entrySt c) (UInt256.ofNat 2)
/-- `tail - head`, as the `SUB` computes it. -/
abbrev queueLen : UInt256 := tailWord₀ c - headWord₀ c
/-- `min(tail - head, 64)`: the number of items drained. -/
def drainWord : UInt256 :=
  if queueLen c < UInt256.ofNat 64 then queueLen c else UInt256.ofNat 64

/-- The state after the two pointer reads. -/
abbrev stP : EvmYul.State .EVM := touch (touch (entrySt c) (UInt256.ofNat 3)) (UInt256.ofNat 2)

/-- **From the entry machine to the loop head**, for the system caller. -/
theorem system_prefix (hsys : callerWord c = sysW) (hg : 4300 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat), c.gas.toNat - 4300 ≤ g.toNat ∧
      ReachesLe depositJumpdests 25 c.entry
        (at_ c (stP c) (mem₀ c) (aw₀ c) g 307
          (UInt256.ofNat 0 :: drainWord c :: headWord₀ c :: tailWord₀ c :: []) e) := by
  have h1 := le_of_exact (gate c (by omega))
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s26 (hcode_of_env c rfl) ((eq_ne_zero_iff _ _).mpr hsys.symm)
      (hvj_deposit 284 (by decide)) (by omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b284 deposit_b284_ok (n := 12) deposit_b284_bound rfl
      (deposit_b284_shape c (entrySt c) _ _ g₁ e₁ []) (hcode_of_env c rfl) rfl (by omega) (by simp)
  clear h2
  simp only [slotW_touch] at h3
  by_cases hlt : queueLen c < UInt256.ofNat 64
  · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_taken deposit_s301 (hcode_of_env c rfl) ((gt_ne_zero_iff _ _).mpr hlt)
        (hvj_deposit 305 (by decide)) (by omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b305 deposit_b305_ok (n := 2) deposit_b305_bound rfl
        (deposit_b305_shape c (stP c) _ _ g₁ e₁ [queueLen c, headWord₀ c, tailWord₀ c])
        (hcode_of_env c rfl) rfl (by omega) (by simp)
    clear h4
    simp only [drainWord, if_pos hlt]
    obtain ⟨g, e, hg', hr⟩ := h5
    exact ⟨g, e, by omega, ReachesLe.mono hr (by omega)⟩
  · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_fallthrough deposit_s301 (hcode_of_env c rfl) ((gt_eq_zero_iff _ _).mpr hlt)
        (by omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b302 deposit_b302_ok (n := 2) deposit_b302_bound rfl
        (deposit_b302_shape c (stP c) _ _ g₁ e₁ (queueLen c) [headWord₀ c, tailWord₀ c])
        (hcode_of_env c rfl) rfl (by omega) (by simp)
    clear h4
    have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b305 deposit_b305_ok (n := 2) deposit_b305_bound rfl
        (deposit_b305_shape c (stP c) _ _ g₁ e₁ [UInt256.ofNat 64, headWord₀ c, tailWord₀ c])
        (hcode_of_env c rfl) rfl (by omega) (by simp)
    clear h5
    simp only [drainWord, if_neg hlt]
    obtain ⟨g, e, hg', hr⟩ := h6
    exact ⟨g, e, by omega, ReachesLe.mono hr (by omega)⟩

/-! ### One iteration of `accum_loop` -/

/-- The `uint64` mask. -/
abbrev mask : UInt256 := UInt256.ofNat 18446744073709551615

/-- **What one `accum_loop` iteration writes.** The six words of the packed
item at `base` go to `off, off+32, …, off+160`; the amount field is re-written
byte by byte, little-endian, at `off+80`. Stated exactly as the pinned code
computes each operand, so that the body lemma is a unification. -/
def writeItem (st : EvmYul.State .EVM) (mem : ByteArray) (off base : UInt256) : ByteArray :=
  let w2 := slotW st (UInt256.ofNat 2 + base)
  let off32 := UInt256.ofNat 32 + off
  let off64 := UInt256.ofNat 32 + off32
  let am := UInt256.land mask (UInt256.shiftRight w2 (UInt256.ofNat 64))
  let off80 := UInt256.ofNat 16 + off64
  let off96 := UInt256.ofNat 32 + off64
  let off128 := UInt256.ofNat 32 + off96
  let off160 := UInt256.ofNat 32 + off128
  let m := mstoreMem mem off (slotW st base)
  let m := mstoreMem m off32 (slotW st (UInt256.ofNat 1 + base))
  let m := mstoreMem m off64 w2
  let m := mstore8Mem m (UInt256.ofNat 7 + off80) (UInt256.shiftRight am (UInt256.ofNat 56))
  let m := mstore8Mem m (UInt256.ofNat 6 + off80) (UInt256.shiftRight am (UInt256.ofNat 48))
  let m := mstore8Mem m (UInt256.ofNat 5 + off80) (UInt256.shiftRight am (UInt256.ofNat 40))
  let m := mstore8Mem m (UInt256.ofNat 4 + off80) (UInt256.shiftRight am (UInt256.ofNat 32))
  let m := mstore8Mem m (UInt256.ofNat 3 + off80) (UInt256.shiftRight am (UInt256.ofNat 24))
  let m := mstore8Mem m (UInt256.ofNat 2 + off80) (UInt256.shiftRight am (UInt256.ofNat 16))
  let m := mstore8Mem m (UInt256.ofNat 1 + off80) (UInt256.shiftRight am (UInt256.ofNat 8))
  let m := mstore8Mem m off80 am
  let m := mstoreMem m off96 (slotW st (UInt256.ofNat 3 + base))
  let m := mstoreMem m off128 (slotW st (UInt256.ofNat 4 + base))
  mstoreMem m off160 (slotW st (UInt256.ofNat 5 + base))

/-- The offsets of one item, as naturals: with `i ≤ 63` nothing wraps. -/
theorem off_toNat {iW : UInt256} (hi : iW.toNat ≤ 63) :
    (UInt256.ofNat 184 * iW).toNat = 184 * iW.toNat :=
  toNat_ofNat_mul_of_lt 184 iW (by rw [size_eq]; omega)

theorem offk_toNat {iW : UInt256} (hi : iW.toNat ≤ 63) (k : Nat) (a : UInt256)
    (ha : a.toNat ≤ 184 * iW.toNat + 200) (hk : k ≤ 200) :
    (UInt256.ofNat k + a).toNat = k + a.toNat :=
  toNat_ofNat_add_of_lt k a (by rw [size_eq]; omega)

/-- The same bound holds for every offset the iteration touches: all are
`184 · i + t` with `t ≤ 192`, so the last byte written is below `12 000` and the
word count stays under `400`. -/
theorem item_offsets {iW : UInt256} (hi : iW.toNat ≤ 63) :
    let off := UInt256.ofNat 184 * iW
    let off32 := UInt256.ofNat 32 + off
    let off64 := UInt256.ofNat 32 + off32
    let off80 := UInt256.ofNat 16 + off64
    let off96 := UInt256.ofNat 32 + off64
    let off128 := UInt256.ofNat 32 + off96
    let off160 := UInt256.ofNat 32 + off128
    off.toNat = 184 * iW.toNat ∧ off32.toNat = 184 * iW.toNat + 32 ∧
      off64.toNat = 184 * iW.toNat + 64 ∧ off80.toNat = 184 * iW.toNat + 80 ∧
      off96.toNat = 184 * iW.toNat + 96 ∧ off128.toNat = 184 * iW.toNat + 128 ∧
      off160.toNat = 184 * iW.toNat + 160 ∧
      (UInt256.ofNat 7 + off80).toNat = 184 * iW.toNat + 87 ∧
      (UInt256.ofNat 6 + off80).toNat = 184 * iW.toNat + 86 ∧
      (UInt256.ofNat 5 + off80).toNat = 184 * iW.toNat + 85 ∧
      (UInt256.ofNat 4 + off80).toNat = 184 * iW.toNat + 84 ∧
      (UInt256.ofNat 3 + off80).toNat = 184 * iW.toNat + 83 ∧
      (UInt256.ofNat 2 + off80).toNat = 184 * iW.toNat + 82 ∧
      (UInt256.ofNat 1 + off80).toNat = 184 * iW.toNat + 81 := by
  intro off off32 off64 off80 off96 off128 off160
  have h0 : off.toNat = 184 * iW.toNat := off_toNat hi
  have h32 : off32.toNat = 184 * iW.toNat + 32 := by
    show (UInt256.ofNat 32 + off).toNat = _
    rw [offk_toNat hi 32 off (by omega) (by omega), h0]; omega
  have h64 : off64.toNat = 184 * iW.toNat + 64 := by
    show (UInt256.ofNat 32 + off32).toNat = _
    rw [offk_toNat hi 32 off32 (by omega) (by omega), h32]; omega
  have h80 : off80.toNat = 184 * iW.toNat + 80 := by
    show (UInt256.ofNat 16 + off64).toNat = _
    rw [offk_toNat hi 16 off64 (by omega) (by omega), h64]; omega
  have h96 : off96.toNat = 184 * iW.toNat + 96 := by
    show (UInt256.ofNat 32 + off64).toNat = _
    rw [offk_toNat hi 32 off64 (by omega) (by omega), h64]; omega
  have h128 : off128.toNat = 184 * iW.toNat + 128 := by
    show (UInt256.ofNat 32 + off96).toNat = _
    rw [offk_toNat hi 32 off96 (by omega) (by omega), h96]; omega
  have h160 : off160.toNat = 184 * iW.toNat + 160 := by
    show (UInt256.ofNat 32 + off128).toNat = _
    rw [offk_toNat hi 32 off128 (by omega) (by omega), h128]; omega
  refine ⟨h0, h32, h64, h80, h96, h128, h160, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [offk_toNat hi _ off80 (by omega) (by omega), h80]; omega)

end Eip8282.Audit.EntryReach.Deposit
