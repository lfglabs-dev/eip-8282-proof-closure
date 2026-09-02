import Eip8282.Audit.EntryReach.Steps
import Eip8282.Audit.EntryReach.Blocks

/-!
# Path glue: jump tables, entry facts, branch words, and `Ends`

The path theorems of `Eip8282.Audit.EntryReach.Deposit` / `Exit` chain the
block and step lemmas from the entry machine to a halting instruction. This
module holds what every such chain needs: the jump tables as `Nat` lists tied to
`Ξ`'s own tables, the fields of `XiCall.entry` the runs start from, the reading
of each branch word the two runtimes test, and `Ends`, the shape of a completed
path.
-/

namespace Eip8282.Audit.EntryReach

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall jumpdestsOf)
open Eip8282.Audit.Model (Kind)

/-! ## Jump tables -/

theorem hvj_deposit : ∀ n ∈ depositJumpdestNats, depositJumpdests.contains (UInt256.ofNat n) = true :=
  fun _ hn =>
    Array.contains_iff_exists_mem_beq.mpr ⟨_, mem_depositJumpdests_of_mem_nats hn, beq_self_uint _⟩

theorem hvj_exit : ∀ n ∈ exitJumpdestNats, exitJumpdests.contains (UInt256.ofNat n) = true :=
  fun _ hn =>
    Array.contains_iff_exists_mem_beq.mpr ⟨_, mem_exitJumpdests_of_mem_nats hn, beq_self_uint _⟩

theorem jumpdestsOf_deposit : jumpdestsOf .deposit = depositJumpdests := rfl
theorem jumpdestsOf_exit : jumpdestsOf .exit = exitJumpdests := rfl

/-! ## The entry machine -/

/-- The state `Ξ` starts from, as a state. -/
abbrev entrySt {kind : Kind} (c : XiCall kind) : EvmYul.State .EVM := c.entry.toState

@[simp] theorem executionEnv_entrySt {kind : Kind} (c : XiCall kind) :
    (entrySt c).executionEnv = c.env := rfl

theorem memory_entry {kind : Kind} (c : XiCall kind) : c.entry.memory = ByteArray.empty := rfl

theorem activeWords_entry {kind : Kind} (c : XiCall kind) : c.entry.activeWords.toNat = 0 := rfl

theorem code_deposit (c : XiCall .deposit) : c.env.code = depositRuntime := c.code_pinned
theorem code_exit (c : XiCall .exit) : c.env.code = exitRuntime := c.code_pinned

/-- Gas arithmetic: unfold the fee-schedule constants and the quadratic memory
bound, then `omega`. -/
macro "gas_omega" : tactic => `(tactic| omega)

/-! ## Environment readers through the state writers -/

theorem perm_of_env {kind : Kind} (c : XiCall kind) {st : EvmYul.State .EVM}
    (h : st.executionEnv = c.env) (hperm : c.env.perm = true) : st.executionEnv.perm = true := by
  rw [h]; exact hperm

@[simp] theorem cdW_sstore (st : EvmYul.State .EVM) (k v off : UInt256) :
    cdW (st.sstore k v) off = cdW st off := by
  unfold cdW EvmYul.State.calldataload
  rw [executionEnv_sstore]

@[simp] theorem callerW_sstore (st : EvmYul.State .EVM) (k v : UInt256) :
    callerW (st.sstore k v) = callerW st := by
  unfold callerW; rw [executionEnv_sstore]

@[simp] theorem valueW_sstore (st : EvmYul.State .EVM) (k v : UInt256) :
    valueW (st.sstore k v) = valueW st := by
  unfold valueW; rw [executionEnv_sstore]

@[simp] theorem cdsizeW_sstore (st : EvmYul.State .EVM) (k v : UInt256) :
    cdsizeW (st.sstore k v) = cdsizeW st := by
  unfold cdsizeW; rw [executionEnv_sstore]

@[simp] theorem cdW_logged (st : EvmYul.State .EVM) (data : ByteArray) (off : UInt256) :
    cdW (logged st data) off = cdW st off := rfl

@[simp] theorem callerW_logged (st : EvmYul.State .EVM) (data : ByteArray) :
    callerW (logged st data) = callerW st := rfl

@[simp] theorem cdsizeW_logged (st : EvmYul.State .EVM) (data : ByteArray) :
    cdsizeW (logged st data) = cdsizeW st := rfl

@[simp] theorem valueW_logged (st : EvmYul.State .EVM) (data : ByteArray) :
    valueW (logged st data) = valueW st := rfl

/-- The environment of a state reached from the entry by touches, stores and logs. -/
macro "env_simp" : tactic =>
  `(tactic| simp only [executionEnv_touch, executionEnv_sstore, executionEnv_logged,
      executionEnv_entrySt])

/-! ## A listed block, with its length and gas bound as literals -/

theorem block_step {kind : Kind} {vj : Array UInt256} {vjNats : List Nat}
    (hvj : ∀ n ∈ vjNats, vj.contains (UInt256.ofNat n) = true)
    {code : ByteArray} (sites : List Site) (hsites : sitesOk code sites = true)
    {K n : Nat} (hK : blockBound sites = K) (hn : sites.length = n)
    {c : XiCall kind} {st st' : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc pc' : Nat} {stk stk' : Stack UInt256} {e : Nat}
    (hshape : symBlock vjNats (sites.map Prod.snd) (at_ c st mem aw g pc stk e)
      = some (at_ c st' mem aw g pc' stk' e))
    (hcode : st.executionEnv.code = code) (hpc : pc = headPc sites)
    (hgas : K ≤ g.toNat) (hlen : stk.length + n ≤ 1024) :
    ∃ g' e', g.toNat - K ≤ g'.toNat ∧
      Reaches vj n (at_ c st mem aw g pc stk e) (at_ c st' mem aw g' pc' stk' e') := by
  subst hK hn
  exact reach_block hvj sites hsites hcode hpc hgas hlen hshape

/-! ## Branch words

Every `JUMPI` of the two runtimes tests one of these words. -/

theorem fromBool_ne_zero (b : Bool) : UInt256.fromBool b ≠ ⟨0⟩ ↔ b = true := by
  cases b <;> simp [UInt256.fromBool, Bool.toUInt256] <;> decide

theorem fromBool_eq_zero (b : Bool) : UInt256.fromBool b = ⟨0⟩ ↔ b = false := by
  cases b <;> simp [UInt256.fromBool, Bool.toUInt256] <;> decide

theorem eq_ne_zero_iff (a b : UInt256) : UInt256.eq a b ≠ ⟨0⟩ ↔ a = b := by
  unfold UInt256.eq
  rw [fromBool_ne_zero, decide_eq_true_eq]

theorem eq_eq_zero_iff (a b : UInt256) : UInt256.eq a b = ⟨0⟩ ↔ a ≠ b := by
  unfold UInt256.eq
  rw [fromBool_eq_zero, decide_eq_false_iff_not]

theorem lt_ne_zero_iff (a b : UInt256) : UInt256.lt a b ≠ ⟨0⟩ ↔ a < b := by
  unfold UInt256.lt
  rw [fromBool_ne_zero, decide_eq_true_eq]

theorem lt_eq_zero_iff (a b : UInt256) : UInt256.lt a b = ⟨0⟩ ↔ ¬ a < b := by
  unfold UInt256.lt
  rw [fromBool_eq_zero, decide_eq_false_iff_not]

theorem gt_ne_zero_iff (a b : UInt256) : UInt256.gt a b ≠ ⟨0⟩ ↔ b < a := by
  unfold UInt256.gt
  rw [fromBool_ne_zero, decide_eq_true_eq]

theorem gt_eq_zero_iff (a b : UInt256) : UInt256.gt a b = ⟨0⟩ ↔ ¬ b < a := by
  unfold UInt256.gt
  rw [fromBool_eq_zero, decide_eq_false_iff_not]

theorem toNat_lt_iff (a b : UInt256) : a < b ↔ a.toNat < b.toNat := Iff.rfl

theorem isZero_ne_zero_iff (a : UInt256) : UInt256.isZero a ≠ ⟨0⟩ ↔ a = ⟨0⟩ := by
  unfold UInt256.isZero UInt256.eq0
  rw [fromBool_ne_zero]
  constructor
  · intro h
    cases a with | mk v =>
    have : v = (0 : Fin UInt256.size) := by
      have h' : (v == (0 : Fin UInt256.size)) = true := h
      exact beq_iff_eq.mp h'
    rw [this]
  · rintro rfl
    exact beq_self_uint _

theorem isZero_eq_zero_iff (a : UInt256) : UInt256.isZero a = ⟨0⟩ ↔ a ≠ ⟨0⟩ := by
  unfold UInt256.isZero UInt256.eq0
  rw [fromBool_eq_zero]
  constructor
  · intro h heq
    subst heq
    have := beq_self_uint (⟨0⟩ : UInt256)
    rw [h] at this
    exact Bool.false_ne_true this
  · intro h
    cases a with | mk v =>
    have hv : v ≠ (0 : Fin UInt256.size) := fun hv => h (by rw [hv])
    show (v == (0 : Fin UInt256.size)) = false
    simp [hv]

/-- The fee loop's condition word: `ISZERO (GT acc 0)` is nonzero exactly when
the accumulator is zero. -/
theorem feeLoop_exit_iff (a : UInt256) :
    UInt256.isZero (UInt256.gt a (UInt256.ofNat 0)) ≠ ⟨0⟩ ↔ a = ⟨0⟩ := by
  rw [isZero_ne_zero_iff]
  constructor
  · intro h
    rw [gt_eq_zero_iff] at h
    cases a with | mk v =>
    have : ¬ (0 : Nat) < v.val := h
    have hv : v.val = 0 := by omega
    show UInt256.mk v = UInt256.mk 0
    congr 1
    exact Fin.ext hv
  · rintro rfl
    rw [gt_eq_zero_iff]
    exact fun h => Nat.lt_irrefl _ h

theorem feeLoop_continue_iff (a : UInt256) :
    UInt256.isZero (UInt256.gt a (UInt256.ofNat 0)) = ⟨0⟩ ↔ a ≠ ⟨0⟩ := by
  constructor
  · intro h ha
    exact ((feeLoop_exit_iff a).mpr ha) h
  · intro ha
    by_contra h
    exact ha ((feeLoop_exit_iff a).mp h)

/-! ## Reachability with a bounded step count

Loops make the exact number of `X` iterations depend on the data, and what the
fuel argument needs is only an upper bound. -/

/-- `s` reaches `s'` in at most `K` non-halting iterations. -/
def ReachesLe (vj : Array UInt256) (K : Nat) (s s' : EVM.State) : Prop :=
  ∃ k, k ≤ K ∧ Reaches vj k s s'

theorem Reaches.le {vj : Array UInt256} {k K : Nat} {s s' : EVM.State}
    (h : Reaches vj k s s') (hk : k ≤ K) : ReachesLe vj K s s' := ⟨k, hk, h⟩

theorem ReachesLe.trans {vj : Array UInt256} {K K' : Nat} {s s' s'' : EVM.State}
    (h₁ : ReachesLe vj K s s') (h₂ : ReachesLe vj K' s' s'') : ReachesLe vj (K + K') s s'' := by
  obtain ⟨k, hk, h₁⟩ := h₁
  obtain ⟨k', hk', h₂⟩ := h₂
  exact ⟨k + k', by omega, h₁.trans h₂⟩

theorem ReachesLe.mono {vj : Array UInt256} {K K' : Nat} {s s' : EVM.State}
    (h : ReachesLe vj K s s') (hK : K ≤ K') : ReachesLe vj K' s s' := by
  obtain ⟨k, hk, h⟩ := h
  exact ⟨k, by omega, h⟩

theorem ReachesLe.xRuns_of_fuel {vj : Array UInt256} {K : Nat} {s s' : EVM.State}
    (h : ReachesLe vj K s s') {fuel : Nat} (hfuel : K + 1 ≤ fuel) :
    ∃ tr rem, XRuns vj fuel s tr (rem + 1) s' := by
  obtain ⟨k, hk, h⟩ := h
  exact h.xRuns_of_fuel (by omega)

/-! ## A completed path -/

/-- **A completed path of `c`.** In at most `K` non-halting iterations the run
reaches the machine `x`, which halts on `w` publishing `out`. -/
def Ends {kind : Kind} (c : XiCall kind) (K : Nat) (x : EVM.State) (w : Operation .EVM)
    (out : ByteArray) : Prop :=
  ReachesLe (jumpdestsOf kind) K c.entry x ∧ Halt (jumpdestsOf kind) x w out


/-! ## Chaining steps

Each step lemma above yields `∃ g' e', g.toNat - K ≤ g'.toNat ∧ Reaches vj k s (F g' e')`
for the machine `F g' e'` it lands on. `chain` composes such steps, threading the
gas lower bound relative to the gas `g₀` the path started with. -/

theorem chain {vj : Array UInt256} {k k' : Nat} {s : EVM.State} {F G : UInt256 → Nat → EVM.State}
    {K K' : Nat} {g₀ : UInt256}
    (h₁ : ∃ g e, g₀.toNat - K ≤ g.toNat ∧ Reaches vj k s (F g e))
    (h₂ : ∀ g e, g₀.toNat - K ≤ g.toNat →
      ∃ g' e', g.toNat - K' ≤ g'.toNat ∧ Reaches vj k' (F g e) (G g' e')) :
    ∃ g' e', g₀.toNat - (K + K') ≤ g'.toNat ∧ Reaches vj (k + k') s (G g' e') := by
  obtain ⟨g, e, hg, hr⟩ := h₁
  obtain ⟨g', e', hg', hr'⟩ := h₂ g e hg
  exact ⟨g', e', by omega, hr.trans hr'⟩

/-- `chain`, with bounded step counts. -/
theorem chainLe {vj : Array UInt256} {k k' : Nat} {s : EVM.State} {F G : UInt256 → Nat → EVM.State}
    {K K' : Nat} {g₀ : UInt256}
    (h₁ : ∃ g e, g₀.toNat - K ≤ g.toNat ∧ ReachesLe vj k s (F g e))
    (h₂ : ∀ g e, g₀.toNat - K ≤ g.toNat →
      ∃ g' e', g.toNat - K' ≤ g'.toNat ∧ ReachesLe vj k' (F g e) (G g' e')) :
    ∃ g' e', g₀.toNat - (K + K') ≤ g'.toNat ∧ ReachesLe vj (k + k') s (G g' e') := by
  obtain ⟨g, e, hg, hr⟩ := h₁
  obtain ⟨g', e', hg', hr'⟩ := h₂ g e hg
  exact ⟨g', e', by omega, hr.trans hr'⟩

/-- An exact-count result, as a bounded one. -/
theorem le_of_exact {vj : Array UInt256} {k : Nat} {s : EVM.State} {G : UInt256 → Nat → EVM.State}
    {K : Nat} {g₀ : UInt256}
    (h : ∃ g' e', g₀.toNat - K ≤ g'.toNat ∧ Reaches vj k s (G g' e')) :
    ∃ g' e', g₀.toNat - K ≤ g'.toNat ∧ ReachesLe vj k s (G g' e') := by
  obtain ⟨g', e', hg, hr⟩ := h
  exact ⟨g', e', hg, Reaches.le hr le_rfl⟩


/-! ## Word arithmetic for offsets -/

theorem size_eq : UInt256.size =
    115792089237316195423570985008687907853269984665640564039457584007913129639936 := rfl

theorem toNat_ofNat_add_of_lt (k : Nat) (a : UInt256) (h : k + a.toNat < UInt256.size) :
    (UInt256.ofNat k + a).toNat = k + a.toNat := by
  show ((UInt256.ofNat k).val + a.val).val = k + a.toNat
  rw [Fin.val_add]
  show (k % UInt256.size + a.toNat) % UInt256.size = k + a.toNat
  rw [Nat.mod_eq_of_lt (by omega : k < UInt256.size)]
  exact Nat.mod_eq_of_lt h

theorem toNat_ofNat_mul_of_lt (k : Nat) (a : UInt256) (h : k * a.toNat < UInt256.size) :
    (UInt256.ofNat k * a).toNat = k * a.toNat := by
  show ((UInt256.ofNat k).val * a.val).val = k * a.toNat
  rw [Fin.val_mul]
  show (k % UInt256.size * a.toNat) % UInt256.size = k * a.toNat
  rcases Nat.eq_zero_or_pos a.toNat with h0 | hpos
  · rw [h0, Nat.mul_zero, Nat.mul_zero, Nat.zero_mod]
  · have hk : k < UInt256.size := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right k hpos) h
    rw [Nat.mod_eq_of_lt hk]
    exact Nat.mod_eq_of_lt h

theorem ofNat_toNat' (a : UInt256) : UInt256.ofNat a.toNat = a := by
  have h : (UInt256.ofNat a.toNat).val = a.val := by
    apply Fin.ext
    show a.toNat % UInt256.size = a.val.val
    exact Nat.mod_eq_of_lt a.val.isLt
  cases hx : UInt256.ofNat a.toNat
  cases hy : a
  simp_all

theorem ofNat_inj_of_lt {m n : Nat} (hm : m < UInt256.size) (hn : n < UInt256.size)
    (h : UInt256.ofNat m = UInt256.ofNat n) : m = n := by
  have := congrArg UInt256.toNat h
  rwa [toNat_ofNat_of_lt hm, toNat_ofNat_of_lt hn] at this

/-! ## Threading a bounded active-word count

Memory writers change `activeWords`; nothing reads it except the next memory
charge, and for that a bound is enough. `chainAw` threads such a bound. -/

theorem chainAw {vj : Array UInt256} {k k' : Nat} {s : EVM.State}
    {F G : UInt256 → UInt256 → Nat → EVM.State} {K K' B : Nat} {g₀ : UInt256}
    (h₁ : ∃ (aw g : UInt256) (e : Nat),
      aw.toNat ≤ B ∧ g₀.toNat - K ≤ g.toNat ∧ ReachesLe vj k s (F aw g e))
    (h₂ : ∀ (aw g : UInt256) (e : Nat), aw.toNat ≤ B → g₀.toNat - K ≤ g.toNat →
      ∃ (aw' g' : UInt256) (e' : Nat),
        aw'.toNat ≤ B ∧ g.toNat - K' ≤ g'.toNat ∧ ReachesLe vj k' (F aw g e) (G aw' g' e')) :
    ∃ (aw' g' : UInt256) (e' : Nat), aw'.toNat ≤ B ∧ g₀.toNat - (K + K') ≤ g'.toNat ∧
      ReachesLe vj (k + k') s (G aw' g' e') := by
  obtain ⟨aw, g, e, haw, hg, hr⟩ := h₁
  obtain ⟨aw', g', e', haw', hg', hr'⟩ := h₂ aw g e haw hg
  exact ⟨aw', g', e', haw', by omega, hr.trans hr'⟩

/-- A step that does not touch memory, in the threaded form. -/
theorem liftAw {vj : Array UInt256} {k : Nat} {s : EVM.State} {G : UInt256 → Nat → EVM.State}
    {K B : Nat} {g₀ aw : UInt256} (haw : aw.toNat ≤ B)
    (h : ∃ (g' : UInt256) (e' : Nat), g₀.toNat - K ≤ g'.toNat ∧ Reaches vj k s (G g' e')) :
    ∃ (aw' g' : UInt256) (e' : Nat), aw'.toNat ≤ B ∧ g₀.toNat - K ≤ g'.toNat ∧
      ReachesLe vj k s (G g' e') := by
  obtain ⟨g', e', hg, hr⟩ := h
  exact ⟨aw, g', e', haw, hg, Reaches.le hr le_rfl⟩

/-- A memory step whose new active-word count is bounded. -/
theorem liftAw' {vj : Array UInt256} {k : Nat} {s : EVM.State} {G : UInt256 → Nat → EVM.State}
    {K B : Nat} {g₀ aw' : UInt256} (haw : aw'.toNat ≤ B)
    (h : ∃ (g' : UInt256) (e' : Nat), g₀.toNat - K ≤ g'.toNat ∧ Reaches vj k s (G g' e')) :
    ∃ (aw'' g' : UInt256) (e' : Nat), aw''.toNat ≤ B ∧ g₀.toNat - K ≤ g'.toNat ∧
      ReachesLe vj k s (G g' e') := by
  obtain ⟨g', e', hg, hr⟩ := h
  exact ⟨aw', g', e', haw, hg, Reaches.le hr le_rfl⟩

/-! ## States equal up to the accessed-keys set -/

/-- `st` is `st₀` with, at most, a different set of accessed keys and refund
balance: what `SLOAD` leaves behind. Every storage read agrees. -/
structure Touched (st₀ st : EvmYul.State .EVM) : Prop where
  accountMap : st.accountMap = st₀.accountMap
  executionEnv : st.executionEnv = st₀.executionEnv
  σ₀ : st.σ₀ = st₀.σ₀
  logs : st.substate.logSeries = st₀.substate.logSeries

theorem Touched.refl (st : EvmYul.State .EVM) : Touched st st := ⟨rfl, rfl, rfl, rfl⟩

theorem Touched.touch {st₀ st : EvmYul.State .EVM} (h : Touched st₀ st) (k : UInt256) :
    Touched st₀ (touch st k) :=
  ⟨h.accountMap, h.executionEnv, h.σ₀, h.logs⟩

theorem Touched.trans {st₀ st₁ st₂ : EvmYul.State .EVM} (h₁ : Touched st₀ st₁)
    (h₂ : Touched st₁ st₂) : Touched st₀ st₂ :=
  ⟨h₂.accountMap.trans h₁.accountMap, h₂.executionEnv.trans h₁.executionEnv,
    h₂.σ₀.trans h₁.σ₀, h₂.logs.trans h₁.logs⟩

theorem slotW_of_touched {st₀ st : EvmYul.State .EVM} (h : Touched st₀ st) (k : UInt256) :
    slotW st k = slotW st₀ k := by
  unfold slotW EvmYul.State.sload EvmYul.State.lookupAccount
  simp only [h.accountMap, h.executionEnv]

theorem cdsizeW_of_touched {st₀ st : EvmYul.State .EVM} (h : Touched st₀ st) :
    cdsizeW st = cdsizeW st₀ := by
  unfold cdsizeW; rw [h.executionEnv]

end Eip8282.Audit.EntryReach
