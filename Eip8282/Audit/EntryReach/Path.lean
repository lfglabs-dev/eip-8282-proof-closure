import Eip8282.Audit.Execution.Paths
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





theorem jumpdestsOf_deposit : jumpdestsOf .deposit = depositJumpdests := rfl
theorem jumpdestsOf_exit : jumpdestsOf .exit = exitJumpdests := rfl

/-! ## The entry machine -/









theorem code_deposit (c : XiCall .deposit) : c.env.code = depositRuntime := c.code_pinned
theorem code_exit (c : XiCall .exit) : c.env.code = exitRuntime := c.code_pinned

/-- Gas arithmetic. Every gas fact has the shape `g.toNat - K ≤ g'.toNat`; `omega` handles
truncated subtraction by case splitting, which exhausts the recursion budget once two such atoms
meet, so the subtractions are first turned into the equivalent `g.toNat ≤ g'.toNat + K`. -/
macro "gas_omega" : tactic =>
  `(tactic| ((try simp only [Nat.sub_le_iff_le_add] at *) <;> omega))

/-! ## Environment readers through the state writers -/



















/-- The environment of a state reached from the entry by touches, stores and logs. -/
macro "env_simp" : tactic =>
  `(tactic| simp only [executionEnv_touch, executionEnv_sstore, executionEnv_logged,
      executionEnv_entrySt])

/-! ## A listed block, with its length and gas bound as literals -/



/-! ## Branch words

Every `JUMPI` of the two runtimes tests one of these words. -/









theorem lt_ne_zero_iff (a b : UInt256) : UInt256.lt a b ≠ ⟨0⟩ ↔ a < b := by
  unfold UInt256.lt
  rw [fromBool_ne_zero, decide_eq_true_eq]











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





/-! ## Reachability with a bounded step count

Loops make the exact number of `X` iterations depend on the data, and what the
fuel argument needs is only an upper bound. -/









theorem ReachesLe.xRuns_of_fuel {vj : Array UInt256} {K : Nat} {s s' : EVM.State}
    (h : ReachesLe vj K s s') {fuel : Nat} (hfuel : K + 1 ≤ fuel) :
    ∃ tr rem, XRuns vj fuel s tr (rem + 1) s' := by
  obtain ⟨k, hk, h⟩ := h
  exact h.xRuns_of_fuel (by omega)

/-! ## A completed path -/




/-! ## Chaining steps

Each step lemma above yields `∃ g' e', g.toNat - K ≤ g'.toNat ∧ Reaches vj k s (F g' e')`
for the machine `F g' e'` it lands on. `chain` composes such steps, threading the
gas lower bound relative to the gas `g₀` the path started with. -/








/-! ## Word arithmetic for offsets -/











/-! ## Threading a bounded active-word count

Memory writers change `activeWords`; nothing reads it except the next memory
charge, and for that a bound is enough. `chainAt` threads such a bound between
named machines; it is stated on `at_` directly so that every unification it
asks for is first-order. -/

theorem ReachesLe.refl (vj : Array UInt256) (s : EVM.State) : ReachesLe vj 0 s s :=
  ⟨0, le_rfl, Reaches.refl vj s⟩





/-! ## States equal up to the accessed-keys set -/







theorem Touched.trans {st₀ st₁ st₂ : EvmYul.State .EVM} (h₁ : Touched st₀ st₁)
    (h₂ : Touched st₁ st₂) : Touched st₀ st₂ :=
  ⟨h₂.accountMap.trans h₁.accountMap, h₂.executionEnv.trans h₁.executionEnv,
    h₂.σ₀.trans h₁.σ₀, h₂.logs.trans h₁.logs⟩



theorem cdsizeW_of_touched {st₀ st : EvmYul.State .EVM} (h : Touched st₀ st) :
    cdsizeW st = cdsizeW st₀ := by
  unfold cdsizeW; rw [h.executionEnv]

/-! ## Words and recurrences shared by both runtimes -/









end Eip8282.Audit.EntryReach
