import Eip8282.Audit.EntryReach.Path

/-!
# The bounded fee-quote evaluator

`quoteWithin numerator steps` runs the pinned fee loop `feeExit` from the
quote's initial state — output `0`, accumulator `17`, counter `1` — for at most
`steps` iterations and, if the loop has stopped by then, returns the output
word divided by `17` (in `UInt256` division). It is an *operational* evaluator:
`none` does not model an EVM revert or an out-of-gas abort. It means only that
the proof evaluator did not witness completion within the given budget.

`QuoteCompletes numerator price` is the corresponding propositional interface:
some budget suffices for the evaluator to return `price`. This module proves
the interface is coherent purely at the helper layer:

* `quoteWithin_eq_some_iff` — the quoted price is exactly the `feeExit` output
  divided by `17` (result correspondence);
* `feeExit_some_mono` / `quoteWithin_stable` — once the loop has stopped,
  enlarging the budget cannot change the result (stability);
* `quoteWithin_unique` — the completed price is unique across budgets;
* `quoteCompletes_of_quoteWithin` / `quoteWithin_of_quoteCompletes` /
  `quoteCompletes_iff` — soundness and completeness of `QuoteCompletes`
  against the bounded evaluator;
* `feeExit_zero_of_acc_ne_zero` / `quoteWithin_zero` — with zero budget and a
  nonzero initial accumulator the evaluator returns `none`;
* `feeExit_stopped_zero_budget` / `feeExit_last_step_stopped` — a loop that has
  already stopped (or stops on its last step) still yields `some`, even with
  zero remaining budget.

Nothing here runs the EVM, references `Model`, or touches the registered
guarantees: the only dependency is `EntryReach.Path`, where `feeExit` lives.
-/

namespace Eip8282.Audit.EntryReach

open EvmYul

/-! ## The evaluator and its propositional interface -/

/-- **The bounded fee quote.** Run `feeExit numerator` from the quote's initial
state `(out, acc, i) = (0, 17, 1)` for at most `steps` iterations; if it stops,
the quote is the output divided by `17`. `none` means only that the evaluator
did not witness completion within the budget — not an EVM revert or
out-of-gas. -/
def quoteWithin (numerator : UInt256) (steps : Nat) : Option UInt256 :=
  (feeExit numerator steps ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1)).map
    (·.1 / UInt256.ofNat 17)

/-- **The quote completes at a price.** Operational: some budget suffices for
`quoteWithin` to return `price`. Not a total function and not a mathematical
tariff. -/
def QuoteCompletes (numerator price : UInt256) : Prop :=
  ∃ steps, quoteWithin numerator steps = some price

/-! ## `feeExit` helper facts -/

/-- A stopped loop (`acc = 0`) returns its output and counter at any budget,
zero included. -/
theorem feeExit_of_acc_zero (X : UInt256) (o i : UInt256) (n : Nat) :
    feeExit X n o ⟨0⟩ i = some (o, i) := by
  cases n <;> simp [feeExit]

/-- With zero budget and a nonzero accumulator the loop has not stopped:
the result is `none`. -/
theorem feeExit_zero_of_acc_ne_zero {X o a i : UInt256} (ha : a ≠ ⟨0⟩) :
    feeExit X 0 o a i = none := by
  simp [feeExit, ha]

/-- **Stability of the loop under extra budget.** Once `feeExit` has returned,
spending more iterations cannot change the result: the loop only ever returns
when `acc = 0`, and from there every budget returns the same pair. -/
theorem feeExit_some_mono {X : UInt256} :
    ∀ {n : Nat} {o a i : UInt256} {r : UInt256 × UInt256},
      feeExit X n o a i = some r → ∀ {m : Nat}, n ≤ m → feeExit X m o a i = some r := by
  intro n
  induction n with
  | zero =>
    intro o a i r h m _
    by_cases ha : a = ⟨0⟩
    · subst ha
      rw [feeExit_of_acc_zero X o i 0] at h
      obtain rfl := Option.some.inj h
      exact feeExit_of_acc_zero X o i m
    · rw [feeExit_zero_of_acc_ne_zero ha] at h
      contradiction
  | succ n ih =>
    intro o a i r h m hm
    by_cases ha : a = ⟨0⟩
    · subst ha
      rw [feeExit_of_acc_zero X o i (n + 1)] at h
      obtain rfl := Option.some.inj h
      exact feeExit_of_acc_zero X o i m
    · have hstep : ∀ k : Nat, feeExit X (k + 1) o a i
          = feeExit X k (a + o) ((X * a) / (i * UInt256.ofNat 17))
              (UInt256.ofNat 1 + i) := by
        intro k; simp [feeExit, ha]
      rw [hstep n] at h
      cases m with
      | zero => omega
      | succ m =>
        rw [hstep m]
        exact ih h (Nat.le_of_succ_le_succ hm)

/-! ## Result correspondence -/

/-- **The quote is the loop's output over `17`.** `quoteWithin` returns
`some price` exactly when `feeExit` stops within the budget from the quote's
initial state and `price` is its output word divided by `17`. -/
theorem quoteWithin_eq_some_iff {X : UInt256} {steps : Nat} {price : UInt256} :
    quoteWithin X steps = some price ↔
      ∃ o i : UInt256,
        feeExit X steps ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) = some (o, i) ∧
          price = o / UInt256.ofNat 17 := by
  constructor
  · intro h
    unfold quoteWithin at h
    cases hf : feeExit X steps ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) with
    | none => rw [hf] at h; contradiction
    | some r =>
      obtain ⟨o, i⟩ := r
      rw [hf] at h
      change some (o / UInt256.ofNat 17) = some price at h
      exact ⟨o, i, rfl, (Option.some.inj h).symm⟩
  · rintro ⟨o, i, hfee, rfl⟩
    simp [quoteWithin, hfee]

/-- A stopped loop determines the quote at that budget. -/
theorem quoteWithin_some_of_feeExit {X o i : UInt256} {steps : Nat}
    (h : feeExit X steps ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) = some (o, i)) :
    quoteWithin X steps = some (o / UInt256.ofNat 17) := by
  exact quoteWithin_eq_some_iff.mpr ⟨o, i, h, rfl⟩

/-! ## Stability and uniqueness across budgets -/

/-- **Stability.** A quote that completes within `m` iterations still completes
at the same price with any larger budget. -/
theorem quoteWithin_stable {X : UInt256} {m n : Nat} {price : UInt256}
    (h : quoteWithin X m = some price) (hle : m ≤ n) :
    quoteWithin X n = some price := by
  obtain ⟨o, i, hfee, rfl⟩ := quoteWithin_eq_some_iff.mp h
  exact quoteWithin_some_of_feeExit (feeExit_some_mono hfee hle)

/-- **Uniqueness.** Two budgets that both witness completion quote the same
price. -/
theorem quoteWithin_unique {X : UInt256} {m n : Nat} {p q : UInt256}
    (hm : quoteWithin X m = some p) (hn : quoteWithin X n = some q) : p = q := by
  rcases le_total m n with h | h
  · rw [quoteWithin_stable hm h] at hn
    exact Option.some.inj hn
  · rw [quoteWithin_stable hn h] at hm
    exact (Option.some.inj hm).symm

/-- The completed price of `QuoteCompletes` is unique. -/
theorem quoteCompletes_unique {X p q : UInt256}
    (hp : QuoteCompletes X p) (hq : QuoteCompletes X q) : p = q := by
  obtain ⟨m, hm⟩ := hp
  obtain ⟨n, hn⟩ := hq
  exact quoteWithin_unique hm hn

/-! ## Soundness and completeness against the bounded evaluator -/

/-- **Soundness.** Whatever the bounded evaluator returns is a completed
quote. -/
theorem quoteCompletes_of_quoteWithin {X price : UInt256} {steps : Nat}
    (h : quoteWithin X steps = some price) : QuoteCompletes X price :=
  ⟨steps, h⟩

/-- **Completeness.** Every completed quote is witnessed by the bounded
evaluator at some budget. -/
theorem quoteWithin_of_quoteCompletes {X price : UInt256}
    (h : QuoteCompletes X price) : ∃ steps, quoteWithin X steps = some price :=
  h

/-- **The interface at the loop level.** `QuoteCompletes` holds exactly when
`feeExit` stops from the quote's initial state at some budget, with the price
its output divided by `17`. -/
theorem quoteCompletes_iff {X price : UInt256} :
    QuoteCompletes X price ↔
      ∃ (steps : Nat) (o i : UInt256),
        feeExit X steps ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) = some (o, i) ∧
          price = o / UInt256.ofNat 17 := by
  constructor
  · rintro ⟨steps, h⟩
    obtain ⟨o, i, hfee, rfl⟩ := quoteWithin_eq_some_iff.mp h
    exact ⟨steps, o, i, hfee, rfl⟩
  · rintro ⟨steps, o, i, hfee, rfl⟩
    exact ⟨steps, quoteWithin_some_of_feeExit hfee⟩

/-! ## The budget edge cases -/

/-- **Zero budget, nonzero initial accumulator: no quote.** The quote's initial
accumulator is `17 ≠ 0`, so at budget `0` the loop has not stopped and the
evaluator returns `none`. Again, `none` is not an EVM revert or out-of-gas:
the evaluator simply did not witness completion. -/
theorem quoteWithin_zero (X : UInt256) : quoteWithin X 0 = none := by
  simp [quoteWithin,
    feeExit_zero_of_acc_ne_zero (show (UInt256.ofNat 17 : UInt256) ≠ ⟨0⟩ by decide)]

/-- **Already stopped: a quote even with zero remaining budget.** If the loop
reaches `acc = 0`, the result is `some` at every remaining budget, `0`
included. -/
theorem feeExit_stopped_zero_budget (X o i : UInt256) :
    feeExit X 0 o ⟨0⟩ i = some (o, i) :=
  feeExit_of_acc_zero X o i 0

/-- **Stopping on the last step still quotes.** If the next accumulator is
zero, the loop stops exactly as the budget runs out and returns the updated
output and counter. -/
theorem feeExit_last_step_stopped {X o i a : UInt256} (ha : a ≠ ⟨0⟩)
    (hnext : (X * a) / (i * UInt256.ofNat 17) = ⟨0⟩) (n : Nat) :
    feeExit X (n + 1) o a i = some (a + o, UInt256.ofNat 1 + i) := by
  have hstep : feeExit X (n + 1) o a i
      = feeExit X n (a + o) ((X * a) / (i * UInt256.ofNat 17))
          (UInt256.ofNat 1 + i) := by
    simp [feeExit, ha]
  rw [hstep, hnext]
  exact feeExit_of_acc_zero X (a + o) (UInt256.ofNat 1 + i) n

/-! ## Pure helper-layer tests -/

/-- No budget, no quote: the evaluator returns `none`. -/
example : quoteWithin (UInt256.ofNat 0) 0 = none := by decide

/-- `X = 0` zeroes the accumulator in one step; the quote is `17 / 17 = 1`. -/
example : quoteWithin (UInt256.ofNat 0) 1 = some (UInt256.ofNat 1) := by decide

/-- `X = 1` takes two steps (`17 ↦ 1 ↦ 0`) and quotes `18 / 17 = 1`. -/
example : quoteWithin (UInt256.ofNat 1) 2 = some (UInt256.ofNat 1) := by decide

/-- Stability, concretely: the same quote at a larger budget. -/
example : quoteWithin (UInt256.ofNat 1) 5 = some (UInt256.ofNat 1) := by decide

/-- Completion at the propositional interface. -/
example : QuoteCompletes (UInt256.ofNat 0) (UInt256.ofNat 1) :=
  ⟨1, by decide⟩

/-- Uniqueness, concretely: `X = 0` cannot complete at any other price. -/
example : ∀ p : UInt256, QuoteCompletes (UInt256.ofNat 0) p → p = UInt256.ofNat 1 := by
  rintro p ⟨s, hs⟩
  exact quoteWithin_unique hs (show quoteWithin (UInt256.ofNat 0) 1 = some (UInt256.ofNat 1) from by decide)

#print axioms quoteWithin_eq_some_iff
#print axioms quoteWithin_stable
#print axioms quoteWithin_unique
#print axioms quoteCompletes_iff
#print axioms quoteWithin_zero
#print axioms feeExit_stopped_zero_budget
#print axioms feeExit_last_step_stopped

end Eip8282.Audit.EntryReach
