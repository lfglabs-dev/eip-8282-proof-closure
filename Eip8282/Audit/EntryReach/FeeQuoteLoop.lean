import Eip8282.Audit.EntryReach.Path
import Eip8282.Audit.EntryReach.FeeQuote

/-!
# FeeQuoteLoop: bounded pure helper facts for the quote witness consumer

This module isolates the contract between `Path.feeExit` (the UInt256 word loop)
and `FeeQuote.quoteWithin` for a local integrator that may later consume a
completed quote witness.

EXACT SCOPE (per d191d4f6c83abe90a1f4ad5146c4550c491b4c79):
- Pure helper layer only.
- `none` from `quoteWithin` / `feeExit` means: the proof evaluator did not
  witness loop completion inside the allotted `Nat` step budget.
- `none` is NEVER interpreted as EVM revert or out-of-gas.
- Stability: a `some` result at budget `n` is the same pair at every `m ≥ n`.
- Uniqueness: completed price is unique across budgets that witness completion.
- Edge cases: zero budget + nonzero accumulator ⇒ `none`;
  zero accumulator ⇒ `some` even at budget 0.
- NO assumptions: no `noWrap`, no `tail < 2^64`, no fee termination as
  a constructor, no reachable-image termination, no gas facts from
  `AdmissibleCall`, no Model, no public IDs.
- Tests remain at the pure helper layer.

This patch is NOT three-guarantee closure. It supplies a completed quote
witness shape that a consumer may use later.
-/

namespace Eip8282.Audit.EntryReach

open EvmYul

/-! ## Semantic contract on `none` (pure evaluator, not EVM) -/

/-- `quoteWithin X steps = none` means the bounded evaluator did not witness
completion of the fee loop (i.e., `acc = 0`) within `steps` iterations.
It does not model an EVM revert and does not model out-of-gas. -/
theorem quoteWithin_none_means_not_witnessed {X : UInt256} {steps : Nat} :
    quoteWithin X steps = none →
      ¬ ∃ o i, feeExit X steps ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) = some (o, i) := by
  intro h ⟨o, i, he⟩
  exact Option.noConfusion (h.symm.trans (quoteWithin_some_of_feeExit he))

/-- `feeExit X n o a i = none` means the evaluator did not witness `acc = 0`
within the budget `n`: the accumulator is nonzero and no budget `k ≤ n`
returns either. It is not an EVM abort. -/
theorem feeExit_none_means_not_witnessed {X o a i : UInt256} {n : Nat}
    (h : feeExit X n o a i = none) :
    a ≠ ⟨0⟩ ∧ ∀ k ≤ n, feeExit X k o a i = none := by
  constructor
  · intro ha
    subst ha
    exact Option.noConfusion (h.symm.trans (feeExit_of_acc_zero X o i n))
  · intro k hk
    cases hk' : feeExit X k o a i with
    | none => rfl
    | some r =>
      exact Option.noConfusion (h.symm.trans (feeExit_some_mono hk' hk))

/-! ## Stability: once `some`, same pair at any larger budget -/

/-- If `feeExit` returns `some r` at budget `n`, it returns the same `r` at
every `m ≥ n`. This is the loop stability fact. -/
theorem feeExit_some_stable {X : UInt256} {n : Nat} {o a i : UInt256} {r : UInt256 × UInt256} :
    feeExit X n o a i = some r → ∀ {m : Nat}, n ≤ m → feeExit X m o a i = some r :=
  feeExit_some_mono

/-- `quoteWithin` is stable: a price witnessed at `m` is witnessed at any `n ≥ m`. -/
theorem quoteWithin_stable_budget {X : UInt256} {m n : Nat} {price : UInt256}
    (h : quoteWithin X m = some price) (hle : m ≤ n) :
    quoteWithin X n = some price :=
  quoteWithin_stable h hle

/-! ## Uniqueness of completed price across budgets -/

/-- Two budgets that both witness a completed quote return the same price. -/
theorem quote_price_unique_across_budgets {X : UInt256} {m n : Nat} {p q : UInt256}
    (hm : quoteWithin X m = some p) (hn : quoteWithin X n = some q) : p = q :=
  quoteWithin_unique hm hn

/-- `QuoteCompletes` determines a unique price. -/
theorem quoteCompletes_price_unique {X p q : UInt256}
    (hp : QuoteCompletes X p) (hq : QuoteCompletes X q) : p = q :=
  quoteCompletes_unique hp hq

/-! ## Zero-budget and zero-accumulator edge cases -/

/-- Zero remaining budget with nonzero accumulator yields `none`.
The evaluator simply did not see completion. -/
theorem feeExit_budget0_nonzero_acc_none {X o a i : UInt256} (ha : a ≠ ⟨0⟩) :
    feeExit X 0 o a i = none :=
  feeExit_zero_of_acc_ne_zero ha

/-- Zero accumulator yields `some` at every budget, including budget 0. -/
theorem feeExit_acc0_yields_some_at_budget0 {X o i : UInt256} :
    feeExit X 0 o ⟨0⟩ i = some (o, i) :=
  feeExit_of_acc_zero X o i 0

/-- `quoteWithin` at budget 0 (initial acc = 17 ≠ 0) yields `none`. -/
theorem quoteWithin_budget0_none (X : UInt256) : quoteWithin X 0 = none :=
  quoteWithin_zero X

/-- At budget 0 both sides are `none` (the quote's initial accumulator is
`17 ≠ 0`), so the correspondence holds vacuously: no price is witnessed at
budget 0, by the evaluator, on either side. -/
theorem quoteWithin_acc0_some_even_at_0 {X o i : UInt256} :
    quoteWithin X 0 = some (o / UInt256.ofNat 17) ↔
      feeExit X 0 ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) = some (o, i) := by
  have h1 : quoteWithin X 0 = none := quoteWithin_zero X
  have h2 : feeExit X 0 ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) = none :=
    feeExit_zero_of_acc_ne_zero (show (UInt256.ofNat 17 : UInt256) ≠ ⟨0⟩ by decide)
  constructor
  · intro h; exact Option.noConfusion (h1.symm.trans h)
  · intro h; exact Option.noConfusion (h2.symm.trans h)

/-! ## Result correspondence at the loop level (pure) -/

/-- `quoteWithin` returns `some price` exactly when `feeExit` from the
quote initial state stops within the budget and `price` is output/17. -/
theorem quoteWithin_corresponds_to_feeExit {X : UInt256} {steps : Nat} {price : UInt256} :
    quoteWithin X steps = some price ↔
      ∃ o i : UInt256,
        feeExit X steps ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) = some (o, i) ∧
          price = o / UInt256.ofNat 17 :=
  quoteWithin_eq_some_iff

/-- `QuoteCompletes` is exactly a stopping `feeExit` from the initial state
with the price being output divided by 17. -/
theorem QuoteCompletes_iff_feeExit {X price : UInt256} :
    QuoteCompletes X price ↔
      ∃ (steps : Nat) (o i : UInt256),
        feeExit X steps ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) = some (o, i) ∧
          price = o / UInt256.ofNat 17 :=
  quoteCompletes_iff

/-! ## Pure helper-layer tests (no EVM, no Model) -/

example : quoteWithin (UInt256.ofNat 0) 0 = none := by decide
example : quoteWithin (UInt256.ofNat 0) 1 = some (UInt256.ofNat 1) := by decide
example : quoteWithin (UInt256.ofNat 1) 2 = some (UInt256.ofNat 1) := by decide
example : quoteWithin (UInt256.ofNat 1) 5 = some (UInt256.ofNat 1) := by decide

example : QuoteCompletes (UInt256.ofNat 0) (UInt256.ofNat 1) := ⟨1, by decide⟩

example : ∀ p : UInt256, QuoteCompletes (UInt256.ofNat 0) p → p = UInt256.ofNat 1 := by
  rintro p ⟨s, hs⟩
  exact quoteWithin_unique hs (show quoteWithin (UInt256.ofNat 0) 1 = some (UInt256.ofNat 1) from by decide)

/-! ## Axiom surface (pure helper facts only) -/

#print axioms quoteWithin_none_means_not_witnessed
#print axioms feeExit_none_means_not_witnessed
#print axioms feeExit_some_stable
#print axioms quoteWithin_stable_budget
#print axioms quote_price_unique_across_budgets
#print axioms quoteCompletes_price_unique
#print axioms feeExit_budget0_nonzero_acc_none
#print axioms feeExit_acc0_yields_some_at_budget0
#print axioms quoteWithin_budget0_none
#print axioms quoteWithin_acc0_some_even_at_0
#print axioms quoteWithin_corresponds_to_feeExit
#print axioms QuoteCompletes_iff_feeExit

end Eip8282.Audit.EntryReach
