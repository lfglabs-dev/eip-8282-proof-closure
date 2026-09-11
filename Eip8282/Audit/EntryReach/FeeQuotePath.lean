import Eip8282.Audit.EntryReach.FeeQuote
import Eip8282.Audit.EntryReach.Deposit

/-!
# QuoteCompletes as a witness for `Deposit.fee_loop`

`FeeQuote.QuoteCompletes` is a helper-layer statement: some budget makes
`quoteWithin` return a price, i.e. `feeExit` stops from the quote's initial
state `(out, acc, i) = (0, 17, 1)` and the price is the output divided by `17`.
`EntryReach.Deposit.fee_loop` is the existing EVM-loop lemma: given
`feeExit X n o a i = some (o', i')` and gas `87 * n + 25`, the pinned
`fake_expo` head at PC 100 reaches the exit block at PC 127.

This module is the adapter. It does **not** replay opcodes, rewrite
`Deposit.lean` / `Exit.lean` / `Path.lean`, or claim Model-256.

* `quoteCompletes_feeExit` is `quoteCompletes_iff`: `QuoteCompletes` is
  exactly a stopping `feeExit` from the quote's initial state.
* `quoteCompletes_deposit_fee_loop` feeds that `feeExit` witness and
  Deposit's gas hypothesis into `Deposit.fee_loop`.

**Honesty.** `quoteWithin = none` is *not* EVM out-of-gas: it means only that
the proof evaluator did not witness completion within the given budget
(see `FeeQuote`). Success of `fee_loop` is conditional on the gas hypothesis
already in `Deposit` (`87 * n + 25` at the loop head). This is not success
with the announced getter-prefix gas `87 * n + 4400` (`Deposit.user_prefix`),
and it is not Model-256 (`FeeLoopEnds` / `feeExit_of_fits` at fuel 256).
-/

namespace Eip8282.Audit.EntryReach

open EvmYul
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall)

/-- **`QuoteCompletes` is a stopping `feeExit`.** Re-export of
`quoteCompletes_iff`: the quote completes at `price` iff some budget `n`
makes `feeExit` stop from `(0, 17, 1)` with output `o` and `price = o / 17`. -/
theorem quoteCompletes_feeExit {X price : UInt256} :
    QuoteCompletes X price ↔
      ∃ (n : Nat) (o i : UInt256),
        feeExit X n ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) = some (o, i) ∧
          price = o / UInt256.ofNat 17 :=
  quoteCompletes_iff

/-- **A completing quote, under Deposit's loop-head gas, reaches PC 127.**
`n` is a `quoteWithin` witness for `QuoteCompletes X price`. The `feeExit`
pair it implies, together with `87 * n + 25 ≤ g`, is exactly the hypothesis
of `Deposit.fee_loop`; the opcode path is not reproved here.

Not EVM OOG, not getter-prefix gas `87 * n + 4400`, not Model-256. -/
theorem quoteCompletes_deposit_fee_loop
    (c : XiCall .deposit) {st : EvmYul.State .EVM} {mem : ByteArray}
    {aw g : UInt256} {e n : Nat} {X price : UInt256}
    (henv : st.executionEnv = c.env) (hqc : QuoteCompletes X price)
    (hn : quoteWithin X n = some price) (hg : 87 * n + 25 ≤ g.toNat) :
    ∃ (o' i' g' : UInt256) (e' : Nat),
      feeExit X n ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) = some (o', i') ∧
        price = Deposit.feeWord o' ∧
        ReachesLe depositJumpdests (24 * n + 7)
          (at_ c st mem aw g 100
            (⟨0⟩ :: UInt256.ofNat 17 :: UInt256.ofNat 1 :: X :: UInt256.ofNat 17 :: []) e)
          (at_ c st mem aw g' 127
            (o' :: ⟨0⟩ :: i' :: X :: UInt256.ofNat 17 :: []) e') := by
  -- `hqc` and `hn` name the same completed price (uniqueness of QuoteCompletes).
  have := quoteCompletes_unique hqc (quoteCompletes_of_quoteWithin hn)
  obtain ⟨o', i', hfee, hprice⟩ := quoteWithin_eq_some_iff.mp hn
  obtain ⟨g', e', _, hr⟩ :=
    Deposit.fee_loop (st := st) (mem := mem) (aw := aw) c X henv
      n ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) g e o' i' hfee hg
  exact ⟨o', i', g', e', hfee, this ▸ hprice, hr⟩

#print axioms quoteCompletes_feeExit
#print axioms quoteCompletes_deposit_fee_loop

end Eip8282.Audit.EntryReach
