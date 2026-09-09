import Eip8282.Audit.EntryReach.FeeQuote
import Eip8282.Audit.EntryReach.Deposit

/-!
# QuoteCompletes / `quoteWithin` onto the getter prefix

`FeeQuotePath` already turns a completing quote into `Deposit.fee_loop`'s
`feeExit` hypothesis, but it drops the remaining-gas conjunct
`g.toNat - (87 * n + 25) ≤ g'.toNat` that `fee_loop` proves. This module
exposes that drop and composes `Deposit.user_prefix` from a `quoteWithin`
witness at `effExcess c`.

The getter tail (`user_getter_returns` → `Ends` on `RETURN`) is already in
`Deposit`; it is applied here under the extra hypotheses it already asks for
(empty calldata, zero value, gas `87 * n + 4500`). That is **not** total
getter success: those hypotheses are still open, and `quoteWithin = none` is
still not EVM out-of-gas.

* Not Model-256 (`FeeLoopEnds` at fuel 256 / `feeExit_of_fits`).
* Not success with only loop-head gas `87 * n + 25`.
* Prefix remaining gas is `c.gas.toNat - (87 * n + 4400)`; getter `Ends`
  needs the extra `100` already in `user_getter_returns`.
-/

namespace Eip8282.Audit.EntryReach

open EvmYul
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall)

/-- The quote's initial accumulator `17` is the word `17 * 1` the deposit
runtime pushes at the loop head. -/
theorem quote_acc_eq : UInt256.ofNat 17 * UInt256.ofNat 1 = UInt256.ofNat 17 := by
  decide

/-- The quote's initial output `ofNat 0` is `⟨0⟩`. -/
theorem quote_out_eq : UInt256.ofNat 0 = (⟨0⟩ : UInt256) := rfl

/-- `FeeLoopEnds`'s `feeExit` is the quote's initial state. -/
theorem feeExit_quote_init (X : UInt256) (n : Nat) :
    feeExit X n (UInt256.ofNat 0) (UInt256.ofNat 17 * UInt256.ofNat 1)
        (UInt256.ofNat 1) =
      feeExit X n ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) := by
  rw [quote_out_eq, quote_acc_eq]

/-- **Remaining gas of `Deposit.fee_loop`.** Same adapter as
`quoteCompletes_deposit_fee_loop`, but the `g.toNat - (87 * n + 25) ≤ g'.toNat`
conjunct `fee_loop` proves is kept.

`quoteWithin = none` is not EVM OOG. Success is conditional on Deposit's
loop-head gas `87 * n + 25`, not on getter-prefix gas `4400` and not Model-256. -/
theorem quoteCompletes_deposit_fee_loop_gas
    (c : XiCall .deposit) {st : EvmYul.State .EVM} {mem : ByteArray}
    {aw g : UInt256} {e n : Nat} {X price : UInt256}
    (henv : st.executionEnv = c.env) (hqc : QuoteCompletes X price)
    (hn : quoteWithin X n = some price) (hg : 87 * n + 25 ≤ g.toNat) :
    ∃ (o' i' g' : UInt256) (e' : Nat),
      feeExit X n ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) = some (o', i') ∧
        price = Deposit.feeWord o' ∧
        g.toNat - (87 * n + 25) ≤ g'.toNat ∧
        ReachesLe depositJumpdests (24 * n + 7)
          (at_ c st mem aw g 100
            (⟨0⟩ :: UInt256.ofNat 17 :: UInt256.ofNat 1 :: X :: UInt256.ofNat 17 :: []) e)
          (at_ c st mem aw g' 127
            (o' :: ⟨0⟩ :: i' :: X :: UInt256.ofNat 17 :: []) e') := by
  obtain ⟨o', i', hfee, hprice⟩ := quoteWithin_eq_some_iff.mp hn
  have := quoteCompletes_unique hqc (quoteCompletes_of_quoteWithin hn)
  obtain ⟨g', e', hgas, hr⟩ :=
    Deposit.fee_loop (st := st) (mem := mem) (aw := aw) c X henv
      n ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) g e o' i' hfee hg
  exact ⟨o', i', g', e', hfee, this ▸ hprice, hgas, hr⟩

/-- **`quoteWithin` at `effExcess` is `FeeLoopEnds`.** -/
theorem quoteWithin_feeLoopEnds (c : XiCall .deposit) {n : Nat} {price : UInt256}
    (hn : quoteWithin (Deposit.effExcess c) n = some price) :
    ∃ o' i' : UInt256,
      Deposit.FeeLoopEnds c n o' i' ∧ price = Deposit.feeWord o' := by
  obtain ⟨o', i', hfee, hprice⟩ := quoteWithin_eq_some_iff.mp hn
  refine ⟨o', i', ?_, hprice⟩
  simpa [Deposit.FeeLoopEnds, feeExit_quote_init] using hfee

/-- **User prefix from a completing quote.** Non-SYSTEM, uninhibited, and
prefix gas `87 * n + 4400`: `Deposit.user_prefix` lands on the calldata-size
dispatch at PC 142 with remaining gas `c.gas.toNat - (87 * n + 4400)`.

Not total getter success (no empty-calldata / zero-value / extra 100 gas),
not Model-256, not EVM OOG. -/
theorem quoteWithin_user_prefix (c : XiCall .deposit)
    (huser : Deposit.callerWord c ≠ sysW) (hen : Deposit.excessWord c ≠ INH)
    {n : Nat} {price : UInt256}
    (hn : quoteWithin (Deposit.effExcess c) n = some price)
    (hg : 87 * n + 4400 ≤ c.gas.toNat) :
    ∃ (o' i' g : UInt256) (e : Nat),
      Deposit.FeeLoopEnds c n o' i' ∧
        price = Deposit.feeWord o' ∧
        c.gas.toNat - (87 * n + 4400) ≤ g.toNat ∧
        ReachesLe depositJumpdests (24 * n + 60) c.entry
          (at_ c (Deposit.st₂ c) c.entry.memory c.entry.activeWords g 142
            (UInt256.ofNat 159 :: UInt256.eq (UInt256.ofNat 184) (Deposit.cdsizeWord c) ::
              Deposit.feeWord o' :: []) e) := by
  obtain ⟨o', i', hfee, hprice⟩ := quoteWithin_feeLoopEnds c hn
  obtain ⟨g, e, hgas, hr⟩ := Deposit.user_prefix c huser hen hfee hg
  exact ⟨o', i', g, e, hfee, hprice, hgas, hr⟩

/-- **Getter `Ends`, when the prefix is a getter.** Empty calldata, zero value,
and getter gas `87 * n + 4500`: `Deposit.user_getter_returns` already proves
the `RETURN` of the 32-byte fee word. Applied here from `quoteWithin`; the
opcode tail is not reproved.

**Hole named if those extra hypotheses are dropped:** without
`cdsizeWord = 0`, `valueWord = 0`, and the extra `100` gas,
`user_getter_returns` does not apply. This is therefore **not** total getter
success, not Model-256, and `quoteWithin = none` is still not EVM OOG. -/
theorem quoteWithin_user_getter_returns (c : XiCall .deposit)
    (huser : Deposit.callerWord c ≠ sysW) (hen : Deposit.excessWord c ≠ INH)
    {n : Nat} {price : UInt256}
    (hn : quoteWithin (Deposit.effExcess c) n = some price)
    (hsize : Deposit.cdsizeWord c = ⟨0⟩) (hval : Deposit.valueWord c = ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) :
    ∃ (o' i' g : UInt256) (e : Nat),
      Deposit.FeeLoopEnds c n o' i' ∧
        price = Deposit.feeWord o' ∧
        Ends c (24 * n + 80)
          (at_ c (Deposit.st₂ c)
            (mstoreMem (Deposit.mem₀ c) (UInt256.ofNat 0) (Deposit.feeWord o'))
            (mAfter (Deposit.aw₀ c) 0 32) g 158
            (UInt256.ofNat 0 :: UInt256.ofNat 32 :: []) e) .RETURN
          ((mstoreMem (Deposit.mem₀ c) (UInt256.ofNat 0) (Deposit.feeWord o')).readWithPadding 0 32) := by
  obtain ⟨o', i', hfee, hprice⟩ := quoteWithin_feeLoopEnds c hn
  obtain ⟨g, e, hend⟩ := Deposit.user_getter_returns c huser hen hfee hsize hval hg
  exact ⟨o', i', g, e, hfee, hprice, hend⟩

#print axioms quoteCompletes_deposit_fee_loop_gas
#print axioms quoteWithin_user_prefix
#print axioms quoteWithin_user_getter_returns

end Eip8282.Audit.EntryReach
