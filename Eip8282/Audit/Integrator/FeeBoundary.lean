import Eip8282.Audit.Integrator.FeeSafeDomain

/-!
# A checked tariff divergence just above the certified interval

These are counterexample certificates, not substitutes for universal proofs.
The natural and word evaluators are the untruncated definitions. Their finite
stopping witnesses establish exact distinct prices; they do not impose a
semantic iteration bound. Protocol reachability of this numerator is separate.
-/
namespace Eip8282.Audit.Integrator.FeeBoundary

open EvmYul
open Eip8282.Audit.EntryReach
open MathFee

set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

def naturalPrice : Nat :=
  80668064690921409049190791237320678716946849613533250306370202067869504081

def wordPrice : UInt256 := UInt256.ofNat
  32087365885911168062721653499988857431024628719292649881555161070975172167

/-- The untruncated natural recurrence stops with this price. -/
theorem natural_quote : quoteWithinNat 2893 462 = some naturalPrice := by decide

/-- The real word recurrence stops earlier after multiplication overflow. -/
theorem word_quote : quoteWithin (UInt256.ofNat 2893) 457 = some wordPrice := by decide

/-- No alternative finite witness can make that operational price the natural
price, by uniqueness of the independent natural recurrence. -/
theorem word_price_not_mathematical : ¬ MathQuoteCompletes 2893 wordPrice.toNat := by
  intro h
  have he := mathQuoteCompletes_unique h (show MathQuoteCompletes 2893 naturalPrice from ⟨462, natural_quote⟩)
  exact (by decide : wordPrice.toNat ≠ naturalPrice) he

/-- The next numerator has a strictly lower operational fee, although the
natural fee strictly increases. -/
theorem local_fee_drop :
    wordPrice.toNat < FeeSafeDomain.certificateOutput/17 ∧
    FeeSafeDomain.certificateOutput/17 < naturalPrice := by decide

theorem operational_counterexample :
    ∃ n price, quoteWithin (UInt256.ofNat 2893) n = some price ∧
      ¬ MathQuoteCompletes 2893 price.toNat :=
  ⟨457, wordPrice, word_quote, word_price_not_mathematical⟩

#print axioms natural_quote
#print axioms word_quote
#print axioms word_price_not_mathematical
#print axioms local_fee_drop
#print axioms operational_counterexample

end Eip8282.Audit.Integrator.FeeBoundary
