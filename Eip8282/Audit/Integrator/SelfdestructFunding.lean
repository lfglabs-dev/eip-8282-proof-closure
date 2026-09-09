import Eip8282.Audit.Integrator.StorageFunding

/-!
# Actual SELFDESTRUCT cannot increase total account balances

The real opcode has different same-address behavior for newly created accounts.
Both burning and keeping that balance are bounded by the same natural total.
No account existence, supply ceiling or desired post-state is assumed.
-/
namespace Eip8282.Audit.Integrator.SelfdestructFunding

open EvmYul EvmYul.EVM
open TransferFunding

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private theorem inserted_other (world : AccountMap .EVM) (source target : AccountAddress)
    (account : Account .EVM) (hne : source ≠ target) :
    (world.insert target account).get? source = world.get? source := by
  exact (Std.TreeMap.getElem?_insert (t := world) (k := target) (a := source) (v := account)).trans
    (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq, Ne.symm hne, ↓reduceIte]; rfl)

/-- Credit a distinct recipient, then zero the old source balance. -/
theorem credit_clear_le (world : AccountMap .EVM) (source target : AccountAddress)
    (fromAcc toAcc : Account .EVM) (hfrom : world.get? source = some fromAcc)
    (hne : source ≠ target)
    (hcredit : toAcc.balance.toNat ≤ worldBalance world target + fromAcc.balance.toNat) :
    worldFunds ((world.insert target toAcc).insert source { fromAcc with balance := ⟨0⟩ }) ≤ worldFunds world := by
  have hc := funds_insert world target toAcc
  have hz := funds_insert (world.insert target toAcc) source { fromAcc with balance := ⟨0⟩ }
  have hi := inserted_other world source target toAcc hne
  simp only [worldBalance, hi, hfrom, Option.map_some, Option.getD_some] at hz
  change worldFunds ((world.insert target toAcc).insert source { fromAcc with balance := ⟨0⟩ }) +
    fromAcc.balance.toNat = worldFunds (world.insert target toAcc) + 0 at hz
  omega

/-- Setting a balance to zero cannot increase the finite total. -/
theorem zero_le (world : AccountMap .EVM) (source : AccountAddress) (account : Account .EVM) :
    worldFunds (world.insert source { account with balance := ⟨0⟩ }) ≤ worldFunds world := by
  have h := funds_insert world source { account with balance := ⟨0⟩ }
  change worldFunds (world.insert source { account with balance := ⟨0⟩ }) +
    worldBalance world source = worldFunds world + 0 at h
  omega

/-- Exact common account-map update from both SELFDESTRUCT branches. -/
def updated (burnSelf : Bool) (world : AccountMap .EVM) (source target : AccountAddress) : AccountMap .EVM :=
  match world.get? source with
  | none => world
  | some fromAcc =>
    match world.get? target with
    | none =>
      if fromAcc.balance == ⟨0⟩ then world
      else (world.insert target { (default : Account .EVM) with balance := fromAcc.balance }).insert
        source { fromAcc with balance := ⟨0⟩ }
    | some toAcc =>
      if target ≠ source then
        (world.insert target { toAcc with balance := toAcc.balance + fromAcc.balance }).insert
          source { fromAcc with balance := ⟨0⟩ }
      else if burnSelf then
        (world.insert target { toAcc with balance := ⟨0⟩ }).insert source { fromAcc with balance := ⟨0⟩ }
      else world

theorem updated_le (burnSelf : Bool) (world : AccountMap .EVM) (source target : AccountAddress) :
    worldFunds (updated burnSelf world source target) ≤ worldFunds world := by
  unfold updated
  cases hs : world.get? source with
  | none => exact Nat.le_refl _
  | some fromAcc =>
    simp only
    cases ht : world.get? target with
    | none =>
      simp only
      split
      · exact Nat.le_refl _
      · have hn : source ≠ target := by intro he; subst target; rw [hs] at ht; cases ht
        apply credit_clear_le world source target fromAcc _ hs hn
        simp only [worldBalance, ht, Option.map_none, Option.getD_none, Nat.zero_add]
        exact Nat.le_refl _
    | some toAcc =>
      simp only
      by_cases hn : target ≠ source
      · rw [if_pos hn]
        apply credit_clear_le world source target fromAcc _ hs (Ne.symm hn)
        simp only [worldBalance, ht, Option.map_some, Option.getD_some]
        exact Nat.mod_le _ _
      · rw [if_neg hn]
        split
        · exact (zero_le _ source fromAcc).trans (zero_le _ target toAcc)
        · exact Nat.le_refl _

/-- Gas charging and stack/PC replacement do not affect this balance result. -/
theorem raw_nonincrease {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (h : EvmYul.step (τ := .EVM) .SELFDESTRUCT arg pre = .ok post) :
    worldFunds post.accountMap ≤ worldFunds pre.accountMap := by
  obtain ⟨sh, pc, stk, ex⟩ := pre
  cases stk with
  | nil => cases h
  | cons dest stk =>
    change (if sh.createdAccounts.contains sh.executionEnv.codeOwner then
      Except.ok _ else Except.ok _) = Except.ok post at h
    split at h
    · cases h
      exact updated_le true sh.accountMap sh.executionEnv.codeOwner (AccountAddress.ofUInt256 dest)
    · cases h
      exact updated_le false sh.accountMap sh.executionEnv.codeOwner (AccountAddress.ofUInt256 dest)

#print axioms updated_le
#print axioms raw_nonincrease

end Eip8282.Audit.Integrator.SelfdestructFunding
