import Eip8282.Audit.Integrator.TransferFrame

/-!
# Natural funds across the actual Θ entry transfer

The finite total observes AccountMap.toList. Sufficient funds is a premise on
the real pre-transfer sender balance. No supply ceiling, poststate agreement,
or alternate transition semantics is assumed. This module concerns the actual
credit-then-debit entryWorld, not subsequent code execution or transaction fees.
-/
namespace Eip8282.Audit.Integrator.TransferFunding

open EvmYul EvmYul.EVM
open MessageCall
open Eip8282.Audit.EntryReach
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

def worldBalance (world : AccountMap .EVM) (addr : AccountAddress) : Nat :=
  ((world.get? addr).map (fun acc => acc.balance.toNat)).getD 0

def worldFunds (world : AccountMap .EVM) : Nat :=
  (world.toList.map (fun kv => kv.2.balance.toNat)).sum

private theorem lookup_insert (world : AccountMap .EVM) (key addr : AccountAddress)
    (account : Account .EVM) :
    (world.insert key account).get? addr = if key = addr then some account else world.get? addr := by
  exact (Std.TreeMap.getElem?_insert (t := world) (k := key) (a := addr) (v := account)).trans
    (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)

private theorem filter_sum (xs : List (AccountAddress × Account .EVM))
    (key : AccountAddress) (old : Account .EVM)
    (hd : (xs.map Prod.fst).Nodup) (hm : (key, old) ∈ xs) :
    ((xs.filter (fun kv => !(key == kv.1))).map (fun kv => kv.2.balance.toNat)).sum +
      old.balance.toNat = (xs.map (fun kv => kv.2.balance.toNat)).sum := by
  induction xs with
  | nil => simp at hm
  | cons kv xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hd
    rcases List.mem_cons.mp hm with he | hm
    · subst kv
      have hf : xs.filter (fun kv => !(key == kv.1)) = xs := by
        apply List.filter_eq_self.mpr
        intro kv hkv
        have hn : key ≠ kv.1 := by
          intro he
          exact hd.1 (List.mem_map.mpr ⟨kv, hkv, he.symm⟩)
        simp [hn]
      simp [hf, Nat.add_comm]
    · have hn : key ≠ kv.1 := by
        intro he
        apply hd.1
        exact List.mem_map.mpr ⟨(key, old), hm, he⟩
      have ht := ih hd.2 hm
      simp only [List.filter_cons, show (key == kv.1) = false from by simp [hn],
        Bool.not_false, ↓reduceIte, List.map_cons, List.sum_cons]
      omega

/-- A replacement identity without natural subtraction or Account BEq laws. -/
theorem funds_insert (world : AccountMap .EVM) (key : AccountAddress)
    (account : Account .EVM) :
    worldFunds (world.insert key account) + worldBalance world key =
      worldFunds world + account.balance.toNat := by
  have hp := (Std.TreeMap.toList_insert_perm (t := world) (k := key) (v := account)).map
    (fun kv => kv.2.balance.toNat)
  have hs := hp.sum_eq
  have heq : (fun kv : AccountAddress × Account .EVM => decide (¬ ((key == kv.1) = true))) =
      (fun kv => !(key == kv.1)) := by
    funext kv
    cases (key == kv.1) <;> rfl
  rw [heq] at hs
  simp only [List.map_cons, List.sum_cons] at hs
  unfold worldFunds worldBalance
  rw [hs]
  cases ho : world.get? key with
  | none =>
    have hf : world.toList.filter (fun kv => !(key == kv.1)) = world.toList := by
      apply List.filter_eq_self.mpr
      intro kv hkv
      have hn : key ≠ kv.1 := by
        intro he
        have hk := (Std.TreeMap.mem_toList_iff_getElem?_eq_some).mp hkv
        change world.get? kv.1 = some kv.2 at hk
        rw [← he, ho] at hk
        cases hk
      simp [hn]
    rw [hf]
    simp [Nat.add_comm]
  | some old =>
    have hd : (world.toList.map Prod.fst).Nodup := by
      rw [Std.TreeMap.map_fst_toList_eq_keys]
      exact Std.TreeMap.nodup_keys
    have ht := filter_sum world.toList key old hd
      (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr ho)
    simp only [Option.map_some, Option.getD_some]
    omega

theorem balance_le_funds (world : AccountMap .EVM) (key : AccountAddress) :
    worldBalance world key ≤ worldFunds world := by
  have hs := funds_insert world key (default : Account .EVM)
  change worldFunds (world.insert key default) + worldBalance world key = worldFunds world + 0 at hs
  omega

private theorem add_toNat_le (a b : UInt256) : (a+b).toNat ≤ a.toNat+b.toNat :=
  Nat.mod_le _ _

private theorem add_sub_cancel_word (a b : UInt256) : (a+b)-b = a := by
  apply congrArg UInt256.mk
  apply Fin.ext
  change (((UInt256.size - b.toNat) + (a.toNat + b.toNat) % UInt256.size) % UInt256.size) = a.toNat
  have ha := toNat_lt_size a
  have hb := toNat_lt_size b
  unfold UInt256.size at *
  omega

/-- The exact credited intermediate map from Context.entryWorld. -/
private def credited (c : Context) : AccountMap .EVM :=
  match c.world.get? c.target with
  | none => if c.value != UInt256.ofNat 0 then
      c.world.insert c.target { (default : Account .EVM) with balance := c.value }
    else c.world
  | some acc => c.world.insert c.target { acc with balance := acc.balance + c.value }

private theorem credit_funds_le (c : Context) :
    worldFunds (credited c) ≤ worldFunds c.world + c.value.toNat := by
  unfold credited
  cases ho : c.world.get? c.target with
  | none =>
    dsimp only
    split
    · have hs := funds_insert c.world c.target { (default : Account .EVM) with balance := c.value }
      simp only [worldBalance, ho, Option.map_none, Option.getD_none, Nat.add_zero] at hs
      exact hs.le
    · omega
  | some acc =>
    dsimp only
    have hs := funds_insert c.world c.target { acc with balance := acc.balance + c.value }
    simp only [worldBalance, ho, Option.map_some, Option.getD_some] at hs
    have ha := add_toNat_le acc.balance c.value
    omega

private theorem credit_lookup_other (c : Context) (addr : AccountAddress)
    (hn : c.target ≠ addr) : (credited c).get? addr = c.world.get? addr := by
  unfold credited
  cases ho : c.world.get? c.target with
  | none =>
    dsimp only
    split
    · rw [lookup_insert, if_neg hn]
    · rfl
  | some acc =>
    dsimp only
    rw [lookup_insert, if_neg hn]

private theorem entry_funds_distinct (c : Context) (hn : c.target ≠ c.caller)
    (hfunded : c.value.toNat ≤ worldBalance c.world c.caller) :
    worldFunds c.entryWorld ≤ worldFunds c.world := by
  have hcredit := credit_funds_le c
  have hl := credit_lookup_other c c.caller hn
  change worldFunds (match (credited c).get? c.caller with
    | none => credited c
    | some acc => (credited c).insert c.caller { acc with balance := acc.balance - c.value }) ≤ _
  rw [hl]
  cases hs : c.world.get? c.caller with
  | none =>
    simp only [worldBalance, hs, Option.map_none, Option.getD_none] at hfunded
    dsimp only
    omega
  | some acc =>
    simp only [worldBalance, hs, Option.map_some, Option.getD_some] at hfunded
    dsimp only
    have hi := funds_insert (credited c) c.caller { acc with balance := acc.balance - c.value }
    simp only [worldBalance, hl, hs, Option.map_some, Option.getD_some] at hi
    have hd := toNat_sub_of_le acc.balance c.value hfunded
    change worldFunds ((credited c).insert c.caller { acc with balance := acc.balance - c.value }) +
      acc.balance.toNat = worldFunds (credited c) + (acc.balance-c.value).toNat at hi
    rw [hd] at hi
    omega

private theorem entry_funds_alias (c : Context) (he : c.caller = c.target)
    (hfunded : c.value.toNat ≤ worldBalance c.world c.caller) :
    worldFunds c.entryWorld = worldFunds c.world := by
  rw [he] at hfunded
  unfold Context.entryWorld
  rw [he]
  cases ho : c.world.get? c.target with
  | none =>
    simp only [worldBalance, ho, Option.map_none, Option.getD_none] at hfunded
    have hv : c.value = UInt256.ofNat 0 :=
      (eq_ofNat_iff_toNat c.value 0 (by decide)).mpr (by omega)
    simp only [hv, show (UInt256.ofNat 0 != UInt256.ofNat 0) = false from rfl,
      Bool.false_eq_true, ↓reduceIte, ho]
  | some acc =>
    dsimp only
    rw [lookup_insert, if_pos rfl]
    dsimp only
    have hj := funds_insert c.world c.target { acc with balance := acc.balance + c.value }
    have hk := funds_insert
      (c.world.insert c.target { acc with balance := acc.balance + c.value }) c.target
      { acc with balance := (acc.balance + c.value) - c.value }
    simp only [worldBalance, lookup_insert, ho, Option.map_some,
      Option.getD_some, add_sub_cancel_word, ↓reduceIte] at hj hk
    rw [add_sub_cancel_word]
    omega

/-- A funded actual Θ entry transfer cannot increase the finite natural total.
All balances and the updated world are read from the existing Context. The
sender may equal the target, and either address may initially be absent. No
supply ceiling or recipient-addition fit is assumed. -/
theorem entry_funds_le (c : Context)
    (hfunded : c.value.toNat ≤ worldBalance c.world c.caller) :
    worldFunds c.entryWorld ≤ worldFunds c.world := by
  by_cases he : c.caller = c.target
  · exact (entry_funds_alias c he hfunded).le
  · exact entry_funds_distinct c (Ne.symm he) hfunded

/-- Any prior total budget therefore also bounds this actual entry world. -/
theorem entry_funds_budget (c : Context) (budget : Nat)
    (hfunded : c.value.toNat ≤ worldBalance c.world c.caller)
    (hbudget : worldFunds c.world ≤ budget) :
    worldFunds c.entryWorld ≤ budget :=
  (entry_funds_le c hfunded).trans hbudget

#print axioms funds_insert
#print axioms balance_le_funds
#print axioms entry_funds_le
#print axioms entry_funds_budget

end Eip8282.Audit.Integrator.TransferFunding
