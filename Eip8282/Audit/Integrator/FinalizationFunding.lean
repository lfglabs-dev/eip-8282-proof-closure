import Eip8282.Audit.Integrator.TransferFunding
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Actual balance credits and transaction world cleanup

The actual AccountMap operations and TreeSet/TreeMap folds are used literally.
Credits are bounded by their natural input amount; erasure and transient-store
cleanup cannot create funds. No assumption about the selected deletion set is
needed for this balance statement.
-/
namespace Eip8282.Audit.Integrator.FinalizationFunding
open EvmYul EvmYul.EVM
open TransferFunding
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

theorem credit_le (world : AccountMap .EVM) (addr : AccountAddress) (amount : UInt256) :
    worldFunds (world.increaseBalance .EVM addr amount) ≤ worldFunds world + amount.toNat := by
  unfold AccountMap.increaseBalance
  cases he : world.get? addr with
  | none =>
    have h := funds_insert world addr { (default : Account .EVM) with balance := amount }
    simp only [worldBalance, he, Option.map_none, Option.getD_none, Nat.add_zero] at h
    exact h.le
  | some account =>
    simp only
    have h := funds_insert world addr { account with balance := account.balance+amount }
    simp only [worldBalance, he, Option.map_some, Option.getD_some] at h
    have ha : (account.balance+amount).toNat ≤ account.balance.toNat+amount.toNat := Nat.mod_le _ _
    omega

theorem erase_le (world : AccountMap .EVM) (addr : AccountAddress) :
    worldFunds (world.erase addr) ≤ worldFunds world := by
  have hn : (world.erase addr).toList.Nodup := by
    apply List.Nodup.of_map Prod.fst
    rw [Std.TreeMap.map_fst_toList_eq_keys]
    exact Std.TreeMap.nodup_keys
  have hs : (world.erase addr).toList ⊆ world.toList := by
    intro kv hkv
    have hk := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hkv
    rw [Std.TreeMap.getElem?_erase] at hk
    split at hk
    · cases hk
    · exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hk
  obtain ⟨xs,hperm,hsub⟩ := hn.subperm hs
  unfold worldFunds
  rw [← (hperm.map (fun kv => kv.2.balance.toNat)).sum_eq]
  exact (hsub.map (fun kv => kv.2.balance.toNat)).sum_le_sum (fun n _ => Nat.zero_le n)

theorem erase_list_le (addresses : List AccountAddress) (world : AccountMap .EVM) :
    worldFunds (addresses.foldl (fun st addr => st.erase addr) world) ≤ worldFunds world := by
  induction addresses generalizing world with
  | nil => exact Nat.le_refl _
  | cons addr rest ih =>
    exact (ih (world.erase addr)).trans (erase_le world addr)

theorem erase_set_le (addresses : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM) :
    worldFunds (addresses.foldl (fun st addr => st.erase addr) world) ≤ worldFunds world := by
  rw [Std.TreeSet.foldl_eq_foldl_toList]
  exact erase_list_le _ _

private theorem rebuild_le (entries : List (AccountAddress × Account .EVM)) (world : AccountMap .EVM) :
    worldFunds (entries.foldl (fun st p => st.insert p.1 {p.2 with tstorage := .empty}) world) ≤
      worldFunds world + (entries.map (fun p => p.2.balance.toNat)).sum := by
  induction entries generalizing world with
  | nil => simp
  | cons kv rest ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    apply (ih (world.insert kv.1 {kv.2 with tstorage := .empty})).trans
    have hs := funds_insert world kv.1 {kv.2 with tstorage := .empty}
    have hb : worldFunds (world.insert kv.1 {kv.2 with tstorage := .empty}) ≤
        worldFunds world + kv.2.balance.toNat := (Nat.le_add_right _ _).trans_eq hs
    exact (Nat.add_le_add_right hb _).trans_eq (Nat.add_assoc _ _ _)

def clearTransient (world : AccountMap .EVM) : AccountMap .EVM :=
  world.foldl (fun st addr account => st.insert addr {account with tstorage := .empty}) ∅

theorem clearTransient_le (world : AccountMap .EVM) :
    worldFunds (clearTransient world) ≤ worldFunds world := by
  unfold clearTransient
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  have h := rebuild_le world.toList ∅
  change worldFunds _ ≤ 0 + worldFunds world at h
  simpa only [Nat.zero_add] using h

/-- Exact two erase folds and transient reset from Υ's finalization. -/
def cleanup (world : AccountMap .EVM) (substate : Substate) : AccountMap .EVM :=
  let afterDestruct := substate.selfDestructSet.foldl (fun st addr => st.erase addr) world
  let dead := substate.touchedAccounts.filter (State.dead world ·)
  clearTransient (dead.foldl (fun st addr => st.erase addr) afterDestruct)

theorem cleanup_le (world : AccountMap .EVM) (substate : Substate) :
    worldFunds (cleanup world substate) ≤ worldFunds world := by
  exact (clearTransient_le _).trans ((erase_set_le _ _).trans (erase_set_le _ _))

#print axioms credit_le
#print axioms erase_le
#print axioms clearTransient_le
#print axioms cleanup_le
end Eip8282.Audit.Integrator.FinalizationFunding
