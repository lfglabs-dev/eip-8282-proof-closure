import Eip8282.Audit.Integrator.CodeStorageFrame
import Eip8282.Audit.Integrator.FinalizationFunding

/-!
# Actual transaction-finalization code and persistent-storage framing

The literal credit, erase-set folds and transient reset are retained. Existing
nonempty code rules out touched-dead deletion in the actual pre-erasure world.
Selfdestruct-set exclusion is explicit; its execution-history producer is not
assumed proved here. Balance, nonce and transient storage are outside Frame.
-/
namespace Eip8282.Audit.Integrator.FinalizationWorldFrame
open EvmYul EvmYul.EVM
open CodeStorageFrame SystemSpec
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private theorem lookup_insert (world : AccountMap .EVM) (key address : AccountAddress)
    (account : Account .EVM) :
    (world.insert key account).get? address =
      if key = address then some account else world.get? address := by
  exact (Std.TreeMap.getElem?_insert (t := world) (k := key) (a := address) (v := account)).trans
    (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)

private theorem lookup_frame {before after : AccountMap .EVM} {address : AccountAddress}
    (h : after.get? address = before.get? address) : Frame before after address := by
  constructor
  · intro old ho
    exact ⟨old,h.trans ho,rfl⟩
  · intro slot
    simp only [worldSlot,h]

/-- Literal increaseBalance preserves installed code and all persistent reads;
it can create a missing recipient with empty code and default storage. -/
theorem credit_frame (world : AccountMap .EVM) (recipient address : AccountAddress)
    (amount : UInt256) : Frame world (world.increaseBalance .EVM recipient amount) address := by
  unfold AccountMap.increaseBalance
  cases ha : world.get? recipient with
  | none =>
    by_cases he : recipient = address
    · subst address
      constructor
      · intro old ho
        rw [ha] at ho
        cases ho
      · intro slot
        simp only [worldSlot,lookup_insert,ite_true,ha,
          Option.map_some,Option.map_none,Option.getD_some,Option.getD_none]
        all_goals rfl
    · apply lookup_frame
      rw [lookup_insert,if_neg he]
  | some account =>
    by_cases he : recipient = address
    · subst address
      constructor
      · intro old ho
        have he : account = old := Option.some.inj (ha.symm.trans ho)
        subst old
        exact ⟨_,Std.TreeMap.getElem?_insert_self,rfl⟩
      · intro slot
        simp only [worldSlot,lookup_insert,ite_true,ha,
          Option.map_some,Option.getD_some]
        all_goals rfl
    · apply lookup_frame
      rw [lookup_insert,if_neg he]

private theorem erase_lookup (world : AccountMap .EVM) (key address : AccountAddress)
    (hne : key ≠ address) : (world.erase key).get? address = world.get? address := by
  change (world.erase key)[address]? = world[address]?
  rw [Std.TreeMap.getElem?_erase]
  simp only [Std.LawfulEqOrd.compare_eq_iff_eq,hne,ite_false]

private theorem erase_list_lookup (addresses : List AccountAddress)
    (world : AccountMap .EVM) (address : AccountAddress) (hn : address ∉ addresses) :
    (addresses.foldl (fun w a => w.erase a) world).get? address = world.get? address := by
  induction addresses generalizing world with
  | nil => rfl
  | cons key rest ih =>
    have hk : key ≠ address := by intro h; apply hn; simp [h]
    have hr : address ∉ rest := by intro h; exact hn (List.mem_cons_of_mem _ h)
    exact (ih (world.erase key) hr).trans (erase_lookup world key address hk)

/-- Exact lookup preservation through the real TreeSet erasure fold. -/
theorem erase_set_lookup (world : AccountMap .EVM)
    (addresses : Std.TreeSet AccountAddress compare) (address : AccountAddress)
    (hn : address ∉ addresses) :
    (addresses.foldl (fun w a => w.erase a) world).get? address = world.get? address := by
  rw [Std.TreeSet.foldl_eq_foldl_toList]
  apply erase_list_lookup
  simpa only [Std.TreeSet.mem_toList] using hn

theorem erase_set_frame (world : AccountMap .EVM)
    (addresses : Std.TreeSet AccountAddress compare) (address : AccountAddress)
    (hn : address ∉ addresses) :
    Frame world (addresses.foldl (fun w a => w.erase a) world) address :=
  lookup_frame (erase_set_lookup world addresses address hn)

private def reset (account : Account .EVM) : Account .EVM :=
  {account with tstorage := .empty}

private def rebuild (entries : List (AccountAddress × Account .EVM))
    (world : AccountMap .EVM) : AccountMap .EVM :=
  entries.foldl (fun w pair => w.insert pair.1 (reset pair.2)) world

private theorem rebuild_fixed (entries : List (AccountAddress × Account .EVM))
    (world : AccountMap .EVM) (address : AccountAddress) (wanted : Account .EVM)
    (good : ∀ pair ∈ entries, pair.1 = address → reset pair.2 = wanted)
    (initial : world.get? address = some wanted) :
    (rebuild entries world).get? address = some wanted := by
  induction entries generalizing world with
  | nil => exact initial
  | cons pair rest ih =>
    apply ih (world.insert pair.1 (reset pair.2))
    · intro p hp
      exact good p (List.mem_cons_of_mem _ hp)
    · rw [lookup_insert]
      split
      · rename_i he
        rw [good pair (by simp) he]
      · exact initial

private theorem rebuild_miss (entries : List (AccountAddress × Account .EVM))
    (world : AccountMap .EVM) (address : AccountAddress)
    (miss : ∀ pair ∈ entries, pair.1 ≠ address) :
    (rebuild entries world).get? address = world.get? address := by
  induction entries generalizing world with
  | nil => rfl
  | cons pair rest ih =>
    have ht := ih (world.insert pair.1 (reset pair.2))
      (fun p hp => miss p (List.mem_cons_of_mem _ hp))
    exact ht.trans (by rw [lookup_insert,if_neg (miss pair (by simp))])

private theorem rebuild_hit (entries : List (AccountAddress × Account .EVM))
    (world : AccountMap .EVM) (address : AccountAddress) (old : Account .EVM)
    (good : ∀ pair ∈ entries, pair.1 = address → pair.2 = old)
    (hit : (address,old) ∈ entries) :
    (rebuild entries world).get? address = some (reset old) := by
  induction entries generalizing world with
  | nil => cases hit
  | cons pair rest ih =>
    rcases List.mem_cons.mp hit with he | ht
    · subst pair
      apply rebuild_fixed rest _ address (reset old)
      · intro p hp he
        rw [good p (List.mem_cons_of_mem _ hp) he]
      · exact Std.TreeMap.getElem?_insert_self
    · exact ih (world.insert pair.1 (reset pair.2))
        (fun p hp => good p (List.mem_cons_of_mem _ hp)) ht

/-- The real fold rebuilds each existing account with exactly its transient
store cleared. None remains none; no persistent field or account is lost. -/
theorem clearTransient_lookup (world : AccountMap .EVM) (address : AccountAddress) :
    (FinalizationFunding.clearTransient world).get? address =
      (world.get? address).map (fun old => {old with tstorage := .empty}) := by
  unfold FinalizationFunding.clearTransient
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  change (rebuild world.toList ∅).get? address = (world.get? address).map reset
  cases ha : world.get? address with
  | none =>
    change (rebuild world.toList ∅).get? address = none
    apply (rebuild_miss world.toList ∅ address ?_).trans rfl
    intro pair hp he
    have hl := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp
    change world.get? pair.1 = some pair.2 at hl
    rw [he,ha] at hl
    cases hl
  | some old =>
    change (rebuild world.toList ∅).get? address = some (reset old)
    apply rebuild_hit world.toList ∅ address old
    · intro pair hp he
      have hl := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp
      change world.get? pair.1 = some pair.2 at hl
      rw [he,ha] at hl
      exact (Option.some.inj hl).symm
    · exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr ha

theorem clear_transient_frame (world : AccountMap .EVM) (address : AccountAddress) :
    Frame world (FinalizationFunding.clearTransient world) address := by
  constructor
  · intro old ho
    refine ⟨{old with tstorage := .empty},?_,rfl⟩
    rw [clearTransient_lookup,ho]
    rfl
  · intro slot
    unfold worldSlot
    rw [clearTransient_lookup]
    cases world.get? address <;> rfl

/-- Nonempty installed code is enough to refute the actual DEAD predicate. -/
theorem nonempty_code_not_dead {world : AccountMap .EVM} {address : AccountAddress}
    {old : Account .EVM} (ho : world.get? address = some old) (hc : old.code ≠ .empty) :
    State.dead world address = false := by
  have hsize : old.code.size ≠ 0 := fun h => hc (ByteArray.size_eq_zero_iff.mp h)
  simp only [State.dead,ho,Option.option,Account.emptyAccount,ByteArray.isEmpty]
  simp [hsize]

/-- Cleanup computes touched-dead membership in `world`, before either erase
fold. That same world's installed code discharges protected deadness. -/
theorem cleanup_frame (world : AccountMap .EVM) (substate : Substate)
    (address : AccountAddress) {old : Account .EVM}
    (ho : world.get? address = some old) (hc : old.code ≠ .empty)
    (hn : address ∉ substate.selfDestructSet) :
    Frame world (FinalizationFunding.cleanup world substate) address := by
  have hd : address ∉ substate.touchedAccounts.filter (State.dead world ·) := by
    intro hm
    obtain ⟨hmem,hdead⟩ := Std.TreeSet.mem_filter.mp hm
    rw [Std.TreeSet.get_eq hmem,nonempty_code_not_dead ho hc] at hdead
    cases hdead
  exact CodeStorageFrame.trans (erase_set_frame world _ address hn)
    (CodeStorageFrame.trans (erase_set_frame _ _ address hd) (clear_transient_frame _ address))

/-- Direct installed-account projection of actual cleanup. -/
theorem cleanup_existing (world : AccountMap .EVM) (substate : Substate)
    (address : AccountAddress) {old : Account .EVM}
    (ho : world.get? address = some old) (hc : old.code ≠ .empty)
    (hn : address ∉ substate.selfDestructSet) :
    ∃ current, (FinalizationFunding.cleanup world substate).get? address = some current ∧
      current.code = old.code ∧ ∀ slot, current.lookupStorage slot = old.lookupStorage slot := by
  have hf := cleanup_frame world substate address ho hc hn
  obtain ⟨current,hcur,hcode⟩ := hf.existing old ho
  refine ⟨current,hcur,hcode,?_⟩
  intro slot
  have hs := hf.storage slot
  simpa only [worldSlot,ho,hcur,Option.map_some,Option.getD_some] using hs

#print axioms credit_frame
#print axioms erase_set_lookup
#print axioms clearTransient_lookup
#print axioms clear_transient_frame
#print axioms nonempty_code_not_dead
#print axioms cleanup_frame
#print axioms cleanup_existing
end Eip8282.Audit.Integrator.FinalizationWorldFrame
