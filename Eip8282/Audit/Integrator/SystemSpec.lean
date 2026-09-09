import Eip8282.Audit.Integrator.ControlSpec
import Eip8282.Audit.Integrator.EndpointState

/-!
# Independent storage postconditions for SYSTEM endpoints

The storage algebra here interprets the concrete SYSTEM endpoint states.
Word arithmetic is intentional; queue bounds and FIFO byte encodings are separate.
The final theorems retain the actual successful `Ξ` result and read its account
map at the call's code owner. Gas, fuel, and owner existence are explicit.
-/

namespace Eip8282.Audit.Integrator.SystemSpec

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.SymExec
open Eip8282.Audit.XiTransport (XiCall)

set_option maxHeartbeats 1600000

def HasOwner (st : EvmYul.State .EVM) : Prop :=
  ∃ acc, st.accountMap.get? st.executionEnv.codeOwner = some acc

theorem accountMap_sstore {st : EvmYul.State .EVM} {acc : Account .EVM}
    (hacc : st.accountMap.get? st.executionEnv.codeOwner = some acc) (k v : UInt256) :
    (st.sstore k v).accountMap =
      st.accountMap.insert st.executionEnv.codeOwner (acc.updateStorage k v) := by
  unfold EvmYul.State.sstore
  dsimp only
  rcases hget : Std.TreeMap.get! st.accountMap st.executionEnv.codeOwner with
    ⟨⟨nonce, bal, sto, code⟩, tst⟩
  have hlookup : st.lookupAccount st.executionEnv.codeOwner = some acc := hacc
  rw [hlookup]
  rfl

theorem owner_sstore {st : EvmYul.State .EVM} (h : HasOwner st) (k v : UInt256) :
    HasOwner (st.sstore k v) := by
  obtain ⟨acc, hacc⟩ := h
  unfold HasOwner
  rw [accountMap_sstore hacc, executionEnv_sstore]
  exact ⟨acc.updateStorage k v, Std.TreeMap.getElem?_insert_self⟩

theorem slot_sstore {st : EvmYul.State .EVM} (h : HasOwner st) (k v q : UInt256) :
    slotW (st.sstore k v) q = if q = k then v else slotW st q := by
  obtain ⟨acc, hacc⟩ := h
  unfold slotW EvmYul.State.sload EvmYul.State.lookupAccount
  simp only [accountMap_sstore hacc, executionEnv_sstore]
  change Option.option ⟨0⟩ (fun a => Account.lookupStorage a q)
    ((st.accountMap.insert st.executionEnv.codeOwner (acc.updateStorage k v))[st.executionEnv.codeOwner]?) =
      if q = k then v else Option.option ⟨0⟩ (fun a => Account.lookupStorage a q)
        (st.accountMap.get? st.executionEnv.codeOwner)
  rw [Std.TreeMap.getElem?_insert_self, hacc]
  dsimp only [Option.option]
  unfold Account.updateStorage Account.lookupStorage
  have hbeq : (v == (default : UInt256)) = true ↔ v = ⟨0⟩ := by
    change (v.val == (0 : Fin UInt256.size)) = true ↔ v = ⟨0⟩
    rw [beq_iff_eq]
    constructor
    · intro he
      cases v
      cases he
      rfl
    · rintro rfl
      rfl
  simp only [hbeq]
  have hcmp : compare k q = .eq ↔ q = k := by
    constructor
    · intro hh
      exact (Std.LawfulEqOrd.compare_eq_iff_eq.mp hh).symm
    · intro hh
      exact Std.LawfulEqOrd.compare_eq_iff_eq.mpr hh.symm
  by_cases hv : v = ⟨0⟩
  · rw [if_pos hv]
    dsimp only
    rw [Std.TreeMap.getD_erase]
    simp only [hcmp, hv]
  · rw [if_neg hv]
    dsimp only
    rw [Std.TreeMap.getD_insert]
    simp only [hcmp]

theorem owner_touched {st st' : EvmYul.State .EVM} (h : Touched st st')
    (ho : HasOwner st) : HasOwner st' := by
  simpa only [HasOwner, h.accountMap, h.executionEnv] using ho

def headUpdate (st : EvmYul.State .EVM) (head tail count : UInt256) : EvmYul.State .EVM :=
  if tail = head + count then
    (st.sstore (UInt256.ofNat 2) ⟨0⟩).sstore (UInt256.ofNat 3) ⟨0⟩
  else st.sstore (UInt256.ofNat 2) (head + count)

theorem environment_headUpdate (st : EvmYul.State .EVM) (head tail count : UInt256) :
    (headUpdate st head tail count).executionEnv = st.executionEnv := by
  unfold headUpdate
  split <;> simp only [executionEnv_sstore]

theorem owner_headUpdate {st : EvmYul.State .EVM} (h : HasOwner st) (head tail count : UInt256) :
    HasOwner (headUpdate st head tail count) := by
  unfold headUpdate
  split
  · exact owner_sstore (owner_sstore h _ _) _ _
  · exact owner_sstore h _ _

theorem slot_headUpdate {st : EvmYul.State .EVM} (h : HasOwner st) (head tail count q : UInt256) :
    slotW (headUpdate st head tail count) q =
      if q = UInt256.ofNat 2 then (if tail = head + count then ⟨0⟩ else head + count)
      else if q = UInt256.ofNat 3 ∧ tail = head + count then ⟨0⟩ else slotW st q := by
  unfold headUpdate
  by_cases hfull : tail = head + count
  · rw [if_pos hfull, slot_sstore (owner_sstore h _ _), slot_sstore h]
    by_cases hq : q = UInt256.ofNat 2
    · subst q
      simp only [hfull, ↓reduceIte, show UInt256.ofNat 2 ≠ UInt256.ofNat 3 by decide]
    · simp only [hq, hfull, ↓reduceIte, and_true]
  · rw [if_neg hfull, slot_sstore h]
    simp only [hfull, ↓reduceIte, and_false]

/-- The observable storage specification: only four control words may change.
The entire formula uses entry words and the actual capped drain word. -/
def expectedSlot (pre : EvmYul.State .EVM) (target count calldataSize q : UInt256) : UInt256 :=
  if q = UInt256.ofNat 0 then
    ControlSpec.systemExcess target (slotW pre (UInt256.ofNat 0))
      (slotW pre (UInt256.ofNat 1)) calldataSize
  else if q = UInt256.ofNat 1 then ⟨0⟩
  else if q = UInt256.ofNat 2 then
    if slotW pre (UInt256.ofNat 3) = slotW pre (UInt256.ofNat 2) + count then ⟨0⟩
    else slotW pre (UInt256.ofNat 2) + count
  else if q = UInt256.ofNat 3 ∧
    slotW pre (UInt256.ofNat 3) = slotW pre (UInt256.ofNat 2) + count then ⟨0⟩
  else slotW pre q

def controlStore (st : EvmYul.State .EVM) (excess : UInt256) : EvmYul.State .EVM :=
  (st.sstore (UInt256.ofNat 0) excess).sstore (UInt256.ofNat 1) ⟨0⟩

theorem system_storage {pre st' stX : EvmYul.State .EVM}
    (ho : HasOwner pre) (ht : Touched pre st') (target count calldataSize : UInt256)
    (hx : Touched (headUpdate st' (slotW pre (UInt256.ofNat 2))
      (slotW pre (UInt256.ofNat 3)) count) stX) :
    ∀ q, slotW (controlStore stX (ControlSpec.systemExcess target
      (slotW stX (UInt256.ofNat 0)) (slotW stX (UInt256.ofNat 1)) calldataSize)) q =
        expectedSlot pre target count calldataSize q := by
  have ho' := owner_touched ht ho
  have hoX := owner_touched hx (owner_headUpdate ho' _ _ _)
  have hs (q : UInt256) := (slotW_of_touched hx q).trans (slot_headUpdate ho' _ _ _ q)
  have hz : slotW stX (UInt256.ofNat 0) = slotW pre (UInt256.ofNat 0) := by
    rw [hs]
    simpa only [show UInt256.ofNat 0 ≠ UInt256.ofNat 2 by decide,
      show UInt256.ofNat 0 ≠ UInt256.ofNat 3 by decide, ↓reduceIte, false_and]
      using slotW_of_touched ht (UInt256.ofNat 0)
  have hc : slotW stX (UInt256.ofNat 1) = slotW pre (UInt256.ofNat 1) := by
    rw [hs]
    simpa only [show UInt256.ofNat 1 ≠ UInt256.ofNat 2 by decide,
      show UInt256.ofNat 1 ≠ UInt256.ofNat 3 by decide, ↓reduceIte, false_and]
      using slotW_of_touched ht (UInt256.ofNat 1)
  intro q
  unfold controlStore expectedSlot
  rw [slot_sstore (owner_sstore hoX _ _), slot_sstore hoX, hz, hc, hs,
    slotW_of_touched ht q]
  by_cases h0 : q = UInt256.ofNat 0
  · subst q
    simp only [show UInt256.ofNat 0 ≠ UInt256.ofNat 1 by decide, ↓reduceIte]
  · by_cases h1 : q = UInt256.ofNat 1
    · subst q
      simp only [show UInt256.ofNat 1 ≠ UInt256.ofNat 0 by decide, ↓reduceIte]
    · simp only [h0, h1, ↓reduceIte]

theorem expectedSlot_excess (pre : EvmYul.State .EVM) (target count calldataSize : UInt256) :
    expectedSlot pre target count calldataSize (UInt256.ofNat 0) =
      ControlSpec.systemExcess target (slotW pre (UInt256.ofNat 0))
        (slotW pre (UInt256.ofNat 1)) calldataSize := by
  simp only [expectedSlot, ↓reduceIte]

theorem expectedSlot_count (pre : EvmYul.State .EVM) (target count calldataSize : UInt256) :
    expectedSlot pre target count calldataSize (UInt256.ofNat 1) = ⟨0⟩ := by
  simp only [expectedSlot, show UInt256.ofNat 1 ≠ UInt256.ofNat 0 by decide, ↓reduceIte]

theorem expectedSlot_head (pre : EvmYul.State .EVM) (target count calldataSize : UInt256) :
    expectedSlot pre target count calldataSize (UInt256.ofNat 2) =
      if slotW pre (UInt256.ofNat 3) = slotW pre (UInt256.ofNat 2) + count then ⟨0⟩
      else slotW pre (UInt256.ofNat 2) + count := by
  simp only [expectedSlot, show UInt256.ofNat 2 ≠ UInt256.ofNat 0 by decide,
    show UInt256.ofNat 2 ≠ UInt256.ofNat 1 by decide, ↓reduceIte]

theorem expectedSlot_tail (pre : EvmYul.State .EVM) (target count calldataSize : UInt256) :
    expectedSlot pre target count calldataSize (UInt256.ofNat 3) =
      if slotW pre (UInt256.ofNat 3) = slotW pre (UInt256.ofNat 2) + count then ⟨0⟩
      else slotW pre (UInt256.ofNat 3) := by
  simp only [expectedSlot, show UInt256.ofNat 3 ≠ UInt256.ofNat 0 by decide,
    show UInt256.ofNat 3 ≠ UInt256.ofNat 1 by decide,
    show UInt256.ofNat 3 ≠ UInt256.ofNat 2 by decide, ↓reduceIte, true_and]

/-- All old record words survive, universally over the word address domain. -/
theorem expectedSlot_record (pre : EvmYul.State .EVM) (target count calldataSize q : UInt256)
    (hq : 4 ≤ q.toNat) : expectedSlot pre target count calldataSize q = slotW pre q := by
  have hn (n : Nat) (h : n < 4) : q ≠ UInt256.ofNat n := by
    intro he
    have he' := congrArg UInt256.toNat he
    have hn' : (UInt256.ofNat n).toNat = n := toNat_ofNat_lit n (by
      have : 4 < UInt256.size := by decide
      omega)
    rw [hn'] at he'
    omega
  simp only [expectedSlot, hn 0 (by decide), hn 1 (by decide), hn 2 (by decide),
    hn 3 (by decide), ↓reduceIte, false_and]

/-- The existing pinned deposit path supplies the witness states; none of the
storage conclusions are assumed. This theorem stops at the reached RETURN. -/
theorem deposit_system_storage_endpoint (c : XiCall .deposit)
    (hsys : Deposit.callerWord c = sysW) (hperm : c.env.perm = true)
    (hg : 2500000 ≤ c.gas.toNat) (ho : HasOwner (entrySt c)) :
    ∃ (x : EVM.State) (out : ByteArray), Ends c 8500 x .RETURN out ∧
      ∀ q, slotW x.toState q = expectedSlot (entrySt c) (UInt256.ofNat 8)
        (Deposit.drainWord c) (Deposit.cdsizeWord c) q := by
  obtain ⟨st', stX, aw, g, e, ht, hx, hend⟩ := Deposit.system_returns c hsys hperm hg
  refine ⟨_, _, hend, ?_⟩
  intro q
  change slotW (controlStore stX (Deposit.newExcess c stX)) q = _
  rw [← ControlSpec.deposit_systemExcess c stX]
  exact system_storage ho ht (UInt256.ofNat 8) (Deposit.drainWord c)
    (Deposit.cdsizeWord c) hx q

/-- Exit counterpart; the cap word is the one the pinned exit path computes. -/
theorem exit_system_storage_endpoint (c : XiCall .exit)
    (hsys : Exit.callerWord c = sysW) (hperm : c.env.perm = true)
    (hg : 250000 ≤ c.gas.toNat) (ho : HasOwner (entrySt c)) :
    ∃ (x : EVM.State) (out : ByteArray), Ends c 800 x .RETURN out ∧
      ∀ q, slotW x.toState q = expectedSlot (entrySt c) (UInt256.ofNat 2)
        (Exit.drainWord c) (Exit.cdsizeWord c) q := by
  obtain ⟨st', stX, aw, g, e, ht, hx, hend⟩ := Exit.system_returns c hsys hperm hg
  refine ⟨_, _, hend, ?_⟩
  intro q
  change slotW (controlStore stX (Exit.newExcess c stX)) q = _
  rw [← ControlSpec.exit_systemExcess c stX]
  exact system_storage ho ht (UInt256.ofNat 2) (Exit.drainWord c)
    (Exit.cdsizeWord c) hx q

/-- A storage observation is read from the actual world and explicit account. -/
def worldSlot (world : AccountMap .EVM) (addr : AccountAddress) (q : UInt256) : UInt256 :=
  ((world.get? addr).map (fun acc => acc.lookupStorage q)).getD ⟨0⟩

theorem worldSlot_state (st : EvmYul.State .EVM) (q : UInt256) :
    worldSlot st.accountMap st.executionEnv.codeOwner q = slotW st q := by
  unfold worldSlot slotW EvmYul.State.sload EvmYul.State.lookupAccount
  dsimp only
  cases st.accountMap.get? st.executionEnv.codeOwner <;> rfl

theorem system_environment {kind : Eip8282.Audit.Model.Kind} {c : XiCall kind}
    {st' stX : EvmYul.State .EVM} (ht : Touched (entrySt c) st')
    (count : UInt256)
    (hx : Touched (headUpdate st' (slotW (entrySt c) (UInt256.ofNat 2))
      (slotW (entrySt c) (UInt256.ofNat 3)) count) stX) (excess : UInt256) :
    (controlStore stX excess).executionEnv = c.env := by
  simp only [controlStore, executionEnv_sstore]
  rw [hx.executionEnv, environment_headUpdate, ht.executionEnv]
  rfl

/-- Full successful deposit `Ξ` storage result. Count, exact word excess,
pointer updates and all old record slots follow by the expectedSlot lemmas.
The returned buffer is the actual staged buffer, not an assumed FIFO encoding. -/
theorem deposit_system_storage_result (c : XiCall .deposit)
    (hsys : Deposit.callerWord c = sysW) (hperm : c.env.perm = true)
    (hg : 2500000 ≤ c.gas.toNat) (hf : 8502 ≤ c.fuel) (ho : HasOwner (entrySt c)) :
    ∃ (world : AccountMap .EVM) (created : Std.TreeSet AccountAddress compare)
      (gas : UInt256) (substate : Substate),
      c.result = .ok (.success (created, world, gas, substate)
        ((Deposit.drainMem (entrySt c) (Deposit.headWord₀ c) (Deposit.mem₀ c)
          (Deposit.drainWord c).toNat).readWithPadding 0
          (UInt256.ofNat 184 * Deposit.drainWord c).toNat)) ∧
      (∃ acc, world.get? c.env.codeOwner = some acc) ∧
      ∀ q, worldSlot world c.env.codeOwner q = expectedSlot (entrySt c) (UInt256.ofNat 8)
        (Deposit.drainWord c) (Deposit.cdsizeWord c) q := by
  obtain ⟨st', stX, gas, ht, hx, hres⟩ := EndpointState.deposit_system_result c hsys hperm hg hf
  let post := controlStore stX (Deposit.newExcess c stX)
  have he : post.executionEnv = c.env := system_environment ht (Deposit.drainWord c) hx _
  have hoX := owner_touched hx (owner_headUpdate (owner_touched ht ho) _ _ _)
  have hoPost : HasOwner post := owner_sstore (owner_sstore hoX _ _) _ _
  have howner : ∃ acc, post.accountMap.get? c.env.codeOwner = some acc := by
    simpa only [HasOwner, he] using hoPost
  refine ⟨post.accountMap, post.createdAccounts, gas, post.substate, hres, howner, ?_⟩
  intro q
  rw [← he, worldSlot_state]
  change slotW (controlStore stX (Deposit.newExcess c stX)) q = _
  rw [← ControlSpec.deposit_systemExcess c stX]
  exact system_storage ho ht (UInt256.ofNat 8) (Deposit.drainWord c)
    (Deposit.cdsizeWord c) hx q

/-- Full successful exit `Ξ` counterpart, with its independent resource bounds. -/
theorem exit_system_storage_result (c : XiCall .exit)
    (hsys : Exit.callerWord c = sysW) (hperm : c.env.perm = true)
    (hg : 250000 ≤ c.gas.toNat) (hf : 802 ≤ c.fuel) (ho : HasOwner (entrySt c)) :
    ∃ (world : AccountMap .EVM) (created : Std.TreeSet AccountAddress compare)
      (gas : UInt256) (substate : Substate),
      c.result = .ok (.success (created, world, gas, substate)
        ((Exit.drainMem (entrySt c) (Exit.headWord₀ c) (Exit.mem₀ c)
          (Exit.drainWord c).toNat).readWithPadding 0
          (UInt256.ofNat 68 * Exit.drainWord c).toNat)) ∧
      (∃ acc, world.get? c.env.codeOwner = some acc) ∧
      ∀ q, worldSlot world c.env.codeOwner q = expectedSlot (entrySt c) (UInt256.ofNat 2)
        (Exit.drainWord c) (Exit.cdsizeWord c) q := by
  obtain ⟨st', stX, gas, ht, hx, hres⟩ := EndpointState.exit_system_result c hsys hperm hg hf
  let post := controlStore stX (Exit.newExcess c stX)
  have he : post.executionEnv = c.env := system_environment ht (Exit.drainWord c) hx _
  have hoX := owner_touched hx (owner_headUpdate (owner_touched ht ho) _ _ _)
  have hoPost : HasOwner post := owner_sstore (owner_sstore hoX _ _) _ _
  have howner : ∃ acc, post.accountMap.get? c.env.codeOwner = some acc := by
    simpa only [HasOwner, he] using hoPost
  refine ⟨post.accountMap, post.createdAccounts, gas, post.substate, hres, howner, ?_⟩
  intro q
  rw [← he, worldSlot_state]
  change slotW (controlStore stX (Exit.newExcess c stX)) q = _
  rw [← ControlSpec.exit_systemExcess c stX]
  exact system_storage ho ht (UInt256.ofNat 2) (Exit.drainWord c)
    (Exit.cdsizeWord c) hx q

#print axioms deposit_system_storage_endpoint
#print axioms exit_system_storage_endpoint
#print axioms expectedSlot_record
#print axioms deposit_system_storage_result
#print axioms exit_system_storage_result

end Eip8282.Audit.Integrator.SystemSpec
