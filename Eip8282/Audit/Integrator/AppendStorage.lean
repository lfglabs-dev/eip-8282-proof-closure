import Eip8282.Audit.Integrator.SystemSpec
import Eip8282.Audit.Integrator.AppendSpec

/-!
# Independent append storage specifications

Physical record words are specified from the call's calldata and source address.
The read-map overlay below is a storage specification, not an EVM interpreter.
Arithmetic bounds are local assumptions; no protocol reachability is claimed.
-/

namespace Eip8282.Audit.Integrator.AppendStorage

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.SymExec
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Model (Kind)
open SystemSpec (HasOwner owner_sstore slot_sstore worldSlot worldSlot_state)

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

def stride : Kind → Nat | .deposit => 6 | .exit => 3

def entryTail (c : XiCall kind) : UInt256 := slotW (entrySt c) (UInt256.ofNat 3)
def entryCount (c : XiCall kind) : UInt256 := slotW (entrySt c) (UInt256.ofNat 1)

def baseWord (c : XiCall kind) : UInt256 :=
  UInt256.ofNat 4 + UInt256.ofNat (stride kind) * entryTail c

def recordKey (c : XiCall kind) : Nat → UInt256
  | 0 => baseWord c
  | i + 1 => UInt256.ofNat 1 + recordKey c i

/-- A 32-byte big-endian calldata word, zero-padded at the end. -/
def calldataWord (c : XiCall kind) (offset : Nat) : UInt256 :=
  uInt256OfByteArray (c.env.calldata.readBytes offset 32)

/-- Deposit's six words contain all 184 calldata bytes (last word padded).
Exit's three physical words are caller, then the two pubkey words. -/
def recordWord (c : XiCall kind) (i : Nat) : UInt256 :=
  match kind with
  | .deposit => calldataWord c (32 * i)
  | .exit => if i = 0 then UInt256.ofNat c.env.source.val else calldataWord c (32 * (i - 1))

def put (read : UInt256 → UInt256) (key value : UInt256) : UInt256 → UInt256 :=
  fun q => if q = key then value else read q

def records (c : XiCall kind) : Nat → (UInt256 → UInt256) → UInt256 → UInt256
  | 0, read => read
  | i + 1, read => put (records c i read) (recordKey c i) (recordWord c i)

/-- Final read map: count increment, one record window, tail increment.
All parameters are entry observations, not fields read from a desired post-state. -/
def expected (c : XiCall kind) : UInt256 → UInt256 :=
  put (records c (stride kind)
    (put (slotW (entrySt c)) (UInt256.ofNat 1) (UInt256.ofNat 1 + entryCount c)))
      (UInt256.ofNat 3) (UInt256.ofNat 1 + entryTail c)

/-- The entire physical window must fit above the four controls. Count and
tail successors fit independently; these are local arithmetic assumptions. -/
def AppendFits (c : XiCall kind) : Prop :=
  4 + stride kind * (entryTail c).toNat + stride kind ≤ UInt256.size ∧
    (entryCount c).toNat + 1 < UInt256.size ∧ (entryTail c).toNat + 1 < UInt256.size

theorem recordKey_toNat (c : XiCall kind) (hf : AppendFits c) :
    ∀ i, i < stride kind → (recordKey c i).toNat = 4 + stride kind * (entryTail c).toNat + i := by
  have hw := hf.1
  have hp : 0 < stride kind := by cases kind <;> decide
  intro i
  induction i with
  | zero =>
    intro hi
    have hm := toNat_ofNat_mul_of_lt (stride kind) (entryTail c) (by omega)
    unfold recordKey baseWord
    rw [toNat_add_of_lt _ _ (by rw [hm]; change 4 + _ < _; omega), hm]
    change 4 + _ = _
    omega
  | succ i ih =>
    intro hi
    have hk := ih (by omega)
    unfold recordKey
    rw [toNat_add_of_lt _ _ (by change 1 + (recordKey c i).toNat < _; rw [hk]; omega), hk]
    change 1 + _ = _
    omega

theorem recordKey_ne_control (c : XiCall kind) (hf : AppendFits c)
    {i : Nat} (hi : i < stride kind) {q : UInt256} (hq : q.toNat < 4) :
    q ≠ recordKey c i := by
  intro he
  have hh := congrArg UInt256.toNat he
  rw [recordKey_toNat c hf i hi] at hh
  omega

theorem recordKey_injective (c : XiCall kind) (hf : AppendFits c)
    {i j : Nat} (hi : i < stride kind) (hj : j < stride kind)
    (he : recordKey c i = recordKey c j) : i = j := by
  have hh := congrArg UInt256.toNat he
  rw [recordKey_toNat c hf i hi, recordKey_toNat c hf j hj] at hh
  omega

theorem records_outside (c : XiCall kind) (read : UInt256 → UInt256) (q : UInt256) :
    ∀ n, (∀ i, i < n → q ≠ recordKey c i) → records c n read q = read q := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    unfold records put
    rw [if_neg (h n (by omega))]
    exact ih (fun i hi => h i (by omega))

theorem records_at (c : XiCall kind) (read : UInt256 → UInt256) (hf : AppendFits c)
    {i : Nat} : ∀ n, n ≤ stride kind → i < n →
      records c n read (recordKey c i) = recordWord c i := by
  intro n
  induction n with
  | zero => intro _ hi; omega
  | succ n ih =>
    intro hn hi
    unfold records put
    by_cases he : i = n
    · subst i
      rw [if_pos rfl]
    · have hk : recordKey c i ≠ recordKey c n := by
        intro h
        exact he (recordKey_injective c hf (by omega) (by omega) h)
      rw [if_neg hk]
      exact ih (by omega) (by omega)

theorem expected_outside (c : XiCall kind) {q : UInt256}
    (hc : q ≠ UInt256.ofNat 1) (ht : q ≠ UInt256.ofNat 3)
    (hr : ∀ i, i < stride kind → q ≠ recordKey c i) :
    expected c q = slotW (entrySt c) q := by
  unfold expected put
  rw [if_neg ht, records_outside c _ q _ hr, if_neg hc]

theorem expected_excess (c : XiCall kind) (hf : AppendFits c) :
    expected c (UInt256.ofNat 0) = slotW (entrySt c) (UInt256.ofNat 0) :=
  expected_outside c (by decide) (by decide)
    (fun _ hi => recordKey_ne_control c hf hi (by decide))

theorem expected_head (c : XiCall kind) (hf : AppendFits c) :
    expected c (UInt256.ofNat 2) = slotW (entrySt c) (UInt256.ofNat 2) :=
  expected_outside c (by decide) (by decide)
    (fun _ hi => recordKey_ne_control c hf hi (by decide))

theorem expected_count (c : XiCall kind) (hf : AppendFits c) :
    expected c (UInt256.ofNat 1) = UInt256.ofNat 1 + entryCount c := by
  unfold expected put
  rw [if_neg (by decide : UInt256.ofNat 1 ≠ UInt256.ofNat 3),
    records_outside c _ _ _ (fun _ hi => recordKey_ne_control c hf hi (by decide)), if_pos rfl]

theorem expected_tail (c : XiCall kind) :
    expected c (UInt256.ofNat 3) = UInt256.ofNat 1 + entryTail c := by
  unfold expected put
  rw [if_pos rfl]

theorem expected_record (c : XiCall kind) (hf : AppendFits c) {i : Nat}
    (hi : i < stride kind) : expected c (recordKey c i) = recordWord c i := by
  unfold expected put
  rw [if_neg (Ne.symm (recordKey_ne_control c hf hi (by decide : (UInt256.ofNat 3).toNat < 4)))]
  exact records_at c _ hf _ (Nat.le_refl _) hi

theorem expected_count_nat (c : XiCall kind) (hf : AppendFits c) :
    (expected c (UInt256.ofNat 1)).toNat = (entryCount c).toNat + 1 := by
  rw [expected_count c hf, toNat_add_of_lt _ _ (by change 1 + _ < _; have h := hf.2.1; omega)]
  change 1 + _ = _
  omega

theorem expected_tail_nat (c : XiCall kind) (hf : AppendFits c) :
    (expected c (UInt256.ofNat 3)).toNat = (entryTail c).toNat + 1 := by
  rw [expected_tail, toNat_add_of_lt _ _ (by change 1 + _ < _; have h := hf.2.2; omega)]
  change 1 + _ = _
  omega

def View (st : EvmYul.State .EVM) (read : UInt256 → UInt256) : Prop :=
  HasOwner st ∧ ∀ q, slotW st q = read q

theorem view_entry (c : XiCall kind) (ho : HasOwner (entrySt c)) :
    View (entrySt c) (slotW (entrySt c)) := ⟨ho, fun _ => rfl⟩

theorem view_touch {st : EvmYul.State .EVM} {read : UInt256 → UInt256}
    (h : View st read) (k : UInt256) : View (touch st k) read := h

theorem view_logged {st : EvmYul.State .EVM} {read : UInt256 → UInt256}
    (h : View st read) (data : ByteArray) : View (logged st data) read := h

theorem view_sstore {st : EvmYul.State .EVM} {read : UInt256 → UInt256}
    (h : View st read) (k v : UInt256) : View (st.sstore k v) (put read k v) := by
  refine ⟨owner_sstore h.1 k v, ?_⟩
  intro q
  rw [slot_sstore h.1, h.2]
  rfl

theorem deposit_tail_after_count (c : XiCall .deposit) (ho : HasOwner (entrySt c)) :
    Deposit.tailWord c = entryTail c := by
  unfold Deposit.tailWord Deposit.countStore
  rw [slot_sstore (show HasOwner (touch (Deposit.st₂ c) (UInt256.ofNat 1)) from ho)]
  rw [if_neg (by decide : UInt256.ofNat 3 ≠ UInt256.ofNat 1)]
  rfl

theorem exit_tail_after_count (c : XiCall .exit) (ho : HasOwner (entrySt c)) :
    Exit.tailWord c = entryTail c := by
  unfold Exit.tailWord Exit.countStore
  rw [slot_sstore (show HasOwner (touch (Exit.st₂ c) (UInt256.ofNat 1)) from ho)]
  rw [if_neg (by decide : UInt256.ofNat 3 ≠ UInt256.ofNat 1)]
  rfl

private def depositRead (c : XiCall .deposit) : UInt256 → UInt256 :=
  put (put (put (put (put (put (put
    (put (slotW (entrySt c)) (UInt256.ofNat 1) (UInt256.ofNat 1 + Deposit.countWord c))
    (Deposit.slotBase c) (Deposit.dw c 0))
    (UInt256.ofNat 1 + Deposit.slotBase c) (Deposit.dw c 32))
    (UInt256.ofNat 1 + (UInt256.ofNat 1 + Deposit.slotBase c)) (Deposit.dw c 64))
    (UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 + Deposit.slotBase c))) (Deposit.dw c 96))
    (UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 + Deposit.slotBase c)))) (Deposit.dw c 128))
    (UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 + Deposit.slotBase c))))) (Deposit.dw c 160))
    (UInt256.ofNat 3) (UInt256.ofNat 1 + Deposit.tailWord c)

private def exitRead (c : XiCall .exit) : UInt256 → UInt256 :=
  put (put (put (put
    (put (slotW (entrySt c)) (UInt256.ofNat 1) (UInt256.ofNat 1 + Exit.countWord c))
    (Exit.slotBase c) (Exit.callerWord c))
    (UInt256.ofNat 1 + Exit.slotBase c) (Exit.dw c 0))
    (UInt256.ofNat 1 + (UInt256.ofNat 1 + Exit.slotBase c)) (Exit.dw c 32))
    (UInt256.ofNat 3) (UInt256.ofNat 1 + Exit.tailWord c)

private theorem expected_depositRead (c : XiCall .deposit) (ho : HasOwner (entrySt c)) :
    expected c = depositRead c := by
  simp only [expected, stride, records, recordKey, baseWord, recordWord, calldataWord]
  simp only [← deposit_tail_after_count c ho]
  rfl

private theorem expected_exitRead (c : XiCall .exit) (ho : HasOwner (entrySt c)) :
    expected c = exitRead c := by
  simp only [expected, stride, records, recordKey, baseWord, recordWord, calldataWord]
  simp only [← exit_tail_after_count c ho]
  rfl

theorem deposit_storage_view (c : XiCall .deposit) (ho : HasOwner (entrySt c)) :
    View (EndpointState.depositAppendState c) (expected c) := by
  rw [expected_depositRead c ho]
  unfold EndpointState.depositAppendState Deposit.appendedSt depositRead
  apply view_sstore
  apply view_logged
  unfold Deposit.itemStored
  repeat apply view_sstore
  apply view_touch
  unfold Deposit.st₂
  repeat apply view_touch
  exact view_entry c ho

theorem exit_storage_view (c : XiCall .exit) (ho : HasOwner (entrySt c)) :
    View (EndpointState.exitAppendState c) (expected c) := by
  rw [expected_exitRead c ho]
  unfold EndpointState.exitAppendState Exit.appendedSt exitRead
  apply view_sstore
  apply view_logged
  unfold Exit.itemStored
  repeat apply view_sstore
  apply view_touch
  unfold Exit.st₂
  repeat apply view_touch
  exact view_entry c ho

/-- Independently observable append guarantees under the local window bounds. -/
def StoragePost (c : XiCall kind) (world : AccountMap .EVM) : Prop :=
  worldSlot world c.env.codeOwner (UInt256.ofNat 0) = slotW (entrySt c) (UInt256.ofNat 0) ∧
  (worldSlot world c.env.codeOwner (UInt256.ofNat 1)).toNat = (entryCount c).toNat + 1 ∧
  worldSlot world c.env.codeOwner (UInt256.ofNat 2) = slotW (entrySt c) (UInt256.ofNat 2) ∧
  (worldSlot world c.env.codeOwner (UInt256.ofNat 3)).toNat = (entryTail c).toNat + 1 ∧
  (∀ i, i < stride kind → worldSlot world c.env.codeOwner (recordKey c i) = recordWord c i) ∧
  (∀ q, q ≠ UInt256.ofNat 1 → q ≠ UInt256.ofNat 3 →
    (∀ i, i < stride kind → q ≠ recordKey c i) →
    worldSlot world c.env.codeOwner q = slotW (entrySt c) q)

theorem storagePost_of_expected (c : XiCall kind) (hf : AppendFits c) (world : AccountMap .EVM)
    (h : ∀ q, worldSlot world c.env.codeOwner q = expected c q) : StoragePost c world := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h, expected_excess c hf]
  · rw [h, expected_count_nat c hf]
  · rw [h, expected_head c hf]
  · rw [h, expected_tail_nat c hf]
  · intro i hi
    rw [h, expected_record c hf hi]
  · intro q hc ht hr
    rw [h, expected_outside c hc ht hr]

/-- An accepted deposit's actual Ξ post-world contains the independently
specified six record words and satisfies the complete control/frame formula.
AppendFits is explicit and has not been derived from protocol histories. -/
theorem deposit_storage_result (c : XiCall .deposit)
    (huser : Deposit.callerWord c ≠ sysW) (hen : Deposit.excessWord c ≠ INH)
    (hperm : c.env.perm = true) {n : Nat} {o i : UInt256}
    (hfee : Deposit.FeeLoopEnds c n o i) (hsize : c.env.calldata.size = 184)
    (hpaid : ¬ Deposit.valueWord c < Deposit.feeWord o)
    (hfloor : ¬ Deposit.amountWord c < UInt256.ofNat 1000000000)
    (hstake : ¬ (Deposit.valueWord c - Deposit.feeWord o) <
      UInt256.ofNat 1000000000 * Deposit.amountWord c)
    (hg : 87 * n + 190000 ≤ c.gas.toNat) (hf : 24 * n + 152 ≤ c.fuel)
    (ho : HasOwner (entrySt c)) (hfit : AppendFits c) :
    ∃ created world gas substate,
      c.result = .ok (.success (created, world, gas, substate) .empty) ∧
      (∃ acc, world.get? c.env.codeOwner = some acc) ∧
      (∀ q, worldSlot world c.env.codeOwner q = expected c q) ∧ StoragePost c world := by
  have hs : Deposit.cdsizeWord c = UInt256.ofNat 184 := by
    change UInt256.ofNat c.env.calldata.size = _
    rw [hsize]
  obtain ⟨gas, hres⟩ := EndpointState.deposit_append_result c huser hen hperm hfee
    hs hpaid hfloor hstake hg hf
  have hv := deposit_storage_view c ho
  have he := (AppendSpec.deposit_append_frame c).1
  have hw (q : UInt256) :
      worldSlot (EndpointState.depositAppendState c).accountMap c.env.codeOwner q = expected c q := by
    rw [← he, worldSlot_state]
    exact hv.2 q
  have howner : ∃ acc, (EndpointState.depositAppendState c).accountMap.get? c.env.codeOwner = some acc := by
    simpa only [HasOwner, he] using hv.1
  exact ⟨_, _, gas, _, hres, howner, hw, storagePost_of_expected c hfit _ hw⟩

/-- Exit counterpart: source address is the call's sender word, followed by
the pubkey's two physical storage words (the second padded). -/
theorem exit_storage_result (c : XiCall .exit)
    (huser : Exit.callerWord c ≠ sysW) (hen : Exit.excessWord c ≠ INH)
    (hperm : c.env.perm = true) {n : Nat} {o i : UInt256}
    (hfee : Exit.FeeLoopEnds c n o i) (hsize : c.env.calldata.size = 48)
    (hpaid : ¬ Exit.valueWord c < Exit.feeWord o)
    (hg : 87 * n + 150000 ≤ c.gas.toNat) (hf : 24 * n + 122 ≤ c.fuel)
    (ho : HasOwner (entrySt c)) (hfit : AppendFits c) :
    ∃ created world gas substate,
      c.result = .ok (.success (created, world, gas, substate) .empty) ∧
      (∃ acc, world.get? c.env.codeOwner = some acc) ∧
      (∀ q, worldSlot world c.env.codeOwner q = expected c q) ∧ StoragePost c world := by
  have hs : Exit.cdsizeWord c = UInt256.ofNat 48 := by
    change UInt256.ofNat c.env.calldata.size = _
    rw [hsize]
  obtain ⟨gas, hres⟩ := EndpointState.exit_append_result c huser hen hperm hfee hs hpaid hg hf
  have hv := exit_storage_view c ho
  have he := (AppendSpec.exit_append_frame c).1
  have hw (q : UInt256) :
      worldSlot (EndpointState.exitAppendState c).accountMap c.env.codeOwner q = expected c q := by
    rw [← he, worldSlot_state]
    exact hv.2 q
  have howner : ∃ acc, (EndpointState.exitAppendState c).accountMap.get? c.env.codeOwner = some acc := by
    simpa only [HasOwner, he] using hv.1
  exact ⟨_, _, gas, _, hres, howner, hw, storagePost_of_expected c hfit _ hw⟩

#print axioms deposit_storage_result
#print axioms exit_storage_result
#print axioms recordKey_toNat
#print axioms expected_record
#print axioms expected_outside

end Eip8282.Audit.Integrator.AppendStorage
