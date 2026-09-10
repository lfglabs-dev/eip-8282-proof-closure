import Eip8282.Audit.Integrator.SystemSpec

/-! Source-shaped storage overlays, EL0cc100eb190b64b23baba72dac0165652eaec252,
state_tracker.py:244-302,433-458,718-825, SHA256
ce420ad5682df9051178d298220d1552448e26c37f67be3b604b9f493541cf4a.
Functional read views represent source dictionaries; this does not prove Python
execution or PreState/account validity. Original-created override and shared
rollback metadata are explicit. Gas, refunds and account fields are not equated.
-/
namespace Eip8282.Audit.Integrator.ReferenceStorageView
open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open SystemSpec Eip8282.Audit.SymExec
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 1600000

private theorem decode_fixed (n w : Nat) (h : n < 256^w) :
    fromBytes' (toLeBytesFixed n w) = n := by
  induction w generalizing n with
  | zero =>
    have hn : n = 0 := Nat.lt_one_iff.mp h
    subst n
    rfl
  | succ w ih =>
    have hd : n/256 < 256^w := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [Nat.pow_succ, Nat.mul_comm] using h
    simp only [toLeBytesFixed,fromBytes']
    rw [ih _ hd]
    change n % 256 % 256 + 256 * (n/256) = n
    rw [Nat.mod_mod]
    exact Nat.mod_add_div n 256

theorem key_injective : Function.Injective UInt256.toByteArray := by
  intro a b he
  have hl := congrArg (fun bytes : ByteArray => bytes.data.toList) he
  rw [UInt256.toList_data_toByteArray,UInt256.toList_data_toByteArray] at hl
  have hr := congrArg (fun bytes => fromBytes' bytes.reverse) hl
  simp only [toBeBytesFixed,List.reverse_reverse] at hr
  rw [decode_fixed a.toNat 32 (by exact a.val.isLt),
    decode_fixed b.toNat 32 (by exact b.val.isLt)] at hr
  cases a with | mk a =>
  cases b with | mk b =>
  exact congrArg UInt256.mk (Fin.ext hr)

abbrev Overlay := AccountAddress → ByteArray → Option UInt256

structure Parent where
  writes : Overlay
  pre : AccountAddress → ByteArray → UInt256

structure Tx where
  writes : Overlay
  created : Set AccountAddress
  reads : Set (AccountAddress × ByteArray)

def parentRead (p : Parent) (a : AccountAddress) (k : ByteArray) : UInt256 :=
  (p.writes a k).getD (p.pre a k)

def current (p : Parent) (s : Tx) (a : AccountAddress) (k : ByteArray) : UInt256 :=
  (s.writes a k).getD (parentRead p a k)

noncomputable def original (p : Parent) (s : Tx) (a : AccountAddress) (k : ByteArray) : UInt256 :=
  if a ∈ s.created then ⟨0⟩ else parentRead p a k

noncomputable def write (s : Tx) (a : AccountAddress) (k : ByteArray) (v : UInt256) : Tx :=
  {s with writes := fun b q => if b = a ∧ q = k then some v else s.writes b q}

def readTracked (s : Tx) (a : AccountAddress) (k : ByteArray) : Tx :=
  {s with reads := insert (a,k) s.reads}

/-- Only the current write overlay is restored in this storage projection.
Created-account and BAL-read sets are retained from the live transaction. -/
def rollback (s snapshot : Tx) : Tx := {s with writes := snapshot.writes}

def commit (p : Parent) (s : Tx) : Parent :=
  {p with writes := fun a k => (s.writes a k).orElse (fun _ => p.writes a k)}

theorem write_read (p : Parent) (s : Tx) (a b : AccountAddress) (k q : ByteArray) (v : UInt256) :
    current p (write s a k v) b q = if b = a ∧ q = k then v else current p s b q := by
  classical
  by_cases he : b = a ∧ q = k
  · simp only [current,write,if_pos he,Option.getD_some]
  · simp only [current,write,if_neg he]

theorem zero_overrides (p : Parent) (s : Tx) (a : AccountAddress) (k : ByteArray) :
    current p (write s a k ⟨0⟩) a k = ⟨0⟩ := by simp [write_read]

theorem tracked_read (p : Parent) (s : Tx) (a b : AccountAddress) (k q : ByteArray) :
    current p (readTracked s a k) b q = current p s b q := rfl

theorem original_created (p : Parent) (s : Tx) (a : AccountAddress) (k : ByteArray)
    (h : a ∈ s.created) : original p s a k = ⟨0⟩ := by simp [original,h]

theorem rollback_current (p : Parent) (s snapshot : Tx) (a : AccountAddress) (k : ByteArray) :
    current p (rollback s snapshot) a k = current p snapshot a k := rfl

theorem rollback_metadata (s snapshot : Tx) :
    (rollback s snapshot).created = s.created ∧ (rollback s snapshot).reads = s.reads := ⟨rfl,rfl⟩

theorem commit_read (p : Parent) (s : Tx) (a : AccountAddress) (k : ByteArray) :
    parentRead (commit p s) a k = current p s a k := by
  change ((s.writes a k).orElse (fun _ => p.writes a k)).getD (p.pre a k) = _
  cases h : s.writes a k <;> simp [current,h,parentRead]

/-- Relate only the currently visible owner slots, not refunds or original state. -/
def Related (p : Parent) (s : Tx) (st : EvmYul.State .EVM) : Prop :=
  ∀ k, current p s st.executionEnv.codeOwner k.toByteArray = slotW st k

theorem write_transport (p : Parent) (s : Tx) (st : EvmYul.State .EVM)
    (h : Related p s st) (owner : HasOwner st) (k v : UInt256) :
    Related p (write s st.executionEnv.codeOwner k.toByteArray v) (st.sstore k v) := by
  intro q
  rw [executionEnv_sstore,write_read,
    SystemSpec.slot_sstore owner]
  have hk : q.toByteArray = k.toByteArray ↔ q = k := key_injective.eq_iff
  simp only [true_and,hk]
  split
  · rfl
  · exact h q

#print axioms key_injective
#print axioms write_read
#print axioms rollback_current
#print axioms commit_read
#print axioms write_transport
end Eip8282.Audit.Integrator.ReferenceStorageView
