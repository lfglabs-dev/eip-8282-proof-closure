import Eip8282.Audit.Integrator.ReferenceSystemBlockReceipt

/-! Storage part of update_builder_from_tx before incorporate_tx_into_block,
EL0cc100eb190b64b23baba72dac0165652eaec252, block_access_lists.py334-368,
601-614,617-672 and state_tracker.py796-822 (archived sources). The SYSTEM
consumer derives empty account/code writes, so account balance/nonce/code
branches are absent. Checked big-endian conversion is performed before each
BAL change, and pre-values come from the unmerged parent. This local storage
projection neither validates the final block BAL cap nor executes Python.
FixedUnsigned.from_be_bytes comes from ethereum-types0.4.1 numeric.py566-577
(SHA47d040d4de043e46d19c2fd9f74b318396b6c83ab01fe346f98a3c477e58db46):
length check first, then big-endian decoding and checked word construction.
BlockAccessIndex is U32 (fork_types.py). None reports conversion failure;
partial mutable-builder state on Python exceptions is outside this successful
projection and is not represented as a rollback. The consumer derives valid
keys and thus never enters that failure branch.
-/
namespace Eip8282.Audit.Integrator.ReferenceSystemBlockAccess
open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open ReferenceStorageView ReferenceSystemBlockFootprint
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def decodeKey (bytes : ByteArray) : Option UInt256 :=
  if 32 < bytes.size then none else
    let n := fromBytes' bytes.data.toList.reverse
    if n < UInt256.size then some (UInt256.ofNat n) else none

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
      simpa [Nat.pow_succ,Nat.mul_comm] using h
    simp only [toLeBytesFixed,fromBytes']
    rw [ih _ hd]
    change n % 256 % 256 + 256 * (n/256) = n
    rw [Nat.mod_mod]
    exact Nat.mod_add_div n 256

theorem decode_word (q : UInt256) : decodeKey q.toByteArray = some q := by
  unfold decodeKey
  rw [UInt256.size_toByteArray,if_neg (by decide : ¬32 < 32)]
  rw [UInt256.toList_data_toByteArray]
  simp only [toBeBytesFixed,List.reverse_reverse]
  rw [decode_fixed q.toNat 32 (by exact q.val.isLt),if_pos (show q.toNat < UInt256.size from q.val.isLt),ofNat_toNat' q]

structure Change where
  index : UInt32
  value : UInt256

/-- Replace the first equal-index change, otherwise append: literal source
loop order. No uniqueness invariant on the incoming builder is needed. -/
def upsert (index : UInt32) (value : UInt256) : List Change → List Change
  | [] => [⟨index,value⟩]
  | change::rest => if change.index = index then ⟨index,value⟩::rest
      else change::upsert index value rest

structure Builder where
  index : UInt32
  accounts : Set AccountAddress
  slots : AccountAddress → UInt256 → Option (List Change)

noncomputable def add (b : Builder) (owner : AccountAddress) (key value : UInt256) : Builder := by
  classical
  exact { b with
    accounts := insert owner b.accounts
    slots := fun a q => if a = owner ∧ q = key
      then some (upsert b.index value ((b.slots a q).getD [])) else b.slots a q }

/-- Functional enumeration of the final owner-local dictionary, not a trace
of SSTORE attempts. Duplicate accesses are removed before enumeration. -/
noncomputable def entries (owner : AccountAddress) (tx : Tx) (keys : List UInt256) : List (ByteArray × UInt256) :=
  keys.dedup.filterMap (fun q => (tx.writes owner q.toByteArray).map (fun value => (q.toByteArray,value)))

theorem entries_complete {owner : AccountAddress} {tx : Tx} {keys : List UInt256}
    (support : Support owner tx keys) (a : AccountAddress) (key : ByteArray) (value : UInt256)
    (written : tx.writes a key = some value) :
    a = owner ∧ (key,value) ∈ entries owner tx keys := by
  obtain ⟨rfl,q,hq,rfl⟩ := support.writes a key value written
  refine ⟨rfl,List.mem_filterMap.mpr ⟨q,?_,?_⟩⟩
  · simpa only [List.mem_dedup] using hq
  · simp only [written,Option.map_some]

theorem entries_typed (owner : AccountAddress) (tx : Tx) (keys : List UInt256) :
    ∀ pair ∈ entries owner tx keys, ∃ q, decodeKey pair.1 = some q := by
  intro pair member
  obtain ⟨q,_,mapped⟩ := List.mem_filterMap.mp member
  obtain ⟨value,_,rfl⟩ := Option.map_eq_some_iff.mp mapped
  exact ⟨q,decode_word q⟩

theorem entries_sound (owner : AccountAddress) (tx : Tx) (keys : List UInt256)
    (pair : ByteArray × UInt256) (member : pair ∈ entries owner tx keys) :
    tx.writes owner pair.1 = some pair.2 := by
  obtain ⟨q,_,mapped⟩ := List.mem_filterMap.mp member
  obtain ⟨value,written,rfl⟩ := Option.map_eq_some_iff.mp mapped
  exact written

theorem entries_unique (owner : AccountAddress) (tx : Tx) (keys : List UInt256) :
    ((entries owner tx keys).map Prod.fst).Nodup := by
  classical
  unfold entries
  rw [List.map_filterMap]
  apply List.Nodup.filterMap ?_ (List.nodup_dedup keys)
  intro a a' bytes ha ha'
  simp only [Option.map_map,Function.comp_def] at ha ha'
  cases hw : tx.writes owner a.toByteArray with
  | none => simp [hw] at ha
  | some value =>
    cases hw' : tx.writes owner a'.toByteArray with
    | none => simp [hw'] at ha'
    | some value' =>
      simp only [hw,hw',Option.map_some,Option.mem_some_iff] at ha ha'
      exact ReferenceStorageView.key_injective (ha.trans ha'.symm)

/-- Net-zero filtering uses pre-incorporation parent reads. An overflowing
key conversion fails before that entry changes the builder. -/
noncomputable def update (parent : Parent) (owner : AccountAddress) :
    List (ByteArray × UInt256) → Builder → Option Builder
  | [],b => some b
  | (key,value)::rest,b =>
      if parentRead parent owner key = value then update parent owner rest b else
        (decodeKey key).bind (fun q => update parent owner rest (add b owner q value))

theorem update_total {parent : Parent} {owner : AccountAddress} {items : List (ByteArray × UInt256)}
    (typed : ∀ pair ∈ items, ∃ q, decodeKey pair.1 = some q) (builder : Builder) :
    ∃ final, update parent owner items builder = some final := by
  classical
  induction items generalizing builder with
  | nil => exact ⟨builder,rfl⟩
  | cons pair rest ih =>
    rcases pair with ⟨key,value⟩
    obtain ⟨q,hq⟩ := typed (key,value) (by simp)
    have tail := fun pair (member : pair ∈ rest) => typed pair (List.mem_cons_of_mem _ member)
    unfold update
    split
    · exact ih tail builder
    · rw [hq,Option.bind_some]
      exact ih tail (add builder owner q value)

/-- The source BlockAccessIndex is U32. Both mandatory drains retain the
incoming post-execution index; producing N+1 from block admission is separate. -/
theorem update_index {parent : Parent} {owner : AccountAddress} {items : List (ByteArray × UInt256)}
    {builder final : Builder} (actual : update parent owner items builder = some final) :
    final.index = builder.index := by
  induction items generalizing builder with
  | nil => cases actual; rfl
  | cons pair rest ih =>
    rcases pair with ⟨key,value⟩
    unfold update at actual
    split at actual
    · exact ih actual
    · obtain ⟨q,_,tail⟩ := Option.bind_eq_some_iff.mp actual
      exact ih (builder := add builder owner q value) tail

/-- Source order: BAL update first; only its successful return makes the
storage overlay available to the next fresh SYSTEM transaction. -/
noncomputable def incorporate (parent : Parent) (owner : AccountAddress) (tx : Tx)
    (keys : List UInt256) (builder : Builder) : Option (Parent × Builder) :=
  (update parent owner (entries owner tx keys) builder).map (fun next => (commit parent tx,next))

theorem incorporated (parent : Parent) (owner : AccountAddress) (tx : Tx)
    (keys : List UInt256) (builder : Builder) :
    ∃ next, incorporate parent owner tx keys builder = some (commit parent tx,next) := by
  obtain ⟨next,updated⟩ := update_total (parent := parent) (owner := owner) (entries_typed owner tx keys) builder
  exact ⟨next,by simp only [incorporate,updated,Option.map_some]⟩

#print axioms decode_word
#print axioms entries_complete
#print axioms entries_typed
#print axioms entries_sound
#print axioms entries_unique
#print axioms update_total
#print axioms update_index
#print axioms incorporated
end Eip8282.Audit.Integrator.ReferenceSystemBlockAccess
