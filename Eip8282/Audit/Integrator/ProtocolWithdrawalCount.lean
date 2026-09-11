import Eip8282.Audit.Integrator.ProtocolCreditEnvelope
import Eip8282.Audit.Integrator.ResourceBounds

/-! Conditional withdrawal-list and dispatch producers for the credit envelope.
Archived CL ad0058fd0d34c5dcf504fa51ea2f4f11077b9996: Capella
Withdrawals.LIMIT=16; Gloas constructs that same bounded list after concatenating
builder pending, validator partial, builder sweep, and validator sweep entries.
Archived EL 0cc100eb190b64b23baba72dac0165652eaec252 credits every list item.
Typed list validity, canonical distinct beacon slots, and exact CL-to-EL list
transport are explicit inputs. No EL block-number width or reference evaluator
correspondence is inferred. -/
namespace Eip8282.Audit.Integrator.ProtocolWithdrawalCount
open EvmYul EvmYul.EVM
open ProtocolCreditEnvelope
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000

/-- All withdrawal classes use the same EL recipient/uint64-Gwei credit fields.
There is no validator-only selector which could omit builder withdrawals. -/
structure Item where
  recipient : AccountAddress
  gwei : ResourceBounds.U64

def Item.amount (item : Item) : UInt256 := UInt256.ofNat (item.gwei.val * 10^9)

theorem numeric : 2^64 * 10^9 < UInt256.size := by decide +kernel
theorem bound_item (item : Item) : item.gwei.val * 10^9 < UInt256.size := by
  exact (Nat.mul_lt_mul_of_pos_right item.gwei.isLt (by decide : 0 < 10^9)).trans numeric
theorem ofNat_toNat (n : Nat) : (UInt256.ofNat n).toNat = n % UInt256.size := rfl

theorem amount_exact (item : Item) : item.amount.toNat = item.gwei.val * 10^9 := by
  rw [Item.amount,ofNat_toNat,Nat.mod_eq_of_lt (bound_item item)]
theorem amount_bounded (item : Item) : item.amount.toNat ≤ withdrawalMaximum := by
  rw [amount_exact]
  have h : item.gwei.val ≤ 2^64-1 := Nat.le_sub_one_of_lt item.gwei.isLt
  exact Nat.mul_le_mul_right (10^9) h



/-- Every actual append increases the combined prior-list length by one, and
is permitted only below the supplied limit. Skipped sweep iterations add no
entry. Transport from the archived Python loops is not asserted here. -/
inductive GuardedAdds {α : Type} (limit : Nat) : Nat → List α → Prop where
  | nil {prior : Nat} (h : prior ≤ limit) : GuardedAdds limit prior []
  | cons {prior : Nat} {head : α} {tail : List α}
      (guard : prior < limit) (rest : GuardedAdds limit (prior+1) tail) :
      GuardedAdds limit prior (head::tail)

theorem guarded_length {α : Type} {limit prior : Nat} {items : List α}
    (h : GuardedAdds limit prior items) : prior+items.length ≤ limit := by
  induction h with
  | nil h => simpa using h
  | cons guard rest ih => simp only [List.length_cons]; omega


/-- A decoded and accepted bounded withdrawal list at its beacon slot.
The bound is the explicit SSZ/list-validity adapter premise, not an arbitrary
assumed lifetime count or a property of the EL block number. -/
structure Payload where
  slot : ResourceBounds.U64
  items : List Item
  bounded : items.length ≤ 16

/-- This constructor retains all four Gloas dispatch lists in source order.
The partial-withdrawal guarded trace remains an explicit producer obligation:
its inherited implementation is absent from the archived local corpus. -/
def gloasPayload (slot : ResourceBounds.U64)
    (builderPending validatorPartial builderSweep validatorSweep : List Item)
    (_pending : GuardedAdds 15 0 builderPending)
    (_partial : GuardedAdds 15 builderPending.length validatorPartial)
    (_builders : GuardedAdds 15 (builderPending.length+validatorPartial.length) builderSweep)
    (validators : GuardedAdds 16
      (builderPending.length+validatorPartial.length+builderSweep.length) validatorSweep) : Payload :=
  { slot := slot, items := builderPending ++ validatorPartial ++ builderSweep ++ validatorSweep,
    bounded := by simpa only [List.length_append] using guarded_length validators }

theorem gloas_items (slot : ResourceBounds.U64)
    (bp vp bs vs : List Item) (hbp : GuardedAdds 15 0 bp)
    (hvp : GuardedAdds 15 bp.length vp) (hbs : GuardedAdds 15 (bp.length+vp.length) bs)
    (hvs : GuardedAdds 16 (bp.length+vp.length+bs.length) vs) :
    (gloasPayload slot bp vp bs vs hbp hvp hbs hvs).items = bp ++ vp ++ bs ++ vs := rfl

def totalItems (payloads : List Payload) : Nat := (payloads.map (fun p => p.items.length)).sum

theorem totalItems_flatMap (payloads : List Payload) :
    totalItems payloads = (payloads.flatMap (·.items)).length := by
  induction payloads with
  | nil => rfl
  | cons p ps ih =>
    simp only [totalItems,List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append]
    exact congrArg (p.items.length + ·) ih


theorem per_payload_sum (payloads : List Payload) : totalItems payloads ≤ 16*payloads.length := by
  induction payloads with
  | nil => simp [totalItems]
  | cons p ps ih =>
    have hp := p.bounded
    simp only [totalItems,List.map_cons,List.sum_cons,List.length_cons]
    change p.items.length + totalItems ps ≤ 16*(ps.length+1)
    omega


/-- Distinct typed beacon slots bound the number of credited payload lists.
Empty slots may be absent; duplicate payload dispatches may not be silently
removed. Their exclusion is the explicit canonical/dispatch input. -/
theorem total_count (payloads : List Payload) (slots : (payloads.map (·.slot)).Nodup) :
    totalItems payloads ≤ 16*2^64 := by
  have hs := slots.length_le_card
  simp only [List.length_map,Fintype.card_fin] at hs
  exact (per_payload_sum payloads).trans (Nat.mul_le_mul_left 16 hs)

/-- Literal existing funding credit updates, in exactly the supplied list
order. Identical recipients or duplicate-valued entries are credited and
counted separately; no payload filtering or deduplication occurs. -/
inductive Dispatch : AccountMap .EVM → List Item → AccountMap .EVM → Prop where
  | nil (world : AccountMap .EVM) : Dispatch world [] world
  | cons {before after : AccountMap .EVM} {item : Item} {items : List Item}
      (tail : Dispatch (before.increaseBalance .EVM item.recipient item.amount) items after) :
      Dispatch before (item::items) after

def credits (items : List Item) : Nat := (items.map (fun item => item.amount.toNat)).sum

/-- Every dispatched item creates precisely one Ledger.withdrawal edge. Its
amount bound follows from the uint64 Gwei input; the count is derived by the
actual list induction, not an extra dispatch-count hypothesis. -/
theorem dispatch_ledger {initial before after : AccountMap .EVM} {p w s c : Nat}
    {items : List Item} (prior : Ledger initial p w s c before) (run : Dispatch before items after) :
    Ledger initial p (w+items.length) s (c+credits items) after := by
  induction run generalizing w c with
  | nil world => simpa [credits] using prior
  | @cons before after item items tail ih =>
    have h := ih (Ledger.withdrawal prior item.recipient item.amount (amount_bounded item))
    simpa only [List.length_cons,credits,List.map_cons,List.sum_cons,Nat.add_assoc,
      Nat.add_left_comm,Nat.add_comm] using h

/-- The current envelope's withdrawal-count field is discharged from payload
lists and slots; PoW ancestry and migration conservation remain independent. -/
theorem counts {pow migrations : Nat} (payloads : List Payload)
    (slots : (payloads.map (·.slot)).Nodup)
    (powBound : pow ≤ 2^64) (migrationConserving : migrations=0) :
    Counts pow (totalItems payloads) migrations :=
  ⟨powBound,total_count payloads slots,migrationConserving⟩

/-- Concrete dispatch plus typed payload enumeration supplies both the ledger
withdrawal count and Counts, with no assumed count of dispatched operations. -/
theorem dispatched_counts {initial before after : AccountMap .EVM} {p s c : Nat}
    (prior : Ledger initial p 0 s c before) (payloads : List Payload)
    (run : Dispatch before (payloads.flatMap (·.items)) after)
    (slots : (payloads.map (·.slot)).Nodup)
    (powBound : p ≤ 2^64) (migrationConserving : s=0) :
    Ledger initial p (totalItems payloads) s (c+credits (payloads.flatMap (·.items))) after ∧
      Counts p (totalItems payloads) s := by
  have h := dispatch_ledger prior run
  rw [Nat.zero_add,←totalItems_flatMap] at h
  exact ⟨h,counts payloads slots powBound migrationConserving⟩

#print axioms amount_exact
#print axioms amount_bounded
#print axioms guarded_length
#print axioms total_count
#print axioms dispatch_ledger
#print axioms dispatched_counts
end Eip8282.Audit.Integrator.ProtocolWithdrawalCount
