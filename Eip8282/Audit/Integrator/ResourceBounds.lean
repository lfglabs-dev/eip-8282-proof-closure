import Eip8282.Audit.Integrator.AppendStorage
import Mathlib.Data.Fintype.Card

/-!
# The finite-slot gas envelope, separated from execution accounting

The reference protocol uses 64-bit slots and payload gas limits. This module
proves the arithmetic implication for a finite canonical history with distinct
slots. It does not assert that arbitrary Θ histories satisfy that envelope.
In particular `charged` must be proved from actual transaction gas accounting,
including nested calls and refunds, before these bounds are protocol invariants.
See audit/PROTOCOL-BOUNDARY.md for immutable reference sources and open bindings.
-/
namespace Eip8282.Audit.Integrator.ResourceBounds

open EvmYul
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall)

abbrev U64 := Fin (2^64)

/-- Accounting inputs, not assumed storage postconditions. -/
structure BlockUsage where
  slot : U64
  gas : U64
  appends : Nat
  charged : appends ≤ gas.val

def totalAppends (blocks : List BlockUsage) : Nat := (blocks.map (·.appends)).sum

theorem total_le (blocks : List BlockUsage) :
    totalAppends blocks ≤ blocks.length * (2^64-1) := by
  induction blocks with
  | nil => simp [totalAppends]
  | cons b bs ih =>
    have hb := b.gas.isLt
    have hc := b.charged
    simp only [totalAppends, List.map_cons, List.sum_cons, List.length_cons]
    change b.appends + totalAppends bs ≤ (bs.length+1)*(2^64-1)
    rw [Nat.add_mul]
    omega

/-- Fewer than 2^128 committed appends within the stated finite slot/gas
accounting envelope. The bound follows from typed resources and distinct slots. -/
theorem total_lt (blocks : List BlockUsage) (hs : (blocks.map (·.slot)).Nodup) :
    totalAppends blocks < 2^128 := by
  have hl := hs.length_le_card
  simp only [List.length_map, Fintype.card_fin] at hl
  have ht := total_le blocks
  have hm := Nat.mul_le_mul_right (2^64-1) hl
  have hc : 2^64*(2^64-1) < 2^128 := by decide
  exact lt_of_le_of_lt (ht.trans hm) hc

/-- Capacity and counter fit follows once actual entry counters have been
bounded by the accounted append count. The state/accounting bridge is explicit. -/
theorem appendFits_of_accounted (c : XiCall kind) (blocks : List BlockUsage)
    (hs : (blocks.map (·.slot)).Nodup)
    (ht : (AppendStorage.entryTail c).toNat ≤ totalAppends blocks)
    (hc : (AppendStorage.entryCount c).toNat ≤ totalAppends blocks) :
    AppendStorage.AppendFits c := by
  have hb := total_lt blocks hs
  have hw : 4+6*2^128+6 < UInt256.size := by decide
  have hstride : AppendStorage.stride kind ≤ 6 := by cases kind <;> decide
  have hm := Nat.mul_le_mul_right (AppendStorage.entryTail c).toNat hstride
  unfold AppendStorage.AppendFits
  omega

/-- Once excess and count are accounted, both control and fee-input additions
fit; this is distinct from the much stronger fee-recurrence product bound. -/
theorem control_sum_fits (excess count : UInt256) (blocks : List BlockUsage)
    (hs : (blocks.map (·.slot)).Nodup)
    (he : excess.toNat ≤ totalAppends blocks) (hc : count.toNat ≤ totalAppends blocks) :
    excess.toNat + count.toNat < UInt256.size := by
  have hb := total_lt blocks hs
  have hsize : 2^129 < UInt256.size := by decide
  omega

#print axioms total_lt
#print axioms appendFits_of_accounted
#print axioms control_sum_fits

end Eip8282.Audit.Integrator.ResourceBounds
