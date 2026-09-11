import Eip8282.Audit.Integrator.ResourceBounds

/-! Aggregate block-gas envelope, complementing `ResourceBounds`.

`ResourceBounds.totalAppends` bounds the total *append count* across all
blocks by `2^128` under the reference protocol's typed 64-bit slot and gas
inputs. This module states and proves the analogous bound on the total
*gas capacity* itself — `totalGas` — so downstream consumers can quote a
uniform 2^128 envelope regardless of which resource they are tracking, and
so the pointwise inequality `totalAppends blocks ≤ totalGas blocks`
becomes a named lemma.

The bound is a corollary of `BlockUsage` typing (`gas : Fin (2^64)`) and
slot uniqueness. It does NOT assert that arbitrary Θ histories actually
satisfy these envelopes: as noted in `ResourceBounds`, `charged` must still
be produced from actual transaction gas accounting, including nested calls
and refunds. See `audit/PROTOCOL-BOUNDARY.md`. -/
namespace Eip8282.Audit.Integrator.ReferenceBlockGasCapacity

open EvmYul
open Eip8282.Audit.Integrator.ResourceBounds
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Natural sum of block gas capacities. -/
def totalGas (blocks : List BlockUsage) : Nat := (blocks.map (fun b => b.gas.val)).sum

/-- Sum of gas capacities is at most `length * (2^64 - 1)`. Mirrors
`ResourceBounds.total_le` on the gas dimension. -/
theorem totalGas_le (blocks : List BlockUsage) :
    totalGas blocks ≤ blocks.length * (2^64-1) := by
  induction blocks with
  | nil => simp [totalGas]
  | cons b bs ih =>
    have hb := b.gas.isLt
    simp only [totalGas, List.map_cons, List.sum_cons, List.length_cons]
    change b.gas.val + totalGas bs ≤ (bs.length+1)*(2^64-1)
    rw [Nat.add_mul]
    omega

/-- Fewer than 2^128 gas across a finite canonical history with distinct
slots. Slot uniqueness bounds `blocks.length ≤ 2^64` via `Fintype.card`. -/
theorem totalGas_lt (blocks : List BlockUsage) (hs : (blocks.map (·.slot)).Nodup) :
    totalGas blocks < 2^128 := by
  have hl := hs.length_le_card
  simp only [List.length_map, Fintype.card_fin] at hl
  have ht := totalGas_le blocks
  have hm := Nat.mul_le_mul_right (2^64-1) hl
  have hc : 2^64*(2^64-1) < 2^128 := by decide
  exact lt_of_le_of_lt (ht.trans hm) hc

/-- The block-level `charged` field constrains appends by gas per block, so
the aggregate append count is bounded by the aggregate gas capacity. -/
theorem totalAppends_le_totalGas (blocks : List BlockUsage) :
    totalAppends blocks ≤ totalGas blocks := by
  induction blocks with
  | nil => simp [totalAppends, totalGas]
  | cons b bs ih =>
    simp only [totalAppends, totalGas, List.map_cons, List.sum_cons]
    change b.appends + totalAppends bs ≤ b.gas.val + totalGas bs
    have hc := b.charged
    omega

/-- Combined uniform envelope: total appends and total gas both fit inside
2^128. Consumers that need one bound on both resources can quote this. -/
theorem uniform_envelope (blocks : List BlockUsage)
    (hs : (blocks.map (·.slot)).Nodup) :
    totalAppends blocks < 2^128 ∧ totalGas blocks < 2^128 :=
  ⟨total_lt blocks hs, totalGas_lt blocks hs⟩

#print axioms totalGas_le
#print axioms totalGas_lt
#print axioms totalAppends_le_totalGas
#print axioms uniform_envelope

end Eip8282.Audit.Integrator.ReferenceBlockGasCapacity
