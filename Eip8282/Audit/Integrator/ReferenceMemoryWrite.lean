import Eip8282.Audit.Integrator.ReferenceMemoryView

/-! Actual sparse ByteArray.write observations. Padding bounds concern the
branches that allocate zeros; no small source-offset or predicted post-memory
relation is assumed. This is a pinned byte-array theorem, not Python execution
or resource adequacy. -/
namespace Eip8282.Audit.Integrator.ReferenceMemoryWrite
open EvmYul ReferenceMemoryView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-- Zero-length and out-of-range-source branches need no destination-gap bound. -/
def Bounds (src dst : ByteArray) (so dest len : Nat) : Prop :=
  len = 0 ∨ (len < 2^System.Platform.numBits ∧
    (so < src.size → dest-dst.size < 2^System.Platform.numBits))

private theorem zeroes (n : Nat) (h : n < 2^System.Platform.numBits) :
    (ffi.ByteArray.zeroes ⟨n⟩).data = Array.replicate n 0 := by
  simp only [ffi.ByteArray.zeroes]
  rw [ffi.ByteArray.toNat_natCast_of_lt n h]

/-- Exact byte observation, including implicit zero suffixes of either buffer. -/
theorem write_byte (src dst : ByteArray) (so dest len i : Nat)
    (bounds : Bounds src dst so dest len) :
    byte (ByteArray.write src so dst dest len) i =
      if dest ≤ i ∧ i < dest+len then byte src (so+(i-dest)) else byte dst i := by
  by_cases hz : len=0
  · subst len
    simp [ByteArray.write]
  · obtain ⟨hlen,hgap⟩ := bounds.resolve_left hz
    unfold ByteArray.write
    rw [if_neg hz]
    split
    · rename_i hout
      dsimp only
      simp only [byte,ByteArray.copySlice]
      rw [zeroes _ (by omega)]
      simp only [Array.getElem?_append,Array.getElem?_extract,
        Array.getElem?_replicate,Array.size_append,Array.size_extract,Array.size_replicate]
      simp only [ByteArray.size] at *
      simp only [Nat.zero_add,Nat.sub_zero,Nat.min_self] at *
      repeat' first | omega | rfl | split
      all_goals try simp only [Option.getD_some,Option.getD_none]
      all_goals first | (rw [Array.getElem?_eq_none (by omega)]; rfl) | (congr 2; omega)
    · rename_i hin
      have hgap' := hgap (by omega)
      dsimp only
      simp only [byte,ByteArray.copySlice,ByteArray.data_append]
      rw [zeroes (dest-dst.size) hgap',zeroes (min dst.size (dest+len)-(dest+min len (src.size-so))) (by omega)]
      simp only [Array.getElem?_append,
        Array.getElem?_extract,Array.getElem?_replicate,Array.size_append,
        Array.size_extract,Array.size_replicate]
      simp only [ByteArray.size] at *
      simp only [Nat.zero_add,Nat.sub_zero,Nat.min_self] at *
      repeat' first | omega | rfl | split
      all_goals try simp only [Option.getD_some,Option.getD_none]
      all_goals first | (rw [Array.getElem?_eq_none (by omega)]; rfl) | (congr 2; omega)

/-- Pointwise input equality suffices even when physical zero suffixes differ. -/
theorem congr (src₁ src₂ dst₁ dst₂ : ByteArray) (so dest len : Nat)
    (sources : Same src₁ src₂) (destinations : Same dst₁ dst₂)
    (bound₁ : Bounds src₁ dst₁ so dest len) (bound₂ : Bounds src₂ dst₂ so dest len) :
    Same (ByteArray.write src₁ so dst₁ dest len) (ByteArray.write src₂ so dst₂ dest len) := by
  intro i
  rw [write_byte _ _ _ _ _ _ bound₁,write_byte _ _ _ _ _ _ bound₂]
  split
  · exact sources _
  · exact destinations _

#print axioms write_byte
#print axioms congr
end Eip8282.Audit.Integrator.ReferenceMemoryWrite
