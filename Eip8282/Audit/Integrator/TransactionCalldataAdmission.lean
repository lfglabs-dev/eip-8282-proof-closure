import Eip8282.Audit.Integrator.TransactionJournal

/-! Actual pinned intrinsic-gas admission bounds transaction calldata.
EvmYul/EVM/Gas.lean intrinsicGas charges a natural4 or16 per data byte.
This does not silently add intrinsic admission to TransactionFunding.Admission;
the protocol/executable transaction validator must supply the explicit gate.
-/
namespace Eip8282.Audit.Integrator.TransactionCalldataAdmission
open EvmYul EvmYul.EVM
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

def byteCost (acc : Nat) (b : UInt8) : Nat := acc + if b == 0 then 4 else 16

private theorem loop_bound (data : ByteArray) (i j acc : Nat) (h : j+i ≤ data.size) :
    acc+4*i ≤ ByteArray.foldlM.loop (m := Id) (fun a b => pure (byteCost a b))
      data data.size (Nat.le_refl _) i j acc := by
  induction i generalizing j acc with
  | zero =>
    rw [ByteArray.foldlM.loop]
    split <;> exact Nat.le_refl _
  | succ i ih =>
    have hj : j < data.size := by omega
    rw [ByteArray.foldlM.loop,dif_pos hj]
    change acc+4*(i+1) ≤ ByteArray.foldlM.loop (m := Id) (fun a b => pure (byteCost a b))
      data data.size (Nat.le_refl _) i (j+1) (byteCost acc data[j])
    have ht := ih (j+1) (byteCost acc data[j]) (by omega)
    have hb : acc+4 ≤ byteCost acc data[j] := by
      unfold byteCost
      split <;> omega
    omega

theorem data_cost (data : ByteArray) : 4*data.size ≤ data.foldl byteCost 0 := by
  have h := loop_bound data data.size 0 0 (by omega)
  simpa only [ByteArray.foldl,ByteArray.foldlM,dif_pos (Nat.le_refl data.size),
    Nat.sub_zero,Id.run,Nat.zero_add] using h

theorem intrinsic_bound (t : Transaction) : 4*t.base.data.size ≤ intrinsicGas t := by
  have h := data_cost t.base.data
  change 4*t.base.data.size ≤ t.base.data.foldl
    (fun acc b => acc + if b == 0 then GasConstants.Gtxdatazero else GasConstants.Gtxdatanonzero) 0 at h
  unfold intrinsicGas
  dsimp only
  omega

theorem calldata_fit (t : Transaction) (admitted : intrinsicGas t ≤ t.base.gasLimit.toNat) :
    t.base.data.size < UInt256.size := by
  have h := intrinsic_bound t
  have hw := t.base.gasLimit.val.isLt
  change t.base.gasLimit.toNat < UInt256.size at hw
  omega

#print axioms data_cost
#print axioms intrinsic_bound
#print axioms calldata_fit
end Eip8282.Audit.Integrator.TransactionCalldataAdmission
