import Eip8282.Audit.Integrator.TransactionCalldataAdmission

/-! Source-transcribed Amsterdam calldata-floor admission, distinct from pinned
EVMYul intrinsicGas (whose base differs). Exact EL commit
0cc100eb190b64b23baba72dac0165652eaec252 transactions.py:56,654-777 SHA256
1fb6202062805d892a2a0100f46220d7a762e88a049ab9871b53f5159f6e0b25;
vm/gas.py:154-158 SHA256
41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c.
The source computes uniform calldata tokens, adds access tokens, multiplies by
16 and adds12000 plus recipient execution cost, then checks the fixed maximum.
This is an audited Nat transcription, not execution of Python validation or
an implication to the different old intrinsicGas gate. Source transaction/data
and cost bindings remain the adapter's explicit responsibility.
-/
namespace Eip8282.Audit.Integrator.ReferenceCalldataAdmission
open EvmYul
set_option autoImplicit false

/-- Preserve the exact source calculation order; all costs are nonnegative. -/
def floor (dataBytes recipientExecution accessTokens : Nat) : Nat :=
  let calldataTokens := dataBytes*4
  let totalTokens := calldataTokens+accessTokens
  let baseExecution := 12000+recipientExecution
  totalTokens*16+baseExecution

/-- Only the actual calldata-floor maximum check, not full transaction validity. -/
def Gate (dataBytes recipientExecution accessTokens : Nat) : Prop :=
  floor dataBytes recipientExecution accessTokens ≤ 16777216

theorem floor_bound {dataBytes recipientExecution accessTokens : Nat}
    (gate : Gate dataBytes recipientExecution accessTokens) : dataBytes ≤ 261956 := by
  unfold Gate floor at gate
  dsimp only at gate
  omega

/-- Fits the pinned word representation without assuming tx.gas has word type. -/
theorem data_fit (data : ByteArray) {recipientExecution accessTokens : Nat}
    (gate : Gate data.size recipientExecution accessTokens) : data.size < UInt256.size := by
  have bound := floor_bound gate
  have maxFits : 261956 < UInt256.size := by decide +kernel
  omega

/-- The uniform bound is sharp for the nonnegative-cost abstraction. Concrete
recipient/authorizations/access-list cases may impose stricter bounds. -/
theorem boundary : Gate 261956 0 0 ∧ ¬ Gate 261957 0 0 := by
  unfold Gate floor
  decide +kernel

#print axioms floor_bound
#print axioms data_fit
#print axioms boundary
end Eip8282.Audit.Integrator.ReferenceCalldataAdmission
