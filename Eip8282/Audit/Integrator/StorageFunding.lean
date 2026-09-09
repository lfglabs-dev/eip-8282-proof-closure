import Eip8282.Audit.Integrator.TransferFunding
import Eip8282.Audit.Integrator.SystemSpec

/-!
# Storage writes preserve the real total of account balances

The total is the finite AccountMap sum, not a model balance. Owner absence is
handled by the real operation. Persistent/transient storage and refund/access
bookkeeping may change, but no funded-transfer or supply assumption is needed.
-/
namespace Eip8282.Audit.Integrator.StorageFunding

open EvmYul EvmYul.EVM
open TransferFunding

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Replacing an existing account without changing its balance preserves funds. -/
theorem replace_preserves (world : AccountMap .EVM) (a : AccountAddress)
    (old new : Account .EVM) (h : world.get? a = some old) (hb : new.balance = old.balance) :
    worldFunds (world.insert a new) = worldFunds world := by
  have hf := funds_insert world a new
  simp only [worldBalance, h, Option.map_some, Option.getD_some, hb] at hf
  omega

theorem sstore_preserves (st : EvmYul.State .EVM) (key value : UInt256) :
    worldFunds (st.sstore key value).accountMap = worldFunds st.accountMap := by
  cases ha : st.accountMap.get? st.executionEnv.codeOwner with
  | none =>
    unfold EvmYul.State.sstore
    dsimp only
    rcases hg : Std.TreeMap.get! st.accountMap st.executionEnv.codeOwner with
      ⟨⟨nonce, bal, storage, code⟩, transient⟩
    have hlookup : st.lookupAccount st.executionEnv.codeOwner = none := ha
    rw [hlookup]
    rfl
  | some account =>
    rw [SystemSpec.accountMap_sstore ha]
    exact replace_preserves st.accountMap st.executionEnv.codeOwner account
      (account.updateStorage key value) ha (by unfold Account.updateStorage; split <;> rfl)

theorem tstore_preserves (st : EvmYul.State .EVM) (key value : UInt256) :
    worldFunds (st.tstore key value).accountMap = worldFunds st.accountMap := by
  cases ha : st.accountMap.get? st.executionEnv.codeOwner with
  | none =>
    unfold EvmYul.State.tstore
    dsimp only
    have hlookup : st.lookupAccount st.executionEnv.codeOwner = none := ha
    rw [hlookup]
    rfl
  | some account =>
    unfold EvmYul.State.tstore
    dsimp only
    have hlookup : st.lookupAccount st.executionEnv.codeOwner = some account := ha
    rw [hlookup]
    exact replace_preserves st.accountMap st.executionEnv.codeOwner account
      (account.updateTransientStorage key value) ha (by unfold Account.updateTransientStorage; split <;> rfl)

#print axioms replace_preserves
#print axioms sstore_preserves
#print axioms tstore_preserves

end Eip8282.Audit.Integrator.StorageFunding
