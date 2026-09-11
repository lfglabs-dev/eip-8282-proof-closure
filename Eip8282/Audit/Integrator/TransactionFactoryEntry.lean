import Eip8282.Audit.Integrator.FactoryCallEntry
import Eip8282.Audit.Integrator.TransactionFunding
import Eip8282.Audit.Integrator.TransactionEventBounds

/-! Actual admitted transaction checkpoint and selected factory message call.
Positive Theta fuel, installed code and actual recipient are explicit. No
initializer success or post-transaction invariant is assumed. -/
namespace Eip8282.Audit.Integrator.TransactionFactoryEntry
open EvmYul EvmYul.EVM
open NestedEvents FactoryRuntimeEntry TransferFunding
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

def call (c : RefundAccounting.Context) : MessageCall.Context :=
  (TransactionEventBounds.message c factoryAddress).context (c.fuel-1) FactoryRuntimeEntry.runtime

theorem call_fuel (c : RefundAccounting.Context) (n : Nat) (hf : c.fuel = n+1) :
    (call c).fuel = n := by change c.fuel-1 = n; omega

theorem checkpoint_factory (c : RefundAccounting.Context) (sender old : Account .EVM)
    (ha : TransactionFunding.Admission c sender)
    (hi : c.world.get? factoryAddress = some old) (hne : c.sender ≠ factoryAddress) :
    c.checkpoint.get? factoryAddress = some old := by
  rw [TransactionFunding.checkpoint_eq c ha]
  have he := Std.TreeMap.getElem?_insert (t := c.world) (k := c.sender)
    (a := factoryAddress) (v := TransactionFunding.debited c sender)
  change (c.world.insert c.sender (TransactionFunding.debited c sender)).get? factoryAddress = _ at he
  rw [he]
  simp only [Std.LawfulEqOrd.compare_eq_iff_eq,hne,if_false]
  exact hi

theorem selected_code (c : RefundAccounting.Context) (sender old : Account .EVM)
    (ha : TransactionFunding.Admission c sender)
    (hi : c.world.get? factoryAddress = some old) (hne : c.sender ≠ factoryAddress)
    (hc : old.code = FactoryRuntimeEntry.runtime) :
    toExecute .EVM c.checkpoint factoryAddress = .Code FactoryRuntimeEntry.runtime :=
  FactoryCallEntry.installed_toExecute c.checkpoint old (checkpoint_factory c sender old ha hi hne) hc

theorem call_funding (c : RefundAccounting.Context) (sender : Account .EVM)
    (ha : TransactionFunding.Admission c sender) :
    (call c).value.toNat ≤ worldBalance (call c).world (call c).caller ∧
      worldFunds (call c).world ≤ worldFunds c.world := by
  refine ⟨TransactionFunding.checkpoint_funded c ha,?_⟩
  have h := TransactionFunding.checkpoint_debit c ha
  change worldFunds c.checkpoint ≤ worldFunds c.world
  omega

theorem call_world_bound (c : RefundAccounting.Context) (sender : Account .EVM)
    (ha : TransactionFunding.Admission c sender) (hw : worldFunds c.world < UInt256.size) :
    worldFunds (call c).world < UInt256.size := (call_funding c sender ha).2.trans_lt hw

/-- The context result is the exact Theta selected by the transaction, including
all returned statuses and errors. Its inner fuel is one below outer Theta fuel. -/
theorem call_result (c : RefundAccounting.Context) (hf : 0 < c.fuel)
    (hc : toExecute .EVM c.checkpoint factoryAddress = .Code FactoryRuntimeEntry.runtime) :
    (call c).result = (Request.theta c.fuel (TransactionEventBounds.message c factoryAddress)).eval := by
  unfold Request.eval TransactionEventBounds.message
  rw [hc]
  change Θ (c.fuel-1+1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
  rw [Nat.sub_add_cancel (by omega)]
  rfl

theorem provisional_of_call (c : RefundAccounting.Context) (hf : 0 < c.fuel)
    (hc : toExecute .EVM c.checkpoint factoryAddress = .Code FactoryRuntimeEntry.runtime)
    (ht : c.transaction.base.recipient = some factoryAddress)
    (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (ss : Substate) (success : Bool) (out : ByteArray)
    (hr : (call c).result = .ok (created,world,gas,ss,success,out)) :
    c.provisional = .ok (world,gas,ss,success) := by
  rw [call_result c hf hc] at hr
  unfold RefundAccounting.Context.provisional
  rw [ht]
  change Θ c.fuel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ at hr
  dsimp only [TransactionEventBounds.message] at hr
  simp only
  rw [hr]

#print axioms call_fuel
#print axioms checkpoint_factory
#print axioms selected_code
#print axioms call_funding
#print axioms call_world_bound
#print axioms call_result
#print axioms provisional_of_call
end Eip8282.Audit.Integrator.TransactionFactoryEntry
