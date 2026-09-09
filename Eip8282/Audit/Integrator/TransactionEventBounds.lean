import Eip8282.Audit.Integrator.NestedEventBounds
import Eip8282.Audit.Integrator.TransactionGas

/-!
# The actual Υ child tree and capped transaction refunds

The request below is exactly the provisional invocation selected by Υ. Its
event budget is extracted, not supplied. Locally executed events remain counted
when final transaction status is false. Committed-record counts and Ethereum
block admission still require separate history/protocol adapters.
-/
namespace Eip8282.Audit.Integrator.TransactionEventBounds
open EvmYul EvmYul.EVM
open RefundAccounting NestedEvents
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1400000

def creation (c : Context) : LambdaArgs :=
  { hashes := c.transaction.blobVersionedHashes, created := .empty,
    genesis := c.genesis, blocks := c.blocks, world := c.checkpoint,
    original := c.checkpoint, substate := c.entrySubstate, source := c.sender,
    origin := c.sender, gas := c.entryGas, price := c.effectivePrice,
    value := c.transaction.base.value, init := c.transaction.base.data,
    depth := ⟨0⟩, salt := none, header := c.header, permission := true }

def message (c : Context) (target : AccountAddress) : ThetaArgs :=
  { hashes := c.transaction.blobVersionedHashes, created := .empty,
    genesis := c.genesis, blocks := c.blocks, world := c.checkpoint,
    original := c.checkpoint, substate := c.entrySubstate, source := c.sender,
    origin := c.sender, target := target, code := toExecute .EVM c.checkpoint target,
    gas := c.entryGas, price := c.effectivePrice, value := c.transaction.base.value,
    apparent := c.transaction.base.value, data := c.transaction.base.data,
    depth := 0, header := c.header, permission := true }

def request (c : Context) : Request :=
  match c.transaction.base.recipient with
  | none => .lambda c.fuel (creation c)
  | some target => .theta c.fuel (message c target)

theorem request_gas (c : Context) : (request c).gas = c.entryGas.toNat := by
  unfold request
  split <;> rfl

theorem provisional_residual (c : Context) {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool}
    (h : c.provisional = .ok (world,gas,substate,success)) :
    (request c).residual (request c).eval = gas.toNat := by
  unfold request Context.provisional at *
  split at h
  · rename_i hr
    rw [hr]
    split at h
    · rename_i he
      change RecursiveEventDebit.lambdaResidual
        (Lambda c.fuel c.transaction.blobVersionedHashes .empty c.genesis c.blocks
          c.checkpoint c.checkpoint c.entrySubstate c.sender c.sender c.entryGas c.effectivePrice
          c.transaction.base.value c.transaction.base.data ⟨0⟩ none c.header true) = _
      rw [he]
      cases h
      rfl
    · cases h
  · rename_i target hr
    rw [hr]
    split at h
    · rename_i he
      change RecursiveEventDebit.thetaResidual
        (Θ c.fuel c.transaction.blobVersionedHashes .empty c.genesis c.blocks
          c.checkpoint c.checkpoint c.entrySubstate c.sender c.sender target
          (toExecute .EVM c.checkpoint target) c.entryGas c.effectivePrice
          c.transaction.base.value c.transaction.base.value c.transaction.base.data 0 c.header true) = _
      rw [he]
      cases h
      rfl
    · cases h

/-- Every actual completed transaction, including status false, has a unique
selected execution tree whose marked event count is bounded by its reported
net gas after the actual capped refund. No aggregate charge is assumed. -/
theorem transaction_events (c : Context) {world : AccountMap .EVM}
    {substate : Substate} {success : Bool} {used : UInt256}
    (hr : c.result = .ok (world,substate,success,used)) :
    ∃ tree, Cert (request c) (request c).eval tree ∧ tree.occurrences.Nodup ∧
      tree.count ≤ used.toNat ∧
      ∀ other, Cert (request c) (request c).eval other → other = tree := by
  obtain ⟨pw,rem,hp,_⟩ := result_inversion c world substate success used hr
  obtain ⟨tree,hc,hn,hb,hu⟩ := extracted_bound (request c)
  have he := provisional_residual c hp
  have hg := request_gas c
  have hl := entryGas_le_limit c
  have hcharge : 919*tree.count ≤ c.transaction.base.gasLimit.toNat-rem.toNat := by omega
  have hused := TransactionGas.count_le_used c tree.count pw world rem used
    substate substate success success hp hr hcharge
  exact ⟨tree,hc,hn,hused,hu⟩

#print axioms request_gas
#print axioms provisional_residual
#print axioms transaction_events
end Eip8282.Audit.Integrator.TransactionEventBounds
