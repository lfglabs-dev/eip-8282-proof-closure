import Eip8282.Audit.Integrator.OrdinaryWorldFrame
import Eip8282.Audit.Integrator.TransferFrame

/-!
# Protected code and persistent-storage projection

Balances, nonce and transient storage may change. A previously existing
protected account must survive with the same code, and every persistent slot
read is retained. The producers below are actual ordinary steps and the exact
message-call entry transfer; no abstract transition equivalence is assumed.
-/
namespace Eip8282.Audit.Integrator.CodeStorageFrame
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open SystemSpec
set_option autoImplicit false

structure Frame (before after : AccountMap .EVM) (address : AccountAddress) : Prop where
  existing : ∀ old, before.get? address = some old →
    ∃ current, after.get? address = some current ∧ current.code = old.code
  storage : ∀ slot, worldSlot after address slot = worldSlot before address slot

theorem refl (world : AccountMap .EVM) (address : AccountAddress) : Frame world world address :=
  ⟨fun old h => ⟨old,h,rfl⟩,fun _ => rfl⟩

theorem trans {before middle after : AccountMap .EVM} {address : AccountAddress}
    (first : Frame before middle address) (second : Frame middle after address) :
    Frame before after address := by
  constructor
  · intro old ho
    obtain ⟨mid,hm,hmc⟩ := first.existing old ho
    obtain ⟨current,hc,hcc⟩ := second.existing mid hm
    exact ⟨current,hc,hcc.trans hmc⟩
  · intro slot
    exact (second.storage slot).trans (first.storage slot)

private theorem observed_storage (world : AccountMap .EVM) (address : AccountAddress) (slot : UInt256) :
    (OrdinaryWorldFrame.observed world address).lookupStorage slot = worldSlot world address slot := by
  unfold OrdinaryWorldFrame.observed OrdinaryWorldFrame.shape worldSlot
  cases world.get? address <;> rfl

/-- Project the stronger ordinary-account shape proof to the persistent view. -/
theorem of_preserved {before after : AccountMap .EVM} {address : AccountAddress}
    (h : OrdinaryWorldFrame.Preserved before after address) : Frame before after address := by
  constructor
  · intro old ho
    obtain ⟨current,hc,hcode,_⟩ := OrdinaryWorldFrame.existing_code_storage h ho
    exact ⟨current,hc,hcode⟩
  · intro slot
    have hs := congrArg (fun account : Account .EVM => account.lookupStorage slot) h.1
    simpa only [observed_storage] using hs

/-- Actual accepted ordinary execution at another owner supplies this frame. -/
theorem ordinary {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {pre mid post : EVM.State} {vj : Array UInt256} {cost fuel : Nat}
    {address : AccountAddress} (hop : OrdinaryGas.Ordinary op)
    (hne : pre.executionEnv.codeOwner ≠ address)
    (hz : Z vj op pre = .ok (mid,cost))
    (hs : StepOk fuel cost (op,arg) mid post) :
    Frame pre.accountMap post.accountMap address :=
  of_preserved (OrdinaryWorldFrame.accepted_step_preserved hop hne hz hs).1

/-- Exact Θ transfer entry, including caller/recipient aliasing. -/
theorem entry (c : MessageCall.Context) (address : AccountAddress) :
    Frame c.world c.entryWorld address := by
  constructor
  · intro old ho
    obtain ⟨current,hc,hcode,_⟩ := TransferFrame.entry_existing_account c ho
    exact ⟨current,hc,hcode⟩
  · exact TransferFrame.entry_storage c address

#print axioms trans
#print axioms of_preserved
#print axioms ordinary
#print axioms entry
end Eip8282.Audit.Integrator.CodeStorageFrame
