import Eip8282.Audit.Integrator.FactoryRuntimeEntry
import Eip8282.Audit.Integrator.PrefundedInitialization

/-! Resources and address-preimage binding for the actual selected factory child.
No child-success premise or canonical-address hash equation is used. -/
namespace Eip8282.Audit.Integrator.FactoryChildResources
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open NestedEvents FactoryRuntimeEntry
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

/-- The actual word conversion is exact because EIP-150 forwards at most the
already charged word gas. No extra no-wrap premise is required. -/
theorem child_gas_exact (kind : Kind) (a : XiArgs) (gas : UInt256) (e : Nat)
    (hg : createCost kind ≤ gas.toNat) :
    (childArgs kind a gas e).gas.toNat = L (gas.toNat-createCost kind) := by
  change (UInt256.ofNat (CreationGas.allowance (createCost kind) (atCreate kind a gas e))).toNat = _
  rw [(CreationGas.forwarded_fit _ _).2]
  unfold CreationGas.allowance
  have hs : (stepPre (createCost kind) (atCreate kind a gas e)).gasAvailable.toNat =
      gas.toNat-createCost kind := toNat_sub_ofNat hg
  rw [hs]

theorem child_gas_sufficient (kind : Kind) (a : XiArgs) (gas : UInt256) (e : Nat)
    (hentry : 1000000 ≤ a.gas.toNat) (hprefix : a.gas.toNat-157 ≤ gas.toNat) :
    InitializerProgress.creationGas kind ≤ (childArgs kind a gas e).gas.toNat := by
  have hc : createCost kind ≤ 32160 := by cases kind <;> decide
  rw [child_gas_exact kind a gas e (by omega)]
  have hb : InitializerProgress.creationGas kind ≤ 126600 := by cases kind <;> decide
  unfold L
  omega

theorem child_permission (kind : Kind) (a : XiArgs) (gas : UInt256) (e : Nat) :
    (childArgs kind a gas e).permission = a.env.perm := rfl

/-- CREATE2 inserts the actual incremented creator account before Lambda. -/
theorem child_has_sender (kind : Kind) (a : XiArgs) (gas : UInt256) (e : Nat) :
    ∃ acc, (childArgs kind a gas e).world.get? (childArgs kind a gas e).source = some acc := by
  exact ⟨_,Std.TreeMap.getElem?_insert_self⟩

/-- The symbolic preimage includes the complete salt and actual opaque init hash.
No assertion about the output hash width or the resulting address is made. -/
def preimage (kind : Kind) : ByteArray :=
  BE 255 ++ factoryAddress.toByteArray ++ saltData kind ++ ffi.KEC (Initialization.initCode kind)

theorem child_preimage (kind : Kind) (a : XiArgs) (gas : UInt256) (e fuel : Nat)
    (ha : a.env.codeOwner = factoryAddress) :
    ((childArgs kind a gas e).context fuel).preimage = some (preimage kind) := by
  change Lambda.L_A (childArgs kind a gas e).source _ (childArgs kind a gas e).salt
    (childArgs kind a gas e).init = _
  rw [child_source kind a gas e ha,child_salt,child_init]
  rfl

/-- All initializer entry resources follow from the actual prefix and child
construction; collision freedom remains an explicit address-state condition. -/
theorem child_domain (kind : Kind) (a : XiArgs) (gas : UInt256) (e steps : Nat)
    (hentry : 1000000 ≤ a.gas.toNat) (hprefix : a.gas.toNat-157 ≤ gas.toNat)
    (hp : a.env.perm = true) (hf : 11 ≤ steps)
    (bytes : ByteArray)
    (hpre : ((childArgs kind a gas e).context (steps+1)).preimage = some bytes)
    (hcollision : ((childArgs kind a gas e).context (steps+1)).collision
      (CreationSettlement.address bytes) = false) :
    PrefundedInitialization.Domain kind ((childArgs kind a gas e).context (steps+1)) bytes steps ∧
      InitializerProgress.creationGas kind ≤ (childArgs kind a gas e).gas.toNat := by
  have hg := child_gas_sufficient kind a gas e hentry hprefix
  refine ⟨⟨hpre,rfl,hcollision,?_⟩,hg⟩
  cases kind with
  | deposit =>
    change 1000 ≤ (childArgs .deposit a gas e).gas.toNat ∧ 8 ≤ steps
    change 126600 ≤ (childArgs .deposit a gas e).gas.toNat at hg
    exact ⟨by omega,by omega⟩
  | exit =>
    change (childArgs .exit a gas e).permission = true ∧
      25000 ≤ (childArgs .exit a gas e).gas.toNat ∧ 11 ≤ steps ∧ _
    change 116600 ≤ (childArgs .exit a gas e).gas.toNat at hg
    exact ⟨hp,by omega,hf,child_has_sender .exit a gas e⟩

/-- Resource-bearing form of the actual prefix selector. Collision is checked
in the actual nonce-incremented child world, independent of gas and PC counters. -/
theorem entry_resources (kind : Kind) (a : XiArgs) (steps : Nat)
    (hcode : a.env.code = FactoryRuntimeEntry.runtime)
    (hdata : a.env.calldata = calldata kind) (ha : a.env.codeOwner = factoryAddress)
    (hp : a.env.perm = true) (hgas : 1000000 ≤ a.gas.toNat) (hf : 11 ≤ steps)
    (hn : (a.world.get? a.env.codeOwner |>.getD default).nonce.toNat < 2^64-1)
    (hv : a.env.weiValue ≤ (a.world.get? a.env.codeOwner |>.option ⟨0⟩ (·.balance)))
    (hd : a.env.depth < 1024)
    (hcollision : ((childArgs kind a a.gas 0).context (steps+1)).collision
      (CreationSettlement.address (preimage kind)) = false) :
    ∃ (gas : UInt256) (e : Nat), ∃ hg : createCost kind ≤ gas.toNat,
      Reaches a.jumps 13 a.entry (atCreate kind a gas e) ∧
      StepChild (steps+3) (createStep kind a gas e hp hg)
        (some (.lambda (steps+2) (childArgs kind a gas e))) ∧
      (Request.lambda (steps+2) (childArgs kind a gas e)).eval =
        ((childArgs kind a gas e).context (steps+1)).result ∧
      PrefundedInitialization.Domain kind ((childArgs kind a gas e).context (steps+1))
        (preimage kind) steps ∧
      InitializerProgress.creationGas kind ≤ (childArgs kind a gas e).gas.toNat := by
  obtain ⟨gas,e,hg,hlo,hr,hsel,_,_,_,_⟩ :=
    entry_selects kind a (steps+2) hcode hdata ha hp (by omega) hn hv hd
  have hcol : ((childArgs kind a gas e).context (steps+1)).collision
      (CreationSettlement.address (preimage kind)) = false := hcollision
  obtain ⟨hdom,hresources⟩ := child_domain kind a gas e steps hgas hlo hp hf
    (preimage kind) (child_preimage kind a gas e (steps+1) ha) hcol
  exact ⟨gas,e,hg,hr,hsel,lambdaArgs_result _ (steps+1),hdom,hresources⟩

#print axioms entry_resources

#print axioms child_gas_exact
#print axioms child_gas_sufficient
#print axioms child_preimage
#print axioms child_domain
end Eip8282.Audit.Integrator.FactoryChildResources
