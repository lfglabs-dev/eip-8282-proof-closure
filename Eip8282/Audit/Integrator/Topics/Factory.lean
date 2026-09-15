import Eip8282.Audit.Integrator.FactoryRuntimeEntry
import Eip8282.Audit.Integrator.FactoryRuntimeReturn
import Eip8282.Audit.Integrator.PrefundedInitialization
import Eip8282.Audit.Integrator.ReturnedGas
import Eip8282.Audit.Integrator.TransferFunding

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## FactoryCallEntry -/

/-! Literal Theta entry transfer and factory Xi argument binding. The distinct
caller/recipient premise is explicit. Credit arithmetic follows the finite
world-funds bound, not a supplied no-wrap or post-transfer balance assumption. -/
namespace Eip8282.Audit.Integrator.FactoryCallEntry
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Model (Kind)
open NestedEvents FactoryRuntimeEntry TransferFunding
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

def args (c : MessageCall.Context) : XiArgs :=
  { created := c.created, genesis := c.genesis, blocks := c.blocks,
    world := c.entryWorld, original := c.originalWorld, gas := c.gas,
    substate := c.substate, env := c.environment }

theorem execution_eq (c : MessageCall.Context) :
    (Request.xi c.fuel (args c)).eval = c.execution := rfl

theorem installed_toExecute (world : AccountMap .EVM) (old : Account .EVM)
    (ha : world.get? factoryAddress = some old) (hc : old.code = FactoryRuntimeEntry.runtime) :
    toExecute .EVM world factoryAddress = .Code FactoryRuntimeEntry.runtime := by
  have hn : factoryAddress ∉ π := by decide +kernel
  simp only [toExecute,hn,↓reduceIte,ha,hc]
  rfl

private theorem lookup_insert (world : AccountMap .EVM) (key addr : AccountAddress)
    (account : Account .EVM) :
    (world.insert key account).get? addr = if key = addr then some account else world.get? addr := by
  exact (Std.TreeMap.getElem?_insert (t := world) (k := key) (a := addr) (v := account)).trans
    (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)

theorem pair_balance_le (world : AccountMap .EVM) (sender target : AccountAddress)
    (hne : sender ≠ target) :
    worldBalance world sender + worldBalance world target ≤ worldFunds world := by
  let zero : Account .EVM := { (world.get? sender).getD default with balance := ⟨0⟩ }
  have hi := funds_insert world sender zero
  have hb := balance_le_funds (world.insert sender zero) target
  have ht : worldBalance (world.insert sender zero) target = worldBalance world target := by
    unfold worldBalance
    rw [lookup_insert,if_neg hne]
  rw [ht] at hb
  change worldFunds (world.insert sender zero)+worldBalance world sender = worldFunds world+0 at hi
  omega

theorem entry_target_account (c : MessageCall.Context) (old : Account .EVM)
    (ha : c.world.get? c.target = some old) (hne : c.caller ≠ c.target) :
    c.entryWorld.get? c.target = some {old with balance := old.balance+c.value} := by
  unfold MessageCall.Context.entryWorld
  rw [ha]
  simp only
  cases hs : (c.world.insert c.target {old with balance := old.balance+c.value}).get? c.caller with
  | none => exact Std.TreeMap.getElem?_insert_self
  | some sender =>
    rw [lookup_insert,if_neg hne]
    exact Std.TreeMap.getElem?_insert_self

theorem entry_target_funded (c : MessageCall.Context) (old : Account .EVM)
    (ha : c.world.get? c.target = some old) (hne : c.caller ≠ c.target)
    (hfunded : c.value.toNat ≤ worldBalance c.world c.caller)
    (hworld : worldFunds c.world < UInt256.size) :
    c.value.toNat ≤ worldBalance c.entryWorld c.target := by
  have hb := pair_balance_le c.world c.caller c.target hne
  have ht : worldBalance c.world c.target = old.balance.toNat := by
    unfold worldBalance
    rw [ha]
    rfl
  rw [ht] at hb
  have hfit : old.balance.toNat+c.value.toNat < UInt256.size := by omega
  unfold worldBalance
  rw [entry_target_account c old ha hne]
  simp only [Option.map_some,Option.getD_some]
  rw [toNat_add_of_lt _ _ hfit]
  omega

/-- The actual message-call entry supplies all factory prefix and CREATE2
admission inputs except gas and collision, which remain separate consumers. -/
theorem entry_gates (kind : Kind) (c : MessageCall.Context) (old : Account .EVM)
    (ht : c.target = factoryAddress) (hcode : c.code = FactoryRuntimeEntry.runtime)
    (ha : c.world.get? c.target = some old) (installed : old.code = FactoryRuntimeEntry.runtime)
    (hn : old.nonce.toNat < 2^64-1) (hne : c.caller ≠ c.target)
    (hfunded : c.value.toNat ≤ worldBalance c.world c.caller)
    (hworld : worldFunds c.world < UInt256.size)
    (hv : c.apparentValue = c.value) (hp : c.permission = true)
    (hd : c.depth < 1024) (hdata : c.calldata = calldata kind) :
    (args c).env.code = FactoryRuntimeEntry.runtime ∧ (args c).env.codeOwner = factoryAddress ∧
    (args c).env.calldata = calldata kind ∧ (args c).env.perm = true ∧
    (args c).env.depth < 1024 ∧
    ((args c).world.get? (args c).env.codeOwner |>.getD default).nonce.toNat < 2^64-1 ∧
    (args c).env.weiValue ≤ ((args c).world.get? (args c).env.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
    ∃ current, (args c).world.get? factoryAddress = some current ∧ current.code = FactoryRuntimeEntry.runtime := by
  have he := entry_target_account c old ha hne
  have hb := entry_target_funded c old ha hne hfunded hworld
  refine ⟨hcode,ht,hdata,hp,hd,?_,?_,?_⟩
  · change ((c.entryWorld.get? c.target).getD default).nonce.toNat < _
    rw [he]
    exact hn
  · change c.apparentValue ≤ (c.entryWorld.get? c.target |>.option ⟨0⟩ (·.balance))
    rw [hv]
    unfold worldBalance at hb
    rw [he] at hb ⊢
    exact hb
  · refine ⟨{old with balance := old.balance+c.value},?_,installed⟩
    change c.entryWorld.get? factoryAddress = _
    rw [← ht]
    exact he

#print axioms installed_toExecute
#print axioms execution_eq
#print axioms pair_balance_le
#print axioms entry_target_account
#print axioms entry_target_funded
#print axioms entry_gates
end Eip8282.Audit.Integrator.FactoryCallEntry

end

section

/-! ## FactoryChildResources -/

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

end

section

/-! ## FactoryPrefixGas -/

/-! Gas upper bounds for the same actual prefix witness used by initialization.
The generic bound follows actual accepted steps, including recursive outcomes,
and does not require a predicted instruction trace or a no-wrap premise. -/
namespace Eip8282.Audit.Integrator.FactoryPrefixGas
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.SymExec
open NestedEvents FactoryRuntimeEntry FactoryChildResources
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem step_gas_nonincrease {vj : Array UInt256} {fuel cost : Nat}
    {pre post : EVM.State} (h : XStepAt vj fuel cost pre post) :
    post.gasAvailable.toNat ≤ pre.gasAvailable.toNat := by
  obtain ⟨mid,hz,hs,_⟩ := h
  exact ReturnedGas.step_remaining fuel hz hs

theorem runs_gas_nonincrease {vj : Array UInt256} {fuel rem : Nat}
    {pre post : EVM.State} {trace : List Labelled}
    (h : XRuns vj fuel pre trace rem post) :
    post.gasAvailable.toNat ≤ pre.gasAvailable.toNat := by
  induction h with
  | refl => exact Nat.le_refl _
  | cons hs _ ih => exact ih.trans (step_gas_nonincrease hs)

theorem reaches_gas_nonincrease {vj : Array UInt256} {k : Nat}
    {pre post : EVM.State} (h : Reaches vj k pre post) :
    post.gasAvailable.toNat ≤ pre.gasAvailable.toNat := by
  obtain ⟨trace,hr⟩ := h 0
  exact runs_gas_nonincrease hr

/-- This applies to the supplied witness, including the witness retained by
FactoryChildResources.entry_resources. -/
theorem atCreate_gas_le {kind : Kind} {a : XiArgs} {gas : UInt256} {e : Nat}
    (h : Reaches a.jumps 13 a.entry (atCreate kind a gas e)) : gas.toNat ≤ a.gas.toNat :=
  reaches_gas_nonincrease h

/-- Both gas bounds describe the same concrete post-prefix state. -/
theorem prefix_bounds (kind : Kind) (a : XiArgs)
    (hcode : a.env.code = FactoryRuntimeEntry.runtime)
    (hdata : a.env.calldata = calldata kind) (hgas : 200 ≤ a.gas.toNat) :
    ∃ gas e, a.gas.toNat-157 ≤ gas.toNat ∧ gas.toNat ≤ a.gas.toNat ∧
      Reaches a.jumps 13 a.entry (atCreate kind a gas e) := by
  obtain ⟨gas,e,hlo,hr⟩ := reaches_create2 kind a hcode hdata hgas
  exact ⟨gas,e,hlo,atCreate_gas_le hr,hr⟩

#print axioms step_gas_nonincrease
#print axioms runs_gas_nonincrease
#print axioms reaches_gas_nonincrease
#print axioms atCreate_gas_le
#print axioms prefix_bounds
end Eip8282.Audit.Integrator.FactoryPrefixGas

end

section

/-! ## FactoryReturnEncoding -/

/-! Exact bytes returned by the factory's MSTORE/RETURN tail. These are generic
word/address encodings, with no hash, creation-success or deployment premise. -/
namespace Eip8282.Audit.Integrator.FactoryReturnEncoding
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.EntryReach
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem output_word (kind : Kind) (word : UInt256) :
    FactoryRuntimeReturn.output kind word = word.toByteArray.extract 12 32 := by
  have hfit : 0 + 32 ≤ (Initialization.initCode kind).size := by cases kind <;> decide
  unfold FactoryRuntimeReturn.output FactoryRuntimeReturn.returnedMemory mstoreMem
  change (ByteArray.write word.toByteArray 0 (Initialization.initCode kind) 0 32).readWithPadding 12 20 = _
  rw [ByteArray.readWithPadding_eq_extract _ 12 20 (by decide) (by decide)
    (by rw [ByteArray.size_write_of_fits _ _ _ _ (by decide) (UInt256.size_toByteArray word) hfit]; omega)]
  rw [ByteArray.write_eq_of_fits _ _ _ _ (by decide) (UInt256.size_toByteArray word) hfit]
  apply ByteArray.ext
  simp only [ByteArray.data_extract, Array.extract_zero, Array.empty_append]
  simpa using Array.extract_append_of_le word.toByteArray.data #[]
    ((Initialization.initCode kind).data.extract 32 (Initialization.initCode kind).size) 12 32
    (by rw [ByteArray.size_data, UInt256.size_toByteArray])

theorem address_bytes (address : AccountAddress) :
    address.toByteArray.data.toList = toBeBytesFixed address.val 20 := by
  have hb : (BE address.val).data.toList = toBytesBigEndian address.val := List.toList_data_toByteArray
  have hs : (BE address.val).size = (toBytesBigEndian address.val).length := List.size_toByteArray
  have hlen := congrArg List.length (toBeBytesFixed_eq_zeroPad address.val 20 address.isLt)
  have hl : (BE address.val).size ≤ 20 := by
    simp only [length_toBeBytesFixed, List.length_append, List.length_replicate] at hlen
    rw [hs]
    omega
  have hw : 20 < 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  have hn : (BE address.val).size < 2 ^ System.Platform.numBits := by omega
  have h20 : (20 : BitVec System.Platform.numBits).toNat = 20 := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
  have hz : ∀ u : USize, (ffi.ByteArray.zeroes u).data.toList = List.replicate u.toNat 0 := by
    intro u; simp [ffi.ByteArray.zeroes]
  rw [toBeBytesFixed_eq_zeroPad address.val 20 address.isLt]
  unfold AccountAddress.toByteArray
  rw [ByteArray.toList_data_append, hz, hb]
  simp only [USize.toNat, BitVec.toNat_sub, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, h20]
  rw [show 2 ^ System.Platform.numBits - (BE address.val).size + 20 =
    2 ^ System.Platform.numBits + (20 - (BE address.val).size) by omega]
  rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt (by omega : 20 - (BE address.val).size < 2 ^ System.Platform.numBits), hs]

theorem address_word_bytes (address : AccountAddress) :
    (UInt256.ofNat address.val).toByteArray.extract 12 32 = address.toByteArray := by
  have hf : address.val < UInt256.size := by
    have := address.isLt
    unfold AccountAddress.size UInt256.size at *
    omega
  have hn : (UInt256.ofNat address.val).toNat = address.val := Nat.mod_eq_of_lt hf
  apply ByteArray.ext
  apply Array.ext'
  simp only [ByteArray.data_extract, Array.toList_extract, UInt256.toList_data_toByteArray,
    hn, address_bytes, List.extract_eq_take_drop]
  apply List.ext_getElem
  · simp
  · intro i hi _
    have hi20 : i < 20 := by simpa using hi
    rw [List.getElem_take, List.getElem_drop, getElem_toBeBytesFixed, getElem_toBeBytesFixed]
    rw [show 32 - 1 - (12 + i) = 20 - 1 - i by omega]

theorem output_address (kind : Kind) (address : AccountAddress) :
    FactoryRuntimeReturn.output kind (UInt256.ofNat address.val) = address.toByteArray := by
  rw [output_word, address_word_bytes]

theorem output_size (kind : Kind) (word : UInt256) :
    (FactoryRuntimeReturn.output kind word).size = 20 := by
  rw [output_word]
  simp [UInt256.size_toByteArray]

#print axioms output_word
#print axioms address_word_bytes
#print axioms output_address
#print axioms output_size
end Eip8282.Audit.Integrator.FactoryReturnEncoding

end
