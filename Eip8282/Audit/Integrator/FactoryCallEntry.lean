import Eip8282.Audit.Integrator.FactoryRuntimeEntry
import Eip8282.Audit.Integrator.TransferFunding

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
