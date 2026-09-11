import Eip8282.Audit.Integrator.ProtocolCreditEnvelope

/-! Literal PoW reward batches at proposed EL reference
0cc100eb190b64b23baba72dac0165652eaec252. Archived full bodies/hashes:
audit/receipts/direct-reference-migration-deployment-sources-20260910.json.
Frontier fork.py:58,516,545-547,581-589; Byzantium/Constantinople:62,597-604.
OPEN adapters: selected fork era, canonical miner and ommer beneficiaries,
validated cardinality/ages, checked recipient addition and EL world transport.
No aggregate reward bound or canonical occurrence is assumed. -/
namespace Eip8282.Audit.Integrator.ProtocolPowRewards
open EvmYul EvmYul.EVM
open ProtocolCreditEnvelope
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

inductive Era where | frontier | byzantium | constantinople

def base : Era → Nat
  | .frontier => 5000000000000000000
  | .byzantium => 3000000000000000000
  | .constantinople => 2000000000000000000

structure Ommer where
  beneficiary : AccountAddress
  age : Nat

structure Admission (ommers : List Ommer) : Prop where
  cardinality : ommers.length ≤ 2
  ages : ∀ o ∈ ommers, 1 ≤ o.age ∧ o.age ≤ 6

def minerReward (era : Era) (ommers : List Ommer) : Nat :=
  base era + ommers.length*(base era/32)

def ommerReward (era : Era) (o : Ommer) : Nat := ((8-o.age)*base era)/8

def payments (era : Era) (miner : AccountAddress) (ommers : List Ommer) : List (AccountAddress × Nat) :=
  (miner,minerReward era ommers)::ommers.map (fun o => (o.beneficiary,ommerReward era o))

private theorem ommer_bound (era : Era) (o : Ommer) (age : 1 ≤ o.age) :
    ommerReward era o ≤ 7*base era/8 := by
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul_right _ (by omega)

private theorem ommer_sum (era : Era) (ommers : List Ommer)
    (ages : ∀ o ∈ ommers, 1 ≤ o.age) :
    (ommers.map (ommerReward era)).sum ≤ ommers.length*(7*base era/8) := by
  induction ommers with
  | nil => simp
  | cons o rest ih =>
    have ho := ommer_bound era o (ages o (by simp))
    have hr := ih (fun a ha => ages a (by simp [ha]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem reward_bound (era : Era) (miner : AccountAddress) (ommers : List Ommer)
    (admitted : Admission ommers) :
    ((payments era miner ommers).map Prod.snd).sum ≤ powMaximum := by
  have hs := ommer_sum era ommers (fun o ho => (admitted.ages o ho).1)
  have hn := admitted.cardinality
  have hminer := Nat.mul_le_mul_right (base era/32) hn
  have hommer := Nat.mul_le_mul_right (7*base era/8) hn
  simp only [payments,List.map_cons,List.map_map,List.sum_cons,Function.comp_def]
  change minerReward era ommers + (ommers.map (ommerReward era)).sum ≤ powMaximum
  unfold minerReward
  have hb : base era + 2*(base era/32) + 2*(7*base era/8) ≤ powMaximum := by
    cases era <;> decide +kernel
  omega

/-- Execute every listed payment in order; collisions do not drop payments. -/
def pay : List (AccountAddress × Nat) → AccountMap .EVM → AccountMap .EVM
  | [], world => world
  | (recipient,amount)::rest, world =>
    pay rest (world.increaseBalance .EVM recipient (UInt256.ofNat amount))

private theorem pay_batch (items : List (AccountAddress × Nat)) (world : AccountMap .EVM)
    (fit : ∀ item ∈ items, item.2 < UInt256.size) :
    CreditBatch world (items.map Prod.snd).sum (pay items world) := by
  induction items generalizing world with
  | nil => exact .nil world
  | cons item rest ih =>
    obtain ⟨recipient,amount⟩ := item
    have hfit := fit (recipient,amount) (by simp)
    have he : (UInt256.ofNat amount).toNat = amount := Nat.mod_eq_of_lt hfit
    have batch := CreditBatch.cons (before := world) recipient (UInt256.ofNat amount)
      (ih _ (fun x hx => fit x (by simp [hx])))
    simpa only [pay,List.map_cons,List.sum_cons,he] using batch

theorem batch (era : Era) (miner : AccountAddress) (ommers : List Ommer)
    (admitted : Admission ommers) (world : AccountMap .EVM) :
    CreditBatch world ((payments era miner ommers).map Prod.snd).sum
      (pay (payments era miner ommers) world) := by
  apply pay_batch
  intro item hi
  have hm : item.2 ∈ (payments era miner ommers).map Prod.snd := List.mem_map.mpr ⟨item,hi,rfl⟩
  have hb := reward_bound era miner ommers admitted
  have hs := List.le_sum_of_mem hm
  have hf : powMaximum < UInt256.size := by decide +kernel
  omega

theorem ledger {initial world : AccountMap .EVM} {p w s c : Nat}
    (prior : Ledger initial p w s c world) (era : Era) (miner : AccountAddress)
    (ommers : List Ommer) (admitted : Admission ommers) :
    Ledger initial (p+1) w s (c+((payments era miner ommers).map Prod.snd).sum)
      (pay (payments era miner ommers) world) :=
  Ledger.pow prior (batch era miner ommers admitted world) (reward_bound era miner ommers admitted)

#print axioms reward_bound
#print axioms batch
#print axioms ledger
end Eip8282.Audit.Integrator.ProtocolPowRewards
