import Eip8282.Audit.Integrator.InitializerProgress

/-! Actual successful initialization at a collision-free address, including an
existing account with a prefunded balance. Empty persistent storage is derived
from the evaluator's collision test; absence and zero-slot hypotheses are not
required. Resources remain conservative explicit evaluator inputs. -/
namespace Eip8282.Audit.Integrator.PrefundedInitialization
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.EntryReach (INH)
open Eip8282.Audit.Correspondence (runtimeCode)
open CreationSettlement (Context address)
open Initialization InitializerProgress SystemSpec
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private local instance : LawfulBEq UInt256 where
  eq_of_beq := by
    intro a b h
    cases a with | mk a =>
    cases b with | mk b =>
    exact congrArg UInt256.mk (beq_iff_eq.mp h)
  rfl := by
    intro a
    cases a with
    | mk v =>
      change (v == v) = true
      exact beq_self_eq_true v

structure Domain (kind : Kind) (c : Context) (preimage : ByteArray) (steps : Nat) : Prop where
  preimage_eq : c.preimage = some preimage
  fuel_eq : c.fuel = steps+1
  no_collision : c.collision (address preimage) = false
  resources : match kind with
    | .deposit => 1000 ≤ c.gas.toNat ∧ 8 ≤ steps
    | .exit => c.permission = true ∧ 25000 ≤ c.gas.toNat ∧ 11 ≤ steps ∧
        ∃ acc, c.world.get? c.sender = some acc

/-- The storage BEq test establishes extensional map equivalence, not an
assumed structural equality of balanced trees. -/
theorem collision_fields (c : Context) (a : AccountAddress)
    (hc : c.collision a = false) :
    (c.existing a).nonce = ⟨0⟩ ∧ (c.existing a).code = .empty ∧
      Std.TreeMap.Equiv (c.existing a).storage (default : Storage) := by
  have hh : (c.existing a).nonce = ⟨0⟩ ∧ (c.existing a).code.size = 0 ∧
      (!(c.existing a).storage == (default : Storage)) = false := by
    simpa only [Context.collision, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      not_not, bne, and_assoc] using hc
  have hb : ((c.existing a).storage == (default : Storage)) = true := by
    cases he : ((c.existing a).storage == (default : Storage)) <;> simp_all
  exact ⟨hh.1, ByteArray.size_eq_zero_iff.mp hh.2.1, Std.TreeMap.equiv_of_beq hb⟩

theorem zero_of_no_collision (c : Context) (a : AccountAddress)
    (hc : c.collision a = false) (slot : UInt256) : worldSlot c.world a slot = ⟨0⟩ := by
  have hs := (collision_fields c a hc).2.2
  have hz : (c.existing a).lookupStorage slot = ⟨0⟩ := hs.getD_eq
  unfold Context.existing at hz
  rw [Std.TreeMap.getD_eq_getD_getElem?] at hz
  unfold worldSlot
  cases ha : c.world.get? a with
  | none => rfl
  | some old =>
    change ((c.world.get? a).getD default).lookupStorage slot = ⟨0⟩ at hz
    rw [ha] at hz
    exact hz

theorem observed_of_success (kind : Kind) (c : Context) (preimage : ByteArray) (steps : Nat)
    (hi : c.init = initCode kind) (hd : Domain kind c preimage steps)
    {a : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {world : AccountMap .EVM} {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hr : c.result = .ok (a,created,world,gas,substate,true,out)) :
    DirectInitialization.Observed kind c preimage a world substate := by
  cases kind with
  | deposit =>
    obtain ⟨ha,hcode,hstorage,hlogs⟩ := CreationSettlement.deposit_creation c hd.preimage_eq
      steps hd.fuel_eq hd.no_collision hi hd.resources.1 hd.resources.2 hr
    have hz (slot : UInt256) : worldSlot world a slot = ⟨0⟩ := by
      rw [hstorage,ha]
      exact zero_of_no_collision c _ hd.no_collision slot
    obtain ⟨hb,he,hq⟩ := InitializedInvariant.initial_invariant .deposit 8
      (worldSlot world a) (hz _) (hz _) (hz _) (Or.inl (hz _))
    exact ⟨ha,hcode,hz _,hb,he,hq,hlogs⟩
  | exit =>
    obtain ⟨ha,hcode,hstorage,hlogs⟩ := CreationSettlement.exit_creation c hd.preimage_eq
      steps hd.fuel_eq hd.no_collision hi hd.resources.1 hd.resources.2.1
      hd.resources.2.2.1 hd.resources.2.2.2 hr
    have hz (slot : UInt256) (hn : slot ≠ ⟨0⟩) : worldSlot world a slot = ⟨0⟩ := by
      rw [hstorage,if_neg hn,ha]
      exact zero_of_no_collision c _ hd.no_collision slot
    have hin : worldSlot world a (UInt256.ofNat 0) = INH := by
      rw [hstorage,if_pos (by decide : UInt256.ofNat 0 = (⟨0⟩ : UInt256))]
    obtain ⟨hb,he,hq⟩ := InitializedInvariant.initial_invariant .exit 2
      (worldSlot world a) (hz _ (by decide)) (hz _ (by decide)) (hz _ (by decide)) (Or.inr hin)
    exact ⟨ha,hcode,hin,hb,he,hq,hlogs⟩

/-- Collision-free nonce/code plus the actual returned gas pass code deposit,
including when the account already holds an arbitrary balance. -/
theorem deposit_guards (kind : Kind) (c : Context) (a : AccountAddress) (gas : UInt256)
    (hc : c.collision a = false) (hg : 200 * runtimeLen kind ≤ gas.toNat) :
    c.depositFailure a gas (runtime kind) = false := by
  obtain ⟨hn,hcode,_⟩ := collision_fields c a hc
  have hsize : (runtime kind).size = runtimeLen kind := by cases kind <;> decide +kernel
  have hf : ¬ gas.toNat < GasConstants.Gcodedeposit * runtimeLen kind := by
    change ¬ gas.toNat < 200 * runtimeLen kind
    omega
  have hs : ¬ runtimeLen kind > 24576 := by cases kind <;> decide
  have hp : (runtime kind)[0]? ≠ some 0xef := by cases kind <;> decide +kernel
  unfold Context.depositFailure
  cases ha : c.world.get? a with
  | none => simp [hsize,hf,hs,hp]
  | some acc =>
    unfold Context.existing at hn hcode
    rw [Std.TreeMap.getD_eq_getD_getElem?] at hn hcode
    change ((c.world.get? a).getD default).nonce = ⟨0⟩ at hn
    change ((c.world.get? a).getD default).code = .empty at hcode
    rw [ha] at hn hcode
    change acc.nonce = ⟨0⟩ at hn
    change acc.code = .empty at hcode
    simp [hn,hcode,hsize,hf,hs,hp]

/-- Actual Lambda success and initial invariants, permitting prefunded targets. -/
theorem initializes_success (kind : Kind)
    (c : CreationSettlement.Context) (preimage : ByteArray) (steps : Nat)
    (hi : c.init = Initialization.initCode kind)
    (hd : Domain kind c preimage steps)
    (hg : creationGas kind ≤ c.gas.toNat) :
    ∃ created world gas substate,
      c.result = .ok (CreationSettlement.address preimage,
        created, world, gas, substate, true, ByteArray.empty) ∧
      DirectInitialization.Observed kind c preimage
        (CreationSettlement.address preimage) world substate := by
  let init := c.initCall (CreationSettlement.address preimage) steps
  have hgas : executionEnvelope kind ≤ init.gas.toNat := by
    change executionEnvelope kind ≤ c.gas.toNat
    cases kind <;> simp only [creationGas, executionEnvelope] at hg ⊢ <;> omega
  have hf : executionSteps kind ≤ init.fuel := by
    cases kind with
    | deposit => exact hd.resources.2
    | exit => exact hd.resources.2.2.1
  have hp : kind = .exit → init.env.perm = true := by
    intro he
    subst kind
    exact hd.resources.1
  have ho : kind = .exit → HasOwner (init.entry .exit).toState := by
    intro he
    subst kind
    exact CreationSettlement.entry_hasOwner c _ steps .exit hd.resources.2.2.2
  obtain ⟨ic, iw, ig, ia, hr, hb, _, _⟩ := execution_budget kind init hgas hf hp ho
  have he : c.execution (CreationSettlement.address preimage) =
      .ok (.success (ic, iw, ig, ia) (runtime kind)) := by
    rw [CreationSettlement.execution_eq_initialization c _ steps kind hd.fuel_eq hd.no_collision hi]
    exact hr
  have hremaining : 200 * runtimeLen kind ≤ ig.toNat := by
    change c.gas.toNat - executionEnvelope kind ≤ ig.toNat at hb
    cases kind <;> simp only [creationGas, runtimeLen, executionEnvelope] at hg hb ⊢ <;> omega
  have hguards := deposit_guards kind c _ ig hd.no_collision hremaining
  have result := CreationSettlement.installs_of_execution c hd.preimage_eq he hguards
  exact ⟨_, _, _, _, result,
    observed_of_success kind c preimage steps hi hd result⟩


#print axioms collision_fields
#print axioms zero_of_no_collision
#print axioms observed_of_success
#print axioms deposit_guards
#print axioms initializes_success
end Eip8282.Audit.Integrator.PrefundedInitialization
