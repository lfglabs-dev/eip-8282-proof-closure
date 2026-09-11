import Eip8282.Audit.Integrator.InitializedInvariant

/-!
# Initializer clause for the direct control guarantee

The specification accepts a parameter initializer image. No original initializer
pin occurs in its input domain. Its output demands the intended installed runtime
and initial controls. The pinned instance reuses actual successful Lambda results;
canonical predeploy installation and transaction validity remain separate.
-/
namespace Eip8282.Audit.Integrator.DirectInitialization

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach (INH)
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Correspondence (runtimeCode)
open SystemSpec
open CreationSettlement (Context address)

def initialExcess : Kind → UInt256 | .deposit => ⟨0⟩ | .exit => INH

def target : Kind → Nat | .deposit => 8 | .exit => 2

/-- Independent inputs under which the existing constructor proofs apply. -/
structure Domain (kind : Kind) (c : Context) (preimage : ByteArray) (steps : Nat) : Prop where
  preimage_eq : c.preimage = some preimage
  fuel_eq : c.fuel = steps+1
  no_collision : c.collision (address preimage) = false
  absent : c.world.get? (address preimage) = none
  resources : match kind with
    | .deposit => 1000 ≤ c.gas.toNat ∧ 8 ≤ steps
    | .exit => c.permission = true ∧ 25000 ≤ c.gas.toNat ∧ 11 ≤ steps ∧
        ∃ acc, c.world.get? c.sender = some acc

def Observed (kind : Kind) (c : Context) (preimage : ByteArray)
    (a : AccountAddress) (world : AccountMap .EVM) (substate : Substate) : Prop :=
  a = address preimage ∧
  (∃ acc, world.get? a = some acc ∧ acc.code = runtimeCode kind) ∧
  worldSlot world a (UInt256.ofNat 0) = initialExcess kind ∧
  AccountedState.Bounded 0 (worldSlot world a) ∧
  FundedDomain.EnabledSafe (target kind) (worldSlot world a) ∧
  QueueInvariant.Represents kind (worldSlot world a) [] ∧
  substate.logSeries = c.substate.logSeries

/-- Runtime behavior is independent of this separately quantified initializer. -/
def Initializes (kind : Kind) (init : ByteArray) : Prop :=
  ∀ (c : Context) (preimage : ByteArray) (steps : Nat),
    c.init = init → Domain kind c preimage steps →
    ∀ (a : AccountAddress) (created : Std.TreeSet AccountAddress compare)
      (world : AccountMap .EVM) (gas : UInt256) (substate : Substate) (out : ByteArray),
      c.result = .ok (a, created, world, gas, substate, true, out) →
      Observed kind c preimage a world substate

theorem pinned (kind : Kind) : Initializes kind (Initialization.initCode kind) := by
  intro c preimage steps hi hd a created world gas substate out hr
  cases kind with
  | deposit =>
    exact InitializedInvariant.deposit_creation c hd.preimage_eq steps hd.fuel_eq hd.no_collision
      hi hd.resources.1 hd.resources.2 hd.absent hr
  | exit =>
    obtain ⟨ha, hc, he, hb, hs, hq, _, hl⟩ := InitializedInvariant.exit_creation c hd.preimage_eq
      steps hd.fuel_eq hd.no_collision hi hd.resources.1 hd.resources.2.1 hd.resources.2.2.1
      hd.resources.2.2.2 hd.absent hr
    exact ⟨ha, hc, he, hb, hs, hq, hl⟩

#print axioms pinned

end Eip8282.Audit.Integrator.DirectInitialization
