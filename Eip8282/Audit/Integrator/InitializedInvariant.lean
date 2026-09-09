import Eip8282.Audit.Integrator.CreationSettlement
import Eip8282.Audit.Integrator.AccountedState
import Eip8282.Audit.Integrator.FundedDomain
import Eip8282.Audit.Integrator.QueueInvariant

/-!
# Initial invariants from actual successful creation

An independently absent pre-deployment target supplies zero storage. The actual
Lambda constructor and code-deposit result supplies the installed runtime and
final storage, from which the initial budget, safe fee domain and empty FIFO
follow. Constructor resource, collision and permission hypotheses remain explicit;
no creation success, canonical address or transaction validity is manufactured.
-/
namespace Eip8282.Audit.Integrator.InitializedInvariant

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach (INH)
open Eip8282.Audit.Correspondence (runtimeCode)
open Eip8282.Audit.Model (Kind)
open SystemSpec AccountedState FundedDomain QueueInvariant
open CreationSettlement (Context address)

/-- Absence is an independent pre-world fact, not a storage postcondition. -/
theorem zero_of_absent (world : AccountMap .EVM) (a : AccountAddress)
    (h : world.get? a = none) (k : UInt256) : worldSlot world a k = ⟨0⟩ := by
  simp only [worldSlot, h, Option.map_none, Option.getD_none]

/-- Initial control observations suffice for all three structural invariants. -/
theorem initial_invariant (kind : Kind) (target : Nat) (read : UInt256 → UInt256)
    (hh : read (UInt256.ofNat 2) = ⟨0⟩) (ht : read (UInt256.ofNat 3) = ⟨0⟩)
    (hc : read (UInt256.ofNat 1) = ⟨0⟩)
    (he : read (UInt256.ofNat 0) = ⟨0⟩ ∨ read (UInt256.ofNat 0) = INH) :
    Bounded 0 read ∧ EnabledSafe target read ∧ Represents kind read [] := by
  refine ⟨AccountedState.initial hh ht hc he, ?_, represents_empty kind read ?_ ?_⟩
  · rcases he with hz | hi
    · right
      simp only [hz, hc, ControlSpec.feeInputNat]
      change 0 + (0 - target) ≤ 2892
      omega
    · exact Or.inl hi
  · change (read (UInt256.ofNat 2)).toNat = 0
    rw [hh]
    rfl
  · change (read (UInt256.ofNat 3)).toNat = 0
    rw [ht]
    rfl

/-- Successful deposit creation at a previously absent target installs the
pinned runtime, begins enabled, and represents an empty queue at budget zero. -/
theorem deposit_creation (c : Context) {preimage : ByteArray}
    (hp : c.preimage = some preimage) (steps : Nat)
    (hf : c.fuel = steps+1) (hc : c.collision (address preimage) = false)
    (hi : c.init = Initialization.initCode .deposit)
    (hg : 1000 ≤ c.gas.toNat) (hs : 8 ≤ steps)
    (habsent : c.world.get? (address preimage) = none)
    {a : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {world : AccountMap .EVM} {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hr : c.result = .ok (a, created, world, gas, substate, true, out)) :
    a = address preimage ∧
      (∃ acc, world.get? a = some acc ∧ acc.code = runtimeCode .deposit) ∧
      worldSlot world a (UInt256.ofNat 0) = ⟨0⟩ ∧
      Bounded 0 (worldSlot world a) ∧ EnabledSafe 8 (worldSlot world a) ∧
      Represents .deposit (worldSlot world a) [] ∧
      substate.logSeries = c.substate.logSeries := by
  obtain ⟨ha, hcode, hstorage, hlogs⟩ :=
    CreationSettlement.deposit_creation c hp steps hf hc hi hg hs hr
  have hz (k : UInt256) : worldSlot world a k = ⟨0⟩ := by
    rw [hstorage, ha]
    exact zero_of_absent c.world _ habsent k
  obtain ⟨hb, he, hq⟩ := initial_invariant .deposit 8 (worldSlot world a)
    (hz _) (hz _) (hz _) (Or.inl (hz _))
  exact ⟨ha, hcode, hz _, hb, he, hq, hlogs⟩

/-- Successful exit creation at a previously absent target installs the pinned
runtime, begins inhibited, and supplies the initial empty FIFO/source-width facts. -/
theorem exit_creation (c : Context) {preimage : ByteArray}
    (hp : c.preimage = some preimage) (steps : Nat)
    (hf : c.fuel = steps+1) (hc : c.collision (address preimage) = false)
    (hi : c.init = Initialization.initCode .exit) (hperm : c.permission = true)
    (hg : 25000 ≤ c.gas.toNat) (hs : 11 ≤ steps)
    (howner : ∃ acc, c.world.get? c.sender = some acc)
    (habsent : c.world.get? (address preimage) = none)
    {a : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {world : AccountMap .EVM} {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hr : c.result = .ok (a, created, world, gas, substate, true, out)) :
    a = address preimage ∧
      (∃ acc, world.get? a = some acc ∧ acc.code = runtimeCode .exit) ∧
      worldSlot world a (UInt256.ofNat 0) = INH ∧
      Bounded 0 (worldSlot world a) ∧ EnabledSafe 2 (worldSlot world a) ∧
      Represents .exit (worldSlot world a) [] ∧ SourceWidth [] ∧
      substate.logSeries = c.substate.logSeries := by
  obtain ⟨ha, hcode, hstorage, hlogs⟩ :=
    CreationSettlement.exit_creation c hp steps hf hc hi hperm hg hs howner hr
  have hz (k : UInt256) (hk : k ≠ ⟨0⟩) : worldSlot world a k = ⟨0⟩ := by
    rw [hstorage, if_neg hk, ha]
    exact zero_of_absent c.world _ habsent k
  have hin : worldSlot world a (UInt256.ofNat 0) = INH := by
    rw [hstorage, if_pos (by decide : UInt256.ofNat 0 = (⟨0⟩ : UInt256))]
  obtain ⟨hb, he, hq⟩ := initial_invariant .exit 2 (worldSlot world a)
    (hz _ (by decide)) (hz _ (by decide)) (hz _ (by decide)) (Or.inr hin)
  exact ⟨ha, hcode, hin, hb, he, hq, source_width_empty, hlogs⟩

#print axioms zero_of_absent
#print axioms initial_invariant
#print axioms deposit_creation
#print axioms exit_creation

end Eip8282.Audit.Integrator.InitializedInvariant
