import Eip8282.Audit.Integrator.ReachableCalls
import Eip8282.Audit.Integrator.UserStateInvariant
import Eip8282.Audit.Integrator.UserQueueInvariant
import Eip8282.Audit.Integrator.SystemStateInvariant
import Eip8282.Audit.Integrator.InitializedInvariant

/-!
# Invariants over concrete, contiguous message-call histories

Every transition binds both full worlds to actual Θ execution. The event count
uses actual status/caller/input, not a desired state or invariant. An independent
bound on the complete event count bounds each prefix. The policy contains only
input-size and user-funding constraints; no storage postcondition or AppendFits.

This is not yet extraction from all Ethereum transactions: external frames,
ancestor rollback, distinct transaction gas accounting and valid block scheduling
must still be linked. The initial invariant can be supplied by InitializedInvariant
on actual successful creation; canonical deployment remains a separate binding.
-/
namespace Eip8282.Audit.Integrator.ConcreteHistory

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach (INH)
open ReachableCalls (Contract Transition)
open MessageCall (Context)
open SystemSpec (worldSlot)
open AccountedState FundedDomain QueueInvariant

/-- Input constraints, independent of the state invariant to be established. -/
def Allowed (c : Context) : Prop :=
  c.calldata.size < UInt256.size ∧
    (c.caller ≠ Eip8282.Audit.EvmRunner.sysAddr → c.value.toNat < fundingCeiling)

def weight (c : Context) (success : Bool) : Nat :=
  if c.caller = Eip8282.Audit.EvmRunner.sysAddr then 0 else UserStateInvariant.weight c success

inductive Trace (kind : Contract) (initial : AccountMap .EVM) : Nat → AccountMap .EVM → Prop where
  | initial : Trace kind initial 0 initial
  | call {budget : Nat} {before after : AccountMap .EVM}
      (prior : Trace kind initial budget before) (t : Transition kind before after)
      (allowed : Allowed t.call) : Trace kind initial (budget + weight t.call t.success) after

/-- Forgetting the event counter recovers the existing actual-call relation. -/
theorem forget {kind : Contract} {initial world : AccountMap .EVM} {budget : Nat}
    (h : Trace kind initial budget world) : ReachableCalls.From kind initial Allowed world := by
  induction h with
  | initial => exact .initial
  | call _ t ha ih => exact .call ih t ha

def Invariant : Contract → Nat → AccountMap .EVM → Prop
  | .deposit, budget, world =>
      Bounded budget (worldSlot world (ReachableCalls.address .deposit)) ∧
      EnabledSafe 8 (worldSlot world (ReachableCalls.address .deposit)) ∧
      ∃ queue : List (Record .deposit), Represents .deposit
        (worldSlot world (ReachableCalls.address .deposit)) queue
  | .exit, budget, world =>
      Bounded budget (worldSlot world (ReachableCalls.address .exit)) ∧
      EnabledSafe 2 (worldSlot world (ReachableCalls.address .exit)) ∧
      ∃ queue : List (Record .exit), Represents .exit
        (worldSlot world (ReachableCalls.address .exit)) queue ∧ SourceWidth queue

/-- A real transition preserves all invariants; its own actual receipt supplies
admission and effects. The budget bound is on the input event count. -/
theorem transition_preserves {kind : Contract} {before after : AccountMap .EVM}
    (t : Transition kind before after) (ha : Allowed t.call) (budget : Nat)
    (hbudget : budget < 2^128) (hi : Invariant kind budget before) :
    Invariant kind (budget + weight t.call t.success) after := by
  have ho : ∃ account, t.call.world.get? t.call.target = some account := by
    obtain ⟨acc, hacc, _⟩ := t.pinned.installed
    exact ⟨acc, hacc⟩
  cases kind with
  | deposit =>
    obtain ⟨hb, hs, queue, hq⟩ := hi
    have hcode : t.call.code = Eip8282.Audit.Correspondence.runtimeCode .deposit := t.pinned.code
    have hb' : Bounded budget (worldSlot t.call.world t.call.target) := by
      rw [t.pre, t.pinned.target]; exact hb
    have hs' : EnabledSafe 8 (worldSlot t.call.world t.call.target) := by
      rw [t.pre, t.pinned.target]; exact hs
    have hq' : Represents .deposit (worldSlot t.call.world t.call.target) queue := by
      rw [t.pre, t.pinned.target]; exact hq
    by_cases hsys : t.call.caller = Eip8282.Audit.EvmRunner.sysAddr
    · obtain ⟨hbp, hsp, hqp, _⟩ := SystemStateInvariant.deposit_system t.call hcode hsys ho
        budget hbudget hb' hs' queue hq' t.executed
      change Invariant .deposit _ after
      simp only [Invariant, weight, if_pos hsys, Nat.add_zero]
      rw [← t.pinned.target]
      exact ⟨hbp, hsp, _, hqp⟩
    · obtain ⟨hbp, hsp⟩ := UserStateInvariant.deposit_user t.call hcode hsys
        t.pinned.ordinaryValue ha.1 ho budget hbudget hb' hs' (ha.2 hsys) t.executed
      have hqp := UserQueueInvariant.deposit_user t.call hcode hsys t.pinned.ordinaryValue
        ha.1 ho queue hq' budget hbudget hb' t.executed
      simp only [Invariant, weight, if_neg hsys]
      rw [← t.pinned.target]
      exact ⟨hbp, hsp, _, hqp⟩
  | exit =>
    obtain ⟨hb, hs, queue, hq, hw⟩ := hi
    have hcode : t.call.code = Eip8282.Audit.Correspondence.runtimeCode .exit := t.pinned.code
    have hb' : Bounded budget (worldSlot t.call.world t.call.target) := by
      rw [t.pre, t.pinned.target]; exact hb
    have hs' : EnabledSafe 2 (worldSlot t.call.world t.call.target) := by
      rw [t.pre, t.pinned.target]; exact hs
    have hq' : Represents .exit (worldSlot t.call.world t.call.target) queue := by
      rw [t.pre, t.pinned.target]; exact hq
    by_cases hsys : t.call.caller = Eip8282.Audit.EvmRunner.sysAddr
    · obtain ⟨hbp, hsp, hqp, hwp, _⟩ := SystemStateInvariant.exit_system t.call hcode hsys ho
        budget hbudget hb' hs' queue hq' hw t.executed
      simp only [Invariant, weight, if_pos hsys, Nat.add_zero]
      rw [← t.pinned.target]
      exact ⟨hbp, hsp, _, hqp, hwp⟩
    · obtain ⟨hbp, hsp⟩ := UserStateInvariant.exit_user t.call hcode hsys
        t.pinned.ordinaryValue ha.1 ho budget hbudget hb' hs' (ha.2 hsys) t.executed
      have hqp := UserQueueInvariant.exit_user t.call hcode hsys t.pinned.ordinaryValue
        ha.1 ho queue hq' budget hbudget hb' t.executed
      have hwp := UserQueueInvariant.exit_source_width
        (CallBridge.codeCall t.call hcode (t.call.fuel-1)) t.success queue hw
      simp only [Invariant, weight, if_neg hsys]
      rw [← t.pinned.target]
      exact ⟨hbp, hsp, _, hqp, hwp⟩

/-- A global bound on actual events yields each pre-call bound by monotonicity;
no invariant is assumed in a history constructor. -/
theorem preserves {kind : Contract} {initial world : AccountMap .EVM} {budget : Nat}
    (h : Trace kind initial budget world) (hi : Invariant kind 0 initial)
    (hb : budget < 2^128) : Invariant kind budget world := by
  induction h with
  | initial => exact hi
  | @call priorBudget before after prior t ha ih =>
    have hp : priorBudget < 2^128 := by omega
    exact transition_preserves t ha priorBudget hp (ih hp)

/-- The actual constructor supplies the initial invariant of this concrete
history. Canonical deployment address and the complete event/funding envelope
remain explicit, independently stated inputs. -/
theorem deposit_from_creation (c : CreationSettlement.Context) {preimage : ByteArray}
    (hp : c.preimage = some preimage) (steps : Nat)
    (hf : c.fuel = steps+1) (hc : c.collision (CreationSettlement.address preimage) = false)
    (hcode : c.init = Initialization.initCode .deposit)
    (hgas : 1000 ≤ c.gas.toNat) (hsteps : 8 ≤ steps)
    (habsent : c.world.get? (CreationSettlement.address preimage) = none)
    {a : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {initial : AccountMap .EVM} {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hcreation : c.result = .ok (a, created, initial, gas, substate, true, out))
    (haddress : a = ReachableCalls.address .deposit)
    {budget : Nat} {world : AccountMap .EVM}
    (history : Trace .deposit initial budget world) (hbudget : budget < 2^128) :
    Invariant .deposit budget world := by
  obtain ⟨_, _, _, hb, hs, hq, _⟩ := InitializedInvariant.deposit_creation c hp steps hf hc hcode
    hgas hsteps habsent hcreation
  have hi : Invariant .deposit 0 initial := by
    simp only [Invariant]
    rw [← haddress]
    exact ⟨hb, hs, [], hq⟩
  exact preserves history hi hbudget

/-- The actual constructor supplies the initial invariant of this concrete
history. Canonical deployment address and the complete event/funding envelope
remain explicit, independently stated inputs. -/
theorem exit_from_creation (c : CreationSettlement.Context) {preimage : ByteArray}
    (hp : c.preimage = some preimage) (steps : Nat)
    (hf : c.fuel = steps+1) (hc : c.collision (CreationSettlement.address preimage) = false)
    (hcode : c.init = Initialization.initCode .exit) (hperm : c.permission = true)
    (hgas : 25000 ≤ c.gas.toNat) (hsteps : 11 ≤ steps)
    (howner : ∃ acc, c.world.get? c.sender = some acc)
    (habsent : c.world.get? (CreationSettlement.address preimage) = none)
    {a : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {initial : AccountMap .EVM} {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hcreation : c.result = .ok (a, created, initial, gas, substate, true, out))
    (haddress : a = ReachableCalls.address .exit)
    {budget : Nat} {world : AccountMap .EVM}
    (history : Trace .exit initial budget world) (hbudget : budget < 2^128) :
    Invariant .exit budget world := by
  obtain ⟨_, _, _, hb, hs, hq, hw, _⟩ := InitializedInvariant.exit_creation c hp steps hf hc hcode hperm
    hgas hsteps howner habsent hcreation
  have hi : Invariant .exit 0 initial := by
    simp only [Invariant]
    rw [← haddress]
    exact ⟨hb, hs, [], hq, hw⟩
  exact preserves history hi hbudget

#print axioms deposit_from_creation
#print axioms exit_from_creation
#print axioms forget
#print axioms transition_preserves
#print axioms preserves

end Eip8282.Audit.Integrator.ConcreteHistory
