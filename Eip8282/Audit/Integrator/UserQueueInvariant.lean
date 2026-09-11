import Eip8282.Audit.Integrator.SuccessfulAppend
import Eip8282.Audit.Integrator.GetterInversion
import Eip8282.Audit.Integrator.AccountedState
import Eip8282.Audit.Integrator.QueueInvariant

/-!
# Actual user calls preserve or extend the represented FIFO

The post-queue is selected only by actual success status and input emptiness.
Append fit is derived from the independently bounded input storage before using
its bytecode postcondition. No user call consumes a list prefix. Initialization,
protocol accounting and the independent budget bound remain separate obligations.
-/
namespace Eip8282.Audit.Integrator.UserQueueInvariant

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall)
open MessageCall CallBridge QueueInvariant SystemSpec
open Eip8282.Audit.Correspondence (runtimeCode)

def after (q : XiCall kind) (success : Bool) (queue : List (Record kind)) : List (Record kind) :=
  if success = true ∧ q.env.calldata.size ≠ 0 then queue ++ [appendedRecord q] else queue

/-- The old list is always a prefix of the independently selected new list. -/
theorem preserves_prefix (q : XiCall kind) (success : Bool) (queue : List (Record kind)) :
    List.IsPrefix queue (after q success queue) := by
  unfold after
  split
  · exact ⟨_, rfl⟩
  · exact ⟨[], by simp⟩

/-- Observe the receipt's independent map in the actual given result world. -/
theorem append_actual_world (c : Context) (q : XiCall kind) (record : ByteArray)
    (queue : List (Record kind)) (hf : AppendStorage.AppendFits q)
    (hp : Represents kind (slotW (entrySt q)) queue)
    (ha : CommittedAppend.AppendResult c q record)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    Represents kind (worldSlot world c.target) (queue ++ [appendedRecord q]) := by
  obtain ⟨ic, iw, ig, ia, hr, _, hslots, _⟩ := ha
  have hw : iw = world := congrArg (fun p => p.2.1) (Except.ok.inj (hr.symm.trans h))
  rw [← hw, funext hslots]
  exact represents_append q hf queue hp

theorem deposit_user (c : Context) (hcode : c.code = runtimeCode .deposit)
    (huser : c.caller ≠ EvmRunner.sysAddr) (hactual : c.apparentValue = c.value)
    (hdata : c.calldata.size < UInt256.size)
    (ho : ∃ acc, c.world.get? c.target = some acc)
    (queue : List (Record .deposit))
    (hp : Represents .deposit (worldSlot c.world c.target) queue)
    (budget : Nat) (hb : budget < 2^128)
    (hs : AccountedState.Bounded budget (worldSlot c.world c.target))
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, success, out)) :
    Represents .deposit (worldSlot world c.target)
      (after (codeCall c hcode (c.fuel-1)) success queue) := by
  cases success with
  | false =>
    obtain ⟨hw, _, _⟩ := failure_restores_journal c created world gas substate out h
    simpa only [after, Bool.false_eq_true, false_and, ↓reduceIte, hw] using hp
  | true =>
    obtain ⟨_, _, _, _, hc⟩ := SuccessfulUser.deposit_admission c hcode huser hactual hdata h
    rcases hc with ⟨hz, _, _⟩ | ⟨hlen, _⟩
    · obtain ⟨_, hw, _, _⟩ := GetterInversion.deposit_getter_readonly c hcode huser hactual hz h
      have hr : worldSlot world c.target = worldSlot c.world c.target := by
        funext k
        unfold worldSlot
        rw [hw]
      change Represents .deposit (worldSlot world c.target)
        (if true = true ∧ c.calldata.size ≠ 0 then _ else queue)
      simpa only [hz, ne_eq, not_true_eq_false, and_false, ↓reduceIte, hr] using hp
    · have hentry := TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1)
        (AccountedState.Bounded budget) hs
      have hf := AccountedState.append_fits _ hentry hb
      have hrep := TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1)
        (fun read => Represents .deposit read queue) hp
      have happ := SuccessfulAppend.deposit_append c hcode huser hlen ho hf h
      have hpost := append_actual_world c (codeCall c hcode (c.fuel-1)) _ queue hf hrep happ h
      change Represents .deposit (worldSlot world c.target)
        (if true = true ∧ c.calldata.size ≠ 0 then _ else queue)
      simpa [hlen] using hpost

theorem exit_user (c : Context) (hcode : c.code = runtimeCode .exit)
    (huser : c.caller ≠ EvmRunner.sysAddr) (hactual : c.apparentValue = c.value)
    (hdata : c.calldata.size < UInt256.size)
    (ho : ∃ acc, c.world.get? c.target = some acc)
    (queue : List (Record .exit))
    (hp : Represents .exit (worldSlot c.world c.target) queue)
    (budget : Nat) (hb : budget < 2^128)
    (hs : AccountedState.Bounded budget (worldSlot c.world c.target))
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, success, out)) :
    Represents .exit (worldSlot world c.target)
      (after (codeCall c hcode (c.fuel-1)) success queue) := by
  cases success with
  | false =>
    obtain ⟨hw, _, _⟩ := failure_restores_journal c created world gas substate out h
    simpa only [after, Bool.false_eq_true, false_and, ↓reduceIte, hw] using hp
  | true =>
    obtain ⟨_, _, _, _, hc⟩ := SuccessfulUser.exit_admission c hcode huser hactual hdata h
    rcases hc with ⟨hz, _, _⟩ | ⟨hlen, _⟩
    · obtain ⟨_, hw, _, _⟩ := GetterInversion.exit_getter_readonly c hcode huser hactual hz h
      have hr : worldSlot world c.target = worldSlot c.world c.target := by
        funext k
        unfold worldSlot
        rw [hw]
      change Represents .exit (worldSlot world c.target)
        (if true = true ∧ c.calldata.size ≠ 0 then _ else queue)
      simpa only [hz, ne_eq, not_true_eq_false, and_false, ↓reduceIte, hr] using hp
    · have hentry := TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1)
        (AccountedState.Bounded budget) hs
      have hf := AccountedState.append_fits _ hentry hb
      have hrep := TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1)
        (fun read => Represents .exit read queue) hp
      have happ := SuccessfulAppend.exit_append c hcode huser hlen ho hf h
      have hpost := append_actual_world c (codeCall c hcode (c.fuel-1)) _ queue hf hrep happ h
      change Represents .exit (worldSlot world c.target)
        (if true = true ∧ c.calldata.size ≠ 0 then _ else queue)
      simpa [hlen] using hpost

theorem exit_source_width (q : XiCall .exit) (success : Bool) (queue : List (Record .exit))
    (h : SourceWidth queue) : SourceWidth (after q success queue) := by
  unfold after
  split
  · exact source_width_append q queue h
  · exact h

#print axioms preserves_prefix
#print axioms deposit_user
#print axioms exit_user
#print axioms exit_source_width

end Eip8282.Audit.Integrator.UserQueueInvariant
