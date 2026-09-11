import Eip8282.Audit.Integrator.SystemDataSpec
import Eip8282.Audit.Integrator.SystemStateInvariant
import Eip8282.Audit.Integrator.UserQueueInvariant
import Eip8282.Audit.Integrator.DirectAppend

/-!
# Code-independent FIFO behavior of actual completed calls

The small observation below inspects actual success status, caller, world and
return bytes against a supplied represented pre-queue. It contains no bytecode
pin and no post-state assumption. Failure consumes nothing; successful SYSTEM
returns and removes the capped prefix; a successful user preserves HEAD and
keeps the complete old queue as a prefix (with exactly one authentic physical
record added for nonempty input). These are data predicates, not another model
of execution. Initial bounds and exit source width remain explicit.
-/
namespace Eip8282.Audit.Integrator.DirectDrain

open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Correspondence (runtimeCode)
open Eip8282.Audit.XiTransport (bytes)
open Eip8282.Audit.EntryReach (slotW entrySt)
open MessageCall CallBridge SystemSpec QueueInvariant

set_option autoImplicit false

def sourceWidth : (kind : Kind) → List (Record kind) → Prop
  | .deposit, _ => True
  | .exit, queue => SourceWidth queue

/-- Independent returned-record encoders, including deposit BE-to-LE amount. -/
def recordBytes : (kind : Kind) → Record kind → List Eip8282.Audit.Model.Byte
  | .deposit => depositBytes
  | .exit => exitBytes

/-- The single physical record determined by input and actual caller. -/
def inputRecord (kind : Kind) (c : Context) : Record kind :=
  fun j => AppendDataSpec.recordWord kind c.calldata c.caller j.val

/-- Successful user calls either quote or add exactly one physical record. -/
def userQueue (kind : Kind) (c : Context) (queue : List (Record kind)) : List (Record kind) :=
  if c.calldata.size = 0 then queue else queue ++ [inputRecord kind c]

theorem userQueue_prefix (kind : Kind) (c : Context) (queue : List (Record kind)) :
    List.IsPrefix queue (userQueue kind c queue) := by
  unfold userQueue
  split
  · exact ⟨[], by simp⟩
  · exact ⟨_, rfl⟩

/-- Only independent pre-call inputs; notably no original-code constraint. -/
structure Domain (kind : Kind) (c : Context) (queue : List (Record kind)) (budget : Nat) : Prop where
  owner : ∃ account, c.world.get? c.target = some account
  ordinaryValue : c.apparentValue = c.value
  calldataFit : c.calldata.size < UInt256.size
  budgetFit : budget < 2^128
  bounded : AccountedState.Bounded budget (worldSlot c.world c.target)
  safe : FundedDomain.EnabledSafe (SystemDataSpec.target kind) (worldSlot c.world c.target)
  represented : Represents kind (worldSlot c.world c.target) queue
  source : sourceWidth kind queue

/-- Actual completed-call behavior, separating user and SYSTEM by caller alone.
Failure makes no statement about returned bytes or remaining gas. -/
def Observed (kind : Kind) (c : Context) (world : AccountMap .EVM)
    (success : Bool) (out : ByteArray) (queue : List (Record kind)) : Prop :=
  if success then
    if c.caller = Eip8282.Audit.EvmRunner.sysAddr then
      SystemDataSpec.DrainSlots kind (worldSlot c.world c.target) (worldSlot world c.target) ∧
      Represents kind (worldSlot world c.target)
        (queue.drop (min queue.length (SystemDataSpec.cap kind))) ∧
      bytes out = (queue.take (min queue.length (SystemDataSpec.cap kind))).flatMap (recordBytes kind)
    else
      worldSlot world c.target (UInt256.ofNat 2) = worldSlot c.world c.target (UInt256.ofNat 2) ∧
      Represents kind (worldSlot world c.target) (userQueue kind c queue) ∧
      List.IsPrefix queue (userQueue kind c queue)
  else
    world = c.world ∧ Represents kind (worldSlot world c.target) queue

private theorem inputRecord_eq {kind : Kind} (c : Context)
    (hcode : c.code = runtimeCode kind) (steps : Nat) :
    inputRecord kind c = appendedRecord (codeCall c hcode steps) := by
  funext j
  exact AppendDataSpec.recordWord_eq (codeCall c hcode steps) j.val

private theorem userQueue_eq {kind : Kind} (c : Context)
    (hcode : c.code = runtimeCode kind) (steps : Nat) (queue : List (Record kind)) :
    userQueue kind c queue = UserQueueInvariant.after (codeCall c hcode steps) true queue := by
  unfold userQueue UserQueueInvariant.after
  change (if c.calldata.size = 0 then _ else _) =
    (if true = true ∧ c.calldata.size ≠ 0 then _ else _)
  by_cases hz : c.calldata.size = 0
  · simp only [hz, ↓reduceIte, ne_eq, not_true_eq_false, and_false]
  · simp only [hz, ↓reduceIte, ne_eq, not_false_eq_true, and_self, inputRecord_eq c hcode steps]

private theorem user_head (kind : Kind) (c : Context) (hcode : c.code = runtimeCode kind)
    (queue : List (Record kind)) (budget : Nat) (hd : Domain kind c queue budget)
    (huser : c.caller ≠ Eip8282.Audit.EvmRunner.sysAddr)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    worldSlot world c.target (UInt256.ofNat 2) = worldSlot c.world c.target (UInt256.ofNat 2) := by
  by_cases hz : c.calldata.size = 0
  · have hr : GetterInversion.ReadOnly c created world substate := by
      cases kind with
      | deposit => exact GetterInversion.deposit_getter_readonly c hcode huser hd.ordinaryValue hz h
      | exit => exact GetterInversion.exit_getter_readonly c hcode huser hd.ordinaryValue hz h
    unfold worldSlot
    rw [hr.2.1]
  · have hs : FundedDomain.EnabledSafe (DirectAdmission.target kind) (worldSlot c.world c.target) := by
      cases kind <;> exact hd.safe
    obtain ⟨ha, _⟩ := DirectAppend.user_append kind c hcode huser hd.ordinaryValue hd.calldataFit hz
      hd.owner budget hd.budgetFit hd.bounded hs h
    exact ha.2.1.2.2.1

/-- Full completed Θ calls satisfy the code-independent FIFO behavior. All
execution resources are arbitrary; the supplied result rules out evaluator
OutOfFuel but does not assume SYSTEM/user success. -/
theorem completed_call (kind : Kind) (c : Context) (hcode : c.code = runtimeCode kind)
    (queue : List (Record kind)) (budget : Nat) (hd : Domain kind c queue budget)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, success, out)) :
    Observed kind c world success out queue := by
  cases success with
  | false =>
    have hw := (failure_restores_journal c created world gas substate out h).1
    change world = c.world ∧ Represents kind (worldSlot world c.target) queue
    exact ⟨hw, by rw [hw]; exact hd.represented⟩
  | true =>
    by_cases hsys : c.caller = Eip8282.Audit.EvmRunner.sysAddr
    · have hslots : SystemDataSpec.Observed kind c world := by
        cases kind with
        | deposit => exact SystemDataSpec.deposit_system c hcode hsys hd.owner h
        | exit => exact SystemDataSpec.exit_system c hcode hsys hd.owner h
      have hprojection := (SystemDataSpec.projections hslots budget hd.bounded
        (hd.budgetFit.trans (by decide)) hd.calldataFit).2
      have hfifo :
          Represents kind (worldSlot world c.target)
            (queue.drop (min queue.length (SystemDataSpec.cap kind))) ∧
          bytes out = (queue.take (min queue.length (SystemDataSpec.cap kind))).flatMap (recordBytes kind) := by
        cases kind with
        | deposit =>
          have hp := SystemStateInvariant.deposit_system c hcode hsys hd.owner budget hd.budgetFit
            hd.bounded hd.safe queue hd.represented h
          refine ⟨?_, hp.2.2.2 rfl⟩
          simpa only [SystemStateInvariant.consumed, SystemDataSpec.cap, ↓reduceIte] using hp.2.2.1
        | exit =>
          have hp := SystemStateInvariant.exit_system c hcode hsys hd.owner budget hd.budgetFit
            hd.bounded hd.safe queue hd.represented hd.source h
          refine ⟨?_, hp.2.2.2.2 rfl⟩
          simpa only [SystemStateInvariant.consumed, SystemDataSpec.cap, ↓reduceIte] using hp.2.2.1
      simpa only [Observed, ↓reduceIte, hsys] using And.intro hprojection hfifo
    · have hhead := user_head kind c hcode queue budget hd hsys h
      have hqueue : Represents kind (worldSlot world c.target) (userQueue kind c queue) := by
        rw [userQueue_eq c hcode (c.fuel-1)]
        cases kind with
        | deposit =>
          exact UserQueueInvariant.deposit_user c hcode hsys hd.ordinaryValue hd.calldataFit
            hd.owner queue hd.represented budget hd.budgetFit hd.bounded h
        | exit =>
          exact UserQueueInvariant.exit_user c hcode hsys hd.ordinaryValue hd.calldataFit
            hd.owner queue hd.represented budget hd.budgetFit hd.bounded h
      simpa only [Observed, ↓reduceIte, hsys] using
        And.intro hhead (And.intro hqueue (userQueue_prefix kind c queue))

#print axioms userQueue_prefix
#print axioms completed_call

end Eip8282.Audit.Integrator.DirectDrain
