import Eip8282.Audit.Integrator.DirectSubmit
import Eip8282.Audit.Integrator.DirectControl
import Eip8282.Audit.Integrator.DirectDrain
import Eip8282.Audit.Integrator.DirectInitialization
import Eip8282.Audit.Integrator.SystemFrame
import Eip8282.Audit.Integrator.SystemProgress

/-!
# Three conditional direct guarantee predicates

Each predicate quantifies actual completed Θ results for a parameter bytecode.
Input domains contain no original-code pin, execution path or postcondition.
The pinned proofs establish the three instances directly; mutation witnesses can
therefore refute these same predicates after changing the bytecode parameter.

These are the registered conditional local guarantees. Protocol-history/domain
justification remains OPEN; same-predicate Θ mutation refutations are separate
test evidence, not conjuncts or assumptions of the correctness parents. Initialization has its own actual Lambda inputs and resources.
-/
namespace Eip8282.Audit.Integrator.DirectGuarantees

open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Correspondence (runtimeCode)
open MessageCall SystemSpec

structure Domain (kind : Kind) (c : Context) (budget : Nat) : Prop where
  owner : ∃ account, c.world.get? c.target = some account
  ordinaryValue : c.apparentValue = c.value
  calldataFit : c.calldata.size < UInt256.size
  budgetFit : budget < 2^128
  bounded : AccountedState.Bounded budget (worldSlot c.world c.target)
  safe : FundedDomain.EnabledSafe (DirectAdmission.target kind) (worldSlot c.world c.target)

/-- SYSTEM has no new log or record-slot writes; only a user can submit. -/
def SubmitObserved (kind : Kind) (c : Context) (created : Std.TreeSet AccountAddress compare)
    (world : AccountMap .EVM) (substate : Substate) (success : Bool) (out : ByteArray) : Prop :=
  if c.caller = Eip8282.Audit.EvmRunner.sysAddr then
    (success = false → UniversalGate.FailedJournal c created world substate success) ∧
    (success = true → substate.logSeries = c.substate.logSeries ∧
      ∀ k, 4 ≤ k.toNat → worldSlot world c.target k = worldSlot c.world c.target k)
  else DirectSubmit.Observed kind c created world substate success out ∧
    (success = true → c.calldata.size = 0 → GetterInversion.ReadOnly c created world substate)

def PSubmit (kind : Kind) (code : ByteArray) : Prop :=
  ∀ (c : Context) (budget : Nat), c.code = code → Domain kind c budget →
    ∀ (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
      (gas : UInt256) (substate : Substate) (success : Bool) (out : ByteArray),
      c.result = .ok (created, world, gas, substate, success, out) →
      SubmitObserved kind c created world substate success out

def PDrain (kind : Kind) (code : ByteArray) : Prop :=
  ∀ (c : Context) (queue : List (QueueInvariant.Record kind)) (budget : Nat),
    c.code = code → DirectDrain.Domain kind c queue budget →
    ∀ (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
      (gas : UInt256) (substate : Substate) (success : Bool) (out : ByteArray),
      c.result = .ok (created, world, gas, substate, success, out) →
      DirectDrain.Observed kind c world success out queue

def RuntimeControl (kind : Kind) (code : ByteArray) : Prop :=
  ∀ (c : Context) (budget : Nat), c.code = code → Domain kind c budget →
    ∀ (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
      (gas : UInt256) (substate : Substate) (success : Bool) (out : ByteArray),
      c.result = .ok (created, world, gas, substate, success, out) →
      DirectControl.Observed kind c created world substate success out

/-- Runtime and initializer execute in independently quantified calls. -/
def PControl (kind : Kind) (code init : ByteArray) : Prop :=
  RuntimeControl kind code ∧ DirectInitialization.Initializes kind init ∧ SystemProgress.Progress code

theorem psubmit1_direct (kind : Kind) : PSubmit kind (runtimeCode kind) := by
  intro c budget hcode hd created world gas substate success out hr
  by_cases hsys : c.caller = Eip8282.Audit.EvmRunner.sysAddr
  · rw [SubmitObserved, if_pos hsys]
    refine ⟨?_, ?_⟩
    · intro hf
      subst success
      obtain ⟨hw, hs, hc⟩ := failure_restores_journal c created world gas substate out hr
      exact ⟨rfl, hc, hw, hs⟩
    · intro ht
      subst success
      have hslots : SystemDataSpec.Observed kind c world := by
        cases kind with
        | deposit => exact SystemDataSpec.deposit_system c hcode hsys hd.owner hr
        | exit => exact SystemDataSpec.exit_system c hcode hsys hd.owner hr
      have hp := (SystemDataSpec.projections hslots budget hd.bounded
        (hd.budgetFit.trans (by decide)) hd.calldataFit).2
      exact ⟨SystemFrame.logs_preserved kind c hcode hsys hr, hp.2.2⟩
  · rw [SubmitObserved, if_neg hsys]
    refine ⟨DirectSubmit.completed kind c hcode hsys hd.ordinaryValue hd.calldataFit hd.owner
      budget hd.budgetFit hd.bounded hd.safe hr, ?_⟩
    intro ht hz
    subst success
    cases kind with
    | deposit => exact GetterInversion.deposit_getter_readonly c hcode hsys hd.ordinaryValue hz hr
    | exit => exact GetterInversion.exit_getter_readonly c hcode hsys hd.ordinaryValue hz hr

theorem pdrain1_direct (kind : Kind) : PDrain kind (runtimeCode kind) := by
  intro c queue budget hcode hd created world gas substate success out hr
  exact DirectDrain.completed_call kind c hcode queue budget hd hr

theorem pcontrol1_direct (kind : Kind) :
    PControl kind (runtimeCode kind) (Initialization.initCode kind) := by
  refine ⟨?_, DirectInitialization.pinned kind, SystemProgress.pinned kind⟩
  intro c budget hcode hd created world gas substate success out hr
  exact DirectControl.completed kind c hcode hd.ordinaryValue hd.calldataFit hd.owner
    budget hd.budgetFit hd.bounded hd.safe hr

#print axioms psubmit1_direct
#print axioms pdrain1_direct
#print axioms pcontrol1_direct

end Eip8282.Audit.Integrator.DirectGuarantees
