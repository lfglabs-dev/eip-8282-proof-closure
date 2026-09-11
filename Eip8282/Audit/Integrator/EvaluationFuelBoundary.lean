import Eip8282.Audit.Integrator.CreationOutcome
import Eip8282.Audit.Integrator.NestedEventCert

/-!
# A finite-evaluator exhaustion boundary for world-history framing

This diagnostic uses the pinned evaluator, not modified audited predeploys.
A valid empty-stack entry reaches an admitted CREATE whose literal Lambda(0)
error is caught as an empty account map. This is a transient evaluator artifact,
not a valid Ethereum execution or an outer-success counterexample. SSTORE does
not recreate the missing owner, so that proposed continuation is refuted.
-/
namespace Eip8282.Audit.Integrator.EvaluationFuelBoundary
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open Eip8282.Audit.SymExec
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def owner : AccountAddress := 100
def protectedAddr : AccountAddress := 200

def diagnosticCode : ByteArray := ⟨#[0x5f, 0x5f, 0x5f, 0xf0, 0x00]⟩

def ownerAccount : Account .EVM := { (default : Account .EVM) with code := diagnosticCode }
def protectedAccount : Account .EVM := { (default : Account .EVM) with balance := ⟨7⟩ }
def world : AccountMap .EVM := ((∅ : AccountMap .EVM).insert owner ownerAccount).insert protectedAddr protectedAccount

def env : ExecutionEnv .EVM :=
  { (default : ExecutionEnv .EVM) with codeOwner := owner, source := owner, code := diagnosticCode, perm := true }

def entry : EVM.State :=
  Eip8282.Audit.XiTransport.entryState ∅ default default world world ⟨1000000⟩ default env

def push (s : EVM.State) : EVM.State :=
  (stepPre 2 s).replaceStackAndIncrPC (⟨0⟩::s.stack)

def beforeCreate : EVM.State := push (push (push entry))

def afterCreate : EVM.State :=
  ({ (stepPre 32000 beforeCreate) with
    accountMap := ∅
    activeWords := ⟨0⟩
    returnData := .empty
    gasAvailable := UInt256.ofNat ((stepPre 32000 beforeCreate).gasAvailable.toNat -
      L (stepPre 32000 beforeCreate).gasAvailable.toNat)}).replaceStackAndIncrPC [⟨0⟩]

theorem empty_stack_entry : entry.stack = [] := rfl

theorem actual_jumps : D_J diagnosticCode ⟨0⟩ = #[] := by decide +kernel

theorem protected_present : entry.accountMap.get? protectedAddr = some protectedAccount := by rfl

private theorem push_one : XStepAt #[] 4 2 entry (push entry) := by
  refine ⟨entry, ?_, ?_, ?_⟩ <;> rfl

private theorem push_two : XStepAt #[] 3 2 (push entry) (push (push entry)) := by
  refine ⟨push entry, ?_, ?_, ?_⟩ <;> rfl

private theorem push_three : XStepAt #[] 2 2 (push (push entry)) beforeCreate := by
  refine ⟨push (push entry), ?_, ?_, ?_⟩ <;> rfl

/-- The selected child is the literal zero-fuel Lambda, before hashing or init execution. -/
theorem child_exhausted :
    CreationGas.child .create 0 32000 beforeCreate ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ = .error .OutOfFuel := rfl

/-- This is an accepted Z plus actual dispatcher step, not a raw opcode fallback. -/
theorem create_step : XStepAt #[] 1 32000 beforeCreate afterCreate := by
  refine ⟨beforeCreate, by rfl, ?_, by rfl⟩
  change EVM.step 1 32000 (some (.CREATE, none)) beforeCreate = .ok afterCreate
  apply Eq.trans (CreationOutcome.admitted_equation .create 0 32000 beforeCreate none
    ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ [] rfl (by unfold CreationGas.nonceAllowed; decide +kernel)
      (by
        unfold CreationGas.gate
        refine ⟨by decide +kernel, by decide +kernel, ?_⟩
        change (beforeCreate.memory.readWithPadding 0 0).size ≤ 49152
        rw [Eip8282.Audit.XiTransport.readWithPadding_size_zero]
        decide))
  rw [child_exhausted]
  rfl

/-- The world-erasing state occurs in the same actual five-fuel X prefix. -/
theorem entry_to_erasure :
    ∃ labels, XRuns #[] 5 entry labels 1 afterCreate := by
  exact ⟨_, .cons push_one (.cons push_two (.cons push_three (.cons create_step (.refl _ _))))⟩

theorem erased : afterCreate.accountMap = ∅ := rfl

theorem protected_missing : afterCreate.accountMap.get? protectedAddr = none := rfl

/-- The proposed SSTORE recreation is false: missing owner means no update. -/
theorem sstore_absent_owner (s : EvmYul.State .EVM) (key value : UInt256)
    (h : s.accountMap.get? s.executionEnv.codeOwner = none) : s.sstore key value = s := by
  simp only [EvmYul.State.sstore, EvmYul.State.lookupAccount, h, Option.option]

/-- Even a paid SSTORE could not make this erased world nonempty. -/
theorem sstore_after_erasure (key value : UInt256) :
    (afterCreate.toState.sstore key value).accountMap = ∅ := by
  rw [sstore_absent_owner _ key value (by rfl)]
  rfl

/-- This short artifact ultimately exhausts evaluator fuel; it does not prove
an outer successful message call with lost accounts. -/
theorem final_error : X 5 #[] entry = .error .OutOfFuel := by
  obtain ⟨labels, hp⟩ := entry_to_erasure
  rw [hp.X_eq]
  rfl

#print axioms entry_to_erasure
#print axioms child_exhausted
#print axioms create_step
#print axioms protected_missing
#print axioms sstore_absent_owner
#print axioms sstore_after_erasure
#print axioms final_error
end Eip8282.Audit.Integrator.EvaluationFuelBoundary
