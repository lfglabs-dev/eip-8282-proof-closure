import Eip8282.Audit.Integrator.ReferenceStorageStep
import Eip8282.Audit.Integrator.ReferenceMemoryStep
import Eip8282.Audit.Integrator.ReferenceRuntimeSites
import Eip8282.Audit.Integrator.RuntimeCodePreservation
import Eip8282.Audit.Integrator.ProtectedLogFrame

/-! A small source-shaped running view for protected-runtime step composition.
The stack is represented top-first (the source list is its reverse). Memory is
rounded and eager; storage retains source overlays/read tracking. Logs include
ALL topics at the code owner's address. This is a view and literal local action
vocabulary, not an assumed recursive interpreter or whole-model equivalence. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeView
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceStorageView
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

structure View where
  env : ExecutionEnv .EVM
  pc : Nat
  stack : Stack UInt256
  memory : ByteArray
  storage : Tx
  logs : List LogEntry

structure Related (parent : Parent) (v : View) (pre : EVM.State) : Prop where
  env : v.env = pre.executionEnv
  pc : v.pc = pre.pc.toNat
  stack : v.stack = pre.stack
  memory : ReferenceMemoryOperations.Related pre.toMachineState v.memory
  storage : ReferenceStorageView.Related parent v.storage pre.toState
  logs : v.logs = ProtectedLogFrame.project pre.executionEnv.codeOwner pre.substate
  owner : SystemSpec.HasOwner pre.toState

def words (v : View) : Nat := v.memory.size/32

theorem words_related {parent : Parent} {v : View} {pre : EVM.State} (h : Related parent v pre) :
    words v = pre.activeWords.toNat := by
  unfold words
  rw [h.memory.size]
  omega

/-- Z and stepPre adjust resource counters, which are not running-view fields. -/
theorem charged {parent : Parent} {v : View} {pre : EVM.State} (h : Related parent v pre)
    (op : Operation .EVM) (gasCost : Nat) : Related parent v (stepPre gasCost (zMid pre op)) :=
  ⟨h.env,h.pc,h.stack,⟨h.memory.coherent,h.memory.size,h.memory.bytes⟩,h.storage,h.logs,h.owner⟩

/-- One actual existing-owner fact is propagated through accepted runtime
steps; later local SSTORE uses this conclusion rather than re-assuming it. -/
theorem owner_next {image : RuntimeExecutionScope.Image} {pre mid post : EVM.State}
    {fuel gasCost : Nat} (hat : RuntimeExecutionScope.At image pre)
    (hz : Z (D_J image.code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk fuel gasCost (decodeAt pre) mid post)
    (owner : SystemSpec.HasOwner pre.toState) : SystemSpec.HasOwner post.toState := by
  obtain ⟨account,ha⟩ := owner
  obtain ⟨account',hb,_⟩ := RuntimeCodePreservation.accepted_preserved hat hz hs pre.executionEnv.codeOwner account ha
  have he := RuntimeExecutionScope.accepted_environment hat hz hs
  exact ⟨account',by rw [he]; exact hb⟩

/-- Literal local updates. No action definition takes the desired post-state. -/
def stackAction (v : View) (pc : Nat) (stack : Stack UInt256) : View :=
  {v with pc := pc, stack := stack}

noncomputable def loadAction (p : Parent) (v : View) (key : UInt256) (rest : Stack UInt256) : View :=
  {v with
    pc := v.pc+1,
    stack := current p v.storage v.env.codeOwner key.toByteArray::rest,
    storage := readTracked v.storage v.env.codeOwner key.toByteArray}

noncomputable def storeAction (v : View) (key value : UInt256) (rest : Stack UInt256) : View :=
  {v with
    pc := v.pc+1, stack := rest,
    storage := ReferenceStorageStep.storeView v.storage v.env.codeOwner key value}

def memoryAction (v : View) (off : UInt256) (bytes : ByteArray) (rest : Stack UInt256) : View :=
  {v with
    pc := v.pc+1, stack := rest,
    memory := ReferenceMemoryOperations.splice v.memory off.toNat bytes
      (32*MachineState.M (words v) off.toNat bytes.size)}

def initial {kind : Eip8282.Audit.Model.Kind} (c : XiCall kind) (tx : Tx) : View :=
  {env := c.env, pc := 0, stack := [], memory := ByteArray.empty, storage := tx,
    logs := ProtectedLogFrame.project c.env.codeOwner c.substate}

/-- Runtime entry supplies empty coherent memory and stack directly. The
source-to-world current-slot relation and existing owner are initial bindings. -/
theorem initial_related {kind : Eip8282.Audit.Model.Kind} (c : XiCall kind) (parent : Parent) (tx : Tx)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) : Related parent (initial c tx) c.entry := by
  refine ⟨rfl,rfl,rfl,?_,slots,rfl,owner⟩
  exact ⟨by change 0 ≤ 32*0; decide,rfl,fun _ => rfl⟩

#print axioms words_related
#print axioms charged
#print axioms owner_next
#print axioms initial_related
end Eip8282.Audit.Integrator.ReferenceRuntimeView
