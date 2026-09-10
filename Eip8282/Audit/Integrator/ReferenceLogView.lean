import Eip8282.Audit.Integrator.ReferenceReturnSlice
import Eip8282.Audit.Integrator.ReferenceAcceptedStack
import Eip8282.Audit.Integrator.RuntimeMemoryCharges

/-! Actual accepted LOG0 and its literal source-shaped effect. Pinned EL0cc
instructions/log.py pops, charges, extends memory, checks static mode, appends
one log and advances PC. This successful-step adapter derives permission from
actual admission; it does not equate exceptional intermediate ordering or use
the SYSTEM payment theorem (whose actual traces contain no LOG0). -/
namespace Eip8282.Audit.Integrator.ReferenceLogView
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def entry (v : View) (off len : UInt256) : LogEntry :=
  ⟨v.env.codeOwner,#[],ReferenceReturnView.output v off len⟩

def logAction (v : View) (off len : UInt256) (rest : Stack UInt256) : View :=
  {v with
    pc := v.pc+1
    stack := rest
    memory := ReferenceReturnView.returnMemory v off len
    logs := v.logs++[entry v off len]}

private theorem permission {vj : Array UInt256} {pre mid : EVM.State} {gasCost : Nat}
    (hz : Z vj .LOG0 pre = .ok (mid,gasCost)) : pre.executionEnv.perm = true := by
  simp only [Z,Bind.bind,Except.bind,pure,Except.pure] at hz
  iterate 8 replace hz := elim_guard hz
  have hn := elim_guard_not hz
  cases hp : pre.executionEnv.perm <;> simp [hp,W] at hn ⊢

private theorem expanded {parent : ReferenceStorageView.Parent} {v : View}
    {pre post : EVM.State} {off len : UInt256} (related : Related parent v pre)
    (hmem : post.memory = pre.memory)
    (hex : post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat len.toNat) :
    ReferenceMemoryOperations.Related post.toMachineState (ReferenceReturnView.returnMemory v off len) := by
  have hb := (ReferenceMemoryCapacity.expansion_bounds pre.activeWords.toNat off.toNat len.toNat).1
  have hsize : v.memory.size ≤ 32*MachineState.M (words v) off.toNat len.toNat := by
    rw [related.memory.size,words_related related]
    omega
  have hext := ReferenceMemoryOperations.extend_same v.memory
    (32*MachineState.M (words v) off.toNat len.toNat) hsize
  refine ⟨?_,?_,?_⟩
  · change post.memory.size ≤ 32*post.activeWords.toNat
    rw [hmem,hex]
    have hc := related.memory.coherent
    change pre.memory.size ≤ 32*pre.activeWords.toNat at hc
    omega
  · rw [ReferenceReturnView.returnMemory,ReferenceMemoryOperations.extend,ReferenceMemoryView.buffer_size,
      words_related related,hex]
  · rw [hmem]
    intro i
    exact (related.memory.bytes i).trans (hext i)

theorem data_slice {parent : ReferenceStorageView.Parent} {v : View} {pre : EVM.State}
    (related : Related parent v pre) (off len : UInt256) :
    (entry v off len).data = (ReferenceReturnView.returnMemory v off len).extract
      off.toNat (off.toNat+len.toNat) :=
  ReferenceReturnSlice.output_eq_extract related off len

theorem accepted {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel gasCost cap : Nat}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (.LOG0,none))
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (decodeAt pre) mid post)
    (related : Related parent v pre)
    (capacity : post.activeWords.toNat ≤ cap) (host : 32*cap < 2^System.Platform.numBits) :
    ∃ off len rest, pre.stack.pop2 = some (rest,off,len) ∧ v.stack = off::len::rest ∧
      v.env.perm = true ∧ Related parent (logAction v off len rest) post := by
  have hex := RuntimeMemoryCharges.accepted_expansion hat hz hs
  rw [decoded] at hz hs hex
  obtain ⟨rest,off,len,hshape,hpop⟩ := ReferenceAcceptedStack.pop2 hz (by decide)
  have hp : v.env.perm = true := by rw [related.env]; exact permission hz
  change post.activeWords.toNat = MachineState.M pre.activeWords.toNat
    pre.stack[0]!.toNat pre.stack[1]!.toNat at hex
  rw [hshape] at hex
  change post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat len.toNat at hex
  have hlen : len.toNat < 2^System.Platform.numBits := by
    by_cases hzlen : len.toNat = 0
    · have hh : 0 < 2^System.Platform.numBits := by positivity
      omega
    · have hb := (ReferenceMemoryCapacity.expansion_bounds pre.activeWords.toNat off.toNat len.toNat).2 (by omega)
      rw [← hex] at hb
      omega
  have h64 : len.toNat < 2^64 := by
    rcases System.Platform.numBits_eq with hn | hn <;> rw [hn] at hlen <;> omega
  have hbytes : pre.memory.readWithPadding off.toNat len.toNat = ReferenceReturnView.output v off len := by
    rw [ReferenceMemoryView.read_eq_buffer _ _ _ h64 hlen]
    exact ReferenceMemoryView.buffer_congr _ _ related.memory.bytes _ _
  have fit : pre.pc.toNat+1 < UInt256.size := by
    have := ReferenceRuntimeSites.pc_fit hat
    omega
  obtain rfl := Z_ok_state hz
  change EVM.step (fuel+1) gasCost (some (.LOG0,none)) (zMid pre .LOG0) = .ok post at hs
  rw [OrdinaryGas.dispatch (by decide)] at hs
  have known := step_LOG0 (s := stepPre gasCost (zMid pre .LOG0)) hshape
  have same := Except.ok.inj (hs.symm.trans known)
  subst post
  refine ⟨off,len,rest,hpop,related.stack.trans hshape,hp,?_⟩
  refine ⟨related.env,?_,rfl,expanded related rfl hex,related.storage,?_,related.owner⟩
  · change v.pc+1 = (pre.pc+UInt256.ofNat 1).toNat
    rw [related.pc,toNat_add_of_lt _ _ fit]
    rfl
  · change v.logs++[entry v off len] = ProtectedLogFrame.project pre.executionEnv.codeOwner
      {pre.substate with
        logSeries := pre.substate.logSeries.push ⟨pre.executionEnv.codeOwner,#[],pre.memory.readWithPadding off.toNat len.toNat⟩}
    rw [ProtectedLogFrame.push_self pre.executionEnv.codeOwner pre.substate
      ⟨pre.executionEnv.codeOwner,#[],pre.memory.readWithPadding off.toNat len.toNat⟩ rfl,
      ← related.logs,hbytes]
    rw [entry,related.env]

#print axioms data_slice
#print axioms accepted
end Eip8282.Audit.Integrator.ReferenceLogView
