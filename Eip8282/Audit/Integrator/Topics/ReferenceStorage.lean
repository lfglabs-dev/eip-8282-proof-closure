import Eip8282.Audit.Integrator.Topics.Protocol
import Eip8282.Audit.Integrator.Topics.Reference
import Eip8282.Audit.Integrator.Topics.ReferenceRuntime3

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceStorageGas -/

/-! Source-transcribed Amsterdam SSTORE gas classification, EL commit
0cc100eb190b64b23baba72dac0165652eaec252. Cached vm/instructions/storage.py
SHA256 d355855a1c50212a4e4753abb533c338919103635755da13bc1e154fcb3ed11b,
lines80-170; vm/gas.py SHA256
41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c,
lines49-113,389-447,604-626. Signed refunds and state-refund order are retained.
This audited transcription is not an equation with an actual Python evaluator.
Stack pops, state reads/writes and access-set mutation require separate adapters.
No reference trace, global progress or protocol adoption is asserted. -/
namespace Eip8282.Audit.Integrator.ReferenceStorageGas
open EvmYul
set_option autoImplicit false

structure Charge where
  access : Nat
  sentry : Nat
  execution : Nat
  state : Nat
  refundDelta : Int
  stateRefund : Nat
  deriving DecidableEq, Repr

def classify (warm : Bool) (original current new : UInt256) : Charge :=
  let access := if warm then 100 else 2100
  let first := original = current ∧ current ≠ new
  let changed := current ≠ new
  { access := access, sentry := max access 2301,
    execution := access + (if first then 10000 else 0),
    state := if first ∧ original = ⟨0⟩ then 97920 else 0,
    refundDelta :=
      (if changed ∧ original ≠ ⟨0⟩ ∧ current ≠ ⟨0⟩ ∧ new = ⟨0⟩ then 11616 else 0) -
      (if changed ∧ original ≠ ⟨0⟩ ∧ current = ⟨0⟩ then 11616 else 0) +
      (if changed ∧ original = new then 10000 else 0),
    stateRefund := if changed ∧ original = new ∧ original = ⟨0⟩ then 97920 else 0 }

theorem charge_bounds (warm : Bool) (original current new : UInt256) :
    (classify warm original current new).execution ≤ 12100 ∧
    (classify warm original current new).state ≤ 97920 ∧
    (classify warm original current new).sentry = 2301 := by
  cases warm <;> simp only [classify, Bool.false_eq_true, ↓reduceIte]
  all_goals split <;> split <;> norm_num

structure Meter where
  execution : Nat
  reservoir : Nat
  spill : Nat
  refund : Int
  deriving DecidableEq, Repr

/-- Source LIFO state refund: execution spill is restored first. -/
def creditState (m : Meter) (amount : Nat) : Meter :=
  let restored := min amount m.spill
  { m with
    execution := m.execution + restored
    spill := m.spill - restored
    reservoir := m.reservoir + (amount-restored) }

def chargeExecution (m : Meter) (amount : Nat) : Option Meter :=
  if amount ≤ m.execution then some {m with execution := m.execution-amount} else none

/-- Reservoir first, then execution spill; includes the actual exhaustion branch. -/
def chargeState (m : Meter) (amount : Nat) : Option Meter :=
  if amount ≤ m.reservoir then some {m with reservoir := m.reservoir-amount}
  else if amount ≤ m.reservoir+m.execution then
    some {m with
      reservoir := 0
      execution := m.execution-(amount-m.reservoir)
      spill := m.spill+(amount-m.reservoir)}
  else none

/-- The source's static rejection and sentry precede state-dependent pricing.
Input original/current values represent subsequent reads, not pre-sentry effects. -/
def storageCharge (isStatic warm : Bool) (original current new : UInt256)
    (m : Meter) : Option Meter :=
  let c := classify warm original current new
  if isStatic then none
  else if c.sentry ≤ m.execution then
    let credited := creditState {m with refund := m.refund+c.refundDelta} c.stateRefund
    (chargeExecution credited c.execution).bind (fun charged => chargeState charged c.state)
  else none

/-- A per-class resource condition proves success in the literal charge order.
No state refund or execution-refund credit is needed in these hypotheses. -/
theorem funded_success (warm : Bool) (original current new : UInt256) (m : Meter)
    (hs : (classify warm original current new).sentry ≤ m.execution)
    (he : (classify warm original current new).execution ≤ m.execution)
    (hr : (classify warm original current new).state ≤ m.reservoir) :
    ∃ post, storageCharge false warm original current new m = some post ∧
      m.execution-(classify warm original current new).execution ≤ post.execution ∧
      m.reservoir-(classify warm original current new).state ≤ post.reservoir := by
  unfold storageCharge
  simp only [Bool.false_eq_true, ↓reduceIte, hs]
  unfold creditState chargeExecution
  rw [if_pos (by dsimp; omega)]
  simp only [Option.bind_some]
  unfold chargeState
  rw [if_pos (by dsimp; omega)]
  exact ⟨_,rfl,by dsimp; omega,by dsimp; omega⟩

theorem conservative_success (warm : Bool) (original current new : UInt256) (m : Meter)
    (he : 12100 ≤ m.execution) (hr : 97920 ≤ m.reservoir) :
    ∃ post, storageCharge false warm original current new m = some post ∧
      m.execution-12100 ≤ post.execution ∧ m.reservoir-97920 ≤ post.reservoir := by
  obtain ⟨hb,hst,hse⟩ := charge_bounds warm original current new
  obtain ⟨post,hp,hpe,hpr⟩ := funded_success warm original current new m
    (by omega) (by omega) (by omega)
  exact ⟨post,hp,by omega,by omega⟩

theorem static_rejects (warm : Bool) (original current new : UInt256) (m : Meter) :
    storageCharge true warm original current new m = none := rfl

#print axioms charge_bounds
#print axioms funded_success
#print axioms conservative_success
#print axioms static_rejects
end Eip8282.Audit.Integrator.ReferenceStorageGas

end

section

/-! ## ReferenceStoragePotential -/

/-! Storage-set state charges and credits telescope on an actual value chain.
A set-then-clear cycle cannot create net state gas. This algebra must be applied
to the same slot's ordered writes; arbitrary unlinked event readings do not
supply that premise. Account lifecycle and nested rollback remain separate. -/
namespace Eip8282.Audit.Integrator.ReferenceStoragePotential
open EvmYul ReferenceStorageGas
set_option autoImplicit false

noncomputable def potential (original current : UInt256) : Int :=
  if original = ⟨0⟩ ∧ current ≠ ⟨0⟩ then 97920 else 0

theorem step (warm : Bool) (original current new : UInt256) :
    ((classify warm original current new).state : Int)-(classify warm original current new).stateRefund =
      potential original new-potential original current := by
  classical
  by_cases ho : original = ⟨0⟩
  · subst original
    by_cases hc : current = ⟨0⟩
    · subst current
      by_cases hn : new = ⟨0⟩
      · subst new; simp [classify,potential]
      · simp [classify,potential,hn,Ne.symm hn]
    · by_cases hn : new = ⟨0⟩
      · subst new; simp [classify,potential,hc,Ne.symm hc]
      · simp [classify,potential,hc,hn,Ne.symm hc,Ne.symm hn]
  · simp [classify,potential,ho]

def finalValue : UInt256 → List UInt256 → UInt256
  | current, [] => current
  | _, new::tail => finalValue new tail

def net : UInt256 → UInt256 → List UInt256 → Int
  | _, _, [] => 0
  | original, current, new::tail =>
    ((classify false original current new).state : Int)-(classify false original current new).stateRefund+
      net original new tail

/-- Arbitrary finite write sequences, with successive current values linked.
This is a per-slot signed state-gas balance, not a count of retained appends. -/
theorem telescope (original current : UInt256) (writes : List UInt256) :
    net original current writes = potential original (finalValue current writes)-potential original current := by
  induction writes generalizing current with
  | nil => simp [net,finalValue]
  | cons new tail ih =>
    simp only [net,finalValue,ih,step]
    omega

/-- A slot starting at its transaction-original value owes no initial state
credit. Net state-gas spending cannot become negative on its linked writes. -/
theorem from_original (original : UInt256) (writes : List UInt256) :
    0 ≤ net original original writes ∧ net original original writes ≤ 97920 := by
  classical
  rw [telescope]
  have hi : potential original original = 0 := by simp [potential]
  rw [hi]
  unfold potential
  split <;> omega

#print axioms step
#print axioms telescope
#print axioms from_original
end Eip8282.Audit.Integrator.ReferenceStoragePotential

end

section

/-! ## ReferenceStorageViewAction -/

/-! Produce complete source-shaped storage actions from actual accepted runtime
steps. The pop operands, natural PC bound and post-view relation are derived.
These local action constructors are not a Python execution semantics; original
storage, warmth/refunds, source account validity and charged replay stay separate.
The retained log projection includes every topic and payload at the owner. -/
namespace Eip8282.Audit.Integrator.ReferenceStorageViewAction
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private theorem memory_frame {pre post : EVM.State} {memory : ByteArray}
    (hf : ReferenceStorageStep.Frame pre post)
    (hm : ReferenceMemoryOperations.Related pre.toMachineState memory) :
    ReferenceMemoryOperations.Related post.toMachineState memory := by
  refine ⟨?_,?_,?_⟩
  · change post.memory.size ≤ 32*post.activeWords.toNat
    rw [hf.memory,hf.activeWords]
    exact hm.coherent
  · rw [hf.activeWords]
    exact hm.size
  · rw [hf.memory]
    exact hm.bytes

private theorem natural_pc {kind : Kind} {pre post : EVM.State}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hf : ReferenceStorageStep.Frame pre post) : post.pc.toNat = pre.pc.toNat+1 := by
  have hfit : pre.pc.toNat+1 < UInt256.size := by
    have := ReferenceRuntimeSites.pc_fit hat
    omega
  rw [hf.pc,toNat_add_of_lt _ _ hfit]
  rfl

private theorem logs_frame {pre post : EVM.State} {logs : List LogEntry}
    (hf : ReferenceStorageStep.Frame pre post)
    (hl : logs = ProtectedLogFrame.project pre.executionEnv.codeOwner pre.substate) :
    logs = ProtectedLogFrame.project post.executionEnv.codeOwner post.substate := by
  simpa only [ProtectedLogFrame.project,hf.executionEnv,hf.logs] using hl

/-- The actual accepted stack supplies the source load key and remainder. -/
theorem sload {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel gasCost : Nat}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hdecode : decodeAt pre = (.SLOAD,none))
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (decodeAt pre) mid post)
    (related : Related parent v pre) :
    ∃ key rest, pre.stack.pop = some (rest,key) ∧ v.stack = key::rest ∧
      Related parent (loadAction parent v key rest) post := by
  rw [hdecode] at hz hs
  obtain ⟨rest,key,hshape,hpop⟩ := ReferenceAcceptedStack.pop1 hz (by decide)
  obtain ⟨hstorage,howner,hstack,hframe,_⟩ := ReferenceStorageStep.sload hz hs
    parent v.storage related.storage related.owner hpop
  refine ⟨key,rest,hpop,related.stack.trans hshape,?_⟩
  refine ⟨related.env.trans hframe.executionEnv.symm,?_,?_,
    memory_frame hframe related.memory,?_,logs_frame hframe related.logs,howner⟩
  · change v.pc+1 = post.pc.toNat
    rw [related.pc,natural_pc hat hframe]
  · change ReferenceStorageView.current parent v.storage v.env.codeOwner key.toByteArray::rest = post.stack
    rw [related.env,hstack]
  · change ReferenceStorageView.Related parent
      (ReferenceStorageView.readTracked v.storage v.env.codeOwner key.toByteArray) post.toState
    rw [related.env]
    exact hstorage

/-- Key and value are produced from actual Z admission. The literal action's
post storage, memory, logs, environment and PC are all proved related. -/
theorem sstore {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel gasCost : Nat}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hdecode : decodeAt pre = (.SSTORE,none))
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (decodeAt pre) mid post)
    (related : Related parent v pre) :
    ∃ key value rest, pre.stack.pop2 = some (rest,key,value) ∧
      v.stack = key::value::rest ∧ Related parent (storeAction v key value rest) post := by
  rw [hdecode] at hz hs
  obtain ⟨rest,key,value,hshape,hpop⟩ := ReferenceAcceptedStack.pop2 hz (by decide)
  obtain ⟨hstorage,howner,hstack,hframe⟩ := ReferenceStorageStep.sstore hz hs
    parent v.storage related.storage related.owner hpop
  refine ⟨key,value,rest,hpop,related.stack.trans hshape,?_⟩
  refine ⟨related.env.trans hframe.executionEnv.symm,?_,hstack.symm,
    memory_frame hframe related.memory,?_,logs_frame hframe related.logs,howner⟩
  · change v.pc+1 = post.pc.toNat
    rw [related.pc,natural_pc hat hframe]
  · change ReferenceStorageView.Related parent
      (ReferenceStorageStep.storeView v.storage v.env.codeOwner key value) post.toState
    rw [related.env]
    exact hstorage

#print axioms sload
#print axioms sstore
end Eip8282.Audit.Integrator.ReferenceStorageViewAction

end

section

/-! ## ReferenceStorageReverse -/

/-! Reverse raw storage effects. The actual existing owner rules out the old
absent-owner SSTORE no-op. Source execution, permission/gas admission and warm
or original-storage correspondence remain separate; no old step is assumed. -/
namespace Eip8282.Audit.Integrator.ReferenceStorageReverse
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private theorem pc_fit {kind : Kind} {pre : EVM.State}
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre) :
    pre.pc.toNat+1 < UInt256.size := by
  have := ReferenceRuntimeSites.pc_fit site
  omega

theorem load {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre : EVM.State} {key : UInt256} {rest : Stack UInt256}
    (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (shape : v.stack = key::rest) :
    ∃ post, EvmYul.step (τ := .EVM) .SLOAD none pre = .ok post ∧
      Related parent (loadAction parent v key rest) post := by
  have stack : pre.stack = key::rest := related.stack.symm.trans shape
  let post := ({pre with toState := (pre.toState.sload key).1} : EVM.State).replaceStackAndIncrPC
    ((pre.toState.sload key).2::rest)
  have raw : EvmYul.step (τ := .EVM) .SLOAD none pre = .ok post := by
    obtain ⟨sh,pc,stk,ex⟩ := pre
    simp only at stack
    subst stack
    rfl
  refine ⟨post,raw,related.env,?_,?_,?_,?_,related.logs,related.owner⟩
  · change v.pc+1 = (pre.pc+UInt256.ofNat 1).toNat
    rw [related.pc,toNat_add_of_lt _ _ (pc_fit site)]
    rfl
  · change ReferenceStorageView.current parent v.storage v.env.codeOwner key.toByteArray::rest =
      slotW pre.toState key::rest
    rw [related.env,related.storage key]
  · exact ⟨related.memory.coherent,related.memory.size,related.memory.bytes⟩
  · intro q
    exact related.storage q

theorem store {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre : EVM.State} {key value : UInt256} {rest : Stack UInt256}
    (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (shape : v.stack = key::value::rest) :
    ∃ post, EvmYul.step (τ := .EVM) .SSTORE none pre = .ok post ∧
      Related parent (storeAction v key value rest) post := by
  have stack : pre.stack = key::value::rest := related.stack.symm.trans shape
  let post := ({pre with toState := pre.toState.sstore key value} : EVM.State).replaceStackAndIncrPC rest
  refine ⟨post,step_SSTORE stack,?_,?_,rfl,?_,?_,?_,?_⟩
  · exact related.env.trans (executionEnv_sstore _ _ _).symm
  · change v.pc+1 = (pre.pc+UInt256.ofNat 1).toNat
    rw [related.pc,toNat_add_of_lt _ _ (pc_fit site)]
    rfl
  · exact ⟨related.memory.coherent,related.memory.size,related.memory.bytes⟩
  · change ReferenceStorageView.Related parent
      (ReferenceStorageStep.storeView v.storage v.env.codeOwner key value) (pre.toState.sstore key value)
    rw [related.env]
    exact ReferenceStorageView.write_transport parent
      (ReferenceStorageView.readTracked v.storage pre.executionEnv.codeOwner key.toByteArray)
      pre.toState related.storage related.owner key value
  · change v.logs = ProtectedLogFrame.project
      (pre.toState.sstore key value).executionEnv.codeOwner (pre.toState.sstore key value).substate
    simpa only [ProtectedLogFrame.project,executionEnv_sstore,AppendSpec.logs_sstore] using related.logs
  · exact SystemSpec.owner_sstore related.owner key value

#print axioms load
#print axioms store
end Eip8282.Audit.Integrator.ReferenceStorageReverse

end
