import Eip8282.Audit.Integrator.ReferenceStorageView
import Eip8282.Audit.Integrator.AppendSpec
import Eip8282.Audit.Integrator.OrdinaryGas

/-! Accepted pinned SLOAD/SSTORE against the source-shaped current storage view.
EL0cc100eb190b64b23baba72dac0165652eaec252 storage.py:37-170
SHA256 d355855a1c50212a4e4753abb533c338919103635755da13bc1e154fcb3ed11b;
state_tracker.py:244-302,433-458 SHA256
ce420ad5682df9051178d298220d1552448e26c37f67be3b604b9f493541cf4a.
SSTORE reads original (no storage-read-set mutation), then current (records the
key), then writes after payment. Current-view/read/write transport is proved;
original values, warmth, refunds, gas and complete substate are not equated.
Actual reference account validity and Python execution remain separate adapters.
-/
namespace Eip8282.Audit.Integrator.ReferenceStorageStep
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open ReferenceStorageView SystemSpec
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

structure Frame (pre post : EVM.State) : Prop where
  executionEnv : post.executionEnv = pre.executionEnv
  memory : post.memory = pre.memory
  activeWords : post.activeWords = pre.activeWords
  logs : post.substate.logSeries = pre.substate.logSeries
  pc : post.pc = pre.pc + UInt256.ofNat 1

/-- Source current read is recorded before the eventual successful write. -/
noncomputable def storeView (tx : Tx) (owner : AccountAddress) (key value : UInt256) : Tx :=
  write (readTracked tx owner key.toByteArray) owner key.toByteArray value

theorem store_metadata (p : Parent) (tx : Tx) (owner : AccountAddress) (key value : UInt256) :
    (storeView tx owner key value).reads = insert (owner,key.toByteArray) tx.reads ∧
    (storeView tx owner key value).created = tx.created ∧
    original p (readTracked tx owner key.toByteArray) owner key.toByteArray =
      original p tx owner key.toByteArray := ⟨rfl,rfl,rfl⟩

private theorem pop1_shape {stack rest : Stack UInt256} {key : UInt256}
    (h : stack.pop = some (rest,key)) : stack = key::rest := by
  cases stack with
  | nil => cases h
  | cons x xs => cases h; rfl

private theorem pop2_shape {stack rest : Stack UInt256} {key value : UInt256}
    (h : stack.pop2 = some (rest,key,value)) : stack = key::value::rest := by
  rcases stack with _ | ⟨x, _ | ⟨y,xs⟩⟩
  · cases h
  · cases h
  · cases h; rfl

private theorem raw_sload {s : EVM.State} {key : UInt256} {rest : Stack UInt256}
    (h : s.stack = key::rest) :
    EvmYul.step (τ := .EVM) .SLOAD none s =
      .ok (({s with toState := (s.toState.sload key).1} : EVM.State).replaceStackAndIncrPC
        ((s.toState.sload key).2::rest)) := by
  obtain ⟨sh,pc,stack,ex⟩ := s
  simp only at h
  subst h
  rfl

/-- Z and the dispatcher preserve the storage-view inputs while changing gas. -/
theorem charged_related (p : Parent) (tx : Tx) (pre : EVM.State) (op : Operation .EVM)
    (gasCost : Nat) (h : Related p tx pre.toState) :
    Related p tx (stepPre gasCost (zMid pre op)).toState := h

/-- The actual load returns the source current value and records the read.
No equality between source read tracking and pinned warmth is asserted. -/
theorem sload {vj : Array UInt256} {pre mid post : EVM.State} {fuel gasCost : Nat}
    (hz : Z vj .SLOAD pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (.SLOAD,none) mid post)
    (p : Parent) (tx : Tx) (related : Related p tx pre.toState)
    (owner : HasOwner pre.toState) {rest : Stack UInt256} {key : UInt256}
    (operands : pre.stack.pop = some (rest,key)) :
    Related p (readTracked tx pre.executionEnv.codeOwner key.toByteArray) post.toState ∧
    HasOwner post.toState ∧
    post.stack = current p tx pre.executionEnv.codeOwner key.toByteArray::rest ∧
    Frame pre post ∧ post.accountMap = pre.accountMap := by
  obtain rfl := Z_ok_state hz
  have hstack := pop1_shape operands
  change EVM.step (fuel+1) gasCost (some (.SLOAD,none)) (zMid pre .SLOAD) = .ok post at hs
  rw [OrdinaryGas.dispatch (by decide)] at hs
  have known := raw_sload (s := stepPre gasCost (zMid pre .SLOAD)) hstack
  have same := Except.ok.inj (hs.symm.trans known)
  subst post
  refine ⟨?_,owner,?_,⟨rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
  · intro q
    exact related q
  · change slotW pre.toState key::rest = current p tx pre.executionEnv.codeOwner key.toByteArray::rest
    rw [related key]

/-- The actual store implements the literal current-read then write overlay.
HasOwner rules out the pinned absent-owner no-op; source account validity is
still its own binding obligation. Refund/original/warm metadata stays separate. -/
theorem sstore {vj : Array UInt256} {pre mid post : EVM.State} {fuel gasCost : Nat}
    (hz : Z vj .SSTORE pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (.SSTORE,none) mid post)
    (p : Parent) (tx : Tx) (related : Related p tx pre.toState)
    (owner : HasOwner pre.toState) {rest : Stack UInt256} {key value : UInt256}
    (operands : pre.stack.pop2 = some (rest,key,value)) :
    Related p (storeView tx pre.executionEnv.codeOwner key value) post.toState ∧
    HasOwner post.toState ∧ post.stack = rest ∧ Frame pre post := by
  obtain rfl := Z_ok_state hz
  have hstack := pop2_shape operands
  change EVM.step (fuel+1) gasCost (some (.SSTORE,none)) (zMid pre .SSTORE) = .ok post at hs
  rw [OrdinaryGas.dispatch (by decide)] at hs
  have known := step_SSTORE (s := stepPre gasCost (zMid pre .SSTORE)) hstack
  have same := Except.ok.inj (hs.symm.trans known)
  subst post
  refine ⟨?_,owner_sstore owner key value,rfl,?_⟩
  · exact write_transport p (readTracked tx pre.executionEnv.codeOwner key.toByteArray)
      pre.toState related owner key value
  · exact ⟨executionEnv_sstore _ _ _,rfl,rfl,AppendSpec.logs_sstore _ _ _,rfl⟩

#print axioms store_metadata
#print axioms charged_related
#print axioms sload
#print axioms sstore
end Eip8282.Audit.Integrator.ReferenceStorageStep
