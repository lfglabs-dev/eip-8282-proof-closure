import Eip8282.Audit.Integrator.ReferenceRefundCounter

/-! Baseline and committed-spill metadata are preserved by every checked
protected handler, including partial errors. This is consumed at actual
exceptional transaction settlement; no desired final metadata is assumed. -/
namespace Eip8282.Audit.Integrator.ReferenceMeterMetadata
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option maxErrors 3

def Same (pre post : Meter) : Prop := post.baseline = pre.baseline ∧ post.committedSpill = pre.committedSpill

def Fields (pre : Meter) : Outcome → Prop
  | .continued _ _ m _ | .eof _ _ m _ | .failed _ _ _ m _ | .unsupported _ _ _ m _ => Same pre m
  | .terminal r => Same pre r.meter

theorem handler (h : Handler) (d : List Nat) (owner : Bool) (p : ReferenceStorageView.Parent)
    (v : View) (w : Warm) (m : Meter) (o : ByteArray) : Fields m (runHandler h d owner p v w m o) := by
  cases h <;> simp only [runHandler,
    ReferenceCheckedBinaryStep.run,ReferenceCheckedEnvironmentStep.run,ReferenceCheckedEnvironmentStep.finish,
    ReferenceCheckedMemoryStore.run,ReferenceCheckedCopyLogStep.run,ReferenceCheckedCopyLogStep.afterPops,
    ReferenceCheckedStorageStep.load,ReferenceCheckedStorageStep.store,ReferenceCheckedStorageStep.storeAfterPop,
    ReferenceCheckedTerminalStep.run,ReferenceCheckedStackControlStep.run]
  all_goals repeat' (split at * <;> try simp_all [Fields,Same,ReferenceMeterBoundary.update])
  all_goals aesop

theorem dispatch (d : List Nat) (owner : Bool) (p : ReferenceStorageView.Parent)
    (v : View) (w : Warm) (m : Meter) (o : ByteArray) : Fields m (ReferenceCheckedDispatch.run d owner p v w m o) := by
  unfold ReferenceCheckedDispatch.run
  cases read v.env.code v.pc <;> try exact ⟨rfl,rfl⟩
  exact handler ..

#print axioms handler
#print axioms dispatch
end Eip8282.Audit.Integrator.ReferenceMeterMetadata
