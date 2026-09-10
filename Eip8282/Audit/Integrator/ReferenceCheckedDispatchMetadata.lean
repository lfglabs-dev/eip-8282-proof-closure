import Eip8282.Audit.Integrator.ReferenceCheckedDispatch

/-! Full-frame metadata through every checked handler result, including partially
executed failures. The handler definitions only modify the core meter using
ReferenceMeterBoundary.update; baseline and committed spill remain those of the
same initial full meter. No successful payment, stack bound, permission, source
owner existence, or exceptional-halt classification is assumed. This does not
perform the separate frame settlement/commit operations. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedDispatchMetadata
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback
open ReferenceMeterBoundary ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def Metadata (pre post : Meter) : Prop :=
  post.baseline = pre.baseline ∧ post.committedSpill = pre.committedSpill

def resultMeter {F : Type} : Except (F × View × Meter) (View × Meter) → Meter
  | .error (_,_,m) => m | .ok (_,m) => m

def storageMeter : ReferenceCheckedStorageStep.Result → Meter
  | .error (_,_,_,m) => m | .ok (_,_,m) => m

def terminalMeter : Except ReferenceCheckedTerminalStep.Partial ReferenceCheckedTerminalStep.End → Meter
  | .error (_,_,m,_) => m | .ok result => result.meter

def outcomeMeter : Outcome → Meter
  | .continued _ _ m _ => m
  | .terminal result => result.meter
  | .eof _ _ m _ => m
  | .failed _ _ _ m _ => m
  | .unsupported _ _ _ m _ => m

theorem binary (h : ReferenceWordOps.Binary) (v : View) (m : Meter) :
    Metadata m (resultMeter (ReferenceCheckedBinaryStep.run h v m)) := by
  unfold ReferenceCheckedBinaryStep.run
  repeat' (split <;> try dsimp only)
  all_goals simp [resultMeter, Metadata, update]

theorem environment (h : ReferenceCheckedEnvironmentStep.Handler) (v : View) (m : Meter) :
    Metadata m (resultMeter (ReferenceCheckedEnvironmentStep.run h v m)) := by
  cases h <;> simp only [ReferenceCheckedEnvironmentStep.run, ReferenceCheckedEnvironmentStep.finish]
  all_goals repeat' (split <;> try dsimp only)
  all_goals simp [resultMeter, Metadata, update]

theorem stackControl (h : ReferenceCheckedStackControlStep.Handler) (d : List Nat) (v : View) (m : Meter) :
    Metadata m (resultMeter (ReferenceCheckedStackControlStep.run h d v m)) := by
  unfold ReferenceCheckedStackControlStep.run
  repeat' (split <;> try dsimp only)
  all_goals simp [resultMeter, Metadata, update]

theorem memoryStore (b : Bool) (v : View) (m : Meter) :
    Metadata m (resultMeter (ReferenceCheckedMemoryStore.run b v m)) := by
  unfold ReferenceCheckedMemoryStore.run
  repeat' (split <;> try dsimp only)
  all_goals simp [resultMeter, Metadata, update]

theorem copyLog (h : ReferenceCheckedCopyLogStep.Handler) (v : View) (m : Meter) :
    Metadata m (resultMeter (ReferenceCheckedCopyLogStep.run h v m)) := by
  cases h <;> simp only [ReferenceCheckedCopyLogStep.run, ReferenceCheckedCopyLogStep.afterPops]
  all_goals repeat' (split <;> try dsimp only)
  all_goals simp [resultMeter, Metadata, update]

theorem load (p : ReferenceStorageView.Parent) (v : View) (w : Warm) (m : Meter) :
    Metadata m (storageMeter (ReferenceCheckedStorageStep.load p v w m)) := by
  unfold ReferenceCheckedStorageStep.load
  repeat' (split <;> try dsimp only)
  all_goals simp [storageMeter, Metadata, update]

theorem store (ownerExists : Bool) (p : ReferenceStorageView.Parent) (v : View) (w : Warm) (m : Meter) :
    Metadata m (storageMeter (ReferenceCheckedStorageStep.store ownerExists p v w m)) := by
  classical
  unfold ReferenceCheckedStorageStep.store ReferenceCheckedStorageStep.storeAfterPop
  repeat' (split <;> try dsimp only)
  all_goals simp [storageMeter, Metadata, update]

theorem terminal (h : ReferenceCheckedTerminalStep.Halt) (v : View) (m : Meter) (o : ByteArray) :
    Metadata m (terminalMeter (ReferenceCheckedTerminalStep.run h v m o)) := by
  unfold ReferenceCheckedTerminalStep.run
  repeat' (split <;> try dsimp only)
  all_goals simp [terminalMeter, Metadata, update]

theorem handler (h : Handler) (d : List Nat) (ownerExists : Bool) (p : ReferenceStorageView.Parent)
    (v : View) (w : Warm) (m : Meter) (o : ByteArray) :
    Metadata m (outcomeMeter (runHandler h d ownerExists p v w m o)) := by
  cases h with
  | binary h =>
    have fact := binary h v m
    simp only [runHandler]
    split <;> simp_all [outcomeMeter, resultMeter]
  | environment h =>
    have fact := environment h v m
    simp only [runHandler]
    split <;> simp_all [outcomeMeter, resultMeter]
  | stackControl h =>
    have fact := stackControl h d v m
    simp only [runHandler]
    split <;> simp_all [outcomeMeter, resultMeter]
  | memoryStore b =>
    have fact := memoryStore b v m
    simp only [runHandler]
    split <;> simp_all [outcomeMeter, resultMeter]
  | copyLog h =>
    have fact := copyLog h v m
    simp only [runHandler]
    split <;> simp_all [outcomeMeter, resultMeter]
  | load =>
    have fact := load p v w m
    simp only [runHandler]
    split <;> simp_all [outcomeMeter, storageMeter]
  | store =>
    have fact := store ownerExists p v w m
    simp only [runHandler]
    split <;> simp_all [outcomeMeter, storageMeter]
  | terminal h =>
    have fact := terminal h v m o
    simp only [runHandler]
    split <;> simp_all [outcomeMeter, terminalMeter]

/-- Both fields survive the same actual outcome, including errors after credit,
execution/state payment, static LOG expansion, or the owner assertion. -/
theorem run_metadata {d : List Nat} {ownerExists : Bool} {p : ReferenceStorageView.Parent}
    {v : View} {w : Warm} {m : Meter} {o : ByteArray} {outcome : Outcome}
    (actual : run d ownerExists p v w m o = outcome) :
    (outcomeMeter outcome).baseline = m.baseline ∧
      (outcomeMeter outcome).committedSpill = m.committedSpill := by
  subst outcome
  unfold run
  split
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩
  · exact handler _ d ownerExists p v w m o

#print axioms binary
#print axioms environment
#print axioms stackControl
#print axioms memoryStore
#print axioms copyLog
#print axioms load
#print axioms store
#print axioms terminal
#print axioms handler
#print axioms run_metadata
end Eip8282.Audit.Integrator.ReferenceCheckedDispatchMetadata
