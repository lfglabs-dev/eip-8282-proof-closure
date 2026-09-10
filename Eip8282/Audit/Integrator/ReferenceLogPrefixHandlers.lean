import Eip8282.Audit.Integrator.ReferenceCheckedAccountEvaluator

/-! Prefixing the same incoming full log list commutes with literal checked
handlers, including partially executed failures. No operation reads the log
list; LOG0 appends after the incoming. Consumers: complete account-evaluator
transport and exhaustive source frame log receipt. -/
namespace Eip8282.Audit.Integrator.ReferenceLogPrefixHandlers
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option maxErrors 10

def view (incoming : List LogEntry) (v : View) : View := {v with logs := incoming++v.logs}

def pair {F : Type} (incoming : List LogEntry) : Except (F × View × Meter) (View × Meter) → Except (F × View × Meter) (View × Meter)
  | .error (e,v,m) => .error (e,view incoming v,m)
  | .ok (v,m) => .ok (view incoming v,m)

def storage (incoming : List LogEntry) : ReferenceCheckedStorageStep.Result → ReferenceCheckedStorageStep.Result
  | .error (e,v,w,m) => .error (e,view incoming v,w,m)
  | .ok (v,w,m) => .ok (view incoming v,w,m)

def ending (incoming : List LogEntry) (r : ReferenceCheckedTerminalStep.End) : ReferenceCheckedTerminalStep.End :=
  {r with view := view incoming r.view}

def terminalResult (incoming : List LogEntry) : Except ReferenceCheckedTerminalStep.Partial ReferenceCheckedTerminalStep.End → Except ReferenceCheckedTerminalStep.Partial ReferenceCheckedTerminalStep.End
  | .error (e,v,m,o) => .error (e,view incoming v,m,o)
  | .ok r => .ok (ending incoming r)

def outcome (incoming : List LogEntry) : Outcome → Outcome
  | .continued v w m e => .continued (view incoming v) w m e
  | .terminal r => .terminal (ending incoming r)
  | .eof v w m o => .eof (view incoming v) w m o
  | .failed f v w m o => .failed f (view incoming v) w m o
  | .unsupported t v w m o => .unsupported t (view incoming v) w m o

theorem binary (incoming : List LogEntry) (h : ReferenceWordOps.Binary) (v : View) (m : Meter) :
    ReferenceCheckedBinaryStep.run h (view incoming v) m = pair incoming (ReferenceCheckedBinaryStep.run h v m) := by
  simp only [ReferenceCheckedBinaryStep.run,view,pair]
  repeat' (split <;> try dsimp only [pair,view])

theorem environment (incoming : List LogEntry) (h : ReferenceCheckedEnvironmentStep.Handler) (v : View) (m : Meter) :
    ReferenceCheckedEnvironmentStep.run h (view incoming v) m = pair incoming (ReferenceCheckedEnvironmentStep.run h v m) := by
  cases h <;> simp only [ReferenceCheckedEnvironmentStep.run,ReferenceCheckedEnvironmentStep.finish,view,pair]
  all_goals repeat' (split <;> try dsimp only [pair,view])

theorem memoryStore (incoming : List LogEntry) (byte : Bool) (v : View) (m : Meter) :
    ReferenceCheckedMemoryStore.run byte (view incoming v) m = pair incoming (ReferenceCheckedMemoryStore.run byte v m) := by
  simp only [ReferenceCheckedMemoryStore.run,view,pair]
  repeat' (split <;> try dsimp only [pair,view])

theorem copyLog (incoming : List LogEntry) (h : ReferenceCheckedCopyLogStep.Handler) (v : View) (m : Meter) :
    ReferenceCheckedCopyLogStep.run h (view incoming v) m = pair incoming (ReferenceCheckedCopyLogStep.run h v m) := by
  cases h <;> simp only [ReferenceCheckedCopyLogStep.run,ReferenceCheckedCopyLogStep.afterPops,
    ReferenceCheckedCopyLogStep.price,ReferenceCheckedCopyLogStep.copied,ReferenceCheckedCopyLogStep.logged,
    ReferenceCheckedCopyLogStep.expanded,view,pair,List.append_assoc]
  all_goals repeat' (split <;> try dsimp only [pair,view])

theorem load (incoming : List LogEntry) (p : ReferenceStorageView.Parent) (v : View) (w : Warm) (m : Meter) :
    ReferenceCheckedStorageStep.load p (view incoming v) w m = storage incoming (ReferenceCheckedStorageStep.load p v w m) := by
  cases hp : ReferenceSourceStackAdmission.pop v.stack with
  | error e => simp [ReferenceCheckedStorageStep.load,view,hp,storage]
  | ok popped =>
    rcases popped with ⟨rest,key⟩
    unfold ReferenceCheckedStorageStep.load
    simp only [show (view incoming v).stack = v.stack from rfl,hp]
    have access : ReferenceCheckedStorageStep.access (view incoming v) key w = ReferenceCheckedStorageStep.access v key w := rfl
    rw [access]
    cases hc : ReferenceStorageGas.chargeExecution (ReferenceMeterBoundary.core m) (ReferenceCheckedStorageStep.access v key w) with
    | none => rfl
    | some charged =>
      dsimp only [view]
      cases hs : ReferenceSourceStackAdmission.push (ReferenceStorageView.current p v.storage v.env.codeOwner key.toByteArray) rest <;> rfl

theorem store (incoming : List LogEntry) (owner : Bool) (p : ReferenceStorageView.Parent) (v : View) (w : Warm) (m : Meter) :
    ReferenceCheckedStorageStep.store owner p (view incoming v) w m = storage incoming (ReferenceCheckedStorageStep.store owner p v w m) := by
  simp only [ReferenceCheckedStorageStep.store,ReferenceCheckedStorageStep.storeAfterPop,ReferenceCheckedStorageStep.access,view,storage]
  repeat' (split <;> try simp_all only [])

theorem terminal (incoming : List LogEntry) (h : ReferenceCheckedTerminalStep.Halt) (v : View) (m : Meter) (o : ByteArray) :
    ReferenceCheckedTerminalStep.run h (view incoming v) m o = terminalResult incoming (ReferenceCheckedTerminalStep.run h v m o) := by
  simp only [ReferenceCheckedTerminalStep.run,ReferenceCheckedCopyLogStep.expanded,view,terminalResult,ending]
  repeat' (split <;> try dsimp only [terminalResult,ending,view])

def prepared (incoming : List LogEntry) : Except (ReferenceCheckedStackControlStep.Failure × View) (View × List UInt256) → Except (ReferenceCheckedStackControlStep.Failure × View) (View × List UInt256)
  | .error (e,v) => .error (e,view incoming v)
  | .ok (v,xs) => .ok (view incoming v,xs)

theorem prepare (incoming : List LogEntry) (h : ReferenceCheckedStackControlStep.Handler) (v : View) :
    ReferenceCheckedStackControlStep.prepare h (view incoming v) = prepared incoming (ReferenceCheckedStackControlStep.prepare h v) := by
  simp only [ReferenceCheckedStackControlStep.prepare,view,prepared]
  repeat' (split <;> try simp_all only [])

def operated (incoming : List LogEntry) : Except ReferenceCheckedStackControlStep.Failure View → Except ReferenceCheckedStackControlStep.Failure View
  | .error e => .error e
  | .ok v => .ok (view incoming v)

theorem operate (incoming : List LogEntry) (h : ReferenceCheckedStackControlStep.Handler) (d : List Nat) (v : View) (xs : List UInt256) :
    ReferenceCheckedStackControlStep.operate h d (view incoming v) xs = operated incoming (ReferenceCheckedStackControlStep.operate h d v xs) := by
  cases h <;> simp only [ReferenceCheckedStackControlStep.operate,ReferenceCheckedStackControlStep.family,
    ReferenceCheckedStackControlStep.push_definition,view,operated]
  all_goals repeat' (split <;> try simp_all only [])

theorem stackControl (incoming : List LogEntry) (h : ReferenceCheckedStackControlStep.Handler) (d : List Nat) (v : View) (m : Meter) :
    ReferenceCheckedStackControlStep.run h d (view incoming v) m = pair incoming (ReferenceCheckedStackControlStep.run h d v m) := by
  unfold ReferenceCheckedStackControlStep.run
  rw [prepare]
  cases hp : ReferenceCheckedStackControlStep.prepare h v with
  | error e => rcases e with ⟨e,mid⟩; rfl
  | ok vp =>
    rcases vp with ⟨mid,xs⟩
    dsimp only [prepared]
    cases hc : ReferenceStorageGas.chargeExecution (ReferenceMeterBoundary.core m) (ReferenceCheckedStackControlStep.charge h) with
    | none => rfl
    | some charged =>
      rw [operate]
      cases ReferenceCheckedStackControlStep.operate h d mid xs <;> rfl

#print axioms binary
#print axioms environment
#print axioms memoryStore
#print axioms copyLog
#print axioms load
#print axioms store
#print axioms terminal
#print axioms prepare
#print axioms operate
#print axioms stackControl
end Eip8282.Audit.Integrator.ReferenceLogPrefixHandlers
