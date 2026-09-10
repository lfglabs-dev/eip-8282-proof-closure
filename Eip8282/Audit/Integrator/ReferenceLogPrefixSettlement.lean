import Eip8282.Audit.Integrator.ReferenceLogPrefixEvaluation
import Eip8282.Audit.Integrator.ReferenceCheckedFrameOutcome

/-! Transport full logs emitted inside a frame through source settlement.
`incoming` here is newly emitted by the current frame (e.g. its transfer LOG3),
not inherited parent logs. Thus the replay prefix passed to settle is empty.
A successful frame forwards this list once; a failed frame discards it while
preserving its internal execution observations. Ancestor commitment is separate.
-/
namespace Eip8282.Audit.Integrator.ReferenceLogPrefixSettlement
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceCheckedDispatch
open ReferenceCheckedFrameOutcome ReferenceLogPrefixHandlers
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def receipt (incoming : List LogEntry) (r : Receipt) : Receipt :=
  {r with beforeSettlement := view incoming r.beforeSettlement, logsForParent := if r.error.isNone then incoming++r.logsForParent else r.logsForParent}

def boundary (incoming : List LogEntry) : Boundary → Boundary
  | .returned r => .returned (receipt incoming r)
  | .uncaught e v w m o => .uncaught e (view incoming v) w m o
  | .unsupported t v w m o => .unsupported t (view incoming v) w m o
  | .running v w m e => .running (view incoming v) w m e

theorem settled (incoming : List LogEntry) (snapshot : ReferenceStorageView.Tx) (w : Warm) (r : Outcome) :
    settle snapshot [] w (outcome incoming r) = boundary incoming (settle snapshot [] w r) := by
  cases r <;> simp only [outcome,ending,settle]
  all_goals repeat' (split <;> try simp_all only [boundary,receipt,success,failure,view,List.length_nil,List.drop_zero,Option.isNone_none,Option.isNone_some,if_true,if_false])
  all_goals rfl

theorem successful (incoming : List LogEntry) (r : Receipt) (ok : r.error = none) :
    (receipt incoming r).logsForParent = incoming++r.logsForParent := by simp [receipt,ok]

theorem failed (incoming : List LogEntry) (r : Receipt) (error : Error) (bad : r.error = some error) :
    (receipt incoming r).logsForParent = r.logsForParent := by simp [receipt,bad]

theorem unchanged (incoming : List LogEntry) (r : Receipt) :
    (receipt incoming r).storage = r.storage ∧ (receipt incoming r).meter = r.meter ∧
    (receipt incoming r).output = r.output ∧ (receipt incoming r).error = r.error ∧
    (receipt incoming r).localWarm = r.localWarm ∧ (receipt incoming r).warmForParent = r.warmForParent :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms settled
#print axioms successful
#print axioms failed
#print axioms unchanged
end Eip8282.Audit.Integrator.ReferenceLogPrefixSettlement
