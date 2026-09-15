import Eip8282.Audit.Integrator.Topics.ReferenceChecked

/-! Source frame settlement for the represented storage/log/resource projection.
Pinned process_call455–474 restores state gas before exceptional forfeiture,
preserves REVERT output, and restores transaction writes on both caught errors.
Internal evm.logs are NOT cleared: process_top_level295–325 and
incorporate_child244–249 suppress their contribution when error is present.
state_tracker752–771 restores writes, but created/read metadata remain live.

The snapshot is the actual pre-message storage projection, not an arbitrary
replacement post-state. Binding that snapshot and the full account/code/
transient-state rollback is still the actual source journal producer's job.
View.logs includes the fixed incoming replay prefix. The prefix is removed
from successful parent contributions so inherited logs are never added twice.
The source log-context producer must identify this prefix with the same frame.
Eligible logs below are local frame contributions, not globally committed
records; ancestor rollback may still discard them. Actual frame log/initial
world bindings remain open. Uncaught conversion/assertion and unsupported
opcodes are not turned into failed EVM receipts. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedFrameOutcome
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceMeterBoundary ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

inductive Error where
  | reverted
  | exceptional (fault : Fault)

structure Receipt where
  beforeSettlement : View
  storage : ReferenceStorageView.Tx
  localWarm : Warm
  meter : Meter
  output : ByteArray
  error : Option Error
  logsForParent : List LogEntry
  warmForParent : Option Warm

/-- These are the represented fields of a successful returned local frame;
being eligible for incorporation is not surviving every enclosing frame. -/
def success (incomingLogs : List LogEntry) (v : View) (warm : Warm) (meter : Meter) (output : ByteArray) : Receipt :=
  ⟨v,v.storage,warm,meter,output,none,v.logs.drop incomingLogs.length,some warm⟩

/-- Preserve the exact internal error view for executed-effect accounting;
only the write overlay is restored in this storage projection. -/
def failure (snapshot : ReferenceStorageView.Tx) (v : View) (warm : Warm)
    (meter : Meter) (output : ByteArray) (error : Error) : Receipt :=
  ⟨v,ReferenceStorageView.rollback v.storage snapshot,warm,meter,output,some error,[],none⟩

inductive Boundary where
  | returned (receipt : Receipt)
  | uncaught (fault : Fault) (v : View) (warm : Warm) (meter : Meter) (output : ByteArray)
  | unsupported (tag : UInt8) (v : View) (warm : Warm) (meter : Meter) (output : ByteArray)
  | running (v : View) (warm : Warm) (meter : Meter) (event : Event)

/-- The fixed replay prefix is not emitted again when this frame returns. -/
theorem success_logs (incomingLogs localLogs : List LogEntry) (v : View) (warm : Warm)
    (meter : Meter) (output : ByteArray) (bound : v.logs = incomingLogs++localLogs) :
    (success incomingLogs v warm meter output).logsForParent = localLogs := by
  simp only [success,bound,List.drop_left]

/-- Classify before settling. terminalWarm is the same running-prefix warmth
at the final dispatcher call; the computed-evaluation consumers derive it. -/
def settle (snapshot : ReferenceStorageView.Tx) (incomingLogs : List LogEntry) (terminalWarm : Warm) : Outcome → Boundary
  | .terminal result =>
    if result.halt = .reverted then
      .returned (failure snapshot result.view terminalWarm
        (ReferenceChildMeter.settle .reverted result.meter) result.output .reverted)
    else .returned (success incomingLogs result.view terminalWarm result.meter result.output)
  | .eof v warm meter output => .returned (success incomingLogs v warm meter output)
  | .failed fault v warm meter output =>
    if ReferenceCheckedFaultClass.caught fault then
      .returned (failure snapshot v warm (ReferenceChildMeter.settle .exceptional meter)
        ByteArray.empty (.exceptional fault))
    else .uncaught fault v warm meter output
  | .unsupported tag v warm meter output => .unsupported tag v warm meter output
  | .continued v warm meter event => .running v warm meter event

/-- Caught exceptional failure forfeits execution only after state-gas restore,
returns no logs/access warming to its parent, and restores all storage keys. -/
theorem failed (snapshot : ReferenceStorageView.Tx) (incomingLogs : List LogEntry) (terminalWarm warm : Warm)
    (fault : Fault) (v : View) (meter : Meter) (output : ByteArray)
    (caught : ReferenceCheckedFaultClass.caught fault = true) :
    ∃ receipt,
      settle snapshot incomingLogs terminalWarm (.failed fault v warm meter output) = .returned receipt ∧
      receipt.beforeSettlement = v ∧ receipt.output = ByteArray.empty ∧
      receipt.meter.execution = 0 ∧ receipt.meter.reservoir = meter.baseline ∧
      receipt.meter.spill = 0 ∧ receipt.meter.refund = 0 ∧
      receipt.meter.committedSpill = meter.committedSpill ∧
      receipt.logsForParent = [] ∧ receipt.warmForParent = none ∧
      receipt.storage.created = v.storage.created ∧ receipt.storage.reads = v.storage.reads ∧
      ∀ parent address key, ReferenceStorageView.current parent receipt.storage address key =
        ReferenceStorageView.current parent snapshot address key := by
  refine ⟨failure snapshot v warm (ReferenceChildMeter.settle .exceptional meter) ByteArray.empty (.exceptional fault),?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  · simp only [settle,caught,if_true]
  · intro parent address key
    exact ReferenceStorageView.rollback_current parent v.storage snapshot address key

/-- Uncaught builtin faults preserve their partial state here; this catch
boundary does not justify either an EVM receipt or restoration for them. -/
theorem uncaught (snapshot : ReferenceStorageView.Tx) (incomingLogs : List LogEntry) (terminalWarm warm : Warm)
    (fault : Fault) (v : View) (meter : Meter) (output : ByteArray)
    (notCaught : ReferenceCheckedFaultClass.caught fault = false) :
    settle snapshot incomingLogs terminalWarm (.failed fault v warm meter output) = .uncaught fault v warm meter output := by
  simp only [settle,notCaught,Bool.false_eq_true,if_false]

/-- REVERT keeps output and returns remaining execution plus restored spill;
its log contribution is discarded but its internal observations are retained. -/
theorem reverted (snapshot : ReferenceStorageView.Tx) (incomingLogs : List LogEntry) (warm : Warm)
    (result : ReferenceCheckedTerminalStep.End) (halt : result.halt = .reverted) :
    ∃ receipt,
      settle snapshot incomingLogs warm (.terminal result) = .returned receipt ∧
      receipt.beforeSettlement = result.view ∧ receipt.output = result.output ∧
      receipt.meter = restore result.meter ∧ receipt.logsForParent = [] ∧ receipt.warmForParent = none ∧
      ∀ parent address key, ReferenceStorageView.current parent receipt.storage address key =
        ReferenceStorageView.current parent snapshot address key := by
  refine ⟨failure snapshot result.view warm (restore result.meter) result.output .reverted,?_,rfl,rfl,rfl,rfl,rfl,?_⟩
  · simp only [settle,halt,if_true,ReferenceChildMeter.settle]
  · intro parent address key
    exact ReferenceStorageView.rollback_current parent result.view.storage snapshot address key

/-- Couple the actual evaluated failing opcode, including its partial effects,
to this settlement. The same successful running prefix is kept for executed
work accounting; it is never identified with persistent queue records. -/
theorem failed_evaluation {kind : Kind} {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {previousOutput : ByteArray} {fuel : Nat}
    {v failedView : View} {warm partialWarm : Warm} {meter partialMeter : Meter}
    {events : List Event} {fault : Fault} {partialOutput : ByteArray}
    (snapshot : ReferenceStorageView.Tx) (incomingLogs : List LogEntry)
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent previousOutput fuel v warm meter =
      some (events,.failed fault failedView partialWarm partialMeter partialOutput))
    (caught : ReferenceCheckedFaultClass.caught fault = true) :
    ∃ finish finalWarm final,
      ReferenceCheckedRuntimeTrace.Run kind parent v warm meter finish finalWarm final events ∧
      ReferenceCheckedDispatch.run destinations ownerExists parent finish finalWarm final previousOutput =
        .failed fault failedView partialWarm partialMeter partialOutput ∧
      settle snapshot incomingLogs finalWarm (.failed fault failedView partialWarm partialMeter partialOutput) =
        .returned (failure snapshot failedView partialWarm (ReferenceChildMeter.settle .exceptional partialMeter)
          ByteArray.empty (.exceptional fault)) := by
  obtain ⟨finish,finalWarm,final,trace,last,_⟩ := ReferenceCheckedEvaluator.extract context actual
  refine ⟨finish,finalWarm,final,trace,last,?_⟩
  simp only [settle,caught,if_true]

#print axioms success_logs
#print axioms failed
#print axioms uncaught
#print axioms reverted
#print axioms failed_evaluation
end Eip8282.Audit.Integrator.ReferenceCheckedFrameOutcome
