import Eip8282.Audit.Integrator.FrameEvents
import Eip8282.Audit.Integrator.AppendGasPath

/-!
# Audited append sites in the unique actual frame event list

The previously extracted bytecode LOG paths now select actual event occurrences
in the same X execution. This is the local injection edge; global distinct call
paths and nested event aggregation remain separate obligations.
-/
namespace Eip8282.Audit.Integrator.AppendEvents
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall jumpdestsOf)
open FrameEvents
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

/-- A path's actual LOG0 belongs to every certificate of this same frame. -/
theorem path_occurrence {kind : Eip8282.Audit.Model.Kind} (q : XiCall kind) (len : UInt256)
    (hlen : 68 ≤ len.toNat) (path : ActualAppendGas.LogPath q len)
    {result : Except ExecutionException (ExecutionResult EVM.State)} {events : List Nat}
    (trace : FrameEvents.Trace (jumpdestsOf kind) q.fuel q.entry result events) :
    ∃ occurrence, occurrence ∈ events := by
  obtain ⟨atLog,afterLog,finish,fLog,fFinish,cost,beforeLabels,afterLabels,off,stk,
    before,_,decoded,stack,step,_,_,_,_⟩ := path
  have marked : FrameEvents.Marked atLog := by
    refine ⟨congrArg Prod.fst decoded, ?_⟩
    simpa only [stack, List.getD_cons_succ, List.getD_cons_zero] using hlen
  exact ⟨fLog,FrameEvents.contains_site trace before step marked⟩

/-- Actual successful exit submission supplies its event, without an assumed
path, quote completion, storage invariant or gas bound. -/
theorem exit_occurrence (q : XiCall .exit)
    (huser : q.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hsize : q.env.calldata.size = 48)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (executed : q.result = .ok (.success (created,world,gas,substate) out))
    {result : Except ExecutionException (ExecutionResult EVM.State)} {events : List Nat}
    (trace : FrameEvents.Trace (jumpdestsOf .exit) q.fuel q.entry result events) :
    ∃ occurrence, occurrence ∈ events :=
  path_occurrence q (UInt256.ofNat 68) (by decide)
    (AppendGasPath.exit_log_path q huser hsize executed) trace

/-- Actual successful deposit submission supplies its own 184-byte event. -/
theorem deposit_occurrence (q : XiCall .deposit)
    (huser : q.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hsize : q.env.calldata.size = 184)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (executed : q.result = .ok (.success (created,world,gas,substate) out))
    {result : Except ExecutionException (ExecutionResult EVM.State)} {events : List Nat}
    (trace : FrameEvents.Trace (jumpdestsOf .deposit) q.fuel q.entry result events) :
    ∃ occurrence, occurrence ∈ events :=
  path_occurrence q (UInt256.ofNat 184) (by decide)
    (AppendGasPath.deposit_log_path q huser hsize executed) trace

/-- The event list is extracted from the actual evaluator and contains the
site of this successful audited append. Distinctness is local to this frame. -/
theorem successful_events {kind : Eip8282.Audit.Model.Kind} (q : XiCall kind)
    (huser : q.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hsize : q.env.calldata.size = match kind with | .deposit => 184 | .exit => 48)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (executed : q.result = .ok (.success (created,world,gas,substate) out)) :
    ∃ events, FrameEvents.Trace (jumpdestsOf kind) q.fuel q.entry
        (X q.fuel (jumpdestsOf kind) q.entry) events ∧ events.Nodup ∧
      (∃ occurrence, occurrence ∈ events) ∧
      FrameEvents.residual (X q.fuel (jumpdestsOf kind) q.entry) +
        919*events.length ≤ q.entry.gasAvailable.toNat := by
  obtain ⟨events,ht,hd,hg⟩ := FrameEvents.extracted_bound (jumpdestsOf kind) q.fuel q.entry
  refine ⟨events,ht,hd,?_,hg⟩
  cases kind with
  | deposit => exact deposit_occurrence q huser hsize executed ht
  | exit => exact exit_occurrence q huser hsize executed ht

#print axioms path_occurrence
#print axioms exit_occurrence
#print axioms deposit_occurrence
#print axioms successful_events
end Eip8282.Audit.Integrator.AppendEvents
