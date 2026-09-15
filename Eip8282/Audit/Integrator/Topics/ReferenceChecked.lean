import Eip8282.Audit.Integrator.Topics.Reference
import Eip8282.Audit.Integrator.ReferenceCheckedCompletion
import Eip8282.Audit.Integrator.ReferenceCheckedDispatch
import Eip8282.Audit.Integrator.ReferenceCheckedEvaluator
import Eip8282.Audit.Integrator.ReferenceCheckedPureForward
import Eip8282.Audit.Integrator.ReferenceCheckedRuntimeTrace
import Eip8282.Audit.Integrator.ReferenceNestedSourceAppend
import Eip8282.Audit.Integrator.Topics.ReferenceSource2

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceCheckedPrefix -/

/-! Resource and context facts at the final dispatcher input of the same
computed evaluation, including failed evaluations. No caught-fault or successful
terminal hypothesis is used. These facts discharge source checked conversions;
the actual source account-presence binding remains separate from old HasOwner.
-/
namespace Eip8282.Audit.Integrator.ReferenceCheckedPrefix
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceCheckedDispatch ReferencePureAction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem family_env {kind : Kind} {v next : View} {arg : Option (UInt256 × Nat)}
    (p : Pure) (effect : familyAction kind p arg v = some next) : next.env = v.env := by
  cases p <;> simp only [familyAction] at effect
  all_goals repeat' first | split at effect | cases effect
  all_goals rfl

private theorem pure_env {kind : Kind} {instr : Instruction} {v next : View}
    (effect : action kind instr v = some next) : next.env = v.env := by
  unfold action at effect
  cases selected : classify instr.1 with
  | none => simp only [selected,Option.bind_none] at effect; contradiction
  | some p =>
    simp only [selected,Option.bind_some] at effect
    exact family_env p effect

theorem action_env {kind : Kind} {parent : ReferenceStorageView.Parent}
    {instr : Instruction} {v next : View}
    (actual : ReferenceRuntimeAction.Action kind parent instr v next) : next.env = v.env := by
  cases actual with
  | base base =>
    cases base with
    | pure effect => exact pure_env effect
    | load => rfl
    | store => rfl
    | word => rfl
    | byte => rfl
  | copy => rfl
  | log => rfl

theorem trace_env {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v finish : View} {warm finalWarm : Warm} {meter final : Meter} {events : List Event}
    (actual : ReferenceCheckedRuntimeTrace.Run kind parent v warm meter finish finalWarm final events)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v) :
    finish.env = v.env := by
  induction actual with
  | refl => rfl
  | cons step tail ih =>
    obtain ⟨action,_,_,_,nextStack⟩ := step.sound stack aligned
    exact (ih nextStack (ReferenceActionMemoryBounds.preserves_alignment action aligned)).trans (action_env action)

/-- Derive both conversion bounds before the last dispatcher runs. The
result may be a fault, EOF, unsupported, or a successful terminal. -/
theorem evaluated_bounds {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm : Warm} {pre : Meter} {fuel : Nat}
    {events : List Event} {result : Outcome} {destinations : List Nat} {ownerExists : Bool}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent ByteArray.empty fuel
      (initial c tx) warm pre = some (events,result))
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (cdfit : c.env.calldata.size < UInt256.size) :
    ∃ finish finalWarm final post,
      run destinations ownerExists parent finish finalWarm final ByteArray.empty = result ∧
      Related parent finish post ∧ RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) post ∧
      finish.env = c.env ∧ finish.env.calldata.size < UInt256.size ∧ finish.pc+1 < UInt256.size := by
  obtain ⟨finish,finalWarm,final,trace,last,_⟩ := ReferenceCheckedEvaluator.extract context actual
  have stack : (initial c tx).stack.length ≤ 1024 := by simp [initial]
  have aligned := ReferenceActionMemoryBounds.empty_aligned (initial c tx) rfl
  have env := trace_env trace stack aligned
  obtain ⟨source,paid,_⟩ := trace.extract stack aligned
  have payment := ReferenceExecutionLedger.bounded (.paid _ paid)
  have bound : ReferenceExecutionLedger.work events+0 ≤ 30000000 := by omega
  obtain ⟨post,_,_,related,site,_⟩ := ReferenceSourceReplayEntry.from_entry c 0 source slots owner warmRelated bound
  refine ⟨finish,finalWarm,final,post,last,related,site,env,?_,?_⟩
  · rw [env]; exact cdfit
  · have fit := ReferenceRuntimeSites.pc_fit site
    rw [related.pc]
    omega

#print axioms action_env
#print axioms trace_env
#print axioms evaluated_bounds
end Eip8282.Audit.Integrator.ReferenceCheckedPrefix

end

section

/-! ## ReferenceCheckedAccountDispatch -/

/-! Bind the SSTORE assertion boolean to the literal optional-account lookup.
The pure peek is not a recorded source read: reads are added only when the
last, post-charge assertion is reached. No account payload/write changes in a
protected instruction. This supplies a concrete account-presence adapter for
checked dispatch; it does not establish deployment or a canonical account map.
-/
namespace Eip8282.Audit.Integrator.ReferenceCheckedAccountDispatch
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- SSTORE reads the optional owner only after all guards and gas charges.
A successful store or its missing-owner assertion reaches that read. -/
def assertionReached (selected : Dispatch) (outcome : Outcome) : Bool :=
  match selected,outcome with
  | .handler .store,.continued .. => true
  | .handler .store,.failed (.storage .missingOwnerAssertion) .. => true
  | _,_ => false

noncomputable def run {Account : Type} (accountsParent : ReferenceAccountLookup.Parent Account)
    (accounts : ReferenceAccountLookup.Tx Account) (destinations : List Nat)
    (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm) (meter : Meter)
    (output : ByteArray) : Outcome × ReferenceAccountLookup.Tx Account :=
  let result := ReferenceCheckedDispatch.run destinations
    (ReferenceAccountLookup.peek accountsParent accounts v.env.codeOwner).isSome parent v warm meter output
  (result,if assertionReached (read v.env.code v.pc) result
    then ReferenceAccountLookup.tracked accounts v.env.codeOwner else accounts)

theorem result {Account : Type} (accountsParent : ReferenceAccountLookup.Parent Account)
    (accounts : ReferenceAccountLookup.Tx Account) (destinations : List Nat)
    (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm) (meter : Meter) (output : ByteArray) :
    (run accountsParent accounts destinations parent v warm meter output).1 =
    ReferenceCheckedDispatch.run destinations
      (ReferenceAccountLookup.peek accountsParent accounts v.env.codeOwner).isSome parent v warm meter output := rfl

/-- No account write, including a deletion, is hidden by the presence adapter. -/
theorem writes {Account : Type} (accountsParent : ReferenceAccountLookup.Parent Account)
    (accounts : ReferenceAccountLookup.Tx Account) (destinations : List Nat)
    (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm) (meter : Meter) (output : ByteArray) :
    (run accountsParent accounts destinations parent v warm meter output).2.writes = accounts.writes := by
  unfold run
  dsimp only
  split <;> rfl

/-- Presence at every address is unchanged, including an explicit deletion. -/
theorem lookup {Account : Type} (accountsParent : ReferenceAccountLookup.Parent Account)
    (accounts : ReferenceAccountLookup.Tx Account) (destinations : List Nat)
    (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm) (meter : Meter) (output : ByteArray)
    (a : AccountAddress) :
    ReferenceAccountLookup.peek accountsParent
      (run accountsParent accounts destinations parent v warm meter output).2 a =
      ReferenceAccountLookup.peek accountsParent accounts a := by
  unfold ReferenceAccountLookup.peek
  rw [writes]

/-- Same continued result supplies environment preservation. This identifies
which lookup is used by the next instruction; no independent owner Bool. -/
theorem continued {Account : Type} {accountsParent : ReferenceAccountLookup.Parent Account}
    {accounts nextAccounts : ReferenceAccountLookup.Tx Account} {kind : Kind}
    {destinations : List Nat} {parent : ReferenceStorageView.Parent}
    {v next : View} {warm nextWarm : Warm} {meter nextMeter : Meter} {output : ByteArray} {event : Event}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : run accountsParent accounts destinations parent v warm meter output =
      (.continued next nextWarm nextMeter event,nextAccounts))
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v) :
    next.env = v.env ∧ next.stack.length ≤ 1024 ∧ ReferenceActionMemoryBounds.Aligned next ∧
      ReferenceAccountLookup.peek accountsParent nextAccounts next.env.codeOwner =
        ReferenceAccountLookup.peek accountsParent accounts v.env.codeOwner := by
  have checked := congrArg Prod.fst actual
  rw [result] at checked
  obtain ⟨action,_,_,_,nextStack⟩ := (ReferenceCheckedDispatch.step context checked).sound stack aligned
  have env := ReferenceCheckedPrefix.action_env action
  refine ⟨env,nextStack,ReferenceActionMemoryBounds.preserves_alignment action aligned,?_⟩
  have same := lookup accountsParent accounts destinations parent v warm meter output v.env.codeOwner
  rw [actual] at same
  simpa only [env] using same

#print axioms result
#print axioms writes
#print axioms lookup
#print axioms continued
end Eip8282.Audit.Integrator.ReferenceCheckedAccountDispatch

end

section

/-! ## ReferenceCheckedAppend -/

/-! Existing nested append consumer now takes one literal checked handler
history. Intermediate source Actions, Price, stack/memory alignment and the
entire payment sequence are derived, including zero-cost STOP. The numerical
entry cap comes from the same surrounding resource ledger's root allocation.
Actual source frame identity/global occurrence coverage and initial world/code/
owner/warm bindings remain distinct producers; EntryAt is not a unique path.
This does not assert success or canonical reachability of a chosen input call. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedAppend
open EvmYul EvmYul.EVM
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceMeterBoundary ReferenceExecutionLedger
open ReferenceResourceEntryBound ReferenceSelectedAppendWork
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private theorem stop_payment {events : List Event} {pre post : Meter}
    (paid : runFull events pre = some post) : runFull (events++[.ordinary 0]) pre = some post := by
  rw [ReferenceCheckedRuntimeTrace.runFull_append,paid,Option.bind_some]
  simp [runFull,ReferenceMeterPath.run,pay,ReferenceStorageGas.chargeExecution,core,update]

theorem exit (c : XiCall .exit) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    {pre post : Meter}
    (actual : ReferenceCheckedRuntimeTrace.Run .exit parent (initial c tx) warm pre finish finalWarm post events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (halt : ReferenceSourceReplayTrace.instruction finish = (.STOP,none))
    (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 48)
    {txGas intrinsic totalWork : Nat} {final : Meter}
    (located : EntryAt (ReferenceTransactionWork.initial txGas intrinsic) final totalWork pre) :
    ProtectedPaid pre post (work events) := by
  obtain ⟨source,paid,_⟩ := actual.extract (by simp [initial])
    (ReferenceActionMemoryBounds.empty_aligned _ rfl)
  exact ReferenceNestedSourceAppend.exit c source slots owner warmRelated halt user size located (stop_payment paid)

theorem deposit (c : XiCall .deposit) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    {pre post : Meter}
    (actual : ReferenceCheckedRuntimeTrace.Run .deposit parent (initial c tx) warm pre finish finalWarm post events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (halt : ReferenceSourceReplayTrace.instruction finish = (.STOP,none))
    (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 184)
    {txGas intrinsic totalWork : Nat} {final : Meter}
    (located : EntryAt (ReferenceTransactionWork.initial txGas intrinsic) final totalWork pre) :
    ProtectedPaid pre post (work events) := by
  obtain ⟨source,paid,_⟩ := actual.extract (by simp [initial])
    (ReferenceActionMemoryBounds.empty_aligned _ rfl)
  exact ReferenceNestedSourceAppend.deposit c source slots owner warmRelated halt user size located (stop_payment paid)

#print axioms exit
#print axioms deposit
end Eip8282.Audit.Integrator.ReferenceCheckedAppend

end

section

/-! ## ReferenceCheckedFaultClass -/

/-! Checked-handler fault classification at the audited Python catch boundary.
EL 0cc100eb, archived in direct-reference-amsterdam-gas-sources-20260910.json:
vm/exceptions.py lines 35–98, SHA256
 e3e4b0b24c5b5702a64851d2ac675d1d2fc526aa3f1a439b17d5c2d22c569a01;
vm/interpreter.py lines 443–474, SHA256
 8281535f92be8cfe663033716baf9418ffc37b6c8861f70ac357e41fb6cf4c82.
Only ExceptionalHalt and Revert are caught around instruction execution.
The Ops ValueError is translated locally to InvalidOpcode, not all ValueErrors.
Checked U256 construction raises builtin OverflowError (ethereum-types 0.4.1,
numeric.py, SHA256 47d040d4de043e46d19c2fd9f74b318396b6c83ab01fe346f98a3c477e58db46,
archived in direct-reference-checked-types-sources-20260910.json).
The owner assertion in state_tracker.py line 454 raises builtin AssertionError
(SHA256 ce420ad5682df9051178d298220d1552448e26c37f67be3b604b9f493541cf4a).
Neither builtin exception inherits the source ExceptionalHalt class.

This is a classification of all represented checked faults, not a mechanical
Python extraction theorem or a proof that arbitrary inputs avoid host failures.
Uncaught means not caught by this process_call boundary, not by every caller.
REVERT is a separate terminal result, not a Fault. EOF, unsupported and proof
fuel exhaustion are also not Faults. No rollback or gas forfeiture is performed
or inferred here; the consumer must bind this classification to the same actual
failure and preserve its partial state before source settlement. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedFaultClass
open ReferenceCheckedDispatch
set_option autoImplicit false

inductive SourceException where
  | stackUnderflow | stackOverflow | outOfGas | invalidJump
  | staticWrite | invalidOpcode | conversionOverflow | ownerAssertion
  deriving DecidableEq, Repr

inductive CatchClass where
  | exceptionalHalt | uncaughtConversion | uncaughtAssertion
  deriving DecidableEq, Repr

def binary : ReferenceCheckedBinaryStep.Failure → SourceException
  | .stack .underflow => .stackUnderflow
  | .stack .overflow => .stackOverflow
  | .outOfGas => .outOfGas

/-- Exhaustive mapping of the represented failures; no default OOG branch. -/
def classify : Fault → SourceException
  | .binary e => binary e
  | .environment (.checked e) => binary e
  | .environment .conversionOverflow => .conversionOverflow
  | .stackControl (.checked e) => binary e
  | .stackControl .conversionOverflow => .conversionOverflow
  | .stackControl .invalidJump => .invalidJump
  | .storage (.checked e) => binary e
  | .storage .staticWrite => .staticWrite
  | .storage .missingOwnerAssertion => .ownerAssertion
  | .copyLog (.checked e) => binary e
  | .copyLog .staticWrite => .staticWrite
  | .invalidOpcode _ => .invalidOpcode

def catchClass : SourceException → CatchClass
  | .conversionOverflow => .uncaughtConversion
  | .ownerAssertion => .uncaughtAssertion
  | _ => .exceptionalHalt

def caught (fault : Fault) : Bool :=
  decide (catchClass (classify fault) = .exceptionalHalt)

/-- Precisely the three represented uncaught constructors, independent of any
source reachability or account-initialization premise. -/
theorem caught_iff (fault : Fault) : caught fault = true ↔
    fault ≠ .environment .conversionOverflow ∧
    fault ≠ .stackControl .conversionOverflow ∧
    fault ≠ .storage .missingOwnerAssertion := by
  cases fault with
  | binary e => cases e with
    | stack e => cases e <;> simp [caught, catchClass, classify, binary]
    | outOfGas => simp [caught, catchClass, classify, binary]
  | environment e => cases e with
    | checked e => cases e with
      | stack e => cases e <;> simp [caught, catchClass, classify, binary]
      | outOfGas => simp [caught, catchClass, classify, binary]
    | conversionOverflow => simp [caught, catchClass, classify]
  | stackControl e => cases e with
    | checked e => cases e with
      | stack e => cases e <;> simp [caught, catchClass, classify, binary]
      | outOfGas => simp [caught, catchClass, classify, binary]
    | conversionOverflow => simp [caught, catchClass, classify]
    | invalidJump => simp [caught, catchClass, classify]
  | storage e => cases e with
    | checked e => cases e with
      | stack e => cases e <;> simp [caught, catchClass, classify, binary]
      | outOfGas => simp [caught, catchClass, classify, binary]
    | staticWrite => simp [caught, catchClass, classify]
    | missingOwnerAssertion => simp [caught, catchClass, classify]
  | copyLog e => cases e with
    | checked e => cases e with
      | stack e => cases e <;> simp [caught, catchClass, classify, binary]
      | outOfGas => simp [caught, catchClass, classify, binary]
    | staticWrite => simp [caught, catchClass, classify]
  | invalidOpcode tag => simp [caught, catchClass, classify]

theorem conversion_classes :
    catchClass (classify (.environment .conversionOverflow)) = .uncaughtConversion ∧
    catchClass (classify (.stackControl .conversionOverflow)) = .uncaughtConversion := by
  exact ⟨rfl,rfl⟩

theorem assertion_class :
    catchClass (classify (.storage .missingOwnerAssertion)) = .uncaughtAssertion := rfl

theorem caught_class (fault : Fault) : caught fault = true ↔
    catchClass (classify fault) = .exceptionalHalt := by
  simp only [caught, decide_eq_true_eq]

#print axioms caught_iff
#print axioms conversion_classes
#print axioms assertion_class
#print axioms caught_class
end Eip8282.Audit.Integrator.ReferenceCheckedFaultClass

end

section

/-! ## ReferenceCheckedConversionSafety -/

/-! Input bounds, not a desired caught-fault hypothesis, exclude the two
represented U256 host conversion errors. CALLDATASIZE checks calldata length;
PUSH checks pc+1 after prefix pops and gas payment. Both use checked conversion
in source order. The account assertion is a separate code-fetch obligation.
-/
namespace Eip8282.Audit.Integrator.ReferenceCheckedConversionSafety
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem environment_no_conversion {h : ReferenceCheckedEnvironmentStep.Handler}
    {v next : View} {meter final : Meter} (fit : v.env.calldata.size < UInt256.size) :
    ReferenceCheckedEnvironmentStep.run h v meter ≠
      .error (.conversionOverflow,next,final) := by
  intro actual
  cases h <;> simp only [ReferenceCheckedEnvironmentStep.run,
    ReferenceCheckedEnvironmentStep.finish,if_pos fit] at actual
  all_goals repeat' first | split at actual | cases actual

private theorem handler_no_environment {h : Handler} {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {v next : View} {warm finalWarm : Warm}
    {meter final : Meter} {output finalOutput : ByteArray} (fit : v.env.calldata.size < UInt256.size) :
    runHandler h destinations ownerExists parent v warm meter output ≠
      .failed (.environment .conversionOverflow) next finalWarm final finalOutput := by
  intro actual
  cases h <;> simp only [runHandler] at actual
  all_goals repeat' first | split at actual | cases actual
  all_goals exact environment_no_conversion fit (by assumption)

private theorem handler_no_control {h : Handler} {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {v next : View} {warm finalWarm : Warm}
    {meter final : Meter} {output finalOutput : ByteArray} (fit : v.pc+1 < UInt256.size) :
    runHandler h destinations ownerExists parent v warm meter output ≠
      .failed (.stackControl .conversionOverflow) next finalWarm final finalOutput := by
  intro actual
  cases h <;> simp only [runHandler] at actual
  all_goals repeat' first | split at actual | cases actual
  all_goals exact ReferenceCheckedStackControlStep.run_no_conversion fit (by assumption)

/-- Literal final dispatcher, including all pre-charge/post-charge failures. -/
theorem dispatch {destinations : List Nat} {ownerExists : Bool} {parent : ReferenceStorageView.Parent}
    {v next : View} {warm finalWarm : Warm} {meter final : Meter} {output finalOutput : ByteArray} {fault : Fault}
    (actual : ReferenceCheckedDispatch.run destinations ownerExists parent v warm meter output =
      .failed fault next finalWarm final finalOutput)
    (calldata : v.env.calldata.size < UInt256.size) (pc : v.pc+1 < UInt256.size) :
    fault ≠ .environment .conversionOverflow ∧ fault ≠ .stackControl .conversionOverflow := by
  constructor <;> intro equal <;> subst fault
  all_goals unfold ReferenceCheckedDispatch.run at actual
  all_goals cases selected : read v.env.code v.pc <;> simp only [selected] at actual
  all_goals first
    | (solve | cases actual)
    | exact handler_no_environment calldata actual
    | exact handler_no_control pc actual

#print axioms dispatch
end Eip8282.Audit.Integrator.ReferenceCheckedConversionSafety

end

section

/-! ## ReferenceCheckedDispatchTerminal -/

/-! Actual checked dispatch terminal inversion. The selected terminal result
comes from the same literal handler, code and PC; its reference decoding is
some terminal, never the replay helper's STOP fallback. No old execution,
Action, desired output or source frame hypothesis is supplied.
Fixed-image coverage is a kernel check of the two existing site tables, not
an execution iteration ceiling or arbitrary-bytecode interpreter parity.
Source interpreter extraction and outer REVERT/error settlement remain separate. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedDispatchTerminal
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback
open ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem handler_terminal {h : Handler} {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {v : View} {warm : Warm} {meter : Meter}
    {output : ByteArray} {result : ReferenceCheckedTerminalStep.End}
    (actual : runHandler h destinations ownerExists parent v warm meter output = .terminal result) :
    ∃ halt, h = .terminal halt ∧ ReferenceCheckedTerminalStep.run halt v meter output = .ok result := by
  cases h
  case terminal halt =>
    simp only [runHandler] at actual
    cases ht : ReferenceCheckedTerminalStep.run halt v meter output with
    | error fault =>
      rcases fault with ⟨e,next,final,previous⟩
      simp only [ht] at actual
      contradiction
    | ok endState =>
      simp only [ht,Outcome.terminal.injEq] at actual
      subst endState
      exact ⟨halt,rfl,ht⟩
  all_goals simp only [runHandler] at actual
  all_goals split at actual <;> contradiction

/-- A dispatched terminal is the exact same successful terminal-handler result
and a successful source-shaped decode at the current code/PC. -/
theorem terminal {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {v : View} {warm : Warm} {meter : Meter}
    {output : ByteArray} {result : ReferenceCheckedTerminalStep.End}
    (actual : run destinations ownerExists parent v warm meter output = .terminal result) :
    ∃ halt,
      ReferenceCheckedTerminalStep.run halt v meter output = .ok result ∧
      ReferenceDecodeSites.referenceDecode v.env.code v.pc =
        some (ReferenceCheckedTerminalStep.opcode halt,none) := by
  unfold run at actual
  cases hd : read v.env.code v.pc <;> rw [hd] at actual
  · contradiction
  · contradiction
  · contradiction
  · obtain ⟨halt,rfl,checked⟩ := handler_terminal actual
    obtain ⟨arg,decoded⟩ := read_handler hd
    have width : argOnNBytesOfInstr (ReferenceCheckedTerminalStep.opcode halt) = 0 := by
      cases halt <;> rfl
    have immediate := ReferenceCheckedDecode.decode_width decoded
    change arg = if argOnNBytesOfInstr (ReferenceCheckedTerminalStep.opcode halt) = 0 then none else _ at immediate
    rw [width,if_pos rfl] at immediate
    subst arg
    exact ⟨halt,checked,decoded⟩

private theorem site_table (kind : Kind) :
    (ReferenceDecodeSites.sites (ReferenceRuntimeSites.reference kind)).all
      (fun pc => match read (ReferenceDecodeSites.code (ReferenceRuntimeSites.reference kind)) pc with
        | .handler _ => true | _ => false) = true := by
  cases kind <;> decide +kernel

/-- Every genuine listed site in either pinned runtime dispatches a supported
handler. This does not classify EOF as a handler or claim site reachability. -/
theorem runtime_coverage (kind : Kind) (v : View)
    (code : v.env.code = ReferenceDecodeSites.code (ReferenceRuntimeSites.reference kind))
    (site : v.pc ∈ ReferenceDecodeSites.sites (ReferenceRuntimeSites.reference kind)) :
    ∃ h, read v.env.code v.pc = .handler h := by
  have covered := List.all_eq_true.mp (site_table kind) v.pc site
  rw [←code] at covered
  cases hd : read v.env.code v.pc <;> simp only [hd] at covered
  · contradiction
  · contradiction
  · contradiction
  · exact ⟨_,rfl⟩

#print axioms terminal
#print axioms runtime_coverage
end Eip8282.Audit.Integrator.ReferenceCheckedDispatchTerminal

end

section

/-! ## ReferenceCheckedExecution -/

/-! Connect the computed checked evaluator to pinned bytecode execution.
No running trace, terminal instruction, terminal operands, prices or payment
annotations are inputs: they are extracted from the evaluator's actual result.
Exact initialized world/owner/warmth remain explicit source frame bindings.
Source and synthetic gas/PC are not equated. REVERT observations are internal;
outer restoration and actual source journal occurrence identity remain open.
-/
namespace Eip8282.Audit.Integrator.ReferenceCheckedExecution
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceCheckedDispatch ReferenceCheckedTerminalStep
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- Same terminal observable tuple. The old gas field of the internal REVERT
witness is deliberately distinct from the actual source terminal meter. -/
def Replayed {kind : Kind} (c : XiCall kind) (parent : ReferenceStorageView.Parent)
    (events : List Event) (result : End) : Prop :=
  ∃ amount post,
    X (events.length+2) (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
      (ReferenceSourceReplayEntry.call c events amount).entry =
      (if result.halt = .reverted then .ok (.revert post.gasAvailable result.output)
        else .ok (.success post result.output)) ∧
    ReferenceCheckedCompletion.Observations parent result.view post

/-- A terminal returned by actual checked evaluation produces the complete
pinned execution and same observations. This is conditional on that terminal
outcome, not an assumption that all calls succeed. -/
theorem terminal {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm : Warm} {pre : Meter} {fuel : Nat}
    {events : List Event} {result : End} {destinations : List Nat} {ownerExists : Bool}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent ByteArray.empty fuel
      (initial c tx) warm pre = some (events,.terminal result))
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000) :
    Replayed c parent events result := by
  obtain ⟨finish,finalWarm,middle,trace,last,_⟩ := ReferenceCheckedEvaluator.extract context actual
  obtain ⟨halt,checked,decoded⟩ := ReferenceCheckedDispatchTerminal.terminal last
  cases halt with
  | stop =>
    obtain ⟨halt,_,post,execution,observed⟩ := ReferenceCheckedCompletion.stop c trace checked decoded slots owner warmRelated grant
    exact ⟨0,post,by simpa only [halt,reduceCtorEq,if_false] using execution,observed⟩
  | returned =>
    obtain ⟨halt,amount,post,_,execution,observed⟩ := ReferenceCheckedCompletion.slice c (by decide) trace checked decoded slots owner warmRelated grant
    exact ⟨amount,post,by simpa only [halt,if_true,reduceCtorEq,if_false] using execution,observed⟩
  | reverted =>
    obtain ⟨halt,amount,post,_,execution,observed⟩ := ReferenceCheckedCompletion.slice c (by decide) trace checked decoded slots owner warmRelated grant
    exact ⟨amount,post,by simpa only [halt,if_true,reduceCtorEq,if_false] using execution,observed⟩

/-- For a transaction nested entry, the replay resource domain is derived
from the literal root allocation and nested grants, rather than supplied. The
numeric location is still not the source occurrence's unique identity. -/
theorem transaction_terminal {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm : Warm} {pre : Meter} {fuel : Nat}
    {events : List Event} {result : End} {destinations : List Nat} {ownerExists : Bool}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent ByteArray.empty fuel
      (initial c tx) warm pre = some (events,.terminal result))
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    {txGas intrinsic totalWork : Nat} {final : Meter}
    (located : ReferenceResourceEntryBound.EntryAt (ReferenceTransactionWork.initial txGas intrinsic) final totalWork pre) :
    Replayed c parent events result := by
  have grant := ReferenceNestedSourceAppend.transaction_entry located
  exact terminal c context actual slots owner warmRelated (by omega)

/-- From exact initialized context, the final checked dispatch lies on a
supported runtime site or genuine EOF. Invalid/unsupported opcodes cannot be
introduced by the helper fallback at this point. EOF is retained explicitly. -/
theorem final_site_or_eof {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {pre final : Meter}
    {finish : View} {events : List Event}
    (trace : ReferenceCheckedRuntimeTrace.Run kind parent (initial c tx) warm pre finish finalWarm final events)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000) :
    (∃ h, read finish.env.code finish.pc = .handler h) ∨ read finish.env.code finish.pc = .eof := by
  obtain ⟨source,paid,_⟩ := trace.extract (by simp [initial]) (ReferenceActionMemoryBounds.empty_aligned _ rfl)
  have payment := ReferenceExecutionLedger.bounded (.paid _ paid)
  have bound : ReferenceExecutionLedger.work events+0 ≤ 30000000 := by omega
  obtain ⟨post,_,_,related,site,_⟩ := ReferenceSourceReplayEntry.from_entry c 0 source slots owner warmRelated bound
  have code : finish.env.code = ReferenceDecodeSites.code (ReferenceRuntimeSites.reference kind) := by
    rw [related.env,site.1,ReferenceRuntimeSites.code_eq]
  rcases ReferenceRuntimeSites.site_or_eof site with hp | he
  · exact Or.inl (ReferenceCheckedDispatchTerminal.runtime_coverage kind finish code (by rw [related.pc]; exact hp))
  · right
    apply read_eof
    rw [code,related.pc,he]
    change (ReferenceDecodeSites.code (ReferenceRuntimeSites.reference kind)).data[
      (ReferenceDecodeSites.code (ReferenceRuntimeSites.reference kind)).data.size]? = none
    simp

#print axioms terminal
#print axioms transaction_terminal
#print axioms final_site_or_eof
end Eip8282.Audit.Integrator.ReferenceCheckedExecution

end

section

/-! ## ReferenceCheckedEOF -/

/-! Genuine code exhaustion has an exact source outcome distinct from STOP.
The checked evaluator preserves PC/view/meter/output at EOF. For a protected
initialized frame with empty previous output, its same running trace produces
the pinned evaluator's EOF fallback result and all terminal observations.
The fallback is used only after actual absence of a code byte is established;
an invalid opcode cannot enter this proof. Outer source receipt/rollback and
initial frame bindings remain separate, as in CheckedExecution. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedEOF
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceMeterBoundary ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem handler_not_eof {h : Handler} {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {v last : View} {warm lastWarm : Warm} {meter lastMeter : Meter}
    {output lastOutput : ByteArray} :
    runHandler h destinations ownerExists parent v warm meter output ≠ .eof last lastWarm lastMeter lastOutput := by
  intro actual
  cases h <;> simp only [runHandler] at actual
  all_goals split at actual <;> contradiction

theorem lookup {bytes : ByteArray} {pc : Nat} (actual : read bytes pc = .eof) : bytes[pc]? = none := by
  unfold ReferenceCheckedDispatch.read at actual
  cases ht : bytes[pc]? with
  | none => rfl
  | some tag =>
    simp only [ht] at actual
    split at actual
    · cases hs : select tag <;> simp only [hs] at actual <;> contradiction
    · contradiction

/-- A genuine EOF leaves every local field unchanged, including PC and the
incoming output. No terminal handler or synthetic PC increment is inserted. -/
theorem fields {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {v last : View} {warm lastWarm : Warm} {meter lastMeter : Meter}
    {output lastOutput : ByteArray}
    (actual : run destinations ownerExists parent v warm meter output = .eof last lastWarm lastMeter lastOutput) :
    v = last ∧ warm = lastWarm ∧ meter = lastMeter ∧ output = lastOutput ∧ v.env.code[v.pc]? = none := by
  unfold ReferenceCheckedDispatch.run at actual
  cases hd : read v.env.code v.pc <;> rw [hd] at actual
  · cases actual
    exact ⟨rfl,rfl,rfl,rfl,lookup hd⟩
  · contradiction
  · contradiction
  · exact False.elim (handler_not_eof actual)

/-- Full EOF replay from the computed evaluator, without treating unsupported
or invalid source opcodes as successful STOP. Empty output is the fresh-frame
binding supplied here; the evaluator preserves it on every running handler. -/
theorem execution {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {pre final : Meter} {fuel : Nat}
    {events : List Event} {last : View} {output : ByteArray} {destinations : List Nat} {ownerExists : Bool}
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent ByteArray.empty fuel
      (initial c tx) warm pre = some (events,.eof last finalWarm final output))
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000) :
    output = ByteArray.empty ∧
    runFull events pre = some final ∧
    ∃ post, X (events.length+2) (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
      (ReferenceSourceReplayEntry.call c events 0).entry = .ok (.success post output) ∧
      ReferenceCheckedCompletion.Observations parent last post := by
  obtain ⟨finish,endWarm,middle,trace,ended,_⟩ := ReferenceCheckedEvaluator.extract context actual
  obtain ⟨viewEq,warmEq,meterEq,outputEq,absent⟩ := fields ended
  subst finish
  subst endWarm
  subst middle
  subst output
  obtain ⟨source,paid,_⟩ := trace.extract (by simp [initial]) (ReferenceActionMemoryBounds.empty_aligned _ rfl)
  have payment := ReferenceExecutionLedger.bounded (.paid _ paid)
  have bound : ReferenceExecutionLedger.work events ≤ 30000000 := by omega
  have halt : ReferenceSourceReplayTrace.instruction last = (.STOP,none) := by
    simp [ReferenceSourceReplayTrace.instruction,ReferenceDecodeSites.referenceDecode,absent]
  obtain ⟨_,post,_,_,_,execution,related⟩ := ReferenceSourceReplayCompletion.stop c source slots owner warmRelated bound halt
  exact ⟨rfl,paid,post,execution,related.env,related.stack,related.memory,related.storage,related.logs,related.owner⟩

#print axioms lookup
#print axioms fields
#print axioms execution
end Eip8282.Audit.Integrator.ReferenceCheckedEOF

end

section

/-! ## ReferenceCheckedMemoryForward -/

/-! Forward checked memory stores for the paid SYSTEM trace consumer. The
price is that of the same computed post-memory; alignment derives the literal
source expansion charge, without a new memory budget or execution hypothesis. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedMemoryForward
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceCheckedMemoryStore ReferenceMemoryExpansionSource
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem store {kind : Kind} {parent : ReferenceStorageView.Parent} {byte : Bool}
    {v : View} {meter final : Meter} {off value : UInt256} {rest : List UInt256}
    (shape : v.stack = off::value::rest) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (paid : runFull [.ordinary (3+(ReferenceMemoryCapacity.cost (words (memoryAction v off (data byte value) rest))-
      ReferenceMemoryCapacity.cost (words v)))] meter = some final) :
    ReferenceCheckedMemoryStore.run byte v meter = .ok (memoryAction v off (data byte value) rest,final) := by
  have dataSize : (data byte value).size = length byte := by
    cases byte <;> simp [data,length,UInt256.size_toByteArray] <;> rfl
  have act : ReferenceRuntimeAction.Action kind parent (opcode byte,none) v
      (memoryAction v off (data byte value) rest) := by
    cases byte with
    | false => exact .base (.word shape)
    | true =>
      have byteEq : UInt8.ofNat (value.toNat%256) = UInt8.ofNat value.toNat := UInt8.ofNat_mod_size
      simpa [opcode,data,byteEq] using
        (ReferenceRuntimeAction.Action.base (ReferenceSystemAction.Action.byte shape) :
          ReferenceRuntimeAction.Action kind parent (.MSTORE8,none) v
            (memoryAction v off ⟨#[UInt8.ofNat value.toNat]⟩ rest))
  have computed := (ReferenceActionMemoryBounds.computed act aligned).2
  have span : ReferenceActionMemoryBounds.span v (opcode byte) = (off.toNat,length byte) := by
    cases byte <;> simp [ReferenceActionMemoryBounds.span,opcode,length,shape]
  rw [span] at computed
  dsimp only at computed
  have expansion := ReferenceMemoryExpansionSource.aligned (words v) off.toNat (length byte)
  rw [←aligned] at expansion
  have capacity : v.memory.size+(calculate v.memory.size off.toNat (length byte)).bytes =
      32*MachineState.M (words v) off.toNat (length byte) := by
    have lower := (ReferenceMemoryCapacity.expansion_bounds (words v) off.toNat (length byte)).1
    change v.memory.size = 32*words v at aligned
    omega
  rw [computed,←expansion.2] at paid
  obtain ⟨charged,hc,rfl⟩ := ReferenceCheckedPureForward.ordinary_paid paid
  simp only [ReferenceCheckedMemoryStore.run,shape,ReferenceSourceStackAdmission.pop,hc,capacity,
    memoryAction,dataSize]

#print axioms store
end Eip8282.Audit.Integrator.ReferenceCheckedMemoryForward

end

section

/-! ## ReferenceCheckedSourceSelection -/

/-! Reverse binding from decoded protected opcodes to actual source handler
selection. Only the fixed byte universe is finite; execution length is not.
Consumer: forward acceptance of the paid SYSTEM trace and its RETURN. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSourceSelection
open EvmYul EvmYul.EVM ReferenceRuntimeView ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem parsed (h : Handler) (tag : UInt8) (decoded : parseInstr tag = some (opcode h)) :
    select tag = some h := by
  have table : ∀ t : Fin 256, parseInstr (UInt8.ofNat t.val) = some (opcode h) →
      select (UInt8.ofNat t.val) = some h := by
    cases h with
    | binary b => cases b <;> decide +kernel
    | environment e => cases e <;> decide +kernel
    | stackControl s => cases s <;> decide +kernel
    | memoryStore b => cases b <;> decide +kernel
    | copyLog c => cases c <;> decide +kernel
    | load => decide +kernel
    | store => decide +kernel
    | terminal t => cases t <;> decide +kernel
  have check := table ⟨tag.toNat,tag.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at check
  exact check decoded

theorem read {bytes : ByteArray} {pc : Nat} {h : Handler} {arg : Option (UInt256 × Nat)}
    (decoded : ReferenceDecodeSites.referenceDecode bytes pc = some (opcode h,arg)) :
    ReferenceCheckedDispatch.read bytes pc = .handler h := by
  cases ht : bytes[pc]? with
  | none => simp [ReferenceDecodeSites.referenceDecode,ht] at decoded
  | some tag =>
    cases hp : parseInstr tag with
    | none => simp [ReferenceDecodeSites.referenceDecode,ht,hp] at decoded
    | some op =>
      have eq : some (op,if ReferenceDecodeSites.pushWidth tag = 0 then none else
          some (uInt256OfByteArray (ReferenceDecodeSites.paddedImmediate bytes pc (ReferenceDecodeSites.pushWidth tag)),ReferenceDecodeSites.pushWidth tag)) =
          some (opcode h,arg) := by simpa [ReferenceDecodeSites.referenceDecode,ht,hp] using decoded
      have opEq := congrArg (fun x => x.map Prod.fst) eq
      simp only [Option.map_some,Option.some.injEq] at opEq
      rw [opEq] at hp
      have selected := parsed h tag hp
      have valid := (select_facts tag selected).1
      simp only [ReferenceCheckedDispatch.read,ht,valid,if_true,selected]

#print axioms parsed
#print axioms read
end Eip8282.Audit.Integrator.ReferenceCheckedSourceSelection

end

section

/-! ## ReferenceCheckedStorageForward -/

/-! Forward acceptance of the paid storage steps constructed in SYSTEM's
coupled actual trace. Owner presence is a checked-entry producer, not a result
of the storage payment; original/current/new readings use the same view. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedStorageForward
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceCheckedStorageStep
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem load {parent : ReferenceStorageView.Parent} {v : View} {warm : Warm}
    {meter final : Meter} {key : UInt256} {rest : List UInt256}
    (shape : v.stack = key::rest) (bound : rest.length+1 ≤ 1024)
    (paid : runFull [.ordinary (if (sourceReading parent v warm).warm then 100 else 2100)] meter = some final) :
    ReferenceCheckedStorageStep.load parent v warm meter =
      .ok (loadAction parent v key rest,warmAfter .SLOAD v warm,final) := by
  classical
  have price : (if (sourceReading parent v warm).warm then 100 else 2100) = access v key warm := by
    simp [sourceReading,shape,access]
  rw [price] at paid
  obtain ⟨charged,hc,rfl⟩ := ReferenceCheckedPureForward.ordinary_paid paid
  have notfull : rest.length ≠ 1024 := by omega
  simp [ReferenceCheckedStorageStep.load,shape,ReferenceSourceStackAdmission.pop,hc,
    ReferenceSourceStackAdmission.push,notfull,loadAction,warmAfter]

/-- Invert the complete ordered storage charge, including the sentry. -/
theorem store_paid {warm : Bool} {original current new : UInt256} {meter final : Meter}
    (paid : runFull [.store warm original current new] meter = some final) :
    ∃ charged, ReferenceStorageGas.storageCharge false warm original current new (core meter) = some charged ∧
      final = update meter charged := by
  unfold runFull ReferenceMeterPath.run ReferenceMeterPath.pay at paid
  cases hc : ReferenceStorageGas.storageCharge false warm original current new (core meter) with
  | none => simp [hc] at paid
  | some charged =>
    simp only [hc,Option.bind_some,ReferenceMeterPath.run,Option.map_some,Option.some.injEq] at paid
    exact ⟨charged,rfl,paid.symm⟩

theorem store {parent : ReferenceStorageView.Parent} {v : View} {warm : Warm}
    {meter final : Meter} {key value : UInt256} {rest : List UInt256}
    (permission : v.env.perm = true) (shape : v.stack = key::value::rest)
    (paid : runFull [.store (sourceReading parent v warm).warm (sourceReading parent v warm).original
      (sourceReading parent v warm).current (sourceReading parent v warm).new] meter = some final) :
    ReferenceCheckedStorageStep.store true parent v warm meter =
      .ok (storeAction v key value rest,warmAfter .SSTORE v warm,final) := by
  classical
  obtain ⟨charged,hc,rfl⟩ := store_paid paid
  simp only [sourceReading,shape,List.getElem!_cons_zero,List.getElem!_cons_succ] at hc
  unfold ReferenceStorageGas.storageCharge at hc
  simp only [Bool.false_eq_true,if_false] at hc
  split at hc
  swap
  · contradiction
  rename_i sentry
  have sentry' : max (access v key warm) 2301 ≤ meter.execution := by
    simpa [ReferenceStorageGas.classify,access,core] using sentry
  simp only [ReferenceCheckedStorageStep.store,permission,if_true,shape,
    ReferenceSourceStackAdmission.pop,storeAfterPop,if_pos sentry']
  dsimp only [core] at hc
  cases he : ReferenceStorageGas.chargeExecution
      (ReferenceStorageGas.creditState
        {core meter with refund := meter.refund + (ReferenceStorageGas.classify
          (decide ((v.env.codeOwner,key.toByteArray) ∈ warm))
          (ReferenceStorageView.original parent v.storage v.env.codeOwner key.toByteArray)
          (ReferenceStorageView.current parent v.storage v.env.codeOwner key.toByteArray) value).refundDelta}
        (ReferenceStorageGas.classify (decide ((v.env.codeOwner,key.toByteArray) ∈ warm))
          (ReferenceStorageView.original parent v.storage v.env.codeOwner key.toByteArray)
          (ReferenceStorageView.current parent v.storage v.env.codeOwner key.toByteArray) value).stateRefund)
      (ReferenceStorageGas.classify (decide ((v.env.codeOwner,key.toByteArray) ∈ warm))
          (ReferenceStorageView.original parent v.storage v.env.codeOwner key.toByteArray)
          (ReferenceStorageView.current parent v.storage v.env.codeOwner key.toByteArray) value).execution with
  | none => simp_all only [core,he,Option.bind_none,reduceCtorEq]
  | some afterExec =>
    dsimp only [core] at he
    rw [he] at hc
    simp only [Option.bind_some] at hc
    dsimp only
    rw [hc]
    simp only [Bool.true_eq,if_true,storeAction,warmAfter,shape,List.getElem!_cons_zero]
    rfl

#print axioms load
#print axioms store_paid
#print axioms store
end Eip8282.Audit.Integrator.ReferenceCheckedStorageForward

end
