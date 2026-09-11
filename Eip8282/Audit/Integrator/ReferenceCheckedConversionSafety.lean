import Eip8282.Audit.Integrator.ReferenceCheckedPrefix
import Eip8282.Audit.Integrator.ReferenceCheckedFaultClass

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
