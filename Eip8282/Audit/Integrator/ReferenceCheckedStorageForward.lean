import Eip8282.Audit.Integrator.ReferenceCheckedPureForward

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
