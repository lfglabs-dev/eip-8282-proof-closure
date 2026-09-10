import Eip8282.Audit.Integrator.ReferenceCheckedBinaryStep

/-! Literal checked SLOAD/SSTORE handlers for EL0cc100eb190b64b23baba72dac0165652eaec252.
Full storage.py SHA256d355855a1c50212a4e4753abb533c338919103635755da13bc1e154fcb3ed11b,
37-170 and gas.py SHA25641d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c
are archived in direct-reference-amsterdam-gas-sources-20260910.json.
SLOAD warms before charging, reads only after charge, then checked-pushes.
SSTORE rejects static execution before popping; the sentry precedes warming
and BAL reads; refund changes and state credit precede execution then state
charges; set_storage then asserts current owner existence before the write.
The explicit ownerExists input projects that source-world lookup and still
requires its actual frame producer; false is an assertion, not ordinary OOG.
Only successful charges and this assertion permit the write and PC increment.
Errors expose partial stack, BAL/warm set and meter, before outer restoration.
The storage/checked handler transcription is audited, not a Python extraction
or a producer of the actual source world, frame or transaction journal. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedStorageStep
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceSourceReadings ReferenceMeterPath
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

inductive Failure where
  | checked (reason : ReferenceCheckedBinaryStep.Failure)
  | staticWrite
  | missingOwnerAssertion

abbrev Result := Except (Failure × View × Warm × Meter) (View × Warm × Meter)

noncomputable def access (v : View) (key : UInt256) (warm : Warm) : Nat := by
  classical
  exact if (v.env.codeOwner,key.toByteArray) ∈ warm then 100 else 2100

noncomputable def load (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm)
    (meter : Meter) : Result :=
  match ReferenceSourceStackAdmission.pop v.stack with
  | .error e => .error (.checked (.stack e),v,warm,meter)
  | .ok (rest,key) =>
    let popped := {v with stack := rest}
    let warmed := insert (v.env.codeOwner,key.toByteArray) warm
    match ReferenceStorageGas.chargeExecution (core meter) (access v key warm) with
    | none => .error (.checked .outOfGas,popped,warmed,meter)
    | some charged =>
      let tracked := {popped with storage := ReferenceStorageView.readTracked v.storage v.env.codeOwner key.toByteArray}
      let value := ReferenceStorageView.current parent v.storage v.env.codeOwner key.toByteArray
      match ReferenceSourceStackAdmission.push value rest with
      | .error e => .error (.checked (.stack e),tracked,warmed,update meter charged)
      | .ok stack => .ok ({tracked with stack := stack,pc := v.pc+1},warmed,update meter charged)

/-- This helper starts only after both pops and the static guard. Its state
read and refund branch occur strictly after the state-independent sentry. -/
noncomputable def storeAfterPop (ownerExists : Bool) (parent : ReferenceStorageView.Parent) (v : View)
    (warm : Warm) (meter : Meter) (key value : UInt256) (rest : List UInt256) : Result := by
  classical
  exact
    let popped := {v with stack := rest}
    if max (access v key warm) 2301 ≤ meter.execution then
      let warmed := insert (v.env.codeOwner,key.toByteArray) warm
      let tracked := {popped with storage := ReferenceStorageView.readTracked v.storage v.env.codeOwner key.toByteArray}
      let original := ReferenceStorageView.original parent v.storage v.env.codeOwner key.toByteArray
      let current := ReferenceStorageView.current parent v.storage v.env.codeOwner key.toByteArray
      let c := ReferenceStorageGas.classify (@decide ((v.env.codeOwner,key.toByteArray) ∈ warm) (Classical.propDecidable _))
        original current value
      let credited := ReferenceStorageGas.creditState
        {core meter with refund := meter.refund+c.refundDelta} c.stateRefund
      match ReferenceStorageGas.chargeExecution credited c.execution with
      | none => .error (.checked .outOfGas,tracked,warmed,update meter credited)
      | some charged =>
        match ReferenceStorageGas.chargeState charged c.state with
        | none => .error (.checked .outOfGas,tracked,warmed,update meter charged)
        | some final =>
          if ownerExists then .ok ({tracked with pc := v.pc+1, storage := ReferenceStorageView.write tracked.storage v.env.codeOwner key.toByteArray value},
            warmed,update meter final)
          else .error (.missingOwnerAssertion,tracked,warmed,update meter final)
    else .error (.checked .outOfGas,popped,warm,meter)

noncomputable def store (ownerExists : Bool) (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm)
    (meter : Meter) : Result :=
  if v.env.perm then
    match ReferenceSourceStackAdmission.pop v.stack with
    | .error e => .error (.checked (.stack e),v,warm,meter)
    | .ok (first,key) =>
      match ReferenceSourceStackAdmission.pop first with
      | .error e => .error (.checked (.stack e),{v with stack := first},warm,meter)
      | .ok (rest,value) => storeAfterPop ownerExists parent v warm meter key value rest
  else .error (.staticWrite,v,warm,meter)

private theorem load_shape {parent : ReferenceStorageView.Parent} {v next : View}
    {warm finalWarm : Warm} {meter final : Meter}
    (actual : load parent v warm meter = .ok (next,finalWarm,final)) :
    ∃ key rest charged,
      v.stack = key::rest ∧
      ReferenceStorageGas.chargeExecution (core meter) (access v key warm) = some charged ∧
      next = loadAction parent v key rest ∧
      finalWarm = insert (v.env.codeOwner,key.toByteArray) warm ∧ final = update meter charged := by
  unfold load at actual
  cases hs : v.stack with
  | nil => simp only [hs,ReferenceSourceStackAdmission.pop] at actual; contradiction
  | cons key rest =>
    simp only [hs,ReferenceSourceStackAdmission.pop] at actual
    cases hc : ReferenceStorageGas.chargeExecution (core meter) (access v key warm) with
    | none => simp only [hc] at actual; contradiction
    | some charged =>
      simp only [hc] at actual
      cases hp : ReferenceSourceStackAdmission.push
          (ReferenceStorageView.current parent v.storage v.env.codeOwner key.toByteArray) rest with
      | error e => simp only [hp] at actual; contradiction
      | ok stack =>
        simp only [hp] at actual
        cases actual
        have he : stack = ReferenceStorageView.current parent v.storage v.env.codeOwner key.toByteArray::rest := by
          unfold ReferenceSourceStackAdmission.push at hp
          split at hp
          · contradiction
          · cases hp; rfl
        subst stack
        exact ⟨key,rest,charged,rfl,hc,rfl,rfl,rfl⟩

/-- Exact same successful checked SLOAD supplies action, access price, payment
and warmth. The input stack bound derives the post bound; no desired view. -/
theorem load_success {parent : ReferenceStorageView.Parent} {v next : View}
    {warm finalWarm : Warm} {meter final : Meter} (kind : Kind)
    (initial : v.stack.length ≤ 1024)
    (actual : load parent v warm meter = .ok (next,finalWarm,final)) :
    ReferenceRuntimeAction.Action kind parent (.SLOAD,none) v next ∧
    ReferenceRuntimeReadings.Price parent v warm next .SLOAD
      (.ordinary (if (sourceReading parent v warm).warm then 100 else 2100)) ∧
    runFull [.ordinary (if (sourceReading parent v warm).warm then 100 else 2100)] meter = some final ∧
    finalWarm = warmAfter .SLOAD v warm ∧ next.stack.length ≤ 1024 := by
  classical
  obtain ⟨key,rest,charged,shape,hc,rfl,rfl,rfl⟩ := load_shape actual
  have cost : (if (sourceReading parent v warm).warm then 100 else 2100) = access v key warm := by
    simp [sourceReading,shape,access]
  refine ⟨.base (.load shape),?_,?_,?_,?_⟩
  · simp [ReferenceRuntimeReadings.Price,ReferenceCopyLogGas.ordinaryCost,
      ReferenceOrdinaryGas.ordinaryCost,loadAction,words]
  · rw [cost]
    simp only [runFull,ReferenceMeterPath.run,pay,hc,Option.bind_some,Option.map_some]
  · simp [warmAfter,shape]
  · rw [shape] at initial
    exact initial

private theorem store_after_shape {ownerExists : Bool} {parent : ReferenceStorageView.Parent} {v next : View}
    {warm finalWarm : Warm} {meter final : Meter} {key value : UInt256} {rest : List UInt256}
    (actual : storeAfterPop ownerExists parent v warm meter key value rest = .ok (next,finalWarm,final)) :
    ∃ charged,
      ReferenceStorageGas.storageCharge false
        (@decide ((v.env.codeOwner,key.toByteArray) ∈ warm) (Classical.propDecidable _))
        (ReferenceStorageView.original parent v.storage v.env.codeOwner key.toByteArray)
        (ReferenceStorageView.current parent v.storage v.env.codeOwner key.toByteArray) value
        (core meter) = some charged ∧
      next = storeAction v key value rest ∧
      finalWarm = insert (v.env.codeOwner,key.toByteArray) warm ∧ final = update meter charged := by
  classical
  unfold storeAfterPop at actual
  split at actual
  · rename_i sentry
    dsimp only at actual
    split at actual
    · contradiction
    · rename_i charged he
      split at actual
      · contradiction
      · rename_i afterState hs
        split at actual
        swap
        · contradiction
        cases actual
        refine ⟨afterState,?_,rfl,rfl,rfl⟩
        unfold ReferenceStorageGas.storageCharge
        simp only [Bool.false_eq_true,if_false]
        have se : (ReferenceStorageGas.classify
            (@decide ((v.env.codeOwner,key.toByteArray) ∈ warm) (Classical.propDecidable _))
            (ReferenceStorageView.original parent v.storage v.env.codeOwner key.toByteArray)
            (ReferenceStorageView.current parent v.storage v.env.codeOwner key.toByteArray) value).sentry
            ≤ (core meter).execution := by
          simpa [ReferenceStorageGas.classify,access,core] using sentry
        rw [if_pos se]
        dsimp only [core] at he ⊢
        rw [he]
        exact hs
  · contradiction

/-- Successful literal SSTORE derives write permission, both operands, the
same original/current/new pricing and full ordered payment. -/
theorem store_success {ownerExists : Bool} {parent : ReferenceStorageView.Parent} {v next : View}
    {warm finalWarm : Warm} {meter final : Meter} (kind : Kind)
    (initial : v.stack.length ≤ 1024)
    (actual : store ownerExists parent v warm meter = .ok (next,finalWarm,final)) :
    ReferenceRuntimeAction.Action kind parent (.SSTORE,none) v next ∧
    ReferenceRuntimeReadings.Price parent v warm next .SSTORE
      (.store (sourceReading parent v warm).warm (sourceReading parent v warm).original
        (sourceReading parent v warm).current (sourceReading parent v warm).new) ∧
    runFull [.store (sourceReading parent v warm).warm (sourceReading parent v warm).original
      (sourceReading parent v warm).current (sourceReading parent v warm).new] meter = some final ∧
    finalWarm = warmAfter .SSTORE v warm ∧ next.stack.length ≤ 1024 := by
  classical
  unfold store at actual
  split at actual
  · rename_i permission
    cases shape : v.stack with
    | nil => simp only [shape,ReferenceSourceStackAdmission.pop] at actual; contradiction
    | cons key first =>
      simp only [shape,ReferenceSourceStackAdmission.pop] at actual
      cases first with
      | nil => contradiction
      | cons value rest =>
        obtain ⟨charged,hc,rfl,rfl,rfl⟩ := store_after_shape actual
        refine ⟨.base (.store permission shape),?_,?_,?_,?_⟩
        · simp [ReferenceRuntimeReadings.Price,storeAction,words]
        · simp only [runFull,ReferenceMeterPath.run,pay,sourceReading,shape,List.getElem!_cons_zero,
            List.getElem!_cons_succ,hc,Option.bind_some,Option.map_some]
        · simp [warmAfter,shape]
        · rw [shape] at initial
          change rest.length ≤ 1024
          simp only [List.length_cons] at initial
          omega
  · contradiction


/-- SLOAD inserts the key into the warm set before an execution-gas failure,
but it has not performed the BAL-tracked storage read. -/
theorem load_out_of_gas (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm)
    (meter : Meter) (key : UInt256) (rest : List UInt256)
    (shape : v.stack = key::rest) (insufficient : meter.execution < access v key warm) :
    load parent v warm meter = .error (.checked .outOfGas,{v with stack := rest},
      insert (v.env.codeOwner,key.toByteArray) warm,meter) := by
  simp only [load,shape,ReferenceSourceStackAdmission.pop,ReferenceStorageGas.chargeExecution,core]
  rw [if_neg (by omega)]

/-- Static SSTORE rejects before either pop, warmth, reads or payment. -/
theorem store_static (ownerExists : Bool) (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm)
    (meter : Meter) (denied : v.env.perm = false) :
    store ownerExists parent v warm meter = .error (.staticWrite,v,warm,meter) := by
  simp only [store,denied,Bool.false_eq_true,if_false]

/-- One-operand SSTORE retains its first pop, before any gas or state access. -/
theorem store_one (ownerExists : Bool) (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm)
    (meter : Meter) (key : UInt256) (allowed : v.env.perm = true) (shape : v.stack = [key]) :
    store ownerExists parent v warm meter =
      .error (.checked (.stack .underflow),{v with stack := []},warm,meter) := by
  simp only [store,allowed,if_true,shape,ReferenceSourceStackAdmission.pop]

/-- The failed sentry retains two pops but precedes all warmth and BAL reads.
This differs from the SLOAD failure above. -/
theorem store_sentry (ownerExists : Bool) (parent : ReferenceStorageView.Parent) (v : View) (warm : Warm)
    (meter : Meter) (key value : UInt256) (rest : List UInt256)
    (allowed : v.env.perm = true) (shape : v.stack = key::value::rest)
    (insufficient : meter.execution < max (access v key warm) 2301) :
    store ownerExists parent v warm meter = .error (.checked .outOfGas,{v with stack := rest},warm,meter) := by
  simp only [store,allowed,if_true,shape,ReferenceSourceStackAdmission.pop,storeAfterPop]
  rw [if_neg (by omega)]

#print axioms load_out_of_gas
#print axioms store_static
#print axioms store_one
#print axioms store_sentry

#print axioms load_success
#print axioms store_success
end Eip8282.Audit.Integrator.ReferenceCheckedStorageStep
