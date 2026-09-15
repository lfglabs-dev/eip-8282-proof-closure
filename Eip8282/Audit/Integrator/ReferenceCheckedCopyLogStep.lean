import Eip8282.Audit.Integrator.ReferenceCheckedEnvironmentStep
import Eip8282.Audit.Integrator.Topics.ReferenceMemory2
import Eip8282.Audit.Integrator.ReferenceActionMemoryBounds

/-! Literal checked CALLDATACOPY/LOG0 at EL0cc100eb190b64b23baba72dac0165652eaec252.
Archive direct-reference-amsterdam-gas-sources-20260910.json: environment.py
SHA2568c57bd699b99ff8b4d8e41e6a9c89cd1a03dda8160bf1d6dffe091932ec03657,
208-243; log.py f62f6cb589811e3a58c3a4644fcf7b979a506df1f09213e2a96e7988a4574874,
32-83. All operands pop before calculation/payment. COPY extends then writes
padded calldata. LOG0 extends before static rejection, then reads the actual
extended-memory slice and appends one owner log with empty topics.
Errors retain completed pops/payment/extension, not outer rollback.
Audited transcript only: source dispatch/frame, Python allocation and full
interpreter extraction remain separate. Alignment is a successful-effect
transport input, derived by initialized histories, never a raw-run guard. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedCopyLogStep
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceMemoryExpansionSource
open ReferenceActionMemoryBounds (Aligned)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

inductive Handler where | copy | log0 deriving DecidableEq
inductive Failure where
  | checked (reason : ReferenceCheckedBinaryStep.Failure)
  | staticWrite
  deriving DecidableEq

def opcode : Handler → Operation .EVM | .copy => .CALLDATACOPY | .log0 => .LOG0

def base (h : Handler) (len : Nat) : Nat :=
  match h with
  | .copy => 3+3*(ReferenceCopyLogGas.sourceCeil32 len/32)
  | .log0 => 375+8*len

def price (h : Handler) (v : View) (off len : UInt256) : Nat :=
  base h len.toNat+(calculate v.memory.size off.toNat len.toNat).cost

/-- Literal event amount is computed from the input stack. Success recovers
these operands from the checked pops, so get! defaults are never used then. -/
def cost (h : Handler) (v : View) : Nat :=
  price h v v.stack[0]! (if h = .copy then v.stack[2]! else v.stack[1]!)

/-- COPY's zero-length branch is the literal empty slice write, which leaves
memory unchanged at every destination; expansion is zero in this branch. -/
def copied (v : View) (off source len : UInt256) (rest : List UInt256) : View :=
  {v with pc := v.pc+1,stack := rest, memory := ReferenceCopyMemory.copyMemory v.memory v.env.calldata off.toNat source.toNat len.toNat (v.memory.size+(calculate v.memory.size off.toNat len.toNat).bytes)}

def expanded (v : View) (off len : UInt256) (rest : List UInt256) : View :=
  {v with stack := rest,memory := ReferenceMemoryOperations.extend v.memory (v.memory.size+(calculate v.memory.size off.toNat len.toNat).bytes)}

def logged (v : View) (off len : UInt256) (rest : List UInt256) : View :=
  let m := expanded v off len rest
  {m with pc := v.pc+1,logs := v.logs++[⟨v.env.codeOwner,#[],m.memory.extract off.toNat (off.toNat+len.toNat)⟩]}

def afterPops (h : Handler) (v : View) (meter : Meter) (off source len : UInt256)
    (rest : List UInt256) : Except (Failure × View × Meter) (View × Meter) :=
  match ReferenceStorageGas.chargeExecution (core meter) (price h v off len) with
  | none => .error (.checked .outOfGas,{v with stack := rest},meter)
  | some charged =>
    let m := update meter charged
    match h with
    | .copy => .ok (copied v off source len rest,m)
    | .log0 => if v.env.perm then .ok (logged v off len rest,m)
        else .error (.staticWrite,expanded v off len rest,m)

def run (h : Handler) (v : View) (meter : Meter) :
    Except (Failure × View × Meter) (View × Meter) :=
  match ReferenceSourceStackAdmission.pop v.stack with
  | .error e => .error (.checked (.stack e),v,meter)
  | .ok (first,off) =>
    match ReferenceSourceStackAdmission.pop first with
    | .error e => .error (.checked (.stack e),{v with stack := first},meter)
    | .ok (second,x) =>
      match h with
      | .log0 => afterPops h v meter off ⟨0⟩ x second
      | .copy =>
        match ReferenceSourceStackAdmission.pop second with
        | .error e => .error (.checked (.stack e),{v with stack := second},meter)
        | .ok (rest,len) => afterPops h v meter off x len rest

theorem expanded_capacity (v : View) (off len : UInt256) (aligned : Aligned v) :
    v.memory.size+(calculate v.memory.size off.toNat len.toNat).bytes =
      32*MachineState.M (words v) off.toNat len.toNat := by
  have expansionFacts := (ReferenceMemoryExpansionSource.aligned (words v) off.toNat len.toNat).1
  have lower := (ReferenceMemoryCapacity.expansion_bounds (words v) off.toNat len.toNat).1
  change v.memory.size = 32*words v at aligned
  rw [←aligned] at expansionFacts
  omega

theorem expanded_slice (v : View) (off len : UInt256) (rest : List UInt256)
    (aligned : Aligned v) :
    (expanded v off len rest).memory.extract off.toNat (off.toNat+len.toNat) =
      ReferenceReturnView.output v off len := by
  have cap := expanded_capacity v off len aligned
  have bounds := ReferenceMemoryCapacity.expansion_bounds (words v) off.toNat len.toNat
  have fits : v.memory.size ≤ 32*MachineState.M (words v) off.toNat len.toNat := by
    change v.memory.size = 32*words v at aligned
    omega
  have same := ReferenceMemoryOperations.extend_same v.memory
    (32*MachineState.M (words v) off.toNat len.toNat) fits
  change _ = ReferenceMemoryView.buffer v.memory off.toNat len.toNat
  rw [ReferenceMemoryView.buffer_congr _ _ same off.toNat len.toNat]
  simp only [expanded,cap]
  have fit : len.toNat = 0 ∨ off.toNat+len.toNat ≤
      (ReferenceMemoryOperations.extend v.memory (32*MachineState.M (words v) off.toNat len.toNat)).size := by
    by_cases hz : len.toNat = 0
    · exact Or.inl hz
    · right
      simpa only [ReferenceMemoryOperations.extend,ReferenceMemoryView.buffer_size] using bounds.2 (by omega)
  have pad : len.toNat-(min (off.toNat+len.toNat)
      (ReferenceMemoryOperations.extend v.memory (32*MachineState.M (words v) off.toNat len.toNat)).size-off.toNat) = 0 := by
    rcases fit with hz | h <;> omega
  apply ByteArray.ext
  simp only [ReferenceMemoryView.buffer,ByteArray.data_extract,pad,Array.replicate_zero,Array.append_empty]

private theorem copied_eq (v : View) (off source len : UInt256) (rest : List UInt256)
    (aligned : Aligned v) : copied v off source len rest = ReferenceCalldataCopy.copyAction v off source len rest := by
  simp only [copied,ReferenceCalldataCopy.copyAction,expanded_capacity v off len aligned]

private theorem logged_eq (v : View) (off len : UInt256) (rest : List UInt256)
    (aligned : Aligned v) : logged v off len rest = ReferenceLogView.logAction v off len rest := by
  have dataEq := expanded_slice v off len rest aligned
  simp only [expanded,expanded_capacity v off len aligned] at dataEq
  simp only [logged,dataEq,expanded,expanded_capacity v off len aligned,ReferenceLogView.logAction,
    ReferenceReturnView.returnMemory,ReferenceLogView.entry]

private theorem price_eq {h : Handler} {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v next : View} {off len : UInt256} (aligned : Aligned v)
    (action : ReferenceRuntimeAction.Action kind parent (opcode h,none) v next)
    (span : ReferenceActionMemoryBounds.span v (opcode h) = (off.toNat,len.toNat)) :
    price h v off len = base h len.toNat+
      (ReferenceMemoryCapacity.cost (words next)-ReferenceMemoryCapacity.cost (words v)) := by
  have expansionFacts := (ReferenceMemoryExpansionSource.aligned (words v) off.toNat len.toNat).2
  rw [←aligned] at expansionFacts
  have computed := (ReferenceActionMemoryBounds.computed action aligned).2
  rw [span] at computed
  simp only [price,expansionFacts,computed]

/-- Successful literal handler results produce their effect, computed price,
exact payment and post-stack bound, without supplied operand or output facts. -/
theorem success {h : Handler} {v next : View} {meter final : Meter}
    (kind : Kind) (parent : ReferenceStorageView.Parent) (warm : ReferenceSourceReadings.Warm)
    (initial : v.stack.length ≤ 1024) (aligned : Aligned v)
    (actual : run h v meter = .ok (next,final)) :
    ReferenceRuntimeAction.Action kind parent (opcode h,none) v next ∧
    ReferenceRuntimeReadings.Price parent v warm next (opcode h) (.ordinary (cost h v)) ∧
    runFull [.ordinary (cost h v)] meter = some final ∧ next.stack.length ≤ 1024 := by
  unfold run at actual
  cases shape : v.stack with
  | nil => simp only [shape,ReferenceSourceStackAdmission.pop] at actual; contradiction
  | cons off first =>
    simp only [shape,ReferenceSourceStackAdmission.pop] at actual
    cases first with
    | nil => contradiction
    | cons x second =>
      cases h with
      | copy =>
        cases second with
        | nil => contradiction
        | cons len rest =>
          dsimp only [ReferenceSourceStackAdmission.pop] at actual
          unfold afterPops at actual
          cases hc : ReferenceStorageGas.chargeExecution (core meter) (price .copy v off len) with
          | none => simp only [hc] at actual; contradiction
          | some charged =>
            simp only [hc] at actual
            cases actual
            rw [copied_eq v off x len rest aligned]
            have action : ReferenceRuntimeAction.Action kind parent (opcode .copy,none) v
                (ReferenceCalldataCopy.copyAction v off x len rest) := .copy shape
            have span : ReferenceActionMemoryBounds.span v (opcode .copy) = (off.toNat,len.toNat) := by
              simp [ReferenceActionMemoryBounds.span,opcode,shape]
            simp only [cost,shape,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true]
            refine ⟨action,?_,?_,?_⟩
            · rw [price_eq aligned action span]
              simp [ReferenceRuntimeReadings.Price,ReferenceCopyLogGas.ordinaryCost,ReferenceCopyLogGas.copyCost,
                base,ReferenceCopyLogGas.ceil_words,opcode,shape]
            · simp only [runFull,ReferenceMeterPath.run,ReferenceMeterPath.pay,hc,Option.bind_some,Option.map_some]
            · rw [shape] at initial
              change rest.length ≤ 1024
              simp only [List.length_cons] at initial
              omega
      | log0 =>
        unfold afterPops at actual
        cases hc : ReferenceStorageGas.chargeExecution (core meter) (price .log0 v off x) with
        | none => simp only [hc] at actual; contradiction
        | some charged =>
          simp only [hc] at actual
          split at actual
          · rename_i perm
            cases actual
            rw [logged_eq v off x second aligned]
            have action : ReferenceRuntimeAction.Action kind parent (opcode .log0,none) v
                (ReferenceLogView.logAction v off x second) := .log perm shape
            have span : ReferenceActionMemoryBounds.span v (opcode .log0) = (off.toNat,x.toNat) := by
              simp [ReferenceActionMemoryBounds.span,opcode,shape]
            simp only [cost,shape,List.getElem!_cons_zero,List.getElem!_cons_succ,
              show Handler.log0 ≠ Handler.copy by decide,ite_false]
            refine ⟨action,?_,?_,?_⟩
            · rw [price_eq aligned action span]
              simp [ReferenceRuntimeReadings.Price,ReferenceCopyLogGas.ordinaryCost,ReferenceCopyLogGas.logCost,
                base,opcode,shape]
            · simp only [runFull,ReferenceMeterPath.run,ReferenceMeterPath.pay,hc,Option.bind_some,Option.map_some]
            · rw [shape] at initial
              change second.length ≤ 1024
              simp only [List.length_cons] at initial
              omega
          · contradiction

/-- Source static rejection retains the already expanded buffer and debit. -/
theorem log_static (v : View) (meter : Meter) (off len : UInt256) (rest : List UInt256)
    (charged : ReferenceStorageGas.Meter) (shape : v.stack = off::len::rest)
    (paid : ReferenceStorageGas.chargeExecution (core meter) (price .log0 v off len) = some charged)
    (denied : v.env.perm = false) :
    run .log0 v meter = .error (.staticWrite,expanded v off len rest,update meter charged) := by
  simp only [run,shape,ReferenceSourceStackAdmission.pop,afterPops,paid,denied,Bool.false_eq_true,if_false]

#print axioms expanded_capacity
#print axioms expanded_slice
#print axioms success
#print axioms log_static
end Eip8282.Audit.Integrator.ReferenceCheckedCopyLogStep
