import Eip8282.Audit.Integrator.ReferenceRuntimeAction

/-! Non-gas old control guards from actual source-shaped protected actions.
Jump membership comes from successful partial source actions and the fixed
jump-table equality; static writes require the permission retained by Action.
No old Z acceptance or source interpreter extraction is assumed or asserted. -/
namespace Eip8282.Audit.Integrator.ReferenceActionControlAdmission
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferencePureAction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem source_jump {kind : Kind} {p : ReferenceStorageView.Parent} {v next : View}
    {arg : Option (UInt256 × Nat)}
    (effect : ReferenceRuntimeAction.Action kind p (.JUMP,arg) v next) :
    ∃ dest rest, v.stack = dest::rest ∧
      dest.toNat ∈ ReferenceDecodeSites.referenceJumps (ReferenceRuntimeSites.reference kind) := by
  cases effect with
  | base base =>
    cases base with
    | pure effect =>
      simp only [action,classify,Option.bind_some,familyAction] at effect
      cases shape : v.stack with
      | nil => simp only [shape] at effect; contradiction
      | cons dest rest =>
        simp only [shape] at effect
        split at effect
        · exact ⟨dest,rest,rfl,by assumption⟩
        · contradiction

private theorem source_jumpi {kind : Kind} {p : ReferenceStorageView.Parent} {v next : View}
    {arg : Option (UInt256 × Nat)}
    (effect : ReferenceRuntimeAction.Action kind p (.JUMPI,arg) v next)
    (taken : v.stack[1]? ≠ some ⟨0⟩) :
    ∃ dest cond rest, v.stack = dest::cond::rest ∧
      dest.toNat ∈ ReferenceDecodeSites.referenceJumps (ReferenceRuntimeSites.reference kind) := by
  cases effect with
  | base base =>
    cases base with
    | pure effect =>
      simp only [action,classify,Option.bind_some,familyAction] at effect
      cases shape : v.stack with
      | nil => simp only [shape] at effect; contradiction
      | cons dest tail =>
        cases tail with
        | nil => simp only [shape] at effect; contradiction
        | cons cond rest =>
          have nonzero : cond ≠ ⟨0⟩ := by
            intro hz
            apply taken
            rw [shape,hz]
            rfl
          simp only [shape,if_neg nonzero] at effect
          split at effect
          · exact ⟨dest,cond,rest,rfl,by assumption⟩
          · contradiction

theorem jump_member {kind : Kind} {dest : UInt256}
    (source : dest.toNat ∈ ReferenceDecodeSites.referenceJumps (ReferenceRuntimeSites.reference kind)) :
    dest ∈ D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩ := by
  rw [ReferenceRuntimeSites.jumps_eq]
  simp only [List.mem_toArray,List.mem_map]
  refine ⟨dest.toNat,source,?_⟩
  cases dest with
  | mk d => exact congrArg UInt256.mk (Fin.ext (Nat.mod_eq_of_lt d.isLt))

private theorem notIn_of_member {vj : Array UInt256} {dest : UInt256} {stack : Stack UInt256}
    (head : stack[0]? = some dest) (member : dest ∈ vj) : X.notIn stack[0]? vj = false := by
  have present : vj.contains dest = true :=
    Array.contains_iff_exists_mem_beq.mpr ⟨dest,member,by cases dest with | mk d => change (d == d) = true; simp⟩
  simp [X.notIn,X.belongs,head,present]

theorem jump_guards {kind : Kind} {p : ReferenceStorageView.Parent} {v next : View} {pre : EVM.State}
    (related : Related p v pre)
    (effect : ReferenceRuntimeAction.Action kind p (decodeAt pre) v next) :
    ((decodeAt pre).1 = .JUMP → X.notIn pre.stack[0]? (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) = false) ∧
    ((decodeAt pre).1 = .JUMPI → pre.stack[1]? ≠ some ⟨0⟩ →
      X.notIn pre.stack[0]? (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) = false) := by
  constructor
  · intro hop
    have decoded : decodeAt pre = (.JUMP,(decodeAt pre).2) := Prod.ext hop rfl
    rw [decoded] at effect
    obtain ⟨dest,rest,shape,member⟩ := source_jump effect
    apply notIn_of_member (dest := dest)
    · rw [←related.stack,shape]; rfl
    · exact jump_member member
  · intro hop taken
    have decoded : decodeAt pre = (.JUMPI,(decodeAt pre).2) := Prod.ext hop rfl
    rw [decoded] at effect
    obtain ⟨dest,cond,rest,shape,member⟩ := source_jumpi effect (by simpa only [related.stack] using taken)
    apply notIn_of_member (dest := dest)
    · rw [←related.stack,shape]; rfl
    · exact jump_member member

private theorem pure_static {kind : Kind} {instr : Instruction} {v next : View} (stack : Stack UInt256)
    (effect : action kind instr v = some next) : W instr.1 stack = false := by
  unfold action at effect
  cases selected : classify instr.1 with
  | none => simp only [selected,Option.bind_none] at effect; contradiction
  | some p =>
    rw [←classify_sound selected]
    cases p <;> try rfl
    rename_i b
    cases b <;> rfl

theorem static_guard {kind : Kind} {p : ReferenceStorageView.Parent} {v next : View} {pre : EVM.State}
    (related : Related p v pre)
    (effect : ReferenceRuntimeAction.Action kind p (decodeAt pre) v next)
    (readonly : pre.executionEnv.perm = false) : W (decodeAt pre).1 pre.stack = false := by
  have permission : v.env.perm = false := by rw [related.env,readonly]
  generalize hd : decodeAt pre = instr at effect ⊢
  cases effect with
  | base base =>
    cases base with
    | pure pure => exact pure_static pre.stack pure
    | load shape => rfl
    | store writable shape => simp [permission] at writable
    | word shape => rfl
    | byte shape => rfl
  | copy shape => rfl
  | log writable shape => simp [permission] at writable

/-- The actual fixed image excludes unsupported/call/create guards, including
RETURNDATACOPY. Signature existence is supplied without old admission. -/
theorem other_guards {kind : Kind} {pre : EVM.State}
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre) :
    δ (decodeAt pre).1 = some ((δ (decodeAt pre).1).getD 0) ∧
    α (decodeAt pre).1 = some ((α (decodeAt pre).1).getD 0) ∧
    (decodeAt pre).1 ≠ .RETURNDATACOPY ∧ (decodeAt pre).1.isCreate = false := by
  have allowed := RuntimeExecutionScope.opcode_allowed site
  have checked : ∀ op ∈ RuntimeOpcodeScope.allowedOps,
      δ op = some ((δ op).getD 0) ∧ α op = some ((α op).getD 0) ∧
      op ≠ .RETURNDATACOPY ∧ op.isCreate = false := by decide +kernel
  exact checked _ allowed

#print axioms jump_member
#print axioms jump_guards
#print axioms static_guard
#print axioms other_guards
end Eip8282.Audit.Integrator.ReferenceActionControlAdmission
