import Eip8282.Audit.Integrator.ReferencePureAction

/-! Actual admitted control/stack steps construct the partial source view action.
Taken jumps use the exact source jump table; an untaken JUMPI bypasses that test.
PUSH width is obtained from the actual decoder. All stack shapes come from Z. -/
namespace Eip8282.Audit.Integrator.ReferencePureControl
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferencePureAction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem pop {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel cost : Nat} {arg : Option (UInt256 × Nat)}
    (h : Related parent v pre)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (.POP,arg))
    (hz : Z (D_J pre.executionEnv.code ⟨0⟩) .POP pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (.POP,arg) mid post) :
    ∃ next, action kind (.POP,arg) v = some next ∧ Related parent next post := by
  obtain ⟨hr,hsraw⟩ := raw_dispatch .pop h hz hs
  obtain ⟨rest,x,shape,_⟩ := ReferenceAcceptedStack.pop1 hz (by decide)
  have fit := ReferenceRuntimeSites.pc_fit hat
  rw [decoded] at fit
  have fit1 : pre.pc.toNat+1 < UInt256.size := by omega
  have known := (ReferenceControlOps.pop (stepPre cost (zMid pre .POP)) x rest shape
    (by simpa [stepPre,zMid] using fit1)).1
  have same := Except.ok.inj (hsraw.symm.trans known)
  subst post
  refine ⟨advance v rest,?_,related_advance hr _ 1 (by simpa [stepPre,zMid] using fit1)⟩
  simp [action,classify,familyAction,h.stack,shape]

theorem jump {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel cost : Nat} {arg : Option (UInt256 × Nat)}
    (h : Related parent v pre)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hz : Z (D_J pre.executionEnv.code ⟨0⟩) .JUMP pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (.JUMP,arg) mid post) :
    ∃ next, action kind (.JUMP,arg) v = some next ∧ Related parent next post := by
  obtain ⟨hr,hsraw⟩ := raw_dispatch .jump h hz hs
  obtain ⟨rest,dest,shape,_⟩ := ReferenceAcceptedStack.pop1 hz (by decide)
  have member := ReferenceControlOps.accepted_jump hz (by rw [shape]; rfl) (Or.inl rfl)
  rw [hat.1] at member
  have valid := ReferenceRuntimeSites.jump_member member
  have known : EvmYul.step (τ := .EVM) .JUMP arg (stepPre cost (zMid pre .JUMP)) =
      .ok {stepPre cost (zMid pre .JUMP) with pc := dest,stack := rest} :=
    pureStep_sound (by decide) (by simp only [pureStep,stepPre,zMid,shape])
  have same := Except.ok.inj (hsraw.symm.trans known)
  subst post
  refine ⟨stackAction v dest.toNat rest,?_,related_jump hr rest dest⟩
  simp [action,classify,familyAction,h.stack,shape,valid]

theorem jumpi {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel cost : Nat} {arg : Option (UInt256 × Nat)}
    (h : Related parent v pre)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (.JUMPI,arg))
    (hz : Z (D_J pre.executionEnv.code ⟨0⟩) .JUMPI pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (.JUMPI,arg) mid post) :
    ∃ next, action kind (.JUMPI,arg) v = some next ∧ Related parent next post := by
  obtain ⟨hr,hsraw⟩ := raw_dispatch .jumpi h hz hs
  obtain ⟨rest,dest,cond,shape,_⟩ := ReferenceAcceptedStack.pop2 hz (by decide)
  by_cases zero : cond = ⟨0⟩
  · have known := step_JUMPI_untaken (s := stepPre cost (zMid pre .JUMPI)) shape zero
    have same := Except.ok.inj (hsraw.symm.trans known)
    subst post
    have fit := ReferenceRuntimeSites.pc_fit hat
    rw [decoded] at fit
    have fit1 : pre.pc.toNat+1 < UInt256.size := by omega
    refine ⟨advance v rest,?_,related_advance hr rest 1 (by simpa [stepPre,zMid] using fit1)⟩
    simp [action,classify,familyAction,h.stack,shape,zero]
  · have member := ReferenceControlOps.accepted_jump hz (by rw [shape]; rfl)
      (Or.inr ⟨rfl,by simpa [shape] using zero⟩)
    rw [hat.1] at member
    have valid := ReferenceRuntimeSites.jump_member member
    have known := step_JUMPI_taken (s := stepPre cost (zMid pre .JUMPI)) shape zero
    have same := Except.ok.inj (hsraw.symm.trans known)
    subst post
    refine ⟨stackAction v dest.toNat rest,?_,related_jump hr rest dest⟩
    simp [action,classify,familyAction,h.stack,shape,zero,valid]

theorem push {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel cost : Nat} {arg : Option (UInt256 × Nat)}
    (p : Operation.POp) (h : Related parent v pre)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (.Push p,arg))
    (hz : Z (D_J pre.executionEnv.code ⟨0⟩) (.Push p) pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (.Push p,arg) mid post) :
    ∃ next, action kind (.Push p,arg) v = some next ∧ Related parent next post := by
  obtain ⟨hr,hsraw⟩ := raw_dispatch (.push p) h hz hs
  have fit := ReferenceRuntimeSites.pc_fit hat
  rw [decoded] at fit
  have fit1 : pre.pc.toNat+1 < UInt256.size := by omega
  by_cases zero : p = .PUSH0
  · subst p
    have known : EvmYul.step (τ := .EVM) .PUSH0 arg (stepPre cost (zMid pre .PUSH0)) =
        .ok ((stepPre cost (zMid pre .PUSH0)).replaceStackAndIncrPC (⟨0⟩::pre.stack)) := rfl
    have same := Except.ok.inj (hsraw.symm.trans known)
    subst post
    refine ⟨advance v (⟨0⟩::v.stack),?_,?_⟩
    · simp [action,classify,familyAction]
    · simpa only [h.stack,stepPre,zMid,opcode] using related_advance hr (⟨0⟩::pre.stack) 1
        (by simpa [stepPre,zMid] using fit1)
  · cases arg with
    | none =>
      cases p <;> contradiction
    | some a =>
      obtain ⟨value,width⟩ := a
      have hw := ReferenceDecodeShape.argument_width pre value width (by rw [decoded])
      rw [decoded] at hw
      change width = argOnNBytesOfInstr (.Push p) at hw
      subst width
      have fit' : (stepPre cost (zMid pre (.Push p))).pc.toNat +
          (argOnNBytesOfInstr (.Push p)+1) < UInt256.size := by
        simpa [stepPre,zMid,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using fit
      have known := (ReferenceControlOps.push p (stepPre cost (zMid pre (.Push p))) value zero fit').1
      have same := Except.ok.inj (hsraw.symm.trans known)
      subst post
      refine ⟨advance v (value::v.stack) (argOnNBytesOfInstr (.Push p)+1),?_,?_⟩
      · simp [action,classify,familyAction,zero]
      · simpa only [h.stack,stepPre,zMid,opcode] using related_advance hr (value::pre.stack) _ fit'

theorem dup {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel cost : Nat} {arg : Option (UInt256 × Nat)}
    (d : Operation.DOp) (h : Related parent v pre)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (.Dup d,arg))
    (hz : Z (D_J pre.executionEnv.code ⟨0⟩) (.Dup d) pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (.Dup d,arg) mid post) :
    ∃ next, action kind (.Dup d,arg) v = some next ∧ Related parent next post := by
  have width : argOnNBytesOfInstr (.Dup d) = 0 := by cases d <;> rfl
  have hn := ReferenceDecodeShape.fixed pre (.Dup d) (congrArg Prod.fst decoded) width
  have ha := (Prod.mk.inj (decoded.symm.trans hn)).2
  subst arg
  obtain ⟨hr,hsraw⟩ := raw_dispatch (.dup d) h hz hs
  obtain ⟨base,above,x,depth,shape⟩ := ReferenceAcceptedStack.dup_inputs d hz
  have known := ReferenceStackOps.dup_step d (stepPre cost (zMid pre (.Dup d))) base above x depth shape
  have same := Except.ok.inj (hsraw.symm.trans known)
  subst post
  have fit := ReferenceRuntimeSites.pc_fit hat
  rw [decoded] at fit
  have fit1 : pre.pc.toNat+1 < UInt256.size := by omega
  refine ⟨advance v (ReferenceWordOps.fromPython ((base++[x]++above)++[x])),?_,
    related_advance hr _ 1 (by simpa [stepPre,zMid] using fit1)⟩
  simp [action,classify,familyAction,h.stack,shape,ReferenceWordOps.fromPython,
    List.reverse_append,List.append_assoc,← depth]

theorem swap {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel cost : Nat} {arg : Option (UInt256 × Nat)}
    (d : Operation.ExOp) (h : Related parent v pre)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (.Exchange d,arg))
    (hz : Z (D_J pre.executionEnv.code ⟨0⟩) (.Exchange d) pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (.Exchange d,arg) mid post) :
    ∃ next, action kind (.Exchange d,arg) v = some next ∧ Related parent next post := by
  have width : argOnNBytesOfInstr (.Exchange d) = 0 := by cases d <;> rfl
  have hn := ReferenceDecodeShape.fixed pre (.Exchange d) (congrArg Prod.fst decoded) width
  have ha := (Prod.mk.inj (decoded.symm.trans hn)).2
  subst arg
  obtain ⟨hr,hsraw⟩ := raw_dispatch (.swap d) h hz hs
  obtain ⟨base,middle,x,top,depth,shape⟩ := ReferenceAcceptedStack.swap_inputs d hz
  have known := ReferenceStackOps.swap_step d (stepPre cost (zMid pre (.Exchange d))) base middle x top depth shape
  have same := Except.ok.inj (hsraw.symm.trans known)
  subst post
  have fit := ReferenceRuntimeSites.pc_fit hat
  rw [decoded] at fit
  have fit1 : pre.pc.toNat+1 < UInt256.size := by omega
  refine ⟨advance v (ReferenceWordOps.fromPython (base++[top]++middle++[x])),?_,
    related_advance hr _ 1 (by simpa [stepPre,zMid] using fit1)⟩
  have hd : List.drop (middle.length+1) middle.reverse = [] :=
    List.drop_eq_nil_of_le (by simp)
  simp [action,classify,familyAction,h.stack,shape,ReferenceWordOps.fromPython,
    List.reverse_append,List.append_assoc,← depth,List.drop_append,hd]

/-- The six control/stack families covered in this module. -/
def Family : Pure → Prop
  | .pop | .jump | .jumpi | .push _ | .dup _ | .swap _ => True
  | _ => False

instance (p : Pure) : Decidable (Family p) := by cases p <;> simp only [Family] <;> infer_instance

theorem accepted {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel cost : Nat} {arg : Option (UInt256 × Nat)}
    (p : Pure) (family : Family p) (h : Related parent v pre)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (opcode p,arg))
    (hz : Z (D_J pre.executionEnv.code ⟨0⟩) (opcode p) pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (opcode p,arg) mid post) :
    ∃ next, action kind (opcode p,arg) v = some next ∧ Related parent next post := by
  cases p with
  | pop => exact pop h hat decoded hz hs
  | jump => exact jump h hat hz hs
  | jumpi => exact jumpi h hat decoded hz hs
  | push p => exact push p h hat decoded hz hs
  | dup d => exact dup d h hat decoded hz hs
  | swap d => exact swap d h hat decoded hz hs
  | _ => cases family

#print axioms pop
#print axioms jump
#print axioms jumpi
#print axioms push
#print axioms dup
#print axioms swap
#print axioms accepted
end Eip8282.Audit.Integrator.ReferencePureControl
