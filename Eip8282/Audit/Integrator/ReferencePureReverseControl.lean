import Eip8282.Audit.Integrator.ReferencePureControl

/-! Reverse raw effects for fixed-runtime POP/JUMP/JUMPI/PUSH/DUP/SWAP.
Successful source-shaped actions supply real operands/indexed items; site and
full decode supply immediate width and natural PC fit. No old Z acceptance,
gas equality, source stack-overflow admission or Python refinement is assumed.
Taken-jump source validity is retained in the action; raw old JUMP itself does
not check it. The guarded replay consumer must separately construct Z. -/
namespace Eip8282.Audit.Integrator.ReferencePureReverseControl
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferencePureAction ReferencePureControl
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem lookup_split {s : List UInt256} {n : Nat} {x : UInt256}
    (h : s[n]? = some x) : ∃ above below, above.length = n ∧ s = above++x::below := by
  induction n generalizing s with
  | zero =>
    cases s with
    | nil => cases h
    | cons head tail => cases h; exact ⟨[],tail,rfl,rfl⟩
  | succ n ih =>
    cases s with
    | nil => cases h
    | cons head tail =>
      obtain ⟨above,below,hlen,shape⟩ := ih (s := tail) h
      exact ⟨head::above,below,by simp [hlen],by simp [shape]⟩

private theorem noarg {pre : EVM.State} {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    (decoded : decodeAt pre = (op,arg)) (width : argOnNBytesOfInstr op = 0) : arg = none :=
  congrArg Prod.snd (decoded.symm.trans (ReferenceDecodeShape.fixed pre op (congrArg Prod.fst decoded) width))

theorem raw {kind : Kind} {parent : ReferenceStorageView.Parent} {v next : View}
    {pre : EVM.State} {arg : Option (UInt256 × Nat)}
    (p : Pure) (family : Family p) (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (opcode p,arg))
    (effect : action kind (opcode p,arg) v = some next) :
    ∃ post, EvmYul.step (opcode p) arg pre = .ok post ∧ Related parent next post := by
  have fit := ReferenceRuntimeSites.pc_fit site
  have fit1 : pre.pc.toNat+1 < UInt256.size := by omega
  cases p with
  | binary b => cases family
  | iszero => cases family
  | caller => cases family
  | value => cases family
  | size => cases family
  | load => cases family
  | jumpdest => cases family
  | pop =>
    have ha := noarg decoded (by rfl)
    subst arg
    cases shape : v.stack with
    | nil => simp [action,opcode,classify,familyAction,shape] at effect
    | cons x rest =>
      have stack := related.stack.symm.trans shape
      simp only [action,opcode,classify,Option.bind_some,familyAction,shape] at effect
      cases effect
      exact ⟨_,(ReferenceControlOps.pop pre x rest stack fit1).1,related_advance related rest 1 fit1⟩
  | jump =>
    cases shape : v.stack with
    | nil => simp [action,opcode,classify,familyAction,shape] at effect
    | cons dest rest =>
      have stack := related.stack.symm.trans shape
      simp only [action,opcode,classify,Option.bind_some,familyAction,shape] at effect
      split at effect
      · cases effect
        refine ⟨{pre with pc := dest,stack := rest},?_,related_jump related rest dest⟩
        exact pureStep_sound (by decide) (by simp only [pureStep,opcode,stack])
      · contradiction
  | jumpi =>
    cases shape : v.stack with
    | nil => simp [action,opcode,classify,familyAction,shape] at effect
    | cons dest tail =>
      cases tail with
      | nil => simp [action,opcode,classify,familyAction,shape] at effect
      | cons cond rest =>
        have stack := related.stack.symm.trans shape
        simp only [action,opcode,classify,Option.bind_some,familyAction,shape] at effect
        split at effect
        · rename_i zero
          cases effect
          exact ⟨_,step_JUMPI_untaken stack zero,related_advance related rest 1 fit1⟩
        · rename_i nonzero
          split at effect
          · cases effect
            exact ⟨_,step_JUMPI_taken stack nonzero,related_jump related rest dest⟩
          · contradiction
  | push op =>
    by_cases zero : op = .PUSH0
    · subst op
      simp only [action,opcode,classify,Option.bind_some,familyAction] at effect
      cases effect
      refine ⟨pre.replaceStackAndIncrPC (⟨0⟩::pre.stack),rfl,?_⟩
      simpa only [related.stack] using related_advance related (⟨0⟩::pre.stack) 1 fit1
    · cases arg with
      | none => simp [action,opcode,classify,familyAction,zero] at effect
      | some pair =>
        obtain ⟨value,width⟩ := pair
        simp only [action,opcode,classify,Option.bind_some,familyAction,if_neg zero] at effect
        split at effect
        · rename_i hw
          subst width
          cases effect
          rw [decoded] at fit
          change pre.pc.toNat+1+argOnNBytesOfInstr (.Push op) < UInt256.size at fit
          have fit' : pre.pc.toNat+(argOnNBytesOfInstr (.Push op)+1) < UInt256.size := by omega
          refine ⟨_,(ReferenceControlOps.push op pre value zero fit').1,?_⟩
          simpa only [related.stack] using related_advance related (value::pre.stack) _ fit'
        · contradiction
  | dup op =>
    have ha := noarg decoded (by cases op <;> rfl)
    subst arg
    simp only [action,opcode,classify,Option.bind_some,familyAction] at effect
    cases selected : v.stack[ReferenceStackOps.dupDepth op-1]? with
    | none => simp only [selected] at effect; contradiction
    | some x =>
      simp only [selected] at effect
      cases effect
      obtain ⟨above,below,hlen,hshape⟩ := lookup_split selected
      have depth : above.reverse.length+1 = ReferenceStackOps.dupDepth op := by
        have hd := (ReferenceStackOps.dup_depth op).1
        simp only [List.length_reverse,hlen]
        omega
      have stack : pre.stack = ReferenceWordOps.fromPython (below.reverse++[x]++above.reverse) := by
        rw [← related.stack,hshape]
        simp [ReferenceWordOps.fromPython,List.reverse_append,List.append_assoc]
      have known := ReferenceStackOps.dup_step op pre below.reverse above.reverse x depth stack
      have actual : EvmYul.step (.Dup op) none pre = .ok (pre.replaceStackAndIncrPC (x::pre.stack)) := by
        simpa [ReferenceWordOps.fromPython,List.reverse_append,← related.stack,hshape,List.append_assoc] using known
      refine ⟨_,actual,?_⟩
      simpa only [related.stack] using related_advance related (x::pre.stack) 1 fit1
  | swap op =>
    have ha := noarg decoded (by cases op <;> rfl)
    subst arg
    cases shape : v.stack with
    | nil => simp [action,opcode,classify,familyAction,shape] at effect
    | cons top tail =>
      simp only [action,opcode,classify,Option.bind_some,familyAction,shape] at effect
      cases selected : tail[ReferenceStackOps.swapDepth op-1]? with
      | none => simp only [selected] at effect; contradiction
      | some x =>
        simp only [selected] at effect
        obtain ⟨middle,below,hlen,hshape⟩ := lookup_split selected
        have depth : middle.reverse.length+1 = ReferenceStackOps.swapDepth op := by
          have hd := (ReferenceStackOps.swap_depth op).1
          simp only [List.length_reverse,hlen]
          omega
        have stack : pre.stack = ReferenceWordOps.fromPython (below.reverse++[x]++middle.reverse++[top]) := by
          rw [← related.stack,shape,hshape]
          simp [ReferenceWordOps.fromPython,List.reverse_append,List.append_assoc]
        have known := ReferenceStackOps.swap_step op pre below.reverse middle.reverse x top depth stack
        have hd : ReferenceStackOps.swapDepth op = middle.length+1 := by simpa using depth.symm
        simp only [hd,Nat.add_sub_cancel,hshape] at effect
        simp only [List.take_append,List.take_length,List.drop_append,
          Nat.sub_self,List.take_zero,
          List.append_nil] at effect
        have drop : middle.drop (middle.length+1) = [] := List.drop_eq_nil_of_le (by omega)
        cases effect
        refine ⟨_,known,?_⟩
        simpa [ReferenceWordOps.fromPython,List.reverse_append,List.append_assoc,drop] using
          related_advance related (ReferenceWordOps.fromPython (below.reverse++[top]++middle.reverse++[x])) 1 fit1

#print axioms raw
end Eip8282.Audit.Integrator.ReferencePureReverseControl
