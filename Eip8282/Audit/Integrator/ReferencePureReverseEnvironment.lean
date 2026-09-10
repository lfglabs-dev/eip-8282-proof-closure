import Eip8282.Audit.Integrator.ReferencePureEnvironment

/-! Reverse raw effect transport for six fixed protected-runtime pure families.
Successful source-shaped action supplies operands and CALLDATASIZE's checked
word-size gate; actual site/decode supplies PC fit and immediate shape. This
constructs the raw pinned effect only: stack overflow, Z/gas admission, actual
source interpreter extraction and outer receipt equivalence are not asserted. -/
namespace Eip8282.Audit.Integrator.ReferencePureReverseEnvironment
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferencePureAction ReferencePureEnvironment
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem raw {kind : Kind} {parent : ReferenceStorageView.Parent} {v next : View}
    {pre : EVM.State} {arg : Option (UInt256 × Nat)}
    (p : Pure) (family : Family p) (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (opcode p,arg))
    (effect : action kind (opcode p,arg) v = some next) :
    ∃ post, EvmYul.step (opcode p) arg pre = .ok post ∧ Related parent next post := by
  have width : argOnNBytesOfInstr (opcode p) = 0 := by
    cases p <;> simp_all [Family,opcode,argOnNBytesOfInstr]
  have fixed := ReferenceDecodeShape.fixed pre (opcode p) (by rw [decoded]) width
  have ha : arg = none := congrArg Prod.snd (decoded.symm.trans fixed)
  subst arg
  have fit := ReferenceRuntimeSites.pc_fit site
  have fit1 : pre.pc.toNat+1 < UInt256.size := by omega
  cases p with
  | binary b => cases family
  | pop => cases family
  | jump => cases family
  | jumpi => cases family
  | push p => cases family
  | dup d => cases family
  | swap d => cases family
  | iszero =>
    cases shape : v.stack with
    | nil => simp [action,opcode,classify,familyAction,shape] at effect
    | cons x rest =>
      have stack : pre.stack = x::rest := related.stack.symm.trans shape
      simp only [action,opcode,classify,Option.bind_some,familyAction,shape] at effect
      cases effect
      exact ⟨_,ReferenceWordOps.isZero_step pre x rest stack,related_advance related _ 1 fit1⟩
  | caller =>
    simp only [action,opcode,classify,Option.bind_some,familyAction] at effect
    cases effect
    refine ⟨_,ReferenceEnvironmentOps.caller_step pre,?_⟩
    simpa only [related.env,related.stack] using
      related_advance related (UInt256.ofNat pre.executionEnv.source.val::pre.stack) 1 fit1
  | value =>
    simp only [action,opcode,classify,Option.bind_some,familyAction] at effect
    cases effect
    refine ⟨_,ReferenceEnvironmentOps.callvalue_step pre,?_⟩
    simpa only [related.env,related.stack] using
      related_advance related (pre.executionEnv.weiValue::pre.stack) 1 fit1
  | size =>
    simp only [action,opcode,classify,Option.bind_some,familyAction] at effect
    split at effect
    · cases effect
      refine ⟨_,ReferenceEnvironmentOps.calldatasize_step pre,?_⟩
      simpa only [related.env,related.stack] using
        related_advance related (UInt256.ofNat pre.executionEnv.calldata.size::pre.stack) 1 fit1
    · contradiction
  | load =>
    cases shape : v.stack with
    | nil => simp [action,opcode,classify,familyAction,shape] at effect
    | cons x rest =>
      have stack : pre.stack = x::rest := related.stack.symm.trans shape
      simp only [action,opcode,classify,Option.bind_some,familyAction,shape] at effect
      cases effect
      refine ⟨_,ReferenceEnvironmentOps.calldataload_step pre x rest stack,?_⟩
      simpa only [related.env] using
        related_advance related (ReferenceEnvironmentOps.load pre.executionEnv.calldata x.toNat::rest) 1 fit1
  | jumpdest =>
    simp only [action,opcode,classify,Option.bind_some,familyAction] at effect
    cases effect
    refine ⟨pre.replaceStackAndIncrPC pre.stack,rfl,?_⟩
    simpa only [related.stack] using related_advance related pre.stack 1 fit1

#print axioms raw
end Eip8282.Audit.Integrator.ReferencePureReverseEnvironment
