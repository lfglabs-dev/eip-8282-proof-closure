import Eip8282.Audit.Integrator.ReferencePureAction

/-! Six pure environment-family cases of the source-shaped running action.
Operands come from actual Z, the known raw step is on the charged state, and
all other view fields are transported by the shared foundation. CALLDATASIZE
keeps its checked size gate; only that family requires the input fit. Source
caller-byte/value binding and Python execution remain separate adapters. -/
namespace Eip8282.Audit.Integrator.ReferencePureEnvironment
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferencePureAction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def Family : Pure → Prop
  | .iszero | .caller | .value | .size | .load | .jumpdest => True
  | _ => False

instance (p : Pure) : Decidable (Family p) := by cases p <;> simp only [Family] <;> infer_instance

/-- Actual accepted instruction produces the partial action's successful
result and complete post-view relation. No postcondition is supplied. -/
theorem accepted {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel cost : Nat} {arg : Option (UInt256 × Nat)}
    (p : Pure) (family : Family p) (h : Related parent v pre)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (opcode p,arg))
    (hz : Z (D_J pre.executionEnv.code ⟨0⟩) (opcode p) pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (opcode p,arg) mid post)
    (cdfit : p = .size → v.env.calldata.size < UInt256.size) :
    ∃ next, action kind (opcode p,arg) v = some next ∧ Related parent next post := by
  obtain ⟨hr,hsraw⟩ := raw_dispatch p h hz hs
  have fit := ReferenceRuntimeSites.pc_fit hat
  rw [decoded] at fit
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
    obtain ⟨rest,x,shape,_⟩ := ReferenceAcceptedStack.pop1 hz (by decide)
    have known := ReferenceWordOps.isZero_step (stepPre cost (zMid pre (opcode .iszero))) x rest shape
    have same := Except.ok.inj (hsraw.symm.trans known)
    subst post
    refine ⟨advance v (UInt256.ofNat (ReferenceWordOps.referenceIsZero x.toNat)::rest),?_,?_⟩
    · simp [action,classify,familyAction,opcode,h.stack,shape]
    · exact related_advance hr _ 1 fit1
  | caller =>
    have known := ReferenceEnvironmentOps.caller_step (stepPre cost (zMid pre (opcode .caller)))
    have same := Except.ok.inj (hsraw.symm.trans known)
    subst post
    refine ⟨advance v (UInt256.ofNat v.env.source.val::v.stack),?_,?_⟩
    · rfl
    · simpa only [h.env,h.stack,stepPre,zMid] using
        related_advance hr (UInt256.ofNat pre.executionEnv.source.val::pre.stack) 1
          fit1
  | value =>
    have known := ReferenceEnvironmentOps.callvalue_step (stepPre cost (zMid pre (opcode .value)))
    have same := Except.ok.inj (hsraw.symm.trans known)
    subst post
    refine ⟨advance v (v.env.weiValue::v.stack),?_,?_⟩
    · rfl
    · simpa only [h.env,h.stack,stepPre,zMid] using
        related_advance hr (pre.executionEnv.weiValue::pre.stack) 1
          fit1
  | size =>
    have known := ReferenceEnvironmentOps.calldatasize_step (stepPre cost (zMid pre (opcode .size)))
    have same := Except.ok.inj (hsraw.symm.trans known)
    subst post
    refine ⟨advance v (UInt256.ofNat v.env.calldata.size::v.stack),?_,?_⟩
    · simp only [action,opcode,classify,Option.bind_some,familyAction,if_pos (cdfit rfl)]
    · simpa only [h.env,h.stack,stepPre,zMid] using
        related_advance hr (UInt256.ofNat pre.executionEnv.calldata.size::pre.stack) 1
          fit1
  | load =>
    obtain ⟨rest,x,shape,_⟩ := ReferenceAcceptedStack.pop1 hz (by decide)
    have known := ReferenceEnvironmentOps.calldataload_step
      (stepPre cost (zMid pre (opcode .load))) x rest shape
    have same := Except.ok.inj (hsraw.symm.trans known)
    subst post
    refine ⟨advance v (ReferenceEnvironmentOps.load v.env.calldata x.toNat::rest),?_,?_⟩
    · simp [action,classify,familyAction,opcode,h.stack,shape]
    · simpa only [h.env,stepPre,zMid] using
        related_advance hr (ReferenceEnvironmentOps.load pre.executionEnv.calldata x.toNat::rest) 1
          fit1
  | jumpdest =>
    have known : EvmYul.step (τ := .EVM) .JUMPDEST arg (stepPre cost (zMid pre .JUMPDEST)) =
        .ok ((stepPre cost (zMid pre .JUMPDEST)).replaceStackAndIncrPC pre.stack) := rfl
    have same := Except.ok.inj (hsraw.symm.trans known)
    subst post
    refine ⟨advance v v.stack,?_,?_⟩
    · rfl
    · simpa only [h.stack,opcode] using related_advance hr pre.stack 1 fit1

#print axioms accepted
end Eip8282.Audit.Integrator.ReferencePureEnvironment
