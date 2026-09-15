import Eip8282.Audit.Integrator.ReferencePureAction
import Eip8282.Audit.Integrator.ReferencePureControl
import Eip8282.Audit.Integrator.ReferencePureReverseControl

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferencePureEnvironment -/

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

end

section

/-! ## ReferencePureComplete -/

/-! All supported pure families on one actual accepted step. Actual decoder
operands and post-state are preserved through the common running-view relation. -/
namespace Eip8282.Audit.Integrator.ReferencePureComplete
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferencePureAction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem family {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel cost : Nat} {arg : Option (UInt256 × Nat)}
    (p : Pure) (h : Related parent v pre)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (opcode p,arg))
    (hz : Z (D_J pre.executionEnv.code ⟨0⟩) (opcode p) pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (opcode p,arg) mid post)
    (cdfit : v.env.calldata.size < UInt256.size) :
    ∃ next, action kind (opcode p,arg) v = some next ∧ Related parent next post := by
  cases p
  all_goals first
    | exact ReferencePureAction.binary _ h hat decoded hz hs
    | exact ReferencePureEnvironment.accepted _ (by trivial) h hat decoded hz hs (fun _ => cdfit)
    | exact ReferencePureControl.accepted _ (by trivial) h hat decoded hz hs

theorem accepted {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel cost : Nat}
    (h : Related parent v pre)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (supported : Supported (decodeAt pre).1)
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (decodeAt pre) mid post)
    (cdfit : v.env.calldata.size < UInt256.size) :
    ∃ next, action kind (decodeAt pre) v = some next ∧ Related parent next post := by
  obtain ⟨p,hp⟩ := supported
  have hd : decodeAt pre = (opcode p,(decodeAt pre).2) := by
    apply Prod.ext
    · exact hp.symm
    · rfl
  have hz' : Z (D_J pre.executionEnv.code ⟨0⟩) (opcode p) pre = .ok (mid,cost) := by
    simpa only [hat.1,hp] using hz
  have hs' : StepOk (fuel+1) cost (opcode p,(decodeAt pre).2) mid post := by
    rw [hd] at hs
    exact hs
  obtain ⟨next,ha,hr⟩ := family p h hat hd hz' hs' cdfit
  exact ⟨next,by rw [hd]; exact ha,hr⟩

#print axioms family
#print axioms accepted
end Eip8282.Audit.Integrator.ReferencePureComplete

end

section

/-! ## ReferencePureReverseBinary -/

/-! Reverse raw arithmetic effects on the fixed protected runtimes. Operands
come from successful source-shaped actions, not old admission. This does not
identify gas meters or assert extraction from the Python interpreter. -/
namespace Eip8282.Audit.Integrator.ReferencePureReverseBinary
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferencePureAction
set_option autoImplicit false

theorem raw {kind : Kind} {parent : ReferenceStorageView.Parent} {v next : View}
    {pre : EVM.State} {arg : Option (UInt256 × Nat)}
    (b : ReferenceWordOps.Binary) (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (ReferenceWordOps.opcode b,arg))
    (effect : action kind (ReferenceWordOps.opcode b,arg) v = some next) :
    ∃ post, EvmYul.step (ReferenceWordOps.opcode b) arg pre = .ok post ∧
      Related parent next post := by
  have fit := ReferenceRuntimeSites.pc_fit site
  rw [decoded] at fit
  have width : argOnNBytesOfInstr (ReferenceWordOps.opcode b) = 0 := by cases b <;> rfl
  have fit1 : pre.pc.toNat+1 < UInt256.size := by simpa [width] using fit
  change (classify (opcode (.binary b))).bind _ = _ at effect
  rw [classify_opcode] at effect
  simp only [Option.bind_some] at effect
  cases shape : v.stack with
  | nil => simp [familyAction,shape] at effect
  | cons x tail =>
    cases tail with
    | nil => simp [familyAction,shape] at effect
    | cons y rest =>
      have stack : pre.stack = x::y::rest := related.stack.symm.trans shape
      simp only [familyAction,shape] at effect
      cases effect
      exact ⟨_,binary_raw b arg pre x y rest stack,related_advance related _ 1 fit1⟩

#print axioms raw
end Eip8282.Audit.Integrator.ReferencePureReverseBinary

end

section

/-! ## ReferencePureReverseEnvironment -/

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

end

section

/-! ## ReferencePureReverseComplete -/

/-! Compose the pure inverse families without assuming a second execution.
The successful action itself supplies classification; actual decode binds its
instruction. Guarded admission and source extraction are separate consumers. -/
namespace Eip8282.Audit.Integrator.ReferencePureReverseComplete
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferencePureAction
set_option autoImplicit false

theorem family {kind : Kind} {parent : ReferenceStorageView.Parent} {v next : View}
    {pre : EVM.State} {arg : Option (UInt256 × Nat)}
    (p : Pure) (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (opcode p,arg))
    (effect : action kind (opcode p,arg) v = some next) :
    ∃ post, EvmYul.step (opcode p) arg pre = .ok post ∧ Related parent next post := by
  cases p
  all_goals first
    | exact ReferencePureReverseBinary.raw _ related site decoded effect
    | exact ReferencePureReverseEnvironment.raw _ (by trivial) related site decoded effect
    | exact ReferencePureReverseControl.raw _ (by trivial) related site decoded effect

theorem raw {kind : Kind} {parent : ReferenceStorageView.Parent} {v next : View}
    {pre : EVM.State} (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (effect : action kind (decodeAt pre) v = some next) :
    ∃ post, EvmYul.step (decodeAt pre).1 (decodeAt pre).2 pre = .ok post ∧
      Related parent next post := by
  cases classified : classify (decodeAt pre).1 with
  | none => simp [action,classified] at effect
  | some p =>
    have op := classify_sound classified
    have decoded : decodeAt pre = (opcode p,(decodeAt pre).2) := Prod.ext op.symm rfl
    obtain ⟨post,step,relatedPost⟩ := family p related site decoded (by simpa only [op] using effect)
    exact ⟨post,by simpa only [op] using step,relatedPost⟩

#print axioms family
#print axioms raw
end Eip8282.Audit.Integrator.ReferencePureReverseComplete

end
