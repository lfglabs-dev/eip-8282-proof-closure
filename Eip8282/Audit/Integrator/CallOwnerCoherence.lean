import Eip8282.Audit.Integrator.JournalInvariant
import Eip8282.Audit.Integrator.NestedEventArgs

/-!
# Actual selected calls bind protected storage owner, installed code and value

An external frame's CALL/STATICCALL to a protected address selects its installed
runtime and an ordinary apparent value. CALLCODE and DELEGATECALL retain that
external frame's storage owner and therefore cannot masquerade as a protected
call. The parent-owner inequality is an explicit traversal invariant; this
module does not infer it merely from code installed somewhere in the world.
-/
namespace Eip8282.Audit.Integrator.CallOwnerCoherence
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open NestedEvents JournalInvariant
open ReachableCalls (Contract address runtime)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def Coherent (kind : Contract) (a : ThetaArgs) : Prop :=
  a.target = address kind → a.code = .Code (runtime kind) ∧ a.apparent = a.value

theorem canonical_not_precompile (kind : Contract) : address kind ∉ π := by
  cases kind <;> decide +kernel

theorem installed_toExecute {kind : Contract} {world : AccountMap .EVM}
    (hc : CodeAt kind world) : toExecute .EVM world (address kind) = .Code (runtime kind) := by
  obtain ⟨account,ha,hcode⟩ := hc
  simp only [toExecute, canonical_not_precompile kind, ↓reduceIte]
  simp only [ha, hcode]
  rfl

private theorem call_coherent (kind : Contract) (pre : EVM.State)
    (requested target value off len : UInt256) (hc : CodeAt kind pre.accountMap) :
    Coherent kind (dispatchCallArgs pre requested target value off len) := by
  intro ht
  constructor
  · change toExecute .EVM pre.accountMap (AccountAddress.ofUInt256 target) = _
    change AccountAddress.ofUInt256 target = address kind at ht
    rw [ht]
    exact installed_toExecute hc
  · rfl

private theorem family_coherent (variant : CallFamilyGas.Variant) (kind : Contract)
    (pre : EVM.State) (requested target value off len : UInt256)
    (hc : CodeAt kind pre.accountMap) (hne : pre.executionEnv.codeOwner ≠ address kind) :
    Coherent kind (familyArgs variant pre requested target value off len) := by
  intro ht
  cases variant with
  | callcode =>
    change AccountAddress.ofUInt256 (UInt256.ofNat pre.executionEnv.codeOwner) = address kind at ht
    rw [CallFamilyGas.address_word] at ht
    exact False.elim (hne ht)
  | delegatecall =>
    change AccountAddress.ofUInt256 (UInt256.ofNat pre.executionEnv.codeOwner) = address kind at ht
    rw [CallFamilyGas.address_word] at ht
    exact False.elim (hne ht)
  | staticcall =>
    constructor
    · change toExecute .EVM pre.accountMap (AccountAddress.ofUInt256 target) = _
      change AccountAddress.ofUInt256 target = address kind at ht
      rw [ht]
      exact installed_toExecute hc
    · rfl

/-- The literal selected call of an external owner has the protected-call
binding. No callee result, final world or successful execution is assumed. -/
theorem selected_theta {kind : Contract} {n fuel : Nat} {a : StepArgs} {b : ThetaArgs}
    (h : StepChild n a (some (.theta fuel b)))
    (hc : CodeAt kind a.pre.accountMap)
    (hne : a.pre.executionEnv.codeOwner ≠ address kind) : Coherent kind b := by
  have hw : a.mid.accountMap = a.pre.accountMap := by rw [Z_ok_state a.guard]; rfl
  have he : a.mid.executionEnv = a.pre.executionEnv := by rw [Z_ok_state a.guard]; rfl
  have hcm : CodeAt kind a.mid.accountMap := by rw [hw]; exact hc
  have hnem : a.mid.executionEnv.codeOwner ≠ address kind := by rw [he]; exact hne
  unfold StepChild selectedChild at h
  split at h
  · cases h
  · split at h
    all_goals repeat first | split at h | contradiction
    all_goals simp only [Option.some.injEq, Request.theta.injEq, reduceCtorEq] at h
    all_goals obtain ⟨_,rfl⟩ := h
    all_goals first
      | exact call_coherent _ _ _ _ _ _ _ hcm
      | exact family_coherent _ _ _ _ _ _ _ _ hcm hnem

/-- The existing code invariant supplies the installed-account witness for
the public concrete transition; coherence supplies only code/value selection. -/
theorem pinned {kind : Contract} {a : ThetaArgs} (fuel : Nat)
    (hc : CodeAt kind a.world) (coherent : Coherent kind a)
    (ht : a.target = address kind) :
    ReachableCalls.PinnedCall kind (a.context fuel (runtime kind)) := by
  obtain ⟨_,hv⟩ := coherent ht
  obtain ⟨account,ha,hcode⟩ := hc
  refine ⟨ht,rfl,?_,hv⟩
  exact ⟨account,by change a.world.get? a.target = some account; rw [ht]; exact ha,hcode⟩

#print axioms canonical_not_precompile
#print axioms installed_toExecute
#print axioms selected_theta
#print axioms pinned
end Eip8282.Audit.Integrator.CallOwnerCoherence
