import Eip8282.Audit.Integrator.ExecutionFunding
import Eip8282.Audit.Integrator.NestedFrameOccurrence

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## NestedFundingInterface -/

/-!
# Entry funding interfaces for actual nested invocation traversal

The world is the literal request input. Only wrapper requests need admission:
Theta's transfer must be affordable, and Lambda additionally starts after a
positive sender nonce update. Actual selected-child gates must derive these
facts; they are not intended as per-child assumptions in the global theorem.
-/
namespace Eip8282.Audit.Integrator.NestedFunding
open EvmYul EvmYul.EVM
open NestedEvents TransferFunding
set_option autoImplicit false

def inputWorld : Request → AccountMap .EVM
  | .x _ _ pre => pre.accountMap
  | .xi _ a => a.world
  | .theta _ a => a.world
  | .lambda _ a => a.world
  | .step _ a => a.pre.accountMap

def GoodFunding : Request → Prop
  | .theta _ a => a.value.toNat ≤ worldBalance a.world a.source
  | .lambda _ a => a.value.toNat ≤ worldBalance a.world a.source ∧
      ExecutionFunding.NonzeroNonce a.world a.source
  | _ => True

end Eip8282.Audit.Integrator.NestedFunding

end

section

/-! ## NestedFundingEdges -/

/-! Funding of the literal selected child inputs and wrapper entries.
The dispatcher gates produce admission; no child budget is assumed. -/
namespace Eip8282.Audit.Integrator.NestedFunding
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open NestedEvents TransferFunding
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem theta_entry {n : Nat} {a : ThetaArgs}
    (funded : GoodFunding (.theta n a)) (bytes : ByteArray) :
    worldFunds (a.xiArgs bytes).world ≤ worldFunds a.world :=
  entry_funds_le (a.context 0 bytes) funded

theorem lambda_entry_distinct {n : Nat} {a : LambdaArgs} {bytes : ByteArray}
    (funded : GoodFunding (.lambda n a))
    (he : a.source ≠ CreationSettlement.address bytes) :
    worldFunds (a.xiArgs bytes).world ≤ worldFunds a.world :=
  CreationFunding.entry_distinct (a.context 0) _ he funded.1

theorem lambda_alias_invalid {n : Nat} {a : LambdaArgs} {bytes : ByteArray}
    (funded : GoodFunding (.lambda n a))
    (he : a.source = CreationSettlement.address bytes) :
    (a.xiArgs bytes).env.code = ⟨#[0xfe]⟩ := by
  obtain ⟨account, hs, hn⟩ := funded.2
  change (a.context 0).selectedCode (CreationSettlement.address bytes) = _
  rw [← he]
  exact CreationFunding.alias_selected_invalid (a.context 0) account hs hn

private theorem call_input (n : Nat) (pre : EVM.State)
    (requested target value off len : UInt256) (hg : CallOutcome.Gate pre value) :
    GoodFunding (.theta n (dispatchCallArgs pre requested target value off len)) := by
  change value.toNat ≤ worldBalance pre.accountMap
    (AccountAddress.ofUInt256 (UInt256.ofNat pre.executionEnv.codeOwner))
  rw [CallFamilyGas.address_word]
  exact CallFunding.gate_to_nat _ _ _ hg.1

private theorem family_input (k : CallFamilyGas.Variant) (n : Nat) (pre : EVM.State)
    (requested target value off len : UInt256) (hg : CallFamilyGas.gate k pre value) :
    GoodFunding (.theta n (familyArgs k pre requested target value off len)) := by
  exact CallFunding.family_funded k n .empty pre requested target value off len hg.1

private theorem creation_input (k : CreationGas.Variant) (n cost : Nat) (pre : EVM.State)
    (value off len salt : UInt256) (hn : CreationGas.nonceAllowed pre)
    (hg : CreationGas.gate pre value off len) :
    GoodFunding (.lambda n (creationArgs k cost pre value off len salt)) := by
  change value.toNat ≤ worldBalance (CreationFunding.nonceWorld pre) pre.executionEnv.codeOwner ∧
    ExecutionFunding.NonzeroNonce (CreationFunding.nonceWorld pre) pre.executionEnv.codeOwner
  constructor
  · rw [CreationFunding.nonce_balance]
    exact CallFunding.gate_to_nat _ _ _ hg.1
  · exact CreationFunding.nonce_positive pre hn

private theorem creation_input_world (k : CreationGas.Variant) (cost : Nat) (pre : EVM.State)
    (value off len salt : UInt256) :
    worldFunds (creationArgs k cost pre value off len salt).world = worldFunds pre.accountMap :=
  CreationFunding.nonce_preserves pre

/-- Every literal selected child receives the gate-derived funds and nonce facts.
The input total is bounded by the real pre-Z world, including creation nonce updates. -/
theorem selected_child_funding {n : Nat} {a : StepArgs} {q : Request}
    (h : StepChild n a (some q)) :
    GoodFunding q ∧ worldFunds (inputWorld q) ≤ worldFunds a.pre.accountMap := by
  have hm : a.mid.accountMap = a.pre.accountMap := by
    rw [Z_ok_state a.guard]
    rfl
  unfold StepChild selectedChild at h
  split at h
  · cases h
  · split at h
    all_goals repeat first | split at h | contradiction
    all_goals simp only [Option.some.injEq, reduceCtorEq] at h
    all_goals subst q
    all_goals constructor
    all_goals first
      | exact call_input _ _ _ _ _ _ _ (by assumption)
      | exact family_input _ _ _ _ _ _ _ _ (by assumption)
      | exact creation_input _ _ _ _ _ _ _ _ (by tauto) (by tauto)
      | (change worldFunds a.mid.accountMap ≤ worldFunds a.pre.accountMap; rw [hm])
      | (change worldFunds (creationArgs _ _ _ _ _ _ _).world ≤ _;
          rw [creation_input_world, hm])

#print axioms theta_entry
#print axioms lambda_entry_distinct
#print axioms lambda_alias_invalid
#print axioms selected_child_funding
end Eip8282.Audit.Integrator.NestedFunding

end
