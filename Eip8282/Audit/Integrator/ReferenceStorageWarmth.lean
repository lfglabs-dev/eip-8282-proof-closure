import Eip8282.Audit.Integrator.ReferenceSourceReadings
import Eip8282.Audit.Integrator.Topics.Reference

/-! Successful local runtime access-set transport. Source warmth is a separate
set from BAL reads. SLOAD inserts its key; SSTORE inserts under actual owner
existence. Other supported runtime instructions preserve this set. Initial
source access-set correspondence and recursive rollback remain external. -/
namespace Eip8282.Audit.Integrator.ReferenceStorageWarmth
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open ReferenceRuntimeView ReferenceSourceReadings RuntimeOpcodeScope
open Std
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private theorem word_compare (a b : UInt256) : compare a b = compare a.val b.val := by
  cases a with | mk a =>
    cases b with | mk b =>
      change (compare a b).then .eq = compare a b
      cases compare a b <;> rfl

private instance : TransCmp Substate.storageKeysCmp := by
  unfold Substate.storageKeysCmp
  infer_instance

private theorem keys_compare_eq (a b : AccountAddress × UInt256) :
    Substate.storageKeysCmp a b = .eq ↔ a = b := by
  change (compare a.1 b.1).then (compare a.2 b.2) = .eq ↔ a = b
  rw [word_compare]
  simp only [Ordering.then_eq_eq,Std.compare_eq_iff_eq]
  constructor
  · rintro ⟨ha,hk⟩
    exact Prod.ext ha (congrArg UInt256.mk hk)
  · intro h
    subst b
    exact ⟨rfl,rfl⟩

private theorem insert_related {w : Warm} {pre post : EVM.State}
    (h : WarmRelated w pre) (a : AccountAddress) (key : UInt256)
    (hk : post.substate.accessedStorageKeys = pre.substate.accessedStorageKeys.insert (a,key)) :
    WarmRelated (insert (a,key.toByteArray) w) post := by
  intro b query
  rw [hk,Std.TreeSet.contains_insert]
  simp only [Set.mem_insert_iff,Bool.or_eq_true,beq_iff_eq,keys_compare_eq]
  have he : (b,query.toByteArray) = (a,key.toByteArray) ↔ (a,key) = (b,query) := by
    simp only [Prod.mk.injEq,ReferenceStorageView.key_injective.eq_iff]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> exact ⟨h₁.symm,h₂.symm⟩
  rw [he,h b query]

private theorem raw_dup (n : Nat) {pre post : EVM.State}
    (hs : EvmYul.dup n pre = .ok post) :
    post.substate.accessedStorageKeys = pre.substate.accessedStorageKeys := by
  unfold EvmYul.dup at hs
  dsimp only at hs
  split at hs
  · cases hs; rfl
  · cases hs

private theorem raw_swap (n : Nat) {pre post : EVM.State}
    (hs : EvmYul.swap n pre = .ok post) :
    post.substate.accessedStorageKeys = pre.substate.accessedStorageKeys := by
  unfold EvmYul.swap at hs
  dsimp only at hs
  split at hs
  · cases hs; rfl
  · cases hs

private theorem raw_other {op : Operation .EVM} (hop : op ∈ allowedOps)
    (hl : op ≠ .SLOAD) (hst : op ≠ .SSTORE)
    {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (hs : EvmYul.step op arg pre = .ok post) :
    post.substate.accessedStorageKeys = pre.substate.accessedStorageKeys := by
  simp only [allowedOps,List.mem_cons,List.not_mem_nil,or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact False.elim (hl rfl)
    | exact False.elim (hst rfl)
    | exact raw_dup _ hs
    | exact raw_swap _ hs
    | skip
  all_goals
    obtain ⟨sh,pc,stk,ex⟩ := pre
    rcases arg with _ | ⟨v,n⟩
    all_goals rcases stk with _ | ⟨x, _ | ⟨y, _ | ⟨z,tail⟩⟩⟩
    all_goals cases hs <;> rfl

private theorem raw_load {pre post : EVM.State} {key : UInt256} {rest : Stack UInt256}
    (shape : pre.stack = key::rest) (hs : EvmYul.step (τ := .EVM) .SLOAD none pre = .ok post) :
    post.substate.accessedStorageKeys =
      pre.substate.accessedStorageKeys.insert (pre.executionEnv.codeOwner,key) := by
  obtain ⟨sh,pc,stk,ex⟩ := pre
  dsimp only at shape
  subst stk
  cases hs
  rfl

private theorem raw_store {pre post : EVM.State} {key value : UInt256} {rest : Stack UInt256}
    (owner : SystemSpec.HasOwner pre.toState) (shape : pre.stack = key::value::rest)
    (hs : EvmYul.step (τ := .EVM) .SSTORE none pre = .ok post) :
    post.substate.accessedStorageKeys =
      pre.substate.accessedStorageKeys.insert (pre.executionEnv.codeOwner,key) := by
  have known : EvmYul.step (τ := .EVM) .SSTORE none pre =
      .ok (({pre with toState := pre.toState.sstore key value} : EVM.State).replaceStackAndIncrPC rest) := by
    obtain ⟨sh,pc,stk,ex⟩ := pre
    dsimp only at shape
    subst stk
    rfl
  have same := Except.ok.inj (hs.symm.trans known)
  subst post
  obtain ⟨account,haccount⟩ := owner
  change (pre.toState.sstore key value).substate.accessedStorageKeys = _
  unfold EvmYul.State.sstore
  dsimp only
  have hlookup : pre.toState.lookupAccount pre.executionEnv.codeOwner = some account := haccount
  rw [hlookup]
  rfl

/-- Actual accepted runtime steps supply access-set evolution. No post-access
set premise is assumed; owner existence excludes pinned absent-owner SSTORE. -/
theorem accepted_warm {image : RuntimeExecutionScope.Image} {parent : ReferenceStorageView.Parent}
    {v : View} {w : Warm} {pre mid post : EVM.State} {fuel cost : Nat}
    (hat : RuntimeExecutionScope.At image pre)
    (hz : Z (D_J image.code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (decodeAt pre) mid post)
    (related : Related parent v pre) (warm : WarmRelated w pre) :
    WarmRelated (warmAfter (decodeAt pre).1 v w) post := by
  have hop := RuntimeExecutionScope.opcode_allowed hat
  have he := allowed_excludes _ hop
  have raw : EvmYul.step (decodeAt pre).1 (decodeAt pre).2
      (stepPre cost (zMid pre (decodeAt pre).1)) = .ok post := by
    rw [Z_ok_state hz] at hs
    change EVM.step (fuel+1) cost (some ((decodeAt pre).1,(decodeAt pre).2)) _ = .ok post at hs
    rw [OrdinaryGas.dispatch ⟨he.2.1,he.2.2.1⟩] at hs
    exact hs
  by_cases hl : (decodeAt pre).1 = .SLOAD
  · have hd := ReferenceDecodeShape.fixed pre .SLOAD hl rfl
    have hz' : Z (D_J image.code ⟨0⟩) .SLOAD pre = .ok (mid,cost) := by simpa only [hl] using hz
    obtain ⟨rest,key,shape,_⟩ := ReferenceAcceptedStack.pop1 hz' (by decide)
    have hk := raw_load (pre := stepPre cost (zMid pre .SLOAD)) shape (by simpa only [hd] using raw)
    have hh := insert_related warm pre.executionEnv.codeOwner key hk
    simpa only [warmAfter,hl,related.env,related.stack,shape,List.getElem!_cons_zero] using hh
  · by_cases hst : (decodeAt pre).1 = .SSTORE
    · have hd := ReferenceDecodeShape.fixed pre .SSTORE hst rfl
      have hz' : Z (D_J image.code ⟨0⟩) .SSTORE pre = .ok (mid,cost) := by simpa only [hst] using hz
      obtain ⟨rest,key,value,shape,_⟩ := ReferenceAcceptedStack.pop2 hz' (by decide)
      have hk := raw_store (pre := stepPre cost (zMid pre .SSTORE)) related.owner shape
        (by simpa only [hd] using raw)
      have hh := insert_related warm pre.executionEnv.codeOwner key hk
      simpa only [warmAfter,hst,related.env,related.stack,shape,List.getElem!_cons_zero] using hh
    · have hk := raw_other hop hl hst raw
      have hw : warmAfter (decodeAt pre).1 v w = w := by
        unfold warmAfter
        split <;> simp_all
      rw [hw]
      intro a key
      rw [hk]
      exact warm a key

#print axioms accepted_warm
end Eip8282.Audit.Integrator.ReferenceStorageWarmth
