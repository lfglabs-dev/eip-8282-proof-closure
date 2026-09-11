import Eip8282.Audit.Integrator.ReferenceSourceReplayTrace
import Eip8282.Audit.Integrator.ReferenceRevertView
import Eip8282.Audit.Integrator.ReferenceStopView

/-! Terminal synthetic replay from input resource and stack guards. Source
operation extraction remains separate. REVERT Result describes only the internal
terminal journal, never enclosing call commitment. STOP's source initial output
binding is separate from the actual evaluator's empty output. -/
namespace Eip8282.Audit.Integrator.ReferenceTerminalReplay
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec
open ReferenceRuntimeView ReferenceMemoryCapacity
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def charge (v : View) (off len : UInt256) : Nat :=
  cost (MachineState.M (words v) off.toNat len.toNat)-cost (words v)

private theorem memory_cost {parent : ReferenceStorageView.Parent} {v : View} {pre : EVM.State}
    {off len : UInt256} {rest : Stack UInt256} {op : Operation .EVM}
    (related : Related parent v pre) (shape : v.stack = off::len::rest)
    (hop : op = .RETURN ∨ op = .REVERT) : memoryExpansionCost pre op = charge v off len := by
  have hs : pre.stack = off::len::rest := related.stack.symm.trans shape
  have fit := RuntimeMemoryMonotone.expansion_fit pre.activeWords off len
  have hm : (memoryExpansionCost.μᵢ' pre op).toNat = MachineState.M pre.activeWords.toNat off.toNat len.toNat := by
    rcases hop with rfl | rfl
    all_goals simpa only [memoryExpansionCost.μᵢ',hs,List.getElem!_cons_zero,List.getElem!_cons_succ] using Eip8282.Audit.EntryReach.toNat_ofNat_lit _ fit
  change cost (memoryExpansionCost.μᵢ' pre op).toNat-cost pre.activeWords.toNat = _
  rw [hm,charge,words_related related]

theorem returned (fuel : Nat) {parent : ReferenceStorageView.Parent} {v : View}
    {vj : Array UInt256} {pre : EVM.State} {off len : UInt256} {rest : Stack UInt256}
    (related : Related parent v pre) (decoded : decodeAt pre = (.RETURN,none))
    (shape : v.stack = off::len::rest) (stack : rest.length ≤ 1024)
    (domain : cost (words v)+charge v off len ≤ 30000000)
    (budget : charge v off len ≤ pre.gasAvailable.toNat) :
    ∃ post, X (fuel+2) vj pre = .ok (.success post (ReferenceReturnView.output v off len)) ∧
      ReferenceReturnView.Result parent v off len rest post ∧
      post.gasAvailable.toNat+charge v off len = pre.gasAvailable.toNat := by
  have hs : pre.stack = off::len::rest := related.stack.symm.trans shape
  have mc := memory_cost related shape (Or.inl rfl : Operation.RETURN = .RETURN ∨ Operation.RETURN = .REVERT)
  have hz := Z_memop (vj := vj) (s := pre) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    rfl rfl (by simp [hs]) (by simpa [hs] using stack)
    (by rw [C'_RETURN,mc]; omega) (fun h => absurd h (by decide))
  obtain ⟨post,step⟩ : ∃ post, StepOk (fuel+1) (C' (charged pre .RETURN) .RETURN) (.RETURN,none) (charged pre .RETURN) post :=
    ⟨_,stepOk_halt (f := fuel) (by decide) (Eip8282.Audit.SymExec.step_RETURN hs)⟩
  have cap : post.activeWords.toNat = MachineState.M (words v) off.toNat len.toNat := by
    have raw := step
    change EVM.step (fuel+1) _ (some (.RETURN,none)) _ = .ok post at raw
    rw [OrdinaryGas.dispatch (by decide)] at raw
    have ex := RuntimeMemoryCharges.raw_expansion (by decide : Operation.RETURN ∈ RuntimeOpcodeScope.allowedOps) raw
    simpa only [stepPre,Eip8282.Audit.SymExec.charged,zMid,RuntimeMemoryMonotone.span,hs,List.getElem!_cons_zero,List.getElem!_cons_succ,←words_related related] using ex
  have host : 32*MachineState.M (words v) off.toNat len.toNat < 2^System.Platform.numBits :=
    ReferenceSourceReplayTrace.host_of_cost (by unfold charge at domain; omega)
  obtain ⟨off',len',rest',pop,shape',result⟩ := ReferenceReturnView.terminal hz step related (by omega : post.activeWords.toNat ≤ MachineState.M (words v) off.toNat len.toNat) host
  have eqs := List.cons.inj (shape.symm.trans shape')
  obtain ⟨rfl,tail⟩ := eqs
  obtain ⟨rfl,rfl⟩ := List.cons.inj tail
  have hout : H post.toMachineState .RETURN = some (ReferenceReturnView.output v off len) := by
    change some post.H_return = _
    rw [result.returned]
  refine ⟨post,?_,result,?_⟩
  · exact X_succ_of_halt decoded hz step hout (by decide)
  · have debit := OrdinaryGas.accepted_step_debit (by decide : OrdinaryGas.Ordinary .RETURN) hz step
    rw [mc,C'_RETURN] at debit
    simpa using debit

theorem reverted (fuel : Nat) {parent : ReferenceStorageView.Parent} {v : View}
    {vj : Array UInt256} {pre : EVM.State} {off len : UInt256} {rest : Stack UInt256}
    (related : Related parent v pre) (decoded : decodeAt pre = (.REVERT,none))
    (shape : v.stack = off::len::rest) (stack : rest.length ≤ 1024)
    (domain : cost (words v)+charge v off len ≤ 30000000)
    (budget : charge v off len ≤ pre.gasAvailable.toNat) :
    ∃ post, X (fuel+2) vj pre = .ok (.revert post.gasAvailable (ReferenceReturnView.output v off len)) ∧
      ReferenceReturnView.Result parent v off len rest post ∧
      post.gasAvailable.toNat+charge v off len = pre.gasAvailable.toNat := by
  have hs : pre.stack = off::len::rest := related.stack.symm.trans shape
  have mc := memory_cost related shape (Or.inr rfl : Operation.REVERT = .RETURN ∨ Operation.REVERT = .REVERT)
  have hz := Z_memop (vj := vj) (s := pre) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
    rfl rfl (by simp [hs]) (by simpa [hs] using stack)
    (by rw [C'_REVERT,mc]; omega) (fun h => absurd h (by decide))
  obtain ⟨post,step⟩ : ∃ post, StepOk (fuel+1) (C' (charged pre .REVERT) .REVERT) (.REVERT,none) (charged pre .REVERT) post :=
    ⟨_,stepOk_halt (f := fuel) (by decide) (Eip8282.Audit.SymExec.step_REVERT hs)⟩
  have cap : post.activeWords.toNat = MachineState.M (words v) off.toNat len.toNat := by
    have raw := step
    change EVM.step (fuel+1) _ (some (.REVERT,none)) _ = .ok post at raw
    rw [OrdinaryGas.dispatch (by decide)] at raw
    have ex := RuntimeMemoryCharges.raw_expansion (by decide : Operation.REVERT ∈ RuntimeOpcodeScope.allowedOps) raw
    simpa only [stepPre,Eip8282.Audit.SymExec.charged,zMid,RuntimeMemoryMonotone.span,hs,List.getElem!_cons_zero,List.getElem!_cons_succ,←words_related related] using ex
  have host : 32*MachineState.M (words v) off.toNat len.toNat < 2^System.Platform.numBits :=
    ReferenceSourceReplayTrace.host_of_cost (by unfold charge at domain; omega)
  obtain ⟨off',len',rest',pop,shape',result⟩ := ReferenceRevertView.terminal hz step related (by omega : post.activeWords.toNat ≤ MachineState.M (words v) off.toNat len.toNat) host
  have eqs := List.cons.inj (shape.symm.trans shape')
  obtain ⟨rfl,tail⟩ := eqs
  obtain ⟨rfl,rfl⟩ := List.cons.inj tail
  have hout : H post.toMachineState .REVERT = some (ReferenceReturnView.output v off len) := by
    change some post.H_return = _
    rw [result.returned]
  refine ⟨post,?_,result,?_⟩
  · exact X_succ_of_revert decoded hz step hout rfl
  · have debit := OrdinaryGas.accepted_step_debit (by decide : OrdinaryGas.Ordinary .REVERT) hz step
    rw [mc,C'_REVERT] at debit
    simpa using debit

theorem stop (fuel : Nat) {parent : ReferenceStorageView.Parent} {v : View}
    {vj : Array UInt256} {pre : EVM.State} (related : Related parent v pre)
    (decoded : decodeAt pre = (.STOP,none)) (stack : v.stack.length ≤ 1024) :
    ∃ post, X (fuel+2) vj pre = .ok (.success post ByteArray.empty) ∧
      Related parent v post ∧ post.gasAvailable.toNat = pre.gasAvailable.toNat := by
  have hc : charged pre .STOP = pre := charged_eq_self (memcost_STOP pre)
  have hz := Z_of_facts vj .STOP pre (d := 0) (a := 0)
    (by rw [memcost_STOP]; omega) (by rw [hc,C'_STOP]; omega)
    rfl rfl (Nat.zero_le _) (by rw [←related.stack]; simpa using stack)
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (by decide)
    (fun _ => by simp +decide [W]) (fun h => absurd h (by decide)) (by decide)
  obtain ⟨post,step⟩ : ∃post, StepOk (fuel+1) (C' (charged pre .STOP) .STOP) (.STOP,none) (charged pre .STOP) post :=
    ⟨_,stepOk_halt (f := fuel) (by decide) (Eip8282.Audit.SymExec.step_STOP pre)⟩
  obtain ⟨result,hout⟩ := ReferenceStopView.terminal hz step related
  refine ⟨post,X_succ_of_halt decoded hz step hout (by decide),result,?_⟩
  have debit := OrdinaryGas.accepted_step_debit (by decide : OrdinaryGas.Ordinary .STOP) hz step
  simpa only [memcost_STOP,C'_STOP,Nat.add_zero] using debit

#print axioms returned
#print axioms reverted
#print axioms stop
end Eip8282.Audit.Integrator.ReferenceTerminalReplay
