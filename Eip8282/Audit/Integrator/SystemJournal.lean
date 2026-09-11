import Eip8282.Audit.Integrator.JournalInvariant
import Eip8282.Audit.Integrator.SystemProgress

/-! Actual SYSTEM receipts preserve each protected journal at the same budget.
The other runtime is framed by its actual accepted instructions and settlement;
no arbitrary SYSTEM code is assigned zero work. Progress remains separate. -/
namespace Eip8282.Audit.Integrator.SystemJournal
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open RuntimeExecutionScope RuntimeOpcodeScope NestedEvents
open Eip8282.Audit.Correspondence (runtimeCode)
open ReachableCalls (Contract Transition address runtime)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem x_frame {image : Image} {fuel : Nat} {pre post : EVM.State} {out : ByteArray}
    (hat : At image pre)
    (hx : X fuel (D_J image.code ⟨0⟩) pre = .ok (.success post out)) (a : AccountAddress) (hne : pre.executionEnv.codeOwner ≠ a) :
    CodeStorageFrame.Frame pre.accountMap post.accountMap a := by
  induction fuel generalizing pre with
  | zero => cases hx
  | succ fuel ih =>
    obtain ⟨n,cost,op,arg,mid,next,hf,hd,hz,hs,ht⟩ := SuccessInversion.success_step hx
    have hn : n = fuel := by omega
    subst n
    have hz' : Z (D_J image.code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,cost) := by simpa only [hd] using hz
    have hs' : EVM.step fuel cost (some (decodeAt pre)) mid = .ok next := by simpa only [hd, StepOk, Step] using hs
    have hop := allowed_excludes _ (opcode_allowed hat)
    have hp := CodeStorageFrame.ordinary ⟨hop.2.1,hop.2.2.1⟩ hne hz' hs'
    have henv := accepted_environment hat hz' hs' 
    rcases ht with ⟨hh,tail⟩ | ⟨_,_,rfl⟩
    · have hh' : H next.toMachineState (decodeAt pre).1 = none := by simpa only [hd] using hh
      exact CodeStorageFrame.trans hp (ih (accepted_next hat hz' hs' hh') tail (by rw [henv]; exact hne))
    · exact hp

private theorem execution_frame (c : MessageCall.Context) {kind : Eip8282.Audit.Model.Kind}
    (hcode : c.code = runtimeCode kind) (a : AccountAddress) (hne : c.target ≠ a)
    {created : Created} {world : World} {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hx : c.execution = .ok (.success (created,world,gas,substate) out)) :
    CodeStorageFrame.Frame c.entryWorld world a := by
  let image : Image := match kind with | .deposit => deposit | .exit => exit
  have hi : c.code = image.code := by cases kind <;> exact hcode
  obtain ⟨fuel,hfuel⟩ : ∃ f, c.fuel = f+1 := by
    cases hf : c.fuel with
    | zero => simp only [MessageCall.Context.execution, hf, Ξ] at hx; cases hx
    | succ f => exact ⟨f,rfl⟩
  unfold MessageCall.Context.execution at hx
  rw [hfuel] at hx
  unfold Ξ at hx
  change (do
    let r ← X fuel (D_J c.environment.code ⟨0⟩)
      (Eip8282.Audit.XiTransport.entryState c.created c.genesis c.blocks c.entryWorld c.originalWorld c.gas c.substate c.environment)
    match r with
    | .success st o => Except.ok (ExecutionResult.success (st.createdAccounts,st.accountMap,st.gasAvailable,st.substate) o)
    | .revert g o => Except.ok (ExecutionResult.revert g o)) = _ at hx
  let entry := Eip8282.Audit.XiTransport.entryState c.created c.genesis c.blocks c.entryWorld c.originalWorld c.gas c.substate c.environment
  have hat : At image entry := ⟨hi, Or.inl image.entry⟩
  change c.code = image.code at hi
  change (do
    let r ← X fuel (D_J c.code ⟨0⟩) entry
    match r with
    | .success st o => Except.ok (ExecutionResult.success (st.createdAccounts,st.accountMap,st.gasAvailable,st.substate) o)
    | .revert g o => Except.ok (ExecutionResult.revert g o)) = _ at hx
  rw [hi] at hx
  cases he : X fuel (D_J image.code ⟨0⟩) entry with
  | error err => simp only [he, Bind.bind, Except.bind] at hx; cases hx
  | ok result =>
    cases result with
    | revert g o => simp only [he, Bind.bind, Except.bind] at hx; cases hx
    | success post o =>
      simp only [he, Bind.bind, Except.bind, Except.ok.injEq, ExecutionResult.success.injEq] at hx
      obtain ⟨hw,ho⟩ := hx
      have hp := x_frame hat he a hne
      have hm := congrArg (fun t : Created × World × UInt256 × Substate => t.2.1) hw
      dsimp only at hm
      rw [hm] at hp
      exact hp

theorem other_runtime_frame (c : MessageCall.Context) {selector : Contract}
    {protectedAddr : AccountAddress} {created : Created} {world : World} {gas : UInt256}
    {substate : Substate} {success : Bool} {out : ByteArray}
    (hcode : c.code = runtime selector) (hne : c.target ≠ protectedAddr)
    (hr : c.result = .ok (created,world,gas,substate,success,out)) :
    CodeStorageFrame.Frame c.world world protectedAddr := by
  have hc : c.code = runtimeCode (JournalInvariant.modelKind selector) := by
    cases selector <;> exact hcode
  rw [MessageCall.result_eq_settle] at hr
  cases he : c.execution with
  | error err =>
    simp only [MessageCall.Context.settle, he] at hr
    split at hr
    · cases hr
    · cases hr; exact CodeStorageFrame.refl _ _
  | ok result =>
    cases result with
    | revert remaining data =>
      simp only [MessageCall.Context.settle, he] at hr
      cases hr; exact CodeStorageFrame.refl _ _
    | success state data =>
      obtain ⟨cr,w,g,ss⟩ := state
      have hp := execution_frame c hc protectedAddr hne he
      have hf := CodeStorageFrame.trans (CodeStorageFrame.entry c protectedAddr) hp
      simp only [MessageCall.Context.settle, he] at hr
      have hw : world = if w == ∅ then c.world else w :=
        (congrArg (fun t => t.2.1) (Except.ok.inj hr)).symm
      rw [hw]
      split
      · exact CodeStorageFrame.refl _ _
      · exact hf

theorem preserves {selector protectedKind : Contract} {before after : World}
    (t : Transition selector before after)
    (hsys : t.call.caller = Eip8282.Audit.EvmRunner.sysAddr)
    (_hvalue : t.call.value = ⟨0⟩)
    (hfit : t.call.calldata.size < UInt256.size)
    {budget : Nat} (hb : budget < 2^128)
    (hi : JournalInvariant.Invariant protectedKind budget before) :
    JournalInvariant.Invariant protectedKind budget after := by
  by_cases hk : selector = protectedKind
  · subst selector
    have ha : ConcreteHistory.Allowed t.call := ⟨hfit,fun hn => False.elim (hn hsys)⟩
    have hp := JournalInvariant.protected_call t ha hb hi
    simpa only [ConcreteHistory.weight,hsys,↓reduceIte,Nat.add_zero] using hp
  · have hne : t.call.target ≠ address protectedKind := by
      rw [t.pinned.target]
      cases selector <;> cases protectedKind <;> first | exact False.elim (hk rfl) | decide +kernel
    have hf := other_runtime_frame t.call t.pinned.code hne t.executed
    rw [t.pre] at hf
    exact JournalInvariant.frame hi hf

#print axioms other_runtime_frame
#print axioms preserves
end Eip8282.Audit.Integrator.SystemJournal
