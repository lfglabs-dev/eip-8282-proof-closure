import Eip8282.Audit.Integrator.RuntimeExecutionScope
import Eip8282.Audit.Integrator.MessageCall

/-! Actual SELFDESTRUCT can add only its current owner. Other ordinary
instructions preserve the set exactly. Pinned-runtime site preservation lifts
this fact through complete X/Xi/Theta executions, including wrapper rollback. -/
namespace Eip8282.Audit.Integrator.SubstateSelfdestructFrame
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open RuntimeExecutionScope RuntimeOpcodeScope NestedEvents
open Eip8282.Audit.Correspondence (runtimeCode)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem sstore_set (s : EvmYul.State .EVM) (key value : UInt256) :
    (s.sstore key value).substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EvmYul.State.sstore
  dsimp only
  cases s.lookupAccount s.executionEnv.codeOwner <;> rfl

private theorem tstore_set (s : EvmYul.State .EVM) (key value : UInt256) :
    (s.tstore key value).substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EvmYul.State.tstore
  dsimp only
  cases s.lookupAccount s.executionEnv.codeOwner <;> rfl

private theorem raw_sstore {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (h : EvmYul.step (τ := .EVM) .SSTORE arg pre = .ok post) :
    post.substate.selfDestructSet = pre.substate.selfDestructSet := by
  obtain ⟨sh,pc,stk,ex⟩ := pre
  rcases stk with _ | ⟨key, _ | ⟨value,tail⟩⟩
  · cases h
  · cases h
  · cases h; exact sstore_set _ key value

private theorem raw_tstore {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (h : EvmYul.step (τ := .EVM) .TSTORE arg pre = .ok post) :
    post.substate.selfDestructSet = pre.substate.selfDestructSet := by
  obtain ⟨sh,pc,stk,ex⟩ := pre
  rcases stk with _ | ⟨key, _ | ⟨value,tail⟩⟩
  · cases h
  · cases h
  · cases h; exact tstore_set _ key value

private theorem raw_extcodehash {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (h : EvmYul.step (τ := .EVM) .EXTCODEHASH arg pre = .ok post) :
    post.substate.selfDestructSet = pre.substate.selfDestructSet := by
  obtain ⟨sh,pc,stk,ex⟩ := pre
  cases stk with
  | nil => cases h
  | cons value stk =>
    cases h
    change (sh.toState.extCodeHash value).1.substate.selfDestructSet = sh.substate.selfDestructSet
    unfold EvmYul.State.extCodeHash
    dsimp only
    split <;> rfl

private theorem raw_dup (n : Nat) {pre post : EVM.State}
    (h : EvmYul.dup n pre = .ok post) :
    post.substate.selfDestructSet = pre.substate.selfDestructSet := by
  unfold EvmYul.dup at h
  dsimp only at h
  split at h
  · cases h; rfl
  · cases h

private theorem raw_swap (n : Nat) {pre post : EVM.State}
    (h : EvmYul.swap n pre = .ok post) :
    post.substate.selfDestructSet = pre.substate.selfDestructSet := by
  unfold EvmYul.swap at h
  dsimp only at h
  split at h
  · cases h; rfl
  · cases h

theorem raw_without_selfdestruct {op : Operation .EVM} (hop : OrdinaryGas.Ordinary op)
    (hv : op ≠ .INVALID) (hn : op ≠ .SELFDESTRUCT)
    {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (h : EvmYul.step op arg pre = .ok post) :
    post.substate.selfDestructSet = pre.substate.selfDestructSet := by
  cases op <;> rename_i op <;> cases op
  all_goals first
    | exact False.elim (hv rfl)
    | exact False.elim (hn rfl)
    | (simp only [OrdinaryGas.Ordinary, Operation.isCall, Operation.isCreate,
        Bool.true_eq_false, false_and, and_false] at hop; done)
    | exact raw_sstore h
    | exact raw_tstore h
    | exact raw_extcodehash h
    | exact raw_dup _ h
    | exact raw_swap _ h
    | skip
  all_goals
    obtain ⟨sh,pc,stk,ex⟩ := pre
    rcases arg with _ | ⟨v,n⟩
    all_goals rcases stk with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨d, _ | ⟨e, _ | ⟨f,tail⟩⟩⟩⟩⟩⟩
    all_goals cases h <;> rfl

private theorem raw_selfdestruct {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    {protectedAddr : AccountAddress} (hne : pre.executionEnv.codeOwner ≠ protectedAddr)
    (hn : protectedAddr ∉ pre.substate.selfDestructSet)
    (h : EvmYul.step (τ := .EVM) .SELFDESTRUCT arg pre = .ok post) :
    protectedAddr ∉ post.substate.selfDestructSet := by
  obtain ⟨sh,pc,stk,ex⟩ := pre
  cases stk with
  | nil => cases h
  | cons dest stk =>
    change (if sh.createdAccounts.contains sh.executionEnv.codeOwner then
      Except.ok _ else Except.ok _) = Except.ok post at h
    split at h
    · cases h
      change protectedAddr ∉ sh.substate.selfDestructSet.insert sh.executionEnv.codeOwner
      simp only [Std.TreeSet.mem_insert, Std.LawfulEqOrd.compare_eq_iff_eq]
      exact fun h => h.elim hne hn
    · cases h; exact hn

theorem accepted_other_owner {op : Operation .EVM} (hop : OrdinaryGas.Ordinary op)
    {arg : Option (UInt256 × Nat)} {pre mid post : EVM.State}
    {vj : Array UInt256} {fuel cost : Nat} {protectedAddr : AccountAddress}
    (hne : pre.executionEnv.codeOwner ≠ protectedAddr)
    (hz : Z vj op pre = .ok (mid,cost)) (hs : StepOk fuel cost (op,arg) mid post)
    (hn : protectedAddr ∉ pre.substate.selfDestructSet) :
    protectedAddr ∉ post.substate.selfDestructSet := by
  cases fuel with
  | zero => cases hs
  | succ fuel =>
    change EVM.step (fuel+1) cost (some (op,arg)) mid = .ok post at hs
    rw [OrdinaryGas.dispatch hop] at hs
    rw [Z_ok_state hz] at hs
    by_cases he : op = .SELFDESTRUCT
    · subst op
      exact raw_selfdestruct (pre := stepPre cost (zMid pre .SELFDESTRUCT)) hne hn hs
    · have hset := raw_without_selfdestruct hop (OrdinaryGas.accepted_valid hz) he hs
      change post.substate.selfDestructSet = pre.substate.selfDestructSet at hset
      rw [hset]
      exact hn

theorem accepted_runtime {image : Image} {pre mid post : EVM.State}
    {fuel cost : Nat} {vj : Array UInt256} (hat : At image pre)
    (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
    (hs : EVM.step fuel cost (some (decodeAt pre)) mid = .ok post) :
    post.substate.selfDestructSet = pre.substate.selfDestructSet := by
  have hop := opcode_allowed hat
  have ho := allowed_excludes _ hop
  have hn : (decodeAt pre).1 ≠ .SELFDESTRUCT := by
    intro he
    rw [he] at hop
    exact (by decide +kernel : (.SELFDESTRUCT : Operation .EVM) ∉ allowedOps) hop
  cases fuel with
  | zero => cases hs
  | succ fuel =>
    rw [OrdinaryGas.dispatch ⟨ho.2.1,ho.2.2.1⟩] at hs
    have hp := raw_without_selfdestruct ⟨ho.2.1,ho.2.2.1⟩ (OrdinaryGas.accepted_valid hz) hn hs
    rw [Z_ok_state hz] at hp
    exact hp

theorem x_runtime {image : Image} {fuel : Nat} {pre post : EVM.State} {out : ByteArray}
    (hat : At image pre)
    (hx : X fuel (D_J image.code ⟨0⟩) pre = .ok (.success post out)) :
    post.substate.selfDestructSet = pre.substate.selfDestructSet := by
  induction fuel generalizing pre with
  | zero => cases hx
  | succ fuel ih =>
    obtain ⟨n,cost,op,arg,mid,next,hf,hd,hz,hs,ht⟩ := SuccessInversion.success_step hx
    have hn : n = fuel := by omega
    subst n
    have hz' : Z (D_J image.code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,cost) := by simpa only [hd] using hz
    have hs' : EVM.step fuel cost (some (decodeAt pre)) mid = .ok next := by simpa only [hd, StepOk, Step] using hs
    have hp := accepted_runtime hat hz' hs'
    rcases ht with ⟨hh,tail⟩ | ⟨_,_,rfl⟩
    · have hh' : H next.toMachineState (decodeAt pre).1 = none := by simpa only [hd] using hh
      exact (ih (accepted_next hat hz' hs' hh') tail).trans hp
    · exact hp

theorem xi_runtime (c : MessageCall.Context) {kind : Eip8282.Audit.Model.Kind}
    (hcode : c.code = runtimeCode kind)
    {created : Created} {world : World} {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hx : c.execution = .ok (.success (created,world,gas,substate) out)) :
    substate.selfDestructSet = c.substate.selfDestructSet := by
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
      have hp := x_runtime hat he
      have hm := congrArg (fun t : Created × World × UInt256 × Substate => t.2.2.2.selfDestructSet) hw
      dsimp only at hm
      rw [hm] at hp
      exact hp

/-- Every completed pinned-runtime Theta outcome retains the input deletion
set exactly, whether success commits or failure restores its journal. -/
theorem theta_runtime (c : MessageCall.Context) {kind : Eip8282.Audit.Model.Kind}
    {created : Created} {world : World} {gas : UInt256}
    {substate : Substate} {success : Bool} {out : ByteArray}
    (hcode : c.code = runtimeCode kind)
    (hr : c.result = .ok (created,world,gas,substate,success,out)) :
    substate.selfDestructSet = c.substate.selfDestructSet := by
  rw [MessageCall.result_eq_settle] at hr
  cases he : c.execution with
  | error err =>
    simp only [MessageCall.Context.settle, he] at hr
    split at hr
    · cases hr
    · cases hr; rfl
  | ok result =>
    cases result with
    | revert remaining data =>
      simp only [MessageCall.Context.settle, he] at hr
      cases hr; rfl
    | success state data =>
      obtain ⟨cr,w,g,ss⟩ := state
      have hp := xi_runtime c hcode he
      simp only [MessageCall.Context.settle, he] at hr
      have hsub : substate = if w == ∅ then c.substate else ss :=
        (congrArg (fun t => t.2.2.2.1) (Except.ok.inj hr)).symm
      rw [hsub]
      split
      · rfl
      · exact hp

theorem theta_exclusion (c : MessageCall.Context) {kind : Eip8282.Audit.Model.Kind}
    {created : Created} {world : World} {gas : UInt256}
    {substate : Substate} {success : Bool} {out : ByteArray} {protectedAddr : AccountAddress}
    (hcode : c.code = runtimeCode kind)
    (hr : c.result = .ok (created,world,gas,substate,success,out))
    (hn : protectedAddr ∉ c.substate.selfDestructSet) :
    protectedAddr ∉ substate.selfDestructSet := by
  rw [theta_runtime c hcode hr]
  exact hn

#print axioms raw_without_selfdestruct
#print axioms accepted_other_owner
#print axioms accepted_runtime
#print axioms x_runtime
#print axioms xi_runtime
#print axioms theta_runtime
#print axioms theta_exclusion
end Eip8282.Audit.Integrator.SubstateSelfdestructFrame
