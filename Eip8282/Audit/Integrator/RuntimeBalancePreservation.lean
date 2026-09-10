import Eip8282.Audit.Integrator.RuntimeExecutionScope
import Eip8282.Audit.Integrator.TransferFunding
import Eip8282.Audit.Integrator.RuntimeCodePreservation
import Eip8282.Audit.Integrator.WorldNonempty

/-! Every actual pinned-runtime opcode preserves all account balances.
The message-call receipt consequently contains the entry-transfer balances on
success and the original balances on failure. No supply, queue, fee, history,
source balance correspondence or sufficient-gas premise is consumed. -/
namespace Eip8282.Audit.Integrator.RuntimeBalancePreservation
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open RuntimeExecutionScope RuntimeOpcodeScope NestedEvents
open Eip8282.Audit.Correspondence (runtimeCode)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def Preserved (before after : AccountMap .EVM) (a : AccountAddress) : Prop :=
  TransferFunding.worldBalance after a = TransferFunding.worldBalance before a

private theorem refl (w : AccountMap .EVM) (a : AccountAddress) : Preserved w w a := rfl

private theorem trans {u v w : AccountMap .EVM} {a : AccountAddress}
    (h : Preserved u v a) (g : Preserved v w a) : Preserved u w a := g.trans h

private theorem sstore (st : EvmYul.State .EVM) (key value : UInt256) (a : AccountAddress) :
    Preserved st.accountMap (st.sstore key value).accountMap a := by
  cases ha : st.accountMap.get? st.executionEnv.codeOwner with
  | none =>
    have hs : st.sstore key value = st := by
      simp only [EvmYul.State.sstore,EvmYul.State.lookupAccount,ha,Option.option]
    rw [hs]
    exact refl _ _
  | some acc =>
    rw [SystemSpec.accountMap_sstore ha]
    unfold Preserved TransferFunding.worldBalance
    rw [show (st.accountMap.insert st.executionEnv.codeOwner (acc.updateStorage key value)).get? a =
      if st.executionEnv.codeOwner = a then some (acc.updateStorage key value) else st.accountMap.get? a from
      (Std.TreeMap.getElem?_insert (t := st.accountMap) (k := st.executionEnv.codeOwner) (a := a)
        (v := acc.updateStorage key value)).trans (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)]
    by_cases same : st.executionEnv.codeOwner = a
    · rw [if_pos same,← same,ha]
      simp only [Option.map_some,Option.getD_some]
      unfold Account.updateStorage
      split <;> rfl
    · rw [if_neg same]

private theorem raw_sstore {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (a : AccountAddress) (h : EvmYul.step (τ := .EVM) .SSTORE arg pre = .ok post) :
    Preserved pre.accountMap post.accountMap a := by
  obtain ⟨sh,pc,stk,ex⟩ := pre
  rcases stk with _ | ⟨key, _ | ⟨value,tail⟩⟩
  · cases h
  · cases h
  · cases h
    exact sstore _ key value a

private theorem raw_dup (n : Nat) {pre post : EVM.State} (a : AccountAddress)
    (h : EvmYul.dup n pre = .ok post) : Preserved pre.accountMap post.accountMap a := by
  unfold EvmYul.dup at h
  dsimp only at h
  split at h
  · cases h; exact refl _ _
  · cases h

private theorem raw_swap (n : Nat) {pre post : EVM.State} (a : AccountAddress)
    (h : EvmYul.swap n pre = .ok post) : Preserved pre.accountMap post.accountMap a := by
  unfold EvmYul.swap at h
  dsimp only at h
  split at h
  · cases h; exact refl _ _
  · cases h

/-- Every opcode admitted by either pinned runtime preserves every balance. -/
theorem raw_preserved {op : Operation .EVM} (hop : op ∈ allowedOps)
    {arg : Option (UInt256 × Nat)} {pre post : EVM.State} (a : AccountAddress)
    (h : EvmYul.step op arg pre = .ok post) : Preserved pre.accountMap post.accountMap a := by
  simp only [allowedOps, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact raw_sstore a h | exact raw_dup _ a h | exact raw_swap _ a h | skip
  all_goals
    obtain ⟨sh,pc,stk,ex⟩ := pre
    rcases arg with _ | ⟨v,n⟩
    all_goals rcases stk with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨d, _ | ⟨e, _ | ⟨f,tail⟩⟩⟩⟩⟩⟩
    all_goals cases h <;> exact refl _ _

theorem accepted_preserved {image : Image} {pre mid post : EVM.State}
    {fuel cost : Nat} {vj : Array UInt256} (hat : At image pre)
    (hz : Z vj (decodeAt pre).1 pre = .ok (mid,cost))
    (hs : EVM.step fuel cost (some (decodeAt pre)) mid = .ok post) (a : AccountAddress) :
    Preserved pre.accountMap post.accountMap a := by
  have hop := opcode_allowed hat
  have ho := allowed_excludes _ hop
  cases fuel with
  | zero => cases hs
  | succ fuel =>
    rw [OrdinaryGas.dispatch ⟨ho.2.1,ho.2.2.1⟩] at hs
    have hp := raw_preserved hop a hs
    rw [Z_ok_state hz] at hp
    exact hp

theorem x_preserved {image : Image} {fuel : Nat} {pre post : EVM.State} {out : ByteArray}
    (hat : At image pre)
    (hx : X fuel (D_J image.code ⟨0⟩) pre = .ok (.success post out)) (a : AccountAddress) :
    Preserved pre.accountMap post.accountMap a := by
  induction fuel generalizing pre with
  | zero => cases hx
  | succ fuel ih =>
    obtain ⟨n,cost,op,arg,mid,next,hf,hd,hz,hs,ht⟩ := SuccessInversion.success_step hx
    have hn : n = fuel := by omega
    subst n
    have hz' : Z (D_J image.code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,cost) := by simpa only [hd] using hz
    have hs' : EVM.step fuel cost (some (decodeAt pre)) mid = .ok next := by simpa only [hd, StepOk, Step] using hs
    have hp := accepted_preserved hat hz' hs' a
    rcases ht with ⟨hh,tail⟩ | ⟨_,_,rfl⟩
    · have hh' : H next.toMachineState (decodeAt pre).1 = none := by simpa only [hd] using hh
      exact trans hp (ih (accepted_next hat hz' hs' hh') tail)
    · exact hp

theorem execution_preserved (c : MessageCall.Context) (a : AccountAddress) {kind : Eip8282.Audit.Model.Kind}
    (hcode : c.code = runtimeCode kind)
    {created : Created} {world : World} {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hx : c.execution = .ok (.success (created,world,gas,substate) out)) :
    Preserved c.entryWorld world a ∧ RuntimeCodePreservation.Preserved c.entryWorld world c.target := by
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
      have hp := x_preserved hat he a
      have owner := RuntimeCodePreservation.x_preserved hat he c.target
      have hm := congrArg (fun t : Created × World × UInt256 × Substate => t.2.1) hw
      dsimp only at hm
      rw [hm] at hp owner
      exact ⟨hp,owner⟩

/-- Same settled Theta receipt: successful calls retain the entry transfer;
failed calls restore the original world. Entry account presence excludes the
old empty-world sentinel on successful runtime execution. -/
theorem theta_balances (c : MessageCall.Context) {kind : Eip8282.Audit.Model.Kind}
    {created : Created} {world : World} {gas : UInt256}
    {substate : Substate} {success : Bool} {out : ByteArray}
    (hcode : c.code = runtimeCode kind)
    (owner : ∃ account, c.entryWorld.get? c.target = some account)
    (hr : c.result = .ok (created,world,gas,substate,success,out)) (a : AccountAddress) :
    TransferFunding.worldBalance world a =
      TransferFunding.worldBalance (if success then c.entryWorld else c.world) a := by
  rw [MessageCall.result_eq_settle] at hr
  cases he : c.execution with
  | error err =>
    simp only [MessageCall.Context.settle,he] at hr
    split at hr
    · cases hr
    · cases hr; rfl
  | ok result =>
    cases result with
    | revert remaining data =>
      simp only [MessageCall.Context.settle,he] at hr
      cases hr; rfl
    | success state data =>
      obtain ⟨cr,w,g,ss⟩ := state
      have hp := execution_preserved c a hcode he
      simp only [MessageCall.Context.settle,he] at hr
      obtain ⟨account,present⟩ := owner
      obtain ⟨current,postPresent,_⟩ := hp.2 account present
      have nonempty : (w == ∅) = false := WorldNonempty.beq_empty_false_of_get_some postPresent
      rw [nonempty] at hr
      cases hr
      exact hp.1

#print axioms raw_preserved
#print axioms accepted_preserved
#print axioms x_preserved
#print axioms execution_preserved
#print axioms theta_balances
end Eip8282.Audit.Integrator.RuntimeBalancePreservation
