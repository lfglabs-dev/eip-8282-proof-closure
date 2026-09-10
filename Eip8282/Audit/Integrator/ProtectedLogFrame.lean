import Eip8282.Audit.Integrator.SubstateSelfdestructFrame
import Eip8282.Audit.Integrator.TransactionFunding

/-! Address-only projection of actual accrued logs. Every topic and payload is
retained, in order. Ordinary foreign-owner LOG instructions cannot emit at the
protected address. These are local journal edges, not ancestor-survival claims. -/
namespace Eip8282.Audit.Integrator.ProtectedLogFrame
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def project (address : AccountAddress) (ss : Substate) : List LogEntry :=
  ss.logSeries.toList.filter (fun entry => decide (entry.address = address))

theorem push_away (address : AccountAddress) (ss : Substate) (entry : LogEntry)
    (hne : entry.address ≠ address) :
    project address {ss with logSeries := ss.logSeries.push entry} = project address ss := by
  simp [project,Array.toList_push,hne]

theorem push_self (address : AccountAddress) (ss : Substate) (entry : LogEntry)
    (he : entry.address = address) :
    project address {ss with logSeries := ss.logSeries.push entry} = project address ss ++ [entry] := by
  simp [project,Array.toList_push,he]

private theorem sstore_logs (s : EvmYul.State .EVM) (key value : UInt256) :
    (s.sstore key value).substate.logSeries = s.substate.logSeries := by
  unfold EvmYul.State.sstore
  dsimp only
  cases s.lookupAccount s.executionEnv.codeOwner <;> rfl

private theorem tstore_logs (s : EvmYul.State .EVM) (key value : UInt256) :
    (s.tstore key value).substate.logSeries = s.substate.logSeries := by
  unfold EvmYul.State.tstore
  dsimp only
  cases s.lookupAccount s.executionEnv.codeOwner <;> rfl

private theorem raw_sstore {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (h : EvmYul.step (τ := .EVM) .SSTORE arg pre = .ok post) :
    post.substate.logSeries = pre.substate.logSeries := by
  obtain ⟨sh,pc,stk,ex⟩ := pre
  rcases stk with _ | ⟨key, _ | ⟨value,tail⟩⟩
  · cases h
  · cases h
  · cases h; exact sstore_logs _ key value

private theorem raw_tstore {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (h : EvmYul.step (τ := .EVM) .TSTORE arg pre = .ok post) :
    post.substate.logSeries = pre.substate.logSeries := by
  obtain ⟨sh,pc,stk,ex⟩ := pre
  rcases stk with _ | ⟨key, _ | ⟨value,tail⟩⟩
  · cases h
  · cases h
  · cases h; exact tstore_logs _ key value

private theorem raw_extcodehash {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (h : EvmYul.step (τ := .EVM) .EXTCODEHASH arg pre = .ok post) :
    post.substate.logSeries = pre.substate.logSeries := by
  obtain ⟨sh,pc,stk,ex⟩ := pre
  cases stk with
  | nil => cases h
  | cons value stk =>
    cases h
    change (sh.toState.extCodeHash value).1.substate.logSeries = sh.substate.logSeries
    unfold EvmYul.State.extCodeHash
    dsimp only
    split <;> rfl

private theorem raw_dup (n : Nat) {pre post : EVM.State}
    (h : EvmYul.dup n pre = .ok post) :
    post.substate.logSeries = pre.substate.logSeries := by
  unfold EvmYul.dup at h
  dsimp only at h
  split at h
  · cases h; rfl
  · cases h

private theorem raw_swap (n : Nat) {pre post : EVM.State}
    (h : EvmYul.swap n pre = .ok post) :
    post.substate.logSeries = pre.substate.logSeries := by
  unfold EvmYul.swap at h
  dsimp only at h
  split at h
  · cases h; rfl
  · cases h

private theorem raw_selfdestruct {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (h : EvmYul.step (τ := .EVM) .SELFDESTRUCT arg pre = .ok post) :
    post.substate.logSeries = pre.substate.logSeries := by
  obtain ⟨sh,pc,stk,ex⟩ := pre
  cases stk with
  | nil => cases h
  | cons dest stk =>
    change (if sh.createdAccounts.contains sh.executionEnv.codeOwner then
      Except.ok _ else Except.ok _) = Except.ok post at h
    split at h <;> cases h <;> rfl

theorem raw_without_logs {op : Operation .EVM} (hop : OrdinaryGas.Ordinary op)
    (hv : op ≠ .INVALID) (hn : op ∉ [.LOG0,.LOG1,.LOG2,.LOG3,.LOG4])
    {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (h : EvmYul.step op arg pre = .ok post) :
    post.substate.logSeries = pre.substate.logSeries := by
  cases op <;> rename_i op <;> cases op
  all_goals first
    | exact False.elim (hv rfl)
    | (simp only [List.mem_cons, List.mem_singleton, true_or] at hn; contradiction)
    | (simp only [OrdinaryGas.Ordinary, Operation.isCall, Operation.isCreate,
        Bool.true_eq_false, false_and, and_false] at hop; done)
    | exact raw_selfdestruct h
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

theorem raw_other_owner {op : Operation .EVM} (hop : OrdinaryGas.Ordinary op)
    (hv : op ≠ .INVALID) {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (address : AccountAddress) (hne : pre.executionEnv.codeOwner ≠ address)
    (h : EvmYul.step op arg pre = .ok post) :
    project address post.substate = project address pre.substate := by
  by_cases hn : op ∈ [.LOG0,.LOG1,.LOG2,.LOG3,.LOG4]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl
    all_goals
      obtain ⟨sh,pc,stk,ex⟩ := pre
      rcases stk with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨d, _ | ⟨e, _ | ⟨f,tail⟩⟩⟩⟩⟩⟩
      all_goals first | cases h
      all_goals exact push_away address sh.substate _ hne
  · unfold project
    rw [raw_without_logs hop hv hn h]

theorem accepted_other_owner {op : Operation .EVM} (hop : OrdinaryGas.Ordinary op)
    {arg : Option (UInt256 × Nat)} {pre mid post : EVM.State}
    {vj : Array UInt256} {fuel cost : Nat} {address : AccountAddress}
    (hne : pre.executionEnv.codeOwner ≠ address)
    (hz : Z vj op pre = .ok (mid,cost)) (hs : StepOk fuel cost (op,arg) mid post) :
    project address post.substate = project address pre.substate := by
  cases fuel with
  | zero => cases hs
  | succ fuel =>
    change EVM.step (fuel+1) cost (some (op,arg)) mid = .ok post at hs
    rw [OrdinaryGas.dispatch hop] at hs
    rw [Z_ok_state hz] at hs
    exact raw_other_owner (pre := stepPre cost (zMid pre op)) hop
      (OrdinaryGas.accepted_valid hz) address (by exact hne) hs

theorem theta_failure (c : MessageCall.Context) (address : AccountAddress)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {ss : Substate} {out : ByteArray}
    (hr : c.result = .ok (created,world,gas,ss,false,out)) :
    project address ss = project address c.substate := by
  rw [(MessageCall.failure_restores_journal c created world gas ss out hr).2.1]

theorem transaction_projection (c : RefundAccounting.Context) (address : AccountAddress)
    {provisionalWorld finalWorld : AccountMap .EVM} {remaining used : UInt256}
    {provisionalSs finalSs : Substate} {provisionalStatus finalStatus : Bool}
    (hp : c.provisional = .ok (provisionalWorld,remaining,provisionalSs,provisionalStatus))
    (hr : c.result = .ok (finalWorld,finalSs,finalStatus,used)) :
    project address finalSs = project address provisionalSs := by
  rw [TransactionFunding.result_equation, hp] at hr
  simp only [Bind.bind,Except.bind,pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at hr
  rw [← hr.2.1]

#print axioms push_away
#print axioms push_self
#print axioms raw_without_logs
#print axioms accepted_other_owner
#print axioms theta_failure
#print axioms transaction_projection
end Eip8282.Audit.Integrator.ProtectedLogFrame
