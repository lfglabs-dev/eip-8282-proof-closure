import Eip8282.Audit.Integrator.NestedEventArgs

/-! Literal wrapper journal projections for recursive invariant extraction.
Completed results identify either rollback or a real successful child; no
successful-child premise or desired post-world frame is supplied. -/
namespace Eip8282.Audit.Integrator.WrapperJournalEdges
open EvmYul EvmYul.EVM
open NestedEvents
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- The actual Xi success comes from the same actual X success and full tuple. -/
theorem xi_success {fuel : Nat} (a : XiArgs)
    {cr : Created} {w : World} {g : UInt256} {ss : Substate} {out : ByteArray}
    (hr : (Request.xi fuel a).eval = .ok (.success (cr,w,g,ss) out)) :
    ∃ n post, fuel = n+1 ∧ X n a.jumps a.entry = .ok (.success post out) ∧
      post.createdAccounts = cr ∧ post.accountMap = w ∧ post.gasAvailable = g ∧ post.substate = ss := by
  cases fuel with
  | zero => cases hr
  | succ n =>
    change (do
      let result ← X n a.jumps a.entry
      match result with
      | .success post data => Except.ok (ExecutionResult.success (post.createdAccounts,post.accountMap,post.gasAvailable,post.substate) data)
      | .revert gas data => Except.ok (ExecutionResult.revert gas data)) = _ at hr
    cases he : X n a.jumps a.entry with
    | error err => simp only [he,Bind.bind,Except.bind] at hr; cases hr
    | ok result =>
      cases result with
      | revert gas data => simp only [he,Bind.bind,Except.bind] at hr; cases hr
      | success post data =>
        simp only [he,Bind.bind,Except.bind,Except.ok.injEq,ExecutionResult.success.injEq,Prod.mk.injEq] at hr
        obtain ⟨⟨hcr,hw,hg,hss⟩,hout⟩ := hr
        subst data
        exact ⟨n,post,rfl,he,hcr,hw,hg,hss⟩

/-- Empty-world fallback and exception/revert rollback select the checkpoint
world and its destruction set together. Otherwise the actual Xi success is exposed. -/
theorem theta_code_world (c : MessageCall.Context)
    {cr : Created} {w : World} {g : UInt256} {ss : Substate} {z : Bool} {out : ByteArray}
    (hr : c.result = .ok (cr,w,g,ss,z,out)) :
    (w = c.world ∧ ss.selfDestructSet = c.substate.selfDestructSet) ∨
      ∃ ic iw ig iss data,
        c.execution = .ok (.success (ic,iw,ig,iss) data) ∧
        w = iw ∧ ss.selfDestructSet = iss.selfDestructSet := by
  rw [MessageCall.result_eq_settle] at hr
  cases he : c.execution with
  | error err =>
    simp only [MessageCall.Context.settle,he] at hr
    split at hr
    · cases hr
    · cases hr; exact Or.inl ⟨rfl,rfl⟩
  | ok result =>
    cases result with
    | revert gas data =>
      simp only [MessageCall.Context.settle,he] at hr
      cases hr
      exact Or.inl ⟨rfl,rfl⟩
    | success state data =>
      obtain ⟨ic,iw,ig,iss⟩ := state
      simp only [MessageCall.Context.settle,he] at hr
      by_cases hh : (iw == ∅) = true
      · simp only [hh] at hr
        cases hr
        exact Or.inl ⟨rfl,rfl⟩
      · simp only [hh] at hr
        cases hr
        exact Or.inr ⟨_,_,_,_,_,rfl,rfl,rfl⟩

/-- Actual completed Lambda gives its computed address and either rollback or
installation on a real successful initializer world. Structural preimage
success is explicit here and can be supplied by CreationPreimageTotal. -/
theorem lambda_context_world (c : CreationSettlement.Context) {bytes : ByteArray}
    (hp : c.preimage = some bytes)
    {addr : AccountAddress} {cr : Created} {w : World} {g : UInt256}
    {ss : Substate} {z : Bool} {out : ByteArray}
    (hr : c.result = .ok (addr,cr,w,g,ss,z,out)) :
    addr = CreationSettlement.address bytes ∧
      ((w = c.world ∧ ss.selfDestructSet = c.substate.selfDestructSet) ∨
        ∃ ic iw ig iss data,
          c.execution (CreationSettlement.address bytes) = .ok (.success (ic,iw,ig,iss) data) ∧
          w = CreationSettlement.install iw (CreationSettlement.address bytes) data ∧
          ss.selfDestructSet = iss.selfDestructSet) := by
  rw [CreationSettlement.result_eq_settle c hp] at hr
  cases he : c.execution (CreationSettlement.address bytes) with
  | error err =>
    simp only [CreationSettlement.Context.settle,he] at hr
    split at hr
    · cases hr
    · cases hr; exact ⟨rfl,Or.inl ⟨rfl,rfl⟩⟩
  | ok result =>
    cases result with
    | revert gas data =>
      simp only [CreationSettlement.Context.settle,he] at hr
      cases hr
      exact ⟨rfl,Or.inl ⟨rfl,rfl⟩⟩
    | success state data =>
      obtain ⟨ic,iw,ig,iss⟩ := state
      simp only [CreationSettlement.Context.settle,he] at hr
      by_cases hh : c.depositFailure (CreationSettlement.address bytes) ig data = true
      · simp only [hh] at hr
        cases hr
        exact ⟨rfl,Or.inl ⟨rfl,rfl⟩⟩
      · simp only [hh] at hr
        cases hr
        exact ⟨rfl,Or.inr ⟨_,_,_,_,_,rfl,rfl,rfl⟩⟩

#print axioms xi_success
#print axioms theta_code_world
#print axioms lambda_context_world
end Eip8282.Audit.Integrator.WrapperJournalEdges
