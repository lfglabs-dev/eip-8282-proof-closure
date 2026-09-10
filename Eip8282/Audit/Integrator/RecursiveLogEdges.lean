import Eip8282.Audit.Integrator.NestedEventArgs

/-! Exact world, log-series and environment projections of recursive steps.
CALL propagates child errors. CREATE's completed-child premise is explicit,
because the pinned evaluator catches child errors and can publish an empty world. -/
namespace Eip8282.Audit.Integrator.RecursiveLogEdges
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open NestedEvents
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2400000

def Published (pre post : EVM.State) (world : World) (ss : Substate) : Prop :=
  post.accountMap = world ∧ post.substate.logSeries = ss.logSeries ∧
    post.executionEnv = pre.executionEnv

private theorem call_finish (n cost : Nat) (hashes : List ByteArray)
    (requested source recipient target value apparent off len outOff outLen : UInt256)
    (perm : Bool) (pre post : EVM.State) (rest : Stack UInt256)
    (hg : CallOutcome.Gate pre value)
    (hr : CallOutcome.finish rest (EVM.call (n+1) cost hashes requested source recipient target
      value apparent off len outOff outLen perm pre) = .ok post) :
    ∃ cr w g ss z out,
      CallGasAccounting.child n hashes requested source recipient target value apparent off len perm pre =
        .ok (cr,w,g,ss,z,out) ∧ Published pre post w ss := by
  cases he : CallGasAccounting.child n hashes requested source recipient target value apparent off len perm pre with
  | error err =>
    unfold CallGasAccounting.child at he
    simp only [CallOutcome.finish,EVM.call,CallOutcome.Gate] at hg hr
    simp only [hg,true_and,↓reduceIte,he,Bind.bind,Except.bind] at hr
    cases hr
  | ok result =>
    obtain ⟨cr,w,g,ss,z,out⟩ := result
    refine ⟨cr,w,g,ss,z,out,rfl,?_⟩
    unfold CallGasAccounting.child at he
    unfold CallOutcome.Gate at hg
    simp only [CallOutcome.finish,EVM.call,hg,true_and,↓reduceIte,he,Bind.bind,Except.bind,
      pure,Except.pure,Except.ok.injEq] at hr
    cases hr
    exact ⟨rfl,rfl,rfl⟩

private theorem call_edge (n : Nat) (a : StepArgs) (hop : a.op = .CALL)
    (hg : CallOutcome.Gate a.mid (operand a 2)) {post : EVM.State}
    (hr : (Request.step (n+2) a).eval = .ok post) :
    ∃ cr w g ss z out,
      (Request.theta n (dispatchCallArgs a.mid (operand a 0) (operand a 1)
        (operand a 2) (operand a 3) (operand a 4))).eval = .ok (cr,w,g,ss,z,out) ∧
      Published a.pre post w ss := by
  rw [call_step_equation n a hop] at hr
  obtain ⟨cr,w,g,ss,z,out,he,hp⟩ := call_finish n a.cost _ _ _ _ _ _ _ _ _ _ _ _
    (CallDispatchGas.entered a.mid) post _ hg hr
  refine ⟨cr,w,g,ss,z,out,he,hp.1,hp.2.1,?_⟩
  exact hp.2.2.trans (by rw [Z_ok_state a.guard]; rfl)

private theorem family_edge (k : CallFamilyGas.Variant) (n : Nat) (a : StepArgs)
    (hop : a.op = CallFamilyGas.opcode k)
    (hg : CallFamilyGas.gate k a.mid (familyValue k a)) {post : EVM.State}
    (hr : (Request.step (n+2) a).eval = .ok post) :
    ∃ cr w g ss z out,
      (Request.theta n (familyArgs k a.mid (operand a 0) (operand a 1)
        (familyValue k a) (familyInOff k a) (familyInLen k a))).eval = .ok (cr,w,g,ss,z,out) ∧
      Published a.pre post w ss := by
  rw [family_step_equation k n a hop] at hr
  obtain ⟨cr,w,g,ss,z,out,he,hp⟩ := call_finish n a.cost _ _ _ _ _ _ _ _ _ _ _ _
    (CallDispatchGas.entered a.mid) post _ hg hr
  refine ⟨cr,w,g,ss,z,out,he,hp.1,hp.2.1,?_⟩
  exact hp.2.2.trans (by rw [Z_ok_state a.guard]; rfl)

/-- Actual completed CALL-family steps have an actual completed child. -/
theorem theta_returned {n f : Nat} {a : StepArgs} {b : ThetaArgs} {post : EVM.State}
    (hc : StepChild n a (some (.theta f b)))
    (hr : (Request.step n a).eval = .ok post) :
    ∃ cr w g ss z out, (Request.theta f b).eval = .ok (cr,w,g,ss,z,out) ∧
      Published a.pre post w ss := by
  unfold StepChild selectedChild at hc
  split at hc
  · cases hc
  · split at hc
    all_goals repeat first | split at hc | contradiction
    all_goals simp only [Option.some.injEq,Request.theta.injEq,reduceCtorEq] at hc
    all_goals rcases hc with ⟨rfl,rfl⟩
    all_goals first
      | exact call_edge _ a (by assumption) (by assumption) hr
      | exact family_edge .callcode _ a (by assumption) (by assumption) hr
      | exact family_edge .delegatecall _ a (by assumption) (by assumption) hr
      | exact family_edge .staticcall _ a (by assumption) (by assumption) hr

private theorem creation_edge (k : CreationGas.Variant) (n : Nat) (a : StepArgs)
    (hop : a.op = CreationGas.opcode k) (hn : CreationGas.nonceAllowed a.mid)
    (hg : CreationGas.gate a.mid (operand a 0) (operand a 1) (operand a 2))
    {addr : AccountAddress} {cr : Created} {w : World} {g : UInt256}
    {ss : Substate} {z : Bool} {out : ByteArray} {post : EVM.State}
    (he : (Request.lambda n (creationArgs k a.cost a.mid (operand a 0) (operand a 1)
      (operand a 2) (creationSalt k a))).eval = .ok (addr,cr,w,g,ss,z,out))
    (hr : (Request.step (n+1) a).eval = .ok post) : Published a.pre post w ss := by
  rw [creation_step_admitted k n a hop hn hg,he] at hr
  unfold CreationOutcome.settle CreationOutcome.select CreationOutcome.finish at hr
  dsimp only at hr
  split at hr
  · cases hr
  · simp only [Bind.bind,Except.bind,pure,Except.pure] at hr
    cases hr
    refine ⟨rfl,rfl,?_⟩
    change a.mid.executionEnv = a.pre.executionEnv
    rw [Z_ok_state a.guard]
    rfl

/-- Child completion is explicit: CREATE does not propagate every child error. -/
theorem lambda_returned {n f : Nat} {a : StepArgs} {b : LambdaArgs}
    {addr : AccountAddress} {cr : Created} {w : World} {g : UInt256}
    {ss : Substate} {z : Bool} {out : ByteArray} {post : EVM.State}
    (hc : StepChild n a (some (.lambda f b)))
    (he : (Request.lambda f b).eval = .ok (addr,cr,w,g,ss,z,out))
    (hr : (Request.step n a).eval = .ok post) : Published a.pre post w ss := by
  unfold StepChild selectedChild at hc
  split at hc
  · cases hc
  · split at hc
    all_goals repeat first | split at hc | contradiction
    all_goals simp only [Option.some.injEq,Request.lambda.injEq,reduceCtorEq] at hc
    all_goals rcases hc with ⟨rfl,rfl⟩
    all_goals first
      | exact creation_edge .create _ a (by assumption) (by tauto) (by tauto) he hr
      | exact creation_edge .create2 _ a (by assumption) (by tauto) (by tauto) he hr

private theorem mid_published (a : StepArgs) :
    Published a.pre a.mid a.pre.accountMap a.pre.substate := by
  rw [Z_ok_state a.guard]
  exact ⟨rfl,rfl,rfl⟩

private theorem denied_finish (n cost : Nat) (hashes : List ByteArray)
    (requested source recipient target value apparent off len outOff outLen : UInt256)
    (perm : Bool) (pre post : EVM.State) (rest : Stack UInt256)
    (hg : ¬ CallOutcome.Gate pre value)
    (hr : CallOutcome.finish rest (EVM.call (n+1) cost hashes requested source recipient target
      value apparent off len outOff outLen perm pre) = .ok post) :
    Published pre post pre.accountMap pre.substate := by
  unfold CallOutcome.Gate at hg
  simp only [CallOutcome.finish,EVM.call,hg,↓reduceIte,Bind.bind,Except.bind,
    pure,Except.pure,Except.ok.injEq] at hr
  cases hr
  exact ⟨rfl,rfl,rfl⟩

private theorem call_denied (n : Nat) (a : StepArgs) (hop : a.op = .CALL)
    (hc : StepChild n a none) {post : EVM.State}
    (hr : (Request.step n a).eval = .ok post) :
    Published a.pre post a.pre.accountMap a.pre.substate := by
  cases n with
  | zero => cases hr
  | succ n =>
    cases n with
    | zero =>
      have he := CallOutcome.step_call_one a.cost a.mid a.arg _ _ _ _ _ _ _ _ (call_stack a hop)
      change EVM.step 1 a.cost (some (a.op,a.arg)) a.mid = _ at hr
      rw [hop,he] at hr
      cases hr
    | succ n =>
      have hg : ¬ CallOutcome.Gate a.mid (operand a 2) := by
        simpa only [StepChild,selectedChild_call n a hop,ite_eq_right_iff,reduceCtorEq,imp_false] using hc
      rw [call_step_equation n a hop] at hr
      have hp := denied_finish n a.cost _ _ _ _ _ _ _ _ _ _ _ _
        (CallDispatchGas.entered a.mid) post _ hg hr
      exact ⟨hp.1.trans (mid_published a).1,hp.2.1.trans (mid_published a).2.1,
        hp.2.2.trans (mid_published a).2.2⟩

private theorem family_denied (k : CallFamilyGas.Variant) (n : Nat) (a : StepArgs)
    (hop : a.op = CallFamilyGas.opcode k) (hc : StepChild n a none) {post : EVM.State}
    (hr : (Request.step n a).eval = .ok post) :
    Published a.pre post a.pre.accountMap a.pre.substate := by
  cases n with
  | zero => cases hr
  | succ n =>
    cases n with
    | zero =>
      have he := CallOutcome.step_family_one k a.cost a.mid a.arg _ _ _ _ _ _ _ _ (family_stack k a hop)
      change EVM.step 1 a.cost (some (a.op,a.arg)) a.mid = _ at hr
      rw [hop,he] at hr
      cases hr
    | succ n =>
      have hg : ¬ CallFamilyGas.gate k a.mid (familyValue k a) := by
        simpa only [StepChild,selectedChild_family k n a hop,ite_eq_right_iff,reduceCtorEq,imp_false] using hc
      rw [family_step_equation k n a hop] at hr
      have hp := denied_finish n a.cost _ _ _ _ _ _ _ _ _ _ _ _
        (CallDispatchGas.entered a.mid) post _ hg hr
      exact ⟨hp.1.trans (mid_published a).1,hp.2.1.trans (mid_published a).2.1,
        hp.2.2.trans (mid_published a).2.2⟩

private theorem creation_denied (k : CreationGas.Variant) (n : Nat) (a : StepArgs)
    (hop : a.op = CreationGas.opcode k) (hc : StepChild n a none) {post : EVM.State}
    (hr : (Request.step n a).eval = .ok post) :
    Published a.pre post a.pre.accountMap a.pre.substate := by
  cases n with
  | zero => cases hr
  | succ n =>
    have hg : ¬ CreationGas.nonceAllowed a.mid ∨
        ¬ CreationGas.gate a.mid (operand a 0) (operand a 1) (operand a 2) := by
      have hh : ¬ (CreationGas.nonceAllowed a.mid ∧
          CreationGas.gate a.mid (operand a 0) (operand a 1) (operand a 2)) := by
        simpa only [StepChild,selectedChild_creation k n a hop,ite_eq_right_iff,reduceCtorEq,imp_false] using hc
      tauto
    rw [creation_step_denied k n a hop hg] at hr
    unfold CreationOutcome.finish at hr
    dsimp only at hr
    split at hr
    · cases hr
    · simp only [Bind.bind,Except.bind,pure,Except.pure] at hr
      cases hr
      exact mid_published a

/-- No selected child on a recursive opcode preserves the literal pre-Z
journal projections when the step actually completes. Ordinary SSTORE is
explicitly outside this no-child statement. -/
theorem denied_recursive {n : Nat} {a : StepArgs} {post : EVM.State}
    (hc : StepChild n a none) (hop : ¬ OrdinaryGas.Ordinary a.op)
    (hr : (Request.step n a).eval = .ok post) :
    Published a.pre post a.pre.accountMap a.pre.substate := by
  rw [OrdinaryGas.ordinary_iff] at hop
  have hh : a.op = .CALL ∨ a.op = .CALLCODE ∨ a.op = .DELEGATECALL ∨
      a.op = .STATICCALL ∨ a.op = .CREATE ∨ a.op = .CREATE2 := by tauto
  rcases hh with he | he | he | he | he | he
  all_goals first
    | exact call_denied n a he hc hr
    | exact family_denied .callcode n a he hc hr
    | exact family_denied .delegatecall n a he hc hr
    | exact family_denied .staticcall n a he hc hr
    | exact creation_denied .create n a he hc hr
    | exact creation_denied .create2 n a he hc hr

/-- The actual Xi success comes from the same actual X success and full tuple. -/
theorem xi_success_logs {fuel : Nat} (a : XiArgs)
    {cr : Created} {w : World} {g : UInt256} {ss : Substate} {out : ByteArray}
    (hr : (Request.xi fuel a).eval = .ok (.success (cr,w,g,ss) out)) :
    ∃ n post, fuel = n+1 ∧ X n a.jumps a.entry = .ok (.success post out) ∧
      post.createdAccounts = cr ∧ post.accountMap = w ∧ post.gasAvailable = g ∧ post.substate.logSeries = ss.logSeries := by
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
        exact ⟨n,post,rfl,he,hcr,hw,hg,congrArg Substate.logSeries hss⟩

/-- Empty-world fallback and exception/revert rollback select the checkpoint
world and its log series together. Otherwise the actual Xi success is exposed. -/
theorem theta_code_logs (c : MessageCall.Context)
    {cr : Created} {w : World} {g : UInt256} {ss : Substate} {z : Bool} {out : ByteArray}
    (hr : c.result = .ok (cr,w,g,ss,z,out)) :
    (w = c.world ∧ ss.logSeries = c.substate.logSeries) ∨
      ∃ ic iw ig iss data,
        c.execution = .ok (.success (ic,iw,ig,iss) data) ∧
        (iw == ∅) = false ∧ w = iw ∧ ss.logSeries = iss.logSeries := by
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
        exact Or.inr ⟨_,_,_,_,_,rfl,by simpa using hh,rfl,rfl⟩

/-- Actual completed Lambda gives its computed address and either rollback or
installation on a real successful initializer world. Structural preimage
success is explicit here and can be supplied by CreationPreimageTotal. -/
theorem lambda_context_logs (c : CreationSettlement.Context) {bytes : ByteArray}
    (hp : c.preimage = some bytes)
    {addr : AccountAddress} {cr : Created} {w : World} {g : UInt256}
    {ss : Substate} {z : Bool} {out : ByteArray}
    (hr : c.result = .ok (addr,cr,w,g,ss,z,out)) :
    addr = CreationSettlement.address bytes ∧
      ((w = c.world ∧ ss.logSeries = c.substate.logSeries) ∨
        ∃ ic iw ig iss data,
          c.execution (CreationSettlement.address bytes) = .ok (.success (ic,iw,ig,iss) data) ∧
          c.depositFailure (CreationSettlement.address bytes) ig data = false ∧
          w = CreationSettlement.install iw (CreationSettlement.address bytes) data ∧
          ss.logSeries = iss.logSeries) := by
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
        exact ⟨rfl,Or.inr ⟨_,_,_,_,_,rfl,by simpa using hh,rfl,rfl⟩⟩


#print axioms theta_returned
#print axioms lambda_returned
#print axioms denied_recursive
#print axioms xi_success_logs
#print axioms theta_code_logs
#print axioms lambda_context_logs
end Eip8282.Audit.Integrator.RecursiveLogEdges
