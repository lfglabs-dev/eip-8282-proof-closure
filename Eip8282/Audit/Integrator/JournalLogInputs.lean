import Eip8282.Audit.Integrator.PrecompileWorldFrame

/-! Actual selected-child input logs and all-status precompiled Theta logs.
No funding, owner, child-success or supplied log equality premise. -/
namespace Eip8282.Audit.Integrator.JournalLogInputs
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open NestedEvents
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem selected_theta_input {n f : Nat} {a : StepArgs} {b : ThetaArgs}
    (hc : StepChild n a (some (.theta f b))) :
    b.substate.logSeries = a.pre.substate.logSeries := by
  have hs : a.mid.substate.logSeries = a.pre.substate.logSeries := by
    rw [Z_ok_state a.guard]; rfl
  unfold StepChild selectedChild at hc
  split at hc
  · cases hc
  · split at hc
    all_goals repeat first | split at hc | contradiction
    all_goals simp only [Option.some.injEq,Request.theta.injEq,reduceCtorEq] at hc
    all_goals obtain ⟨_,rfl⟩ := hc
    all_goals exact hs

theorem selected_lambda_input {n f : Nat} {a : StepArgs} {b : LambdaArgs}
    (hc : StepChild n a (some (.lambda f b))) :
    b.substate.logSeries = a.pre.substate.logSeries := by
  have hs : a.mid.substate.logSeries = a.pre.substate.logSeries := by
    rw [Z_ok_state a.guard]; rfl
  unfold StepChild selectedChild at hc
  split at hc
  · cases hc
  · split at hc
    all_goals repeat first | split at hc | contradiction
    all_goals simp only [Option.some.injEq,Request.lambda.injEq,reduceCtorEq] at hc
    all_goals obtain ⟨_,rfl⟩ := hc
    all_goals exact hs

private def Choice (_world : World) (substate : Substate)
    (result : Bool × World × UInt256 × Substate × ByteArray) : Prop :=
  result.2.1 = ∅ ∨ result.2.2.2.1.logSeries = substate.logSeries

private theorem ecrec (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_ECREC world gas substate env) := by
  dsimp only [Choice, Ξ_ECREC]
  repeat' first
    | exact Or.inr rfl
    | exact Or.inl rfl
    | split

private theorem sha256 (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_SHA256 world gas substate env) := by
  dsimp only [Choice, Ξ_SHA256]
  repeat' first
    | exact Or.inr rfl
    | exact Or.inl rfl
    | split

private theorem rip160 (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_RIP160 world gas substate env) := by
  dsimp only [Choice, Ξ_RIP160]
  repeat' first
    | exact Or.inr rfl
    | exact Or.inl rfl
    | split

private theorem id (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_ID world gas substate env) := by
  dsimp only [Choice, Ξ_ID]
  repeat' first
    | exact Or.inr rfl
    | exact Or.inl rfl
    | split

private theorem expmod (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_EXPMOD world gas substate env) := by
  dsimp only [Choice, Ξ_EXPMOD]
  repeat' first
    | exact Or.inr rfl
    | exact Or.inl rfl
    | split

private theorem bn_add (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_BN_ADD world gas substate env) := by
  dsimp only [Choice, Ξ_BN_ADD]
  repeat' first
    | exact Or.inr rfl
    | exact Or.inl rfl
    | split

private theorem bn_mul (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_BN_MUL world gas substate env) := by
  dsimp only [Choice, Ξ_BN_MUL]
  repeat' first
    | exact Or.inr rfl
    | exact Or.inl rfl
    | split

private theorem snarkv (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_SNARKV world gas substate env) := by
  dsimp only [Choice, Ξ_SNARKV]
  repeat' first
    | exact Or.inr rfl
    | exact Or.inl rfl
    | split

private theorem blake2_f (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_BLAKE2_F world gas substate env) := by
  dsimp only [Choice, Ξ_BLAKE2_F]
  repeat' first
    | exact Or.inr rfl
    | exact Or.inl rfl
    | split

private theorem pointeval (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_PointEval world gas substate env) := by
  dsimp only [Choice, Ξ_PointEval]
  repeat' first
    | exact Or.inr rfl
    | exact Or.inl rfl
    | split

/-- Includes unsupported targets' actual default result, not only targets 1–10. -/
theorem precompile_choice (target : AccountAddress) (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM)
    {created' : Created} {world' : World} {gas' : UInt256}
    {substate' : Substate} {success : Bool} {out : ByteArray}
    (h : ReturnedGas.precompileResult target world gas substate env =
      .ok (created',success,world',gas',substate',out)) :
    world' = ∅ ∨ substate'.logSeries = substate.logSeries := by
  change Choice world substate (success,world',gas',substate',out)
  unfold ReturnedGas.precompileResult at h
  split at h
  · have hr := congrArg (fun t => t.2) (Except.ok.inj h)
    dsimp only at hr
    rw [← hr]
    exact ecrec world gas substate env
  · have hr := congrArg (fun t => t.2) (Except.ok.inj h)
    dsimp only at hr
    rw [← hr]
    exact sha256 world gas substate env
  · have hr := congrArg (fun t => t.2) (Except.ok.inj h)
    dsimp only at hr
    rw [← hr]
    exact rip160 world gas substate env
  · have hr := congrArg (fun t => t.2) (Except.ok.inj h)
    dsimp only at hr
    rw [← hr]
    exact id world gas substate env
  · have hr := congrArg (fun t => t.2) (Except.ok.inj h)
    dsimp only at hr
    rw [← hr]
    exact expmod world gas substate env
  · have hr := congrArg (fun t => t.2) (Except.ok.inj h)
    dsimp only at hr
    rw [← hr]
    exact bn_add world gas substate env
  · have hr := congrArg (fun t => t.2) (Except.ok.inj h)
    dsimp only at hr
    rw [← hr]
    exact bn_mul world gas substate env
  · have hr := congrArg (fun t => t.2) (Except.ok.inj h)
    dsimp only at hr
    rw [← hr]
    exact snarkv world gas substate env
  · have hr := congrArg (fun t => t.2) (Except.ok.inj h)
    dsimp only at hr
    rw [← hr]
    exact blake2_f world gas substate env
  · have hr := congrArg (fun t => t.2) (Except.ok.inj h)
    dsimp only at hr
    rw [← hr]
    exact pointeval world gas substate env
  · have hr := congrArg (fun t => t.2) (Except.ok.inj h)
    dsimp only at hr
    rw [← hr]
    exact Or.inl rfl

theorem precompile_logs {fuel : Nat} {a : ThetaArgs} {target : AccountAddress}
    (hc : a.code = .Precompiled target)
    {created : Created} {world : World} {gas : UInt256} {substate : Substate}
    {success : Bool} {out : ByteArray}
    (h : (Request.theta fuel a).eval = .ok (created,world,gas,substate,success,out))
    : substate.logSeries = a.substate.logSeries := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
    let c := a.context 0 ByteArray.empty
    let env : ExecutionEnv .EVM := { c.environment with code := ByteArray.empty }
    change Θ (fuel+1) a.hashes a.created a.genesis a.blocks a.world a.original a.substate
      a.source a.origin a.target a.code a.gas a.price a.value a.apparent a.data a.depth a.header
      a.permission = .ok (created,world,gas,substate,success,out) at h
    rw [hc] at h
    have hh : (do
      let (cr,z,w,g,ss,data) ← ReturnedGas.precompileResult target c.entryWorld c.gas c.substate env
      pure (cr,if w == ∅ then c.world else w,g,if w == ∅ then c.substate else ss,z,data)) =
        Except.ok (created,world,gas,substate,success,out) := by
      convert h using 1
      unfold Θ ReturnedGas.precompileResult
      dsimp only
      split
      all_goals first | rfl | (split <;> first | rfl | contradiction)
    cases he : ReturnedGas.precompileResult target c.entryWorld c.gas c.substate env with
    | error err => simp only [he, Bind.bind, Except.bind] at hh; cases hh
    | ok result =>
      obtain ⟨cr,z,w,g,ss,data⟩ := result
      have choice := precompile_choice target c.entryWorld c.gas c.substate env he
      simp only [he, Bind.bind, Except.bind, pure, Except.pure] at hh
      have hs : substate = if w == ∅ then c.substate else ss :=
        (congrArg (fun t => t.2.2.2.1) (Except.ok.inj hh)).symm
      rw [hs]
      split
      · rfl
      · rename_i hn
        rcases choice with hew | hel
        · subst w
          have hempty : ((∅ : World) == ∅) = true := by rfl
          exact False.elim (hn hempty)
        · exact hel

#print axioms selected_theta_input
#print axioms selected_lambda_input
#print axioms precompile_logs
end Eip8282.Audit.Integrator.JournalLogInputs
