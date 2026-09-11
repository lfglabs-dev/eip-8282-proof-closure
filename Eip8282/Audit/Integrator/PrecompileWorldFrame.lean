import Eip8282.Audit.Integrator.CodeStorageFrame
import Eip8282.Audit.Integrator.NestedEventArgs

/-!
Actual precompile outputs preserve the input world or return its empty failure
sentinel. Theta's literal fallback restores the checkpoint for that sentinel.
No FFI success, gas adequacy or created-account preservation is assumed.
-/
namespace Eip8282.Audit.Integrator.PrecompileWorldFrame
open EvmYul EvmYul.EVM
open NestedEvents
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private def Choice (world : World) (substate : Substate)
    (result : Bool × World × UInt256 × Substate × ByteArray) : Prop :=
  (result.2.1 = world ∨ result.2.1 = ∅) ∧
    (result.2.2.2.1.selfDestructSet = substate.selfDestructSet ∨
      result.2.2.2.1.selfDestructSet = ∅)

private theorem ecrec (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_ECREC world gas substate env) := by
  dsimp only [Choice, Ξ_ECREC]
  repeat' first
    | exact ⟨Or.inl rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inr rfl⟩
    | split

private theorem sha256 (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_SHA256 world gas substate env) := by
  dsimp only [Choice, Ξ_SHA256]
  repeat' first
    | exact ⟨Or.inl rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inr rfl⟩
    | split

private theorem rip160 (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_RIP160 world gas substate env) := by
  dsimp only [Choice, Ξ_RIP160]
  repeat' first
    | exact ⟨Or.inl rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inr rfl⟩
    | split

private theorem id (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_ID world gas substate env) := by
  dsimp only [Choice, Ξ_ID]
  repeat' first
    | exact ⟨Or.inl rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inr rfl⟩
    | split

private theorem expmod (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_EXPMOD world gas substate env) := by
  dsimp only [Choice, Ξ_EXPMOD]
  repeat' first
    | exact ⟨Or.inl rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inr rfl⟩
    | split

private theorem bn_add (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_BN_ADD world gas substate env) := by
  dsimp only [Choice, Ξ_BN_ADD]
  repeat' first
    | exact ⟨Or.inl rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inr rfl⟩
    | split

private theorem bn_mul (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_BN_MUL world gas substate env) := by
  dsimp only [Choice, Ξ_BN_MUL]
  repeat' first
    | exact ⟨Or.inl rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inr rfl⟩
    | split

private theorem snarkv (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_SNARKV world gas substate env) := by
  dsimp only [Choice, Ξ_SNARKV]
  repeat' first
    | exact ⟨Or.inl rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inr rfl⟩
    | split

private theorem blake2_f (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_BLAKE2_F world gas substate env) := by
  dsimp only [Choice, Ξ_BLAKE2_F]
  repeat' first
    | exact ⟨Or.inl rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inr rfl⟩
    | split

private theorem pointeval (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Choice world substate (Ξ_PointEval world gas substate env) := by
  dsimp only [Choice, Ξ_PointEval]
  repeat' first
    | exact ⟨Or.inl rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inl rfl⟩
    | exact ⟨Or.inr rfl, Or.inr rfl⟩
    | split

/-- Includes unsupported targets' actual default result, not only targets 1–10. -/
theorem precompile_choice (target : AccountAddress) (world : World) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM)
    {created' : Created} {world' : World} {gas' : UInt256}
    {substate' : Substate} {success : Bool} {out : ByteArray}
    (h : ReturnedGas.precompileResult target world gas substate env =
      .ok (created',success,world',gas',substate',out)) :
    (world' = world ∨ world' = ∅) ∧
      (substate'.selfDestructSet = substate.selfDestructSet ∨ substate'.selfDestructSet = ∅) := by
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
    exact ⟨Or.inr rfl, Or.inr rfl⟩

/-- All returned statuses of the actual precompiled Theta request preserve
protected code/storage and cannot add a self-destruct address. -/
theorem theta_preserved {fuel : Nat} {a : ThetaArgs} {target : AccountAddress}
    (hc : a.code = .Precompiled target)
    {created : Created} {world : World} {gas : UInt256} {substate : Substate}
    {success : Bool} {out : ByteArray}
    (h : (Request.theta fuel a).eval = .ok (created,world,gas,substate,success,out))
    (address : AccountAddress) :
    CodeStorageFrame.Frame a.world world address ∧
      (substate.selfDestructSet = a.substate.selfDestructSet ∨ substate.selfDestructSet = ∅) := by
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
      have hw : world = if w == ∅ then c.world else w :=
        (congrArg (fun t => t.2.1) (Except.ok.inj hh)).symm
      have hs : substate = if w == ∅ then c.substate else ss :=
        (congrArg (fun t => t.2.2.2.1) (Except.ok.inj hh)).symm
      constructor
      · rw [hw]
        rcases choice.1 with hew | hew
        · rw [hew]
          split
          · exact CodeStorageFrame.refl _ _
          · exact CodeStorageFrame.entry c address
        · rw [hew]
          exact CodeStorageFrame.refl _ _
      · rw [hs]
        split
        · exact Or.inl rfl
        · exact choice.2

theorem theta_frame {fuel : Nat} {a : ThetaArgs} {target : AccountAddress}
    (hc : a.code = .Precompiled target)
    {created : Created} {world : World} {gas : UInt256} {substate : Substate}
    {success : Bool} {out : ByteArray}
    (h : (Request.theta fuel a).eval = .ok (created,world,gas,substate,success,out))
    (address : AccountAddress) : CodeStorageFrame.Frame a.world world address :=
  (theta_preserved hc h address).1

theorem theta_exclusion {fuel : Nat} {a : ThetaArgs} {target : AccountAddress}
    (hc : a.code = .Precompiled target)
    {created : Created} {world : World} {gas : UInt256} {substate : Substate}
    {success : Bool} {out : ByteArray}
    (h : (Request.theta fuel a).eval = .ok (created,world,gas,substate,success,out))
    {address : AccountAddress} (hn : address ∉ a.substate.selfDestructSet) :
    address ∉ substate.selfDestructSet := by
  rcases (theta_preserved hc h address).2 with hs | hs
  · rw [hs]; exact hn
  · rw [hs]; simp

#print axioms precompile_choice
#print axioms theta_preserved
#print axioms theta_frame
#print axioms theta_exclusion
end Eip8282.Audit.Integrator.PrecompileWorldFrame
