import Eip8282.Audit.Integrator.CallFamilyGas
import Eip8282.Audit.Integrator.CreationGas

/-!
# Remaining gas of the actual mutually recursive evaluator

Only actual completed results carry remaining gas. Interpreter errors do not
receive invented endpoints. Recursive child bounds follow from smaller
actual fuel; precompiles use their real guarded gas subtraction.
-/
namespace Eip8282.Audit.Integrator.ReturnedGas
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open ActualAppendGas
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def xGas : ExecutionResult EVM.State → UInt256
  | .success st _ => st.gasAvailable | .revert gas _ => gas

def xiGas : ExecutionResult (Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate) → UInt256
  | .success (_,_,gas,_) _ => gas | .revert gas _ => gas

def XBound (fuel : Nat) : Prop := ∀ {vj : Array UInt256} {pre : EVM.State} {r : ExecutionResult EVM.State},
  X fuel vj pre = .ok r → (xGas r).toNat ≤ pre.gasAvailable.toNat

def XiBound (fuel : Nat) : Prop :=
  ∀ {created : Std.TreeSet AccountAddress compare} {genesis : BlockHeader} {blocks : ProcessedBlocks}
    {world original : AccountMap .EVM} {gas : UInt256} {substate : Substate} {env : ExecutionEnv .EVM}
    {r : ExecutionResult (Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate)},
    Ξ fuel created genesis blocks world original gas substate env = .ok r →
      (xiGas r).toNat ≤ gas.toNat

def ThetaBound (fuel : Nat) : Prop :=
  ∀ {hashes : List ByteArray} {created : Std.TreeSet AccountAddress compare} {genesis header : BlockHeader}
    {blocks : ProcessedBlocks} {world original : AccountMap .EVM} {substate : Substate}
    {source origin target : AccountAddress} {code : ToExecute .EVM} {gas price value apparent : UInt256}
    {data : ByteArray} {depth : Nat} {permission : Bool}
    {created' : Std.TreeSet AccountAddress compare} {world' : AccountMap .EVM} {gas' : UInt256}
    {substate' : Substate} {success : Bool} {out : ByteArray},
    Θ fuel hashes created genesis blocks world original substate source origin target code gas price value apparent
      data depth header permission = .ok (created',world',gas',substate',success,out) → gas'.toNat ≤ gas.toNat

def LambdaBound (fuel : Nat) : Prop :=
  ∀ {hashes : List ByteArray} {created : Std.TreeSet AccountAddress compare} {genesis header : BlockHeader}
    {blocks : ProcessedBlocks} {world original : AccountMap .EVM} {substate : Substate}
    {source origin : AccountAddress} {gas price value depth : UInt256} {init : ByteArray}
    {salt : Option ByteArray} {permission : Bool} {addr : AccountAddress}
    {created' : Std.TreeSet AccountAddress compare} {world' : AccountMap .EVM} {gas' : UInt256}
    {substate' : Substate} {success : Bool} {out : ByteArray},
    Lambda fuel hashes created genesis blocks world original substate source origin gas price value init depth salt
      header permission = .ok (addr,created',world',gas',substate',success,out) → gas'.toNat ≤ gas.toNat

def StepBound (fuel : Nat) : Prop :=
  ∀ {vj : Array UInt256} {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {pre mid post : EVM.State} {cost : Nat}, Z vj op pre = .ok (mid,cost) →
    StepOk fuel cost (op,arg) mid post → post.gasAvailable.toNat ≤ pre.gasAvailable.toNat

private theorem sub_nonincrease (gas : UInt256) (cost : Nat) (hc : cost ≤ gas.toNat) :
    (gas - UInt256.ofNat cost).toNat ≤ gas.toNat := by
  rw [toNat_sub_ofNat hc]
  exact Nat.sub_le _ _

theorem precompile_ecrec (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    (Ξ_ECREC world gas substate env).2.2.1.toNat ≤ gas.toNat := by
  dsimp only [Ξ_ECREC]
  repeat' first
    | exact Nat.zero_le _
    | (apply sub_nonincrease; omega)
    | split

theorem precompile_sha256 (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    (Ξ_SHA256 world gas substate env).2.2.1.toNat ≤ gas.toNat := by
  dsimp only [Ξ_SHA256]
  repeat' first
    | exact Nat.zero_le _
    | (apply sub_nonincrease; omega)
    | split

theorem precompile_rip160 (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    (Ξ_RIP160 world gas substate env).2.2.1.toNat ≤ gas.toNat := by
  dsimp only [Ξ_RIP160]
  repeat' first
    | exact Nat.zero_le _
    | (apply sub_nonincrease; omega)
    | split

theorem precompile_id (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    (Ξ_ID world gas substate env).2.2.1.toNat ≤ gas.toNat := by
  dsimp only [Ξ_ID]
  repeat' first
    | exact Nat.zero_le _
    | (apply sub_nonincrease; omega)
    | split

theorem precompile_expmod (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    (Ξ_EXPMOD world gas substate env).2.2.1.toNat ≤ gas.toNat := by
  dsimp only [Ξ_EXPMOD]
  repeat' first
    | exact Nat.zero_le _
    | (apply sub_nonincrease; omega)
    | split

theorem precompile_bn_add (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    (Ξ_BN_ADD world gas substate env).2.2.1.toNat ≤ gas.toNat := by
  dsimp only [Ξ_BN_ADD]
  repeat' first
    | exact Nat.zero_le _
    | (apply sub_nonincrease; omega)
    | split

theorem precompile_bn_mul (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    (Ξ_BN_MUL world gas substate env).2.2.1.toNat ≤ gas.toNat := by
  dsimp only [Ξ_BN_MUL]
  repeat' first
    | exact Nat.zero_le _
    | (apply sub_nonincrease; omega)
    | split

theorem precompile_snarkv (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    (Ξ_SNARKV world gas substate env).2.2.1.toNat ≤ gas.toNat := by
  dsimp only [Ξ_SNARKV]
  repeat' first
    | exact Nat.zero_le _
    | (apply sub_nonincrease; omega)
    | split

theorem precompile_blake2_f (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    (Ξ_BLAKE2_F world gas substate env).2.2.1.toNat ≤ gas.toNat := by
  dsimp only [Ξ_BLAKE2_F]
  repeat' first
    | exact Nat.zero_le _
    | (apply sub_nonincrease; omega)
    | split

theorem precompile_pointeval (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    (Ξ_PointEval world gas substate env).2.2.1.toNat ≤ gas.toNat := by
  dsimp only [Ξ_PointEval]
  repeat' first
    | exact Nat.zero_le _
    | (apply sub_nonincrease; omega)
    | split

theorem x_zero : XBound 0 := by
  intro vj pre r h
  cases h

theorem xi_zero : XiBound 0 := by
  intro created genesis blocks world original gas substate env r h
  cases h

theorem theta_zero : ThetaBound 0 := by
  intro hashes created genesis header blocks world original substate source origin target code gas price value apparent
    data depth permission created' world' gas' substate' success out h
  cases h

theorem lambda_zero : LambdaBound 0 := by
  intro hashes created genesis header blocks world original substate source origin gas price value depth init salt permission
    addr created' world' gas' substate' success out h
  cases h

theorem step_zero : StepBound 0 := by
  intro vj op arg pre mid post cost hz hs
  cases hs

/-- Actual one-step decomposition covers successful and reverted X results. -/
theorem x_succ (fuel : Nat) (hx : XBound fuel) (hst : StepBound fuel) : XBound (fuel+1) := by
  intro vj pre r h
  rcases hd : decodeAt pre with ⟨op,arg⟩
  cases hz : Z vj op pre with
  | error err => rw [X_succ_of_Z_error hd hz] at h; cases h
  | ok charged =>
    obtain ⟨mid,cost⟩ := charged
    cases hs : EVM.step fuel cost (some (op,arg)) mid with
    | error err => rw [X_succ_of_step_error hd hz hs] at h; cases h
    | ok post =>
      have hg := hst hz hs
      cases hh : H post.toMachineState op with
      | none =>
        rw [X_succ_of_continue hd hz hs hh] at h
        exact (hx h).trans hg
      | some out =>
        by_cases hr : op = .REVERT
        · rw [X_succ_of_revert hd hz hs hh hr] at h
          cases h
          exact hg
        · rw [X_succ_of_halt hd hz hs hh hr] at h
          cases h
          exact hg

/-- Ξ preserves the exact returned gas of its actual X evaluation. -/
theorem xi_succ (fuel : Nat) (hx : XBound fuel) : XiBound (fuel+1) := by
  intro created genesis blocks world original gas substate env r h
  let pre : EVM.State :=
    { (default : EVM.State) with
      accountMap := world, σ₀ := original, executionEnv := env, substate := substate,
      createdAccounts := created, gasAvailable := gas, blocks := blocks, genesisBlockHeader := genesis }
  change (do
    let result ← X fuel (D_J env.code ⟨0⟩) pre
    match result with
    | .success st out => pure (.success (st.createdAccounts,st.accountMap,st.gasAvailable,st.substate) out)
    | .revert remaining out => pure (.revert remaining out)) = Except.ok r at h
  cases he : X fuel (D_J env.code ⟨0⟩) pre with
  | error err => simp only [he, Bind.bind, Except.bind] at h; cases h
  | ok result =>
    have hg := hx he
    cases result with
    | success st out =>
      simp only [he, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst r
      exact hg
    | revert remaining out =>
      simp only [he, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst r
      exact hg

/-- Code-branch Θ settlement preserves init gas on both Bool statuses, or
returns zero for an actual exceptional halt. OutOfFuel stays an error. -/
theorem context_theta (fuel : Nat) (hxi : XiBound fuel) (c : MessageCall.Context)
    (hf : c.fuel = fuel) {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,success,out)) : gas.toNat ≤ c.gas.toNat := by
  rw [MessageCall.result_eq_settle] at h
  have hi : ∀ {r}, c.execution = .ok r → (xiGas r).toNat ≤ c.gas.toNat := by
    intro r hr
    unfold MessageCall.Context.execution at hr
    rw [hf] at hr
    exact hxi hr
  cases he : c.execution with
  | error err =>
    simp only [MessageCall.Context.settle, he] at h
    split at h
    · cases h
    · have hg : gas = ⟨0⟩ := (congrArg (fun t => t.2.2.1) (Except.ok.inj h)).symm
      rw [hg]
      exact Nat.zero_le _
  | ok result =>
    have hb := hi he
    cases result with
    | revert remaining data =>
      simp only [MessageCall.Context.settle, he] at h
      have hg : gas = remaining := (congrArg (fun t => t.2.2.1) (Except.ok.inj h)).symm
      rw [hg]
      exact hb
    | success state data =>
      obtain ⟨cr,w,g,ss⟩ := state
      simp only [MessageCall.Context.settle, he] at h
      have hg : gas = g := (congrArg (fun t => t.2.2.1) (Except.ok.inj h)).symm
      rw [hg]
      exact hb

/-- This is exactly Θ's precompile dispatch table, including its default case. -/
def precompileResult (target : AccountAddress) (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    Except ExecutionException (Std.TreeSet AccountAddress compare × Bool × AccountMap .EVM × UInt256 × Substate × ByteArray) :=
  match target with
  | 1 => .ok (∅, Ξ_ECREC world gas substate env)
  | 2 => .ok (∅, Ξ_SHA256 world gas substate env)
  | 3 => .ok (∅, Ξ_RIP160 world gas substate env)
  | 4 => .ok (∅, Ξ_ID world gas substate env)
  | 5 => .ok (∅, Ξ_EXPMOD world gas substate env)
  | 6 => .ok (∅, Ξ_BN_ADD world gas substate env)
  | 7 => .ok (∅, Ξ_BN_MUL world gas substate env)
  | 8 => .ok (∅, Ξ_SNARKV world gas substate env)
  | 9 => .ok (∅, Ξ_BLAKE2_F world gas substate env)
  | 10 => .ok (∅, Ξ_PointEval world gas substate env)
  | _ => default

theorem precompile_result_bound (target : AccountAddress) (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM)
    {created' : Std.TreeSet AccountAddress compare} {world' : AccountMap .EVM} {gas' : UInt256}
    {substate' : Substate} {success : Bool} {out : ByteArray}
    (h : precompileResult target world gas substate env = .ok (created',success,world',gas',substate',out)) :
    gas'.toNat ≤ gas.toNat := by
  unfold precompileResult at h
  split at h
  · have hg := congrArg (fun t => t.2.2.2.1) (Except.ok.inj h)
    dsimp only at hg
    rw [← hg]
    exact precompile_ecrec world gas substate env
  · have hg := congrArg (fun t => t.2.2.2.1) (Except.ok.inj h)
    dsimp only at hg
    rw [← hg]
    exact precompile_sha256 world gas substate env
  · have hg := congrArg (fun t => t.2.2.2.1) (Except.ok.inj h)
    dsimp only at hg
    rw [← hg]
    exact precompile_rip160 world gas substate env
  · have hg := congrArg (fun t => t.2.2.2.1) (Except.ok.inj h)
    dsimp only at hg
    rw [← hg]
    exact precompile_id world gas substate env
  · have hg := congrArg (fun t => t.2.2.2.1) (Except.ok.inj h)
    dsimp only at hg
    rw [← hg]
    exact precompile_expmod world gas substate env
  · have hg := congrArg (fun t => t.2.2.2.1) (Except.ok.inj h)
    dsimp only at hg
    rw [← hg]
    exact precompile_bn_add world gas substate env
  · have hg := congrArg (fun t => t.2.2.2.1) (Except.ok.inj h)
    dsimp only at hg
    rw [← hg]
    exact precompile_bn_mul world gas substate env
  · have hg := congrArg (fun t => t.2.2.2.1) (Except.ok.inj h)
    dsimp only at hg
    rw [← hg]
    exact precompile_snarkv world gas substate env
  · have hg := congrArg (fun t => t.2.2.2.1) (Except.ok.inj h)
    dsimp only at hg
    rw [← hg]
    exact precompile_blake2_f world gas substate env
  · have hg := congrArg (fun t => t.2.2.2.1) (Except.ok.inj h)
    dsimp only at hg
    rw [← hg]
    exact precompile_pointeval world gas substate env
  · have hg := congrArg (fun t => t.2.2.2.1) (Except.ok.inj h)
    dsimp only at hg
    rw [← hg]
    exact Nat.zero_le _

/-- Θ's actual precompile settlement retains the dispatched remaining gas,
including both empty-world fallback choices and any Bool status. -/
theorem precompile_theta (fuel : Nat) (c : MessageCall.Context) (target : AccountAddress)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : Θ (fuel+1) c.blobHashes c.created c.genesis c.blocks c.world c.originalWorld c.substate
      c.caller c.origin c.target (.Precompiled target) c.gas c.gasPrice c.value c.apparentValue c.calldata
      c.depth c.header c.permission = .ok (created,world,gas,substate,success,out)) : gas.toNat ≤ c.gas.toNat := by
  let env : ExecutionEnv .EVM := { c.environment with code := ByteArray.empty }
  have h : (do
    let (cr,z,w,g,ss,data) ← precompileResult target c.entryWorld c.gas c.substate env
    pure (cr,if w == ∅ then c.world else w,g,if w == ∅ then c.substate else ss,z,data)) =
      Except.ok (created,world,gas,substate,success,out) := by
    convert h using 1
    unfold Θ precompileResult
    dsimp only
    split
    all_goals first | rfl | (split <;> first | rfl | contradiction)
  cases he : precompileResult target c.entryWorld c.gas c.substate env with
  | error err => simp only [he, Bind.bind, Except.bind] at h; cases h
  | ok result =>
    obtain ⟨cr,z,w,g,ss,data⟩ := result
    have hb := precompile_result_bound target c.entryWorld c.gas c.substate env he
    simp only [he, Bind.bind, Except.bind, pure, Except.pure] at h
    have hg := (congrArg (fun t => t.2.2.1) (Except.ok.inj h)).symm
    dsimp only at hg
    rw [hg]
    exact hb

theorem theta_succ (fuel : Nat) (hxi : XiBound fuel) : ThetaBound (fuel+1) := by
  intro hashes created genesis header blocks world original substate source origin target code gas price value apparent
    data depth permission created' world' gas' substate' success out h
  cases code with
  | Code bytes =>
    let c : MessageCall.Context :=
      { fuel := fuel, created := created, genesis := genesis, blocks := blocks, world := world,
        originalWorld := original, substate := substate, caller := source, origin := origin, target := target,
        code := bytes, gas := gas, gasPrice := price, value := value, apparentValue := apparent,
        calldata := data, depth := depth, header := header, permission := permission, blobHashes := hashes }
    exact context_theta fuel hxi c rfl h
  | Precompiled p =>
    let c : MessageCall.Context :=
      { fuel := fuel, created := created, genesis := genesis, blocks := blocks, world := world,
        originalWorld := original, substate := substate, caller := source, origin := origin, target := target,
        code := .empty, gas := gas, gasPrice := price, value := value, apparentValue := apparent,
        calldata := data, depth := depth, header := header, permission := permission, blobHashes := hashes }
    exact precompile_theta fuel c p h

/-- Every actual completed Lambda settlement decreases or preserves the gas
of its init execution, including rejected code deposit and REVERT. -/
theorem context_lambda (fuel : Nat) (hxi : XiBound fuel) (c : CreationSettlement.Context)
    (hf : c.fuel = fuel) {addr : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {world : AccountMap .EVM} {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (addr,created,world,gas,substate,success,out)) : gas.toNat ≤ c.gas.toNat := by
  cases hp : c.preimage with
  | none =>
    unfold CreationSettlement.Context.result Lambda at h
    change Lambda.L_A c.sender ((c.world.get? c.sender |>.option ⟨0⟩ (·.nonce))-⟨1⟩) c.salt c.init = none at hp
    dsimp only at h
    rw [hp] at h
    cases h
  | some preimage =>
    rw [CreationSettlement.result_eq_settle c hp] at h
    have hi : ∀ {r}, c.execution (CreationSettlement.address preimage) = .ok r → (xiGas r).toNat ≤ c.gas.toNat := by
      intro r hr
      unfold CreationSettlement.Context.execution at hr
      rw [hf] at hr
      exact hxi hr
    cases he : c.execution (CreationSettlement.address preimage) with
    | error err =>
      simp only [CreationSettlement.Context.settle, he] at h
      split at h
      · cases h
      · have hg : gas = ⟨0⟩ := (congrArg (fun t => t.2.2.2.1) (Except.ok.inj h)).symm
        rw [hg]
        exact Nat.zero_le _
    | ok result =>
      have hb := hi he
      cases result with
      | revert remaining data =>
        simp only [CreationSettlement.Context.settle, he] at h
        have hg : gas = remaining := (congrArg (fun t => t.2.2.2.1) (Except.ok.inj h)).symm
        rw [hg]
        exact hb
      | success state code =>
        obtain ⟨cr,w,g,ss⟩ := state
        cases hd : c.depositFailure (CreationSettlement.address preimage) g code
        · simp only [CreationSettlement.Context.settle, he, hd, Bool.false_eq_true, ↓reduceIte] at h
          have hg : gas = UInt256.ofNat (g.toNat - GasConstants.Gcodedeposit * code.size) :=
            (congrArg (fun t => t.2.2.2.1) (Except.ok.inj h)).symm
          have hfit : g.toNat - GasConstants.Gcodedeposit * code.size < UInt256.size :=
            (Nat.sub_le _ _).trans_lt g.val.isLt
          rw [hg, toNat_ofNat_lit _ hfit]
          exact (Nat.sub_le _ _).trans hb
        · simp only [CreationSettlement.Context.settle, he, hd, ↓reduceIte] at h
          have hg : gas = UInt256.ofNat 0 := (congrArg (fun t => t.2.2.2.1) (Except.ok.inj h)).symm
          rw [hg]
          exact Nat.zero_le _

theorem lambda_succ (fuel : Nat) (hxi : XiBound fuel) : LambdaBound (fuel+1) := by
  intro hashes created genesis header blocks world original substate source origin gas price value depth init salt permission
    addr created' world' gas' substate' success out h
  let c : CreationSettlement.Context :=
    { fuel := fuel, blobHashes := hashes, created := created, genesis := genesis, blocks := blocks,
      world := world, originalWorld := original, substate := substate, sender := source, origin := origin,
      gas := gas, gasPrice := price, value := value, init := init, depth := depth, salt := salt,
      header := header, permission := permission }
  exact context_lambda fuel hxi c rfl h

/-- Actual Z supplies the stack operands required for recursive dispatch. -/
theorem accepted_stack {vj : Array UInt256} {op : Operation .EVM} {pre mid : EVM.State} {cost : Nat}
    (h : Z vj op pre = .ok (mid,cost)) : (δ op).getD 0 ≤ pre.stack.length := by
  simp only [Z, Bind.bind, Except.bind, pure, Except.pure] at h
  replace h := elim_guard h
  replace h := elim_guard h
  replace h := elim_guard h
  exact Nat.le_of_not_gt (elim_guard_not h)

private theorem stack3 (s : Stack UInt256) (h : 3 ≤ s.length) :
    ∃ a0 a1 a2 rest, s = a0::a1::a2::rest := by
  rcases s with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, rest⟩⟩⟩ <;> simp_all

private theorem stack4 (s : Stack UInt256) (h : 4 ≤ s.length) :
    ∃ a0 a1 a2 a3 rest, s = a0::a1::a2::a3::rest := by
  rcases s with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, rest⟩⟩⟩⟩ <;> simp_all

private theorem stack6 (s : Stack UInt256) (h : 6 ≤ s.length) :
    ∃ a0 a1 a2 a3 a4 a5 rest, s = a0::a1::a2::a3::a4::a5::rest := by
  rcases s with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, rest⟩⟩⟩⟩⟩⟩ <;> simp_all

private theorem stack7 (s : Stack UInt256) (h : 7 ≤ s.length) :
    ∃ a0 a1 a2 a3 a4 a5 a6 rest, s = a0::a1::a2::a3::a4::a5::a6::rest := by
  rcases s with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, rest⟩⟩⟩⟩⟩⟩⟩ <;> simp_all

/-- CALL's smaller-fuel Θ bound discharges its local returned-gas obligation. -/
theorem call_step (fuel : Nat) (ht : ThetaBound fuel)
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat} {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::rest)
    (hz : Z vj .CALL pre = .ok (mid,cost))
    (hs : StepOk (fuel+2) cost (.CALL,arg) mid post) : post.gasAvailable.toNat ≤ pre.gasAvailable.toNat := by
  by_cases hg : value ≤ (mid.accountMap.get? mid.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧ mid.executionEnv.depth < 1024
  · obtain ⟨cr,w,g,ss,z,out,hchild,hd⟩ := CallDispatchGas.accepted_step_call_debit fuel
      requested target value inOff inLen outOff outLen rest hstack hz hg hs
    have hb := ht hchild
    have hf := (CallGasAccounting.accepted_call_forwarded_fit hstack hz).2
    change g.toNat ≤ (UInt256.ofNat (Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
      value requested mid.accountMap mid.toMachineState mid.substate)).toNat at hb
    rw [hf] at hb
    have he := hd hb
    omega
  · have he := (CallDispatchGas.accepted_step_call_denied_debit fuel
      requested target value inOff inLen outOff outLen rest hstack hz hg hs).2
    omega

/-- The same smaller-fuel argument covers CALLCODE, DELEGATECALL and STATICCALL. -/
theorem family_step (kind : CallFamilyGas.Variant) (fuel : Nat) (ht : ThetaBound fuel)
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat} {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = CallFamilyGas.stack kind requested target value inOff inLen outOff outLen rest)
    (hz : Z vj (CallFamilyGas.opcode kind) pre = .ok (mid,cost))
    (hs : StepOk (fuel+2) cost (CallFamilyGas.opcode kind,arg) mid post) :
    post.gasAvailable.toNat ≤ pre.gasAvailable.toNat := by
  by_cases hg : CallFamilyGas.gate kind mid value
  · obtain ⟨cr,w,g,ss,z,out,hchild,hd⟩ := CallFamilyGas.accepted_step_debit kind fuel
      requested target value inOff inLen outOff outLen rest hstack hz hg hs
    have hb := ht hchild
    change g.toNat ≤ (UInt256.ofNat (CallFamilyGas.allowance kind mid requested target value)).toNat at hb
    rw [(CallFamilyGas.accepted_forwarded_fit kind hstack hz).2] at hb
    have he := hd hb
    omega
  · have he := (CallFamilyGas.accepted_denied_debit kind fuel
      requested target value inOff inLen outOff outLen rest hstack hz hg hs).2
    omega

/-- CREATE's real caught-error branch needs no false completed child result.
Only its actual completed child branch uses the smaller-fuel Lambda bound. -/
theorem creation_step (kind : CreationGas.Variant) (fuel : Nat) (hl : LambdaBound fuel)
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat} {arg : Option (UInt256 × Nat)}
    (value off len salt : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = CreationGas.stack kind value off len salt rest)
    (hz : Z vj (CreationGas.opcode kind) pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (CreationGas.opcode kind,arg) mid post) :
    post.gasAvailable.toNat ≤ pre.gasAvailable.toNat := by
  by_cases hn : CreationGas.nonceAllowed mid
  · by_cases hg : CreationGas.gate mid value off len
    · rcases CreationGas.accepted_child_debit kind fuel value off len salt rest hstack hz hn hg hs with hchild | herr
      · obtain ⟨addr,cr,w,g,ss,z,out,hchild,hd⟩ := hchild
        have hb := hl hchild
        change g.toNat ≤ (UInt256.ofNat (CreationGas.allowance cost mid)).toNat at hb
        rw [(CreationGas.forwarded_fit cost mid).2] at hb
        have he := hd hb
        omega
      · obtain ⟨err,_,hd,_⟩ := herr
        omega
    · have he := (CreationGas.accepted_denied_debit kind fuel value off len salt rest hstack hz (Or.inr hg) hs).1
      omega
  · have he := (CreationGas.accepted_denied_debit kind fuel value off len salt rest hstack hz (Or.inl hn) hs).1
    omega

/-- All recursive dispatch bounds are discharged by strictly smaller actual
fuel. No child remaining-gas estimate is an assumption of the final induction. -/
theorem step_of_children (fuel : Nat)
    (ht : ∀ n, n < fuel → ThetaBound n) (hl : ∀ n, n < fuel → LambdaBound n) : StepBound fuel := by
  intro vj op arg pre mid post cost hz hs
  cases fuel with
  | zero => cases hs
  | succ fuel =>
    by_cases ho : OrdinaryGas.Ordinary op
    · exact OrdinaryGas.accepted_step_nonincrease ho hz hs
    have hsize := accepted_stack hz
    simp only [OrdinaryGas.ordinary_iff, not_and_or, not_not] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨a0,a1,a2,a3,a4,a5,a6,rest,hstack⟩ := stack7 pre.stack (by simpa only [δ, Option.getD_some] using hsize)
      cases fuel with
      | zero =>
        have hpop : mid.stack.pop7 = some (rest,a0,a1,a2,a3,a4,a5,a6) := by
          rw [Z_ok_stack hz, hstack]
          rfl
        simp only [StepOk, Step, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at hs
        rw [hpop] at hs
        change Except.error ExecutionException.OutOfFuel = Except.ok post at hs
        cases hs
      | succ fuel =>
        exact call_step fuel (ht fuel (by omega)) a0 a1 a2 a3 a4 a5 a6 rest hstack hz hs
    · obtain ⟨a0,a1,a2,a3,a4,a5,a6,rest,hstack⟩ := stack7 pre.stack (by simpa only [δ, Option.getD_some] using hsize)
      cases fuel with
      | zero =>
        have hpop : mid.stack.pop7 = some (rest,a0,a1,a2,a3,a4,a5,a6) := by
          rw [Z_ok_stack hz, hstack]
          rfl
        simp only [StepOk, Step, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at hs
        rw [hpop] at hs
        change Except.error ExecutionException.OutOfFuel = Except.ok post at hs
        cases hs
      | succ fuel =>
        exact family_step .callcode fuel (ht fuel (by omega)) a0 a1 a2 a3 a4 a5 a6 rest hstack hz hs
    · obtain ⟨a0,a1,a2,a3,a4,a5,rest,hstack⟩ := stack6 pre.stack (by simpa only [δ, Option.getD_some] using hsize)
      cases fuel with
      | zero =>
        have hpop : mid.stack.pop6 = some (rest,a0,a1,a2,a3,a4,a5) := by
          rw [Z_ok_stack hz, hstack]
          rfl
        simp only [StepOk, Step, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at hs
        rw [hpop] at hs
        change Except.error ExecutionException.OutOfFuel = Except.ok post at hs
        cases hs
      | succ fuel =>
        exact family_step .delegatecall fuel (ht fuel (by omega)) a0 a1 ⟨0⟩ a2 a3 a4 a5 rest hstack hz hs
    · obtain ⟨a0,a1,a2,a3,a4,a5,rest,hstack⟩ := stack6 pre.stack (by simpa only [δ, Option.getD_some] using hsize)
      cases fuel with
      | zero =>
        have hpop : mid.stack.pop6 = some (rest,a0,a1,a2,a3,a4,a5) := by
          rw [Z_ok_stack hz, hstack]
          rfl
        simp only [StepOk, Step, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at hs
        rw [hpop] at hs
        change Except.error ExecutionException.OutOfFuel = Except.ok post at hs
        cases hs
      | succ fuel =>
        exact family_step .staticcall fuel (ht fuel (by omega)) a0 a1 ⟨0⟩ a2 a3 a4 a5 rest hstack hz hs
    · obtain ⟨a0,a1,a2,rest,hstack⟩ := stack3 pre.stack (by simpa only [δ, Option.getD_some] using hsize)
      exact creation_step .create fuel (hl fuel (by omega)) a0 a1 a2 ⟨0⟩ rest hstack hz hs
    · obtain ⟨a0,a1,a2,a3,rest,hstack⟩ := stack4 pre.stack (by simpa only [δ, Option.getD_some] using hsize)
      exact creation_step .create2 fuel (hl fuel (by omega)) a0 a1 a2 a3 rest hstack hz hs

/-- Mutual strong induction on evaluator fuel proves all five actual gas
bounds together. Every recursive edge uses a strictly smaller fuel index. -/
theorem all_bounds (fuel : Nat) :
    XBound fuel ∧ XiBound fuel ∧ ThetaBound fuel ∧ LambdaBound fuel ∧ StepBound fuel := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    have hs : StepBound fuel := step_of_children fuel
      (fun n hn => (ih n hn).2.2.1) (fun n hn => (ih n hn).2.2.2.1)
    cases fuel with
    | zero => exact ⟨x_zero,xi_zero,theta_zero,lambda_zero,hs⟩
    | succ fuel =>
      obtain ⟨hx,hxi,ht,hl,hst⟩ := ih fuel (Nat.lt_succ_self _)
      exact ⟨x_succ fuel hx hst,xi_succ fuel hx,theta_succ fuel hxi,lambda_succ fuel hxi,hs⟩

/-- Universal actual X bound, for both success and REVERT. -/
theorem x_remaining (fuel : Nat) : XBound fuel := (all_bounds fuel).1

/-- Universal actual Ξ bound, for both success and REVERT. -/
theorem xi_remaining (fuel : Nat) : XiBound fuel := (all_bounds fuel).2.1

/-- Universal actual Θ bound, for code/precompiles and either completed status. -/
theorem theta_remaining (fuel : Nat) : ThetaBound fuel := (all_bounds fuel).2.2.1

/-- Universal actual Λ bound, including failed creation and rejected code deposit. -/
theorem lambda_remaining (fuel : Nat) : LambdaBound fuel := (all_bounds fuel).2.2.2.1

/-- Every actual accepted and completed opcode step, including child operations,
has nonincreasing natural gas. Errors still carry no invented endpoint. -/
theorem step_remaining (fuel : Nat) : StepBound fuel := (all_bounds fuel).2.2.2.2

/-- Complete ordinary message-call interface, for either actual Bool status. -/
theorem message_remaining (c : MessageCall.Context)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,success,out)) : gas.toNat ≤ c.gas.toNat :=
  theta_remaining (c.fuel+1) h

/-- Complete creation interface, with address derivation and all actual
code-deposit/error branches covered by the universal Lambda theorem. -/
theorem creation_remaining (c : CreationSettlement.Context)
    {addr : AccountAddress} {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (addr,created,world,gas,substate,success,out)) : gas.toNat ≤ c.gas.toNat :=
  lambda_remaining (c.fuel+1) h

#print axioms step_of_children
#print axioms all_bounds
#print axioms x_remaining
#print axioms xi_remaining
#print axioms theta_remaining
#print axioms lambda_remaining
#print axioms step_remaining
#print axioms message_remaining
#print axioms creation_remaining
end Eip8282.Audit.Integrator.ReturnedGas
