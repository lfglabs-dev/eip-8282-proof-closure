import Eip8282.Audit.Integrator.CreationFunding
import Eip8282.Audit.Integrator.CreationWorld
import Eip8282.Audit.Integrator.OrdinaryFunding
import Eip8282.Audit.Integrator.CallWorld
import Eip8282.Audit.Integrator.ReturnedGas

/-!
# Funding through actual recursive execution

Bounds concern the finite sum of actual account balances. Theta requires the
real sender to afford the transfer. Lambda additionally requires a nonzero
sender nonce, which internal CREATE derives from its admitted increment.
No supply ceiling or post-state invariant is supplied by a caller.
-/
namespace Eip8282.Audit.Integrator.ExecutionFunding
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open TransferFunding
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def XBound (fuel : Nat) : Prop :=
  ∀ {vj : Array UInt256} {pre post : EVM.State} {out : ByteArray},
    X fuel vj pre = .ok (.success post out) → worldFunds post.accountMap ≤ worldFunds pre.accountMap

def XiBound (fuel : Nat) : Prop :=
  ∀ {created : Std.TreeSet AccountAddress compare} {genesis : BlockHeader} {blocks : ProcessedBlocks}
    {world original : AccountMap .EVM} {gas : UInt256} {substate : Substate} {env : ExecutionEnv .EVM}
    {created' : Std.TreeSet AccountAddress compare} {world' : AccountMap .EVM} {gas' : UInt256}
    {substate' : Substate} {out : ByteArray},
    Ξ fuel created genesis blocks world original gas substate env =
      .ok (.success (created',world',gas',substate') out) → worldFunds world' ≤ worldFunds world

def ThetaBound (fuel : Nat) : Prop :=
  ∀ {hashes : List ByteArray} {created : Std.TreeSet AccountAddress compare} {genesis header : BlockHeader}
    {blocks : ProcessedBlocks} {world original : AccountMap .EVM} {substate : Substate}
    {source origin target : AccountAddress} {code : ToExecute .EVM} {gas price value apparent : UInt256}
    {data : ByteArray} {depth : Nat} {permission : Bool}
    {created' : Std.TreeSet AccountAddress compare} {world' : AccountMap .EVM} {gas' : UInt256}
    {substate' : Substate} {success : Bool} {out : ByteArray},
    value.toNat ≤ worldBalance world source →
    Θ fuel hashes created genesis blocks world original substate source origin target code gas price value apparent
      data depth header permission = .ok (created',world',gas',substate',success,out) → worldFunds world' ≤ worldFunds world

def NonzeroNonce (world : AccountMap .EVM) (sender : AccountAddress) : Prop :=
  ∃ account, world.get? sender = some account ∧ account.nonce ≠ ⟨0⟩

def LambdaBound (fuel : Nat) : Prop :=
  ∀ {hashes : List ByteArray} {created : Std.TreeSet AccountAddress compare} {genesis header : BlockHeader}
    {blocks : ProcessedBlocks} {world original : AccountMap .EVM} {substate : Substate}
    {source origin : AccountAddress} {gas price value depth : UInt256} {init : ByteArray}
    {salt : Option ByteArray} {permission : Bool} {addr : AccountAddress}
    {created' : Std.TreeSet AccountAddress compare} {world' : AccountMap .EVM} {gas' : UInt256}
    {substate' : Substate} {success : Bool} {out : ByteArray},
    value.toNat ≤ worldBalance world source → NonzeroNonce world source →
    Lambda fuel hashes created genesis blocks world original substate source origin gas price value init depth salt
      header permission = .ok (addr,created',world',gas',substate',success,out) → worldFunds world' ≤ worldFunds world

def StepBound (fuel : Nat) : Prop :=
  ∀ {vj : Array UInt256} {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {pre mid post : EVM.State} {cost : Nat}, Z vj op pre = .ok (mid,cost) →
    StepOk fuel cost (op,arg) mid post → worldFunds post.accountMap ≤ worldFunds pre.accountMap

theorem x_succ (fuel : Nat) (hx : XBound fuel) (hst : StepBound fuel) : XBound (fuel+1) := by
  intro vj pre post out h
  obtain ⟨rest,cost,op,arg,mid,final,hfuel,hd,hz,hs,hc⟩ := SuccessInversion.success_step h
  have he : rest = fuel := by omega
  subst rest
  have hg := hst hz hs
  rcases hc with ⟨hn,hr⟩ | ⟨hh,hop,he⟩
  · exact (hx hr).trans hg
  · subst final
    exact hg

theorem xi_succ (fuel : Nat) (hx : XBound fuel) : XiBound (fuel+1) := by
  intro created genesis blocks world original gas substate env created' world' gas' substate' out h
  let pre : EVM.State :=
    { (default : EVM.State) with
      accountMap := world, σ₀ := original, executionEnv := env,
      substate := substate, createdAccounts := created, gasAvailable := gas, blocks := blocks,
      genesisBlockHeader := genesis }
  change (do
    let result ← X fuel (D_J env.code ⟨0⟩) pre
    match result with
    | .success st out => pure (ExecutionResult.success (st.createdAccounts,st.accountMap,st.gasAvailable,st.substate) out)
    | .revert remaining out => pure (ExecutionResult.revert remaining out)) =
      Except.ok (ExecutionResult.success (created',world',gas',substate') out) at h
  cases he : X fuel (D_J env.code ⟨0⟩) pre with
  | error err => simp only [he, Bind.bind, Except.bind] at h; cases h
  | ok result =>
    cases result with
    | revert remaining data => simp only [he, Bind.bind, Except.bind, pure, Except.pure] at h; cases h
    | success st data =>
      have hg := hx he
      simp only [he, Bind.bind, Except.bind, pure, Except.pure] at h
      cases h
      exact hg

theorem context_theta (fuel : Nat) (hxi : XiBound fuel) (c : MessageCall.Context)
    (hf : c.fuel = fuel) (hfund : c.value.toNat ≤ worldBalance c.world c.caller)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,success,out)) : worldFunds world ≤ worldFunds c.world := by
  rw [MessageCall.result_eq_settle] at h
  cases he : c.execution with
  | error err =>
    simp only [MessageCall.Context.settle, he] at h
    split at h
    · cases h
    · have hw : world = c.world := (congrArg (fun t => t.2.1) (Except.ok.inj h)).symm
      rw [hw]
  | ok result =>
    cases result with
    | revert remaining data =>
      simp only [MessageCall.Context.settle, he] at h
      have hw : world = c.world := (congrArg (fun t => t.2.1) (Except.ok.inj h)).symm
      rw [hw]
    | success state data =>
      obtain ⟨cr,iw,ig,ss⟩ := state
      have hi : worldFunds iw ≤ worldFunds c.entryWorld := by
        unfold MessageCall.Context.execution at he
        rw [hf] at he
        exact hxi he
      have hb := hi.trans (entry_funds_le c hfund)
      simp only [MessageCall.Context.settle, he] at h
      have hw : world = if iw == ∅ then c.world else iw :=
        (congrArg (fun t => t.2.1) (Except.ok.inj h)).symm
      rw [hw]
      split
      · exact Nat.le_refl _
      · exact hb

theorem precompile_ecrec (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    worldFunds (Ξ_ECREC world gas substate env).2.1 ≤ worldFunds world := by
  dsimp only [Ξ_ECREC]
  repeat' first
    | exact Nat.le_refl _
    | exact Nat.zero_le _
    | split

theorem precompile_sha256 (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    worldFunds (Ξ_SHA256 world gas substate env).2.1 ≤ worldFunds world := by
  dsimp only [Ξ_SHA256]
  repeat' first
    | exact Nat.le_refl _
    | exact Nat.zero_le _
    | split

theorem precompile_rip160 (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    worldFunds (Ξ_RIP160 world gas substate env).2.1 ≤ worldFunds world := by
  dsimp only [Ξ_RIP160]
  repeat' first
    | exact Nat.le_refl _
    | exact Nat.zero_le _
    | split

theorem precompile_id (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    worldFunds (Ξ_ID world gas substate env).2.1 ≤ worldFunds world := by
  dsimp only [Ξ_ID]
  repeat' first
    | exact Nat.le_refl _
    | exact Nat.zero_le _
    | split

theorem precompile_expmod (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    worldFunds (Ξ_EXPMOD world gas substate env).2.1 ≤ worldFunds world := by
  dsimp only [Ξ_EXPMOD]
  repeat' first
    | exact Nat.le_refl _
    | exact Nat.zero_le _
    | split

theorem precompile_bn_add (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    worldFunds (Ξ_BN_ADD world gas substate env).2.1 ≤ worldFunds world := by
  dsimp only [Ξ_BN_ADD]
  repeat' first
    | exact Nat.le_refl _
    | exact Nat.zero_le _
    | split

theorem precompile_bn_mul (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    worldFunds (Ξ_BN_MUL world gas substate env).2.1 ≤ worldFunds world := by
  dsimp only [Ξ_BN_MUL]
  repeat' first
    | exact Nat.le_refl _
    | exact Nat.zero_le _
    | split

theorem precompile_snarkv (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    worldFunds (Ξ_SNARKV world gas substate env).2.1 ≤ worldFunds world := by
  dsimp only [Ξ_SNARKV]
  repeat' first
    | exact Nat.le_refl _
    | exact Nat.zero_le _
    | split

theorem precompile_blake2_f (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    worldFunds (Ξ_BLAKE2_F world gas substate env).2.1 ≤ worldFunds world := by
  dsimp only [Ξ_BLAKE2_F]
  repeat' first
    | exact Nat.le_refl _
    | exact Nat.zero_le _
    | split

theorem precompile_pointeval (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) :
    worldFunds (Ξ_PointEval world gas substate env).2.1 ≤ worldFunds world := by
  dsimp only [Ξ_PointEval]
  repeat' first
    | exact Nat.le_refl _
    | exact Nat.zero_le _
    | split

theorem precompile_result_bound (target : AccountAddress) (world : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM)
    {created' : Std.TreeSet AccountAddress compare} {world' : AccountMap .EVM} {gas' : UInt256}
    {substate' : Substate} {success : Bool} {out : ByteArray}
    (h : ReturnedGas.precompileResult target world gas substate env = .ok (created',success,world',gas',substate',out)) :
    worldFunds world' ≤ worldFunds world := by
  unfold ReturnedGas.precompileResult at h
  split at h
  · have hw := congrArg (fun t => t.2.2.1) (Except.ok.inj h)
    dsimp only at hw
    rw [← hw]
    exact precompile_ecrec world gas substate env
  · have hw := congrArg (fun t => t.2.2.1) (Except.ok.inj h)
    dsimp only at hw
    rw [← hw]
    exact precompile_sha256 world gas substate env
  · have hw := congrArg (fun t => t.2.2.1) (Except.ok.inj h)
    dsimp only at hw
    rw [← hw]
    exact precompile_rip160 world gas substate env
  · have hw := congrArg (fun t => t.2.2.1) (Except.ok.inj h)
    dsimp only at hw
    rw [← hw]
    exact precompile_id world gas substate env
  · have hw := congrArg (fun t => t.2.2.1) (Except.ok.inj h)
    dsimp only at hw
    rw [← hw]
    exact precompile_expmod world gas substate env
  · have hw := congrArg (fun t => t.2.2.1) (Except.ok.inj h)
    dsimp only at hw
    rw [← hw]
    exact precompile_bn_add world gas substate env
  · have hw := congrArg (fun t => t.2.2.1) (Except.ok.inj h)
    dsimp only at hw
    rw [← hw]
    exact precompile_bn_mul world gas substate env
  · have hw := congrArg (fun t => t.2.2.1) (Except.ok.inj h)
    dsimp only at hw
    rw [← hw]
    exact precompile_snarkv world gas substate env
  · have hw := congrArg (fun t => t.2.2.1) (Except.ok.inj h)
    dsimp only at hw
    rw [← hw]
    exact precompile_blake2_f world gas substate env
  · have hw := congrArg (fun t => t.2.2.1) (Except.ok.inj h)
    dsimp only at hw
    rw [← hw]
    exact precompile_pointeval world gas substate env
  · have hw := congrArg (fun t => t.2.2.1) (Except.ok.inj h)
    dsimp only at hw
    rw [← hw]
    exact Nat.zero_le _

theorem precompile_theta (fuel : Nat) (c : MessageCall.Context) (target : AccountAddress)
    (hfund : c.value.toNat ≤ worldBalance c.world c.caller)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : Θ (fuel+1) c.blobHashes c.created c.genesis c.blocks c.world c.originalWorld c.substate
      c.caller c.origin c.target (.Precompiled target) c.gas c.gasPrice c.value c.apparentValue c.calldata
      c.depth c.header c.permission = .ok (created,world,gas,substate,success,out)) :
    worldFunds world ≤ worldFunds c.world := by
  let env : ExecutionEnv .EVM := { c.environment with code := ByteArray.empty }
  have h : (do
    let (cr,z,w,g,ss,data) ← ReturnedGas.precompileResult target c.entryWorld c.gas c.substate env
    pure (cr,if w == ∅ then c.world else w,g,if w == ∅ then c.substate else ss,z,data)) =
      Except.ok (created,world,gas,substate,success,out) := by
    convert h using 1
    unfold Θ ReturnedGas.precompileResult
    dsimp only
    split
    all_goals first | rfl | (split <;> first | rfl | contradiction)
  cases he : ReturnedGas.precompileResult target c.entryWorld c.gas c.substate env with
  | error err => simp only [he, Bind.bind, Except.bind] at h; cases h
  | ok result =>
    obtain ⟨cr,z,w,g,ss,data⟩ := result
    have hb := (precompile_result_bound target c.entryWorld c.gas c.substate env he).trans (entry_funds_le c hfund)
    simp only [he, Bind.bind, Except.bind, pure, Except.pure] at h
    have hw : world = if w == ∅ then c.world else w :=
      (congrArg (fun t => t.2.1) (Except.ok.inj h)).symm
    rw [hw]
    split
    · exact Nat.le_refl _
    · exact hb

theorem theta_succ (fuel : Nat) (hxi : XiBound fuel) : ThetaBound (fuel+1) := by
  intro hashes created genesis header blocks world original substate source origin target code gas price value apparent
    data depth permission created' world' gas' substate' success out hfund h
  cases code with
  | Code bytes =>
    let c : MessageCall.Context :=
      { fuel := fuel, created := created, genesis := genesis, blocks := blocks, world := world,
        originalWorld := original, substate := substate, caller := source, origin := origin, target := target,
        code := bytes, gas := gas, gasPrice := price, value := value, apparentValue := apparent,
        calldata := data, depth := depth, header := header, permission := permission, blobHashes := hashes }
    exact context_theta fuel hxi c rfl hfund h
  | Precompiled p =>
    let c : MessageCall.Context :=
      { fuel := fuel, created := created, genesis := genesis, blocks := blocks, world := world,
        originalWorld := original, substate := substate, caller := source, origin := origin, target := target,
        code := .empty, gas := gas, gasPrice := price, value := value, apparentValue := apparent,
        calldata := data, depth := depth, header := header, permission := permission, blobHashes := hashes }
    exact precompile_theta fuel c p hfund h

theorem context_lambda (fuel : Nat) (hxi : XiBound fuel) (c : CreationSettlement.Context)
    (hf : c.fuel = fuel) (hfund : c.value.toNat ≤ worldBalance c.world c.sender)
    (hnonce : NonzeroNonce c.world c.sender)
    {addr : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {world : AccountMap .EVM} {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (addr,created,world,gas,substate,success,out)) :
    worldFunds world ≤ worldFunds c.world := by
  cases hp : c.preimage with
  | none =>
    unfold CreationSettlement.Context.result Lambda at h
    change Lambda.L_A c.sender ((c.world.get? c.sender |>.option ⟨0⟩ (·.nonce))-⟨1⟩) c.salt c.init = none at hp
    dsimp only at h
    rw [hp] at h
    cases h
  | some preimage =>
    rw [CreationSettlement.result_eq_settle c hp] at h
    by_cases ha : c.sender = CreationSettlement.address preimage
    · rw [← ha] at h
      obtain ⟨account,hs,hn⟩ := hnonce
      rw [CreationFunding.alias_settle_world c account hs hn _ h]
    · have hb := CreationFunding.entry_distinct c (CreationSettlement.address preimage) ha hfund
      cases he : c.execution (CreationSettlement.address preimage) with
      | error err =>
        simp only [CreationSettlement.Context.settle, he] at h
        split at h
        · cases h
        · have hw : world = c.world := (congrArg (fun t => t.2.2.1) (Except.ok.inj h)).symm
          rw [hw]
      | ok result =>
        cases result with
        | revert remaining data =>
          simp only [CreationSettlement.Context.settle, he] at h
          have hw : world = c.world := (congrArg (fun t => t.2.2.1) (Except.ok.inj h)).symm
          rw [hw]
        | success state code =>
          obtain ⟨cr,w,g,ss⟩ := state
          have hi : worldFunds w ≤ worldFunds (c.entryWorld (CreationSettlement.address preimage)) := by
            unfold CreationSettlement.Context.execution at he
            rw [hf] at he
            exact hxi he
          simp only [CreationSettlement.Context.settle, he] at h
          have hw : world = if c.depositFailure (CreationSettlement.address preimage) g code then c.world
              else CreationSettlement.install w (CreationSettlement.address preimage) code :=
            (congrArg (fun t => t.2.2.1) (Except.ok.inj h)).symm
          rw [hw]
          split
          · exact Nat.le_refl _
          · rw [CreationFunding.install_preserves]
            exact hi.trans hb

theorem lambda_succ (fuel : Nat) (hxi : XiBound fuel) : LambdaBound (fuel+1) := by
  intro hashes created genesis header blocks world original substate source origin gas price value depth init salt permission
    addr created' world' gas' substate' success out hfund hnonce h
  let c : CreationSettlement.Context :=
    { fuel := fuel, blobHashes := hashes, created := created, genesis := genesis, blocks := blocks,
      world := world, originalWorld := original, substate := substate, sender := source, origin := origin,
      gas := gas, gasPrice := price, value := value, init := init, depth := depth, salt := salt,
      header := header, permission := permission }
  exact context_lambda fuel hxi c rfl hfund hnonce h

theorem call_step (fuel : Nat) (ht : ThetaBound fuel)
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat} {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::rest)
    (hz : Z vj .CALL pre = .ok (mid,cost))
    (hs : StepOk (fuel+2) cost (.CALL,arg) mid post) :
    worldFunds post.accountMap ≤ worldFunds pre.accountMap := by
  have hm : mid.accountMap = pre.accountMap := by rw [Z_ok_state hz]; rfl
  have hstack' := (Z_ok_stack hz).trans hstack
  by_cases hg : value ≤ (mid.accountMap.get? mid.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧ mid.executionEnv.depth < 1024
  · obtain ⟨cr,w,g,ss,z,out,hchild,hw⟩ := CallWorld.step_call_world fuel cost
      requested target value inOff inLen outOff outLen rest hstack' hg hs
    have hf : value.toNat ≤ worldBalance (CallDispatchGas.entered mid).accountMap
        (AccountAddress.ofUInt256 (UInt256.ofNat mid.executionEnv.codeOwner)) := by
      rw [CallFamilyGas.address_word]
      exact CallFunding.gate_to_nat _ _ _ hg.1
    have hb := ht hf hchild
    rw [hw]
    rw [← hm]
    exact hb
  · have hw := (CallWorld.step_call_denied_world fuel cost
      requested target value inOff inLen outOff outLen rest hstack' hg hs).2
    rw [hw,hm]

theorem family_step (kind : CallFamilyGas.Variant) (fuel : Nat) (ht : ThetaBound fuel)
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat} {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = CallFamilyGas.stack kind requested target value inOff inLen outOff outLen rest)
    (hz : Z vj (CallFamilyGas.opcode kind) pre = .ok (mid,cost))
    (hs : StepOk (fuel+2) cost (CallFamilyGas.opcode kind,arg) mid post) :
    worldFunds post.accountMap ≤ worldFunds pre.accountMap := by
  have hm : mid.accountMap = pre.accountMap := by rw [Z_ok_state hz]; rfl
  have hstack' := (Z_ok_stack hz).trans hstack
  by_cases hg : CallFamilyGas.gate kind mid value
  · obtain ⟨cr,w,g,ss,z,out,hchild,hw⟩ := CallWorld.step_family_world kind fuel cost
      requested target value inOff inLen outOff outLen rest hstack' hg hs
    have hf := CallFunding.family_funded kind fuel .empty mid requested target value inOff inLen hg.1
    have hb := ht hf hchild
    rw [hw,← hm]
    exact hb
  · have hw := (CallWorld.step_family_denied_world kind fuel cost
      requested target value inOff inLen outOff outLen rest hstack' hg hs).2
    rw [hw,hm]

theorem creation_step (kind : CreationGas.Variant) (fuel : Nat) (hl : LambdaBound fuel)
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat} {arg : Option (UInt256 × Nat)}
    (value off len salt : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = CreationGas.stack kind value off len salt rest)
    (hz : Z vj (CreationGas.opcode kind) pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (CreationGas.opcode kind,arg) mid post) :
    worldFunds post.accountMap ≤ worldFunds pre.accountMap := by
  have hm : mid.accountMap = pre.accountMap := by rw [Z_ok_state hz]; rfl
  have hstack' := (Z_ok_stack hz).trans hstack
  by_cases hn : CreationGas.nonceAllowed mid
  · by_cases hg : CreationGas.gate mid value off len
    · rcases CreationWorld.step_world kind fuel cost value off len salt rest hstack' hn hg hs with hchild | herr
      · obtain ⟨addr,cr,w,g,ss,z,out,hchild,hw⟩ := hchild
        have hf : value.toNat ≤ worldBalance (CreationFunding.nonceWorld mid) mid.executionEnv.codeOwner := by
          rw [CreationFunding.nonce_balance]
          exact CallFunding.gate_to_nat _ _ _ hg.1
        have hnonce := CreationFunding.nonce_positive mid hn
        have hb := hl hf hnonce hchild
        rw [hw,← hm]
        exact hb.trans_eq (CreationFunding.nonce_preserves mid)
      · obtain ⟨err,_,hw⟩ := herr
        rw [hw]
        exact Nat.zero_le _
    · have hw := (CreationGas.step_denied kind fuel cost value off len salt rest hstack' (Or.inr hg) hs).2.2.1
      rw [hw,hm]
  · have hw := (CreationGas.step_denied kind fuel cost value off len salt rest hstack' (Or.inl hn) hs).2.2.1
    rw [hw,hm]

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


theorem step_of_children (fuel : Nat)
    (ht : ∀ n, n < fuel → ThetaBound n) (hl : ∀ n, n < fuel → LambdaBound n) : StepBound fuel := by
  intro vj op arg pre mid post cost hz hs
  cases fuel with
  | zero => cases hs
  | succ fuel =>
    by_cases ho : OrdinaryGas.Ordinary op
    · exact OrdinaryFunding.accepted_step_nonincrease ho hz hs
    have hsize := ReturnedGas.accepted_stack hz
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


theorem x_zero : XBound 0 := by intro vj pre post out h; cases h
theorem xi_zero : XiBound 0 := by
  intro created genesis blocks world original gas substate env created' world' gas' substate' out h
  cases h
theorem theta_zero : ThetaBound 0 := by
  intro hashes created genesis header blocks world original substate source origin target code gas price value apparent
    data depth permission created' world' gas' substate' success out hfund h
  cases h
theorem lambda_zero : LambdaBound 0 := by
  intro hashes created genesis header blocks world original substate source origin gas price value depth init salt permission
    addr created' world' gas' substate' success out hfund hnonce h
  cases h

/-- Strong induction derives child conservation from their real smaller fuel. -/
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

theorem x_funds (fuel : Nat) : XBound fuel := (all_bounds fuel).1
theorem xi_funds (fuel : Nat) : XiBound fuel := (all_bounds fuel).2.1
theorem theta_funds (fuel : Nat) : ThetaBound fuel := (all_bounds fuel).2.2.1
theorem lambda_funds (fuel : Nat) : LambdaBound fuel := (all_bounds fuel).2.2.2.1
theorem step_funds (fuel : Nat) : StepBound fuel := (all_bounds fuel).2.2.2.2

#print axioms all_bounds
#print axioms x_funds
#print axioms xi_funds
#print axioms theta_funds
#print axioms lambda_funds
#print axioms step_funds

end Eip8282.Audit.Integrator.ExecutionFunding
