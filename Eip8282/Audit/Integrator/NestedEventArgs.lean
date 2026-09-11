import Eip8282.Audit.Integrator.WrapperEventDebit

/-!
# Exact requests and selected recursive invocations

The request evaluator below is a nonrecursive abbreviation for the pinned
mutual evaluator. Child selection inspects only its dispatch inputs and gates;
it does not evaluate a child, select by its result, or supply a gas bound.
-/
namespace Eip8282.Audit.Integrator.NestedEvents
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

abbrev Created := Std.TreeSet AccountAddress compare
abbrev World := AccountMap .EVM
abbrev XResult := Except ExecutionException (ExecutionResult EVM.State)
abbrev XiResult := WrapperEventDebit.XiResult
abbrev ThetaResult := Except ExecutionException
  (Created × World × UInt256 × Substate × Bool × ByteArray)
abbrev LambdaResult := CreationOutcome.ChildResult
abbrev StepResult := Except ExecutionException EVM.State

structure XiArgs where
  created : Created
  genesis : BlockHeader
  blocks : ProcessedBlocks
  world : World
  original : World
  gas : UInt256
  substate : Substate
  env : ExecutionEnv .EVM

structure ThetaArgs where
  hashes : List ByteArray
  created : Created
  genesis : BlockHeader
  blocks : ProcessedBlocks
  world : World
  original : World
  substate : Substate
  source : AccountAddress
  origin : AccountAddress
  target : AccountAddress
  code : ToExecute .EVM
  gas : UInt256
  price : UInt256
  value : UInt256
  apparent : UInt256
  data : ByteArray
  depth : Nat
  header : BlockHeader
  permission : Bool

structure LambdaArgs where
  hashes : List ByteArray
  created : Created
  genesis : BlockHeader
  blocks : ProcessedBlocks
  world : World
  original : World
  substate : Substate
  source : AccountAddress
  origin : AccountAddress
  gas : UInt256
  price : UInt256
  value : UInt256
  init : ByteArray
  depth : UInt256
  salt : Option ByteArray
  header : BlockHeader
  permission : Bool

/-- The pre-Z state pays memory and opcode costs; the actual step receives mid. -/
structure StepArgs where
  vj : Array UInt256
  pre : EVM.State
  mid : EVM.State
  cost : Nat
  op : Operation .EVM
  arg : Option (UInt256 × Nat)
  guard : Z vj op pre = .ok (mid,cost)

inductive Request where
  | x (fuel : Nat) (vj : Array UInt256) (pre : EVM.State)
  | xi (fuel : Nat) (a : XiArgs)
  | theta (fuel : Nat) (a : ThetaArgs)
  | lambda (fuel : Nat) (a : LambdaArgs)
  | step (fuel : Nat) (a : StepArgs)

def Request.Outcome : Request → Type
  | .x .. => XResult
  | .xi .. => XiResult
  | .theta .. => ThetaResult
  | .lambda .. => LambdaResult
  | .step .. => StepResult

/-- No recursive definition: each branch is the original evaluator call. -/
def Request.eval (q : Request) : q.Outcome :=
  match q with
  | .x n vj pre => X n vj pre
  | .xi n a => Ξ n a.created a.genesis a.blocks a.world a.original a.gas a.substate a.env
  | .theta n a => Θ n a.hashes a.created a.genesis a.blocks a.world a.original a.substate
      a.source a.origin a.target a.code a.gas a.price a.value a.apparent a.data a.depth a.header a.permission
  | .lambda n a => Lambda n a.hashes a.created a.genesis a.blocks a.world a.original a.substate
      a.source a.origin a.gas a.price a.value a.init a.depth a.salt a.header a.permission
  | .step n a => EVM.step n a.cost (some (a.op,a.arg)) a.mid

def Request.fuel : Request → Nat
  | .x n .. | .xi n .. | .theta n .. | .lambda n .. | .step n .. => n

def Request.gas : Request → Nat
  | .x _ _ pre => pre.gasAvailable.toNat
  | .xi _ a => a.gas.toNat
  | .theta _ a => a.gas.toNat
  | .lambda _ a => a.gas.toNat
  | .step _ a => a.pre.gasAvailable.toNat

def Request.residual (q : Request) : q.Outcome → Nat :=
  match q with
  | .x .. => FrameEvents.residual
  | .xi .. => WrapperEventDebit.xiResidual
  | .theta .. => RecursiveEventDebit.thetaResidual
  | .lambda .. => RecursiveEventDebit.lambdaResidual
  | .step .. => RecursiveEventDebit.stepResidual

def XiArgs.entry (a : XiArgs) : EVM.State :=
  WrapperEventDebit.entry a.created a.genesis a.blocks a.world a.original a.gas a.substate a.env

def XiArgs.jumps (a : XiArgs) : Array UInt256 := D_J a.env.code ⟨0⟩

/-- The context's fuel is the inner Ξ fuel, not the outer Θ fuel. -/
def ThetaArgs.context (a : ThetaArgs) (n : Nat) (bytes : ByteArray) : MessageCall.Context :=
  { fuel := n, created := a.created, genesis := a.genesis, blocks := a.blocks,
    world := a.world, originalWorld := a.original, substate := a.substate,
    caller := a.source, origin := a.origin, target := a.target, code := bytes,
    gas := a.gas, gasPrice := a.price, value := a.value, apparentValue := a.apparent,
    calldata := a.data, depth := a.depth, header := a.header,
    permission := a.permission, blobHashes := a.hashes }

def ThetaArgs.xiArgs (a : ThetaArgs) (bytes : ByteArray) : XiArgs :=
  let c := a.context 0 bytes
  { created := c.created, genesis := c.genesis, blocks := c.blocks,
    world := c.entryWorld, original := c.originalWorld, gas := c.gas,
    substate := c.substate, env := c.environment }

def LambdaArgs.context (a : LambdaArgs) (n : Nat) : CreationSettlement.Context :=
  { fuel := n, blobHashes := a.hashes, created := a.created, genesis := a.genesis,
    blocks := a.blocks, world := a.world, originalWorld := a.original,
    substate := a.substate, sender := a.source, origin := a.origin, gas := a.gas,
    gasPrice := a.price, value := a.value, init := a.init, depth := a.depth,
    salt := a.salt, header := a.header, permission := a.permission }

def LambdaArgs.preimage (a : LambdaArgs) : Option ByteArray := (a.context 0).preimage

def LambdaArgs.xiArgs (a : LambdaArgs) (preimage : ByteArray) : XiArgs :=
  let c := a.context 0
  let addr := CreationSettlement.address preimage
  { created := c.selectedCreated addr, genesis := c.genesis, blocks := c.blocks,
    world := c.entryWorld addr, original := c.originalWorld, gas := c.gas,
    substate := c.accessed addr, env := c.environment addr }

/-- Literal raw helper child arguments, including target/recipient separation. -/
def callArgs (hashes : List ByteArray)
    (requested source recipient target value apparent inOff inLen : UInt256)
    (permission : Bool) (pre : EVM.State) : ThetaArgs :=
  { hashes := hashes, created := pre.createdAccounts, genesis := pre.genesisBlockHeader,
    blocks := pre.blocks, world := pre.accountMap, original := pre.σ₀,
    substate := (pre.addAccessedAccount (AccountAddress.ofUInt256 target)).substate,
    source := AccountAddress.ofUInt256 source, origin := pre.executionEnv.sender,
    target := AccountAddress.ofUInt256 recipient,
    code := toExecute .EVM pre.accountMap (AccountAddress.ofUInt256 target),
    gas := UInt256.ofNat (Ccallgas (AccountAddress.ofUInt256 target)
      (AccountAddress.ofUInt256 recipient) value requested pre.accountMap pre.toMachineState pre.substate),
    price := UInt256.ofNat pre.executionEnv.gasPrice, value := value, apparent := apparent,
    data := pre.memory.readWithPadding inOff.toNat inLen.toNat,
    depth := pre.executionEnv.depth+1, header := pre.executionEnv.header, permission := permission }

def dispatchCallArgs (pre : EVM.State) (requested target value inOff inLen : UInt256) : ThetaArgs :=
  callArgs pre.executionEnv.blobVersionedHashes requested
    (UInt256.ofNat pre.executionEnv.codeOwner) target target value value inOff inLen
    pre.executionEnv.perm (CallDispatchGas.entered pre)

def familyArgs (kind : CallFamilyGas.Variant) (pre : EVM.State)
    (requested target value inOff inLen : UInt256) : ThetaArgs :=
  callArgs pre.executionEnv.blobVersionedHashes requested (CallFamilyGas.source kind pre)
    (CallFamilyGas.recipient kind pre target) target (CallFamilyGas.transfer kind value)
    (CallFamilyGas.apparent kind pre value) inOff inLen (CallFamilyGas.permission kind pre)
    (CallDispatchGas.entered pre)

def creationArgs (kind : CreationGas.Variant) (cost : Nat) (pre : EVM.State)
    (value off len salt : UInt256) : LambdaArgs :=
  let charged := stepPre cost pre
  let owner := charged.executionEnv.codeOwner
  let account := charged.accountMap.get? owner |>.getD default
  { hashes := charged.executionEnv.blobVersionedHashes, created := charged.createdAccounts,
    genesis := charged.genesisBlockHeader, blocks := charged.blocks,
    world := charged.accountMap.insert owner {account with nonce := account.nonce+⟨1⟩},
    original := charged.σ₀, substate := charged.substate, source := owner,
    origin := charged.executionEnv.sender, gas := UInt256.ofNat (L charged.gasAvailable.toNat),
    price := UInt256.ofNat charged.executionEnv.gasPrice, value := value,
    init := CreationGas.init charged off len, depth := UInt256.ofNat (charged.executionEnv.depth+1),
    salt := CreationGas.saltBytes kind salt, header := charged.executionEnv.header,
    permission := charged.executionEnv.perm }

theorem callArgs_eval (n : Nat) (hashes : List ByteArray)
    (requested source recipient target value apparent inOff inLen : UInt256)
    (permission : Bool) (pre : EVM.State) :
    (Request.theta n (callArgs hashes requested source recipient target value apparent inOff inLen permission pre)).eval =
      CallGasAccounting.child n hashes requested source recipient target value apparent inOff inLen permission pre := rfl

theorem dispatchCallArgs_eval (n : Nat) (pre : EVM.State)
    (requested target value inOff inLen : UInt256) :
    (Request.theta n (dispatchCallArgs pre requested target value inOff inLen)).eval =
      CallGasAccounting.child n pre.executionEnv.blobVersionedHashes requested
        (UInt256.ofNat pre.executionEnv.codeOwner) target target value value inOff inLen
        pre.executionEnv.perm (CallDispatchGas.entered pre) := rfl

theorem familyArgs_eval (kind : CallFamilyGas.Variant) (n : Nat) (pre : EVM.State)
    (requested target value inOff inLen : UInt256) :
    (Request.theta n (familyArgs kind pre requested target value inOff inLen)).eval =
      CallFamilyGas.childResult kind n pre requested target value inOff inLen := rfl

theorem creationArgs_eval (kind : CreationGas.Variant) (n cost : Nat) (pre : EVM.State)
    (value off len salt : UInt256) :
    (Request.lambda n (creationArgs kind cost pre value off len salt)).eval =
      CreationGas.child kind n cost pre value off len salt := rfl

theorem thetaArgs_execution (a : ThetaArgs) (n : Nat) (bytes : ByteArray) :
    (Request.xi n (a.xiArgs bytes)).eval = (a.context n bytes).execution := rfl

theorem thetaArgs_result (a : ThetaArgs) (n : Nat) (bytes : ByteArray)
    (hc : a.code = .Code bytes) :
    (Request.theta (n+1) a).eval = (a.context n bytes).result := by
  change Θ _ _ _ _ _ _ _ _ _ _ _ a.code _ _ _ _ _ _ _ _ = _
  rw [hc]
  rfl

theorem lambdaArgs_execution (a : LambdaArgs) (n : Nat) (bytes : ByteArray) :
    (Request.xi n (a.xiArgs bytes)).eval =
      (a.context n).execution (CreationSettlement.address bytes) := rfl

theorem lambdaArgs_result (a : LambdaArgs) (n : Nat) :
    (Request.lambda (n+1) a).eval = (a.context n).result := rfl

/-- Total stack operands are used only after Z has accepted their arity.
There is no malformed-stack fallback branch that could erase a real child. -/
def operand (a : StepArgs) (i : Nat) : UInt256 := a.mid.stack.getD i ⟨0⟩

local instance (s : EVM.State) (v : UInt256) : Decidable (CallOutcome.Gate s v) := by
  unfold CallOutcome.Gate
  infer_instance
local instance (k : CallFamilyGas.Variant) (s : EVM.State) (v : UInt256) :
    Decidable (CallFamilyGas.gate k s v) := by
  unfold CallFamilyGas.gate
  infer_instance
local instance (s : EVM.State) : Decidable (CreationGas.nonceAllowed s) := by
  unfold CreationGas.nonceAllowed
  infer_instance
local instance (s : EVM.State) (v off len : UInt256) : Decidable (CreationGas.gate s v off len) := by
  unfold CreationGas.gate
  infer_instance

/-- Select just the literal recursive invocation. This function never runs it. -/
def selectedChild (n : Nat) (a : StepArgs) : Option Request :=
  match n with
  | 0 => none
  | m+1 =>
    match a.op with
    | .CALL => match m with
      | 0 => none
      | f+1 => if CallOutcome.Gate a.mid (operand a 2) then
          some (.theta f (dispatchCallArgs a.mid (operand a 0) (operand a 1)
            (operand a 2) (operand a 3) (operand a 4))) else none
    | .CALLCODE => match m with
      | 0 => none
      | f+1 => if CallFamilyGas.gate .callcode a.mid (operand a 2) then
          some (.theta f (familyArgs .callcode a.mid (operand a 0) (operand a 1)
            (operand a 2) (operand a 3) (operand a 4))) else none
    | .DELEGATECALL => match m with
      | 0 => none
      | f+1 => if CallFamilyGas.gate .delegatecall a.mid ⟨0⟩ then
          some (.theta f (familyArgs .delegatecall a.mid (operand a 0) (operand a 1)
            ⟨0⟩ (operand a 2) (operand a 3))) else none
    | .STATICCALL => match m with
      | 0 => none
      | f+1 => if CallFamilyGas.gate .staticcall a.mid ⟨0⟩ then
          some (.theta f (familyArgs .staticcall a.mid (operand a 0) (operand a 1)
            ⟨0⟩ (operand a 2) (operand a 3))) else none
    | .CREATE => if CreationGas.nonceAllowed a.mid ∧
        CreationGas.gate a.mid (operand a 0) (operand a 1) (operand a 2) then
          some (.lambda m (creationArgs .create a.cost a.mid (operand a 0)
            (operand a 1) (operand a 2) ⟨0⟩)) else none
    | .CREATE2 => if CreationGas.nonceAllowed a.mid ∧
        CreationGas.gate a.mid (operand a 0) (operand a 1) (operand a 2) then
          some (.lambda m (creationArgs .create2 a.cost a.mid (operand a 0)
            (operand a 1) (operand a 2) (operand a 3))) else none
    | _ => none

def StepChild (n : Nat) (a : StepArgs) (child : Option Request) : Prop :=
  selectedChild n a = child

theorem stepChild_total (n : Nat) (a : StepArgs) : ∃ child, StepChild n a child :=
  ⟨selectedChild n a, rfl⟩

theorem stepChild_unique {n : Nat} {a : StepArgs} {c₁ c₂ : Option Request}
    (h₁ : StepChild n a c₁) (h₂ : StepChild n a c₂) : c₁ = c₂ := h₁.symm.trans h₂

theorem stepChild_fuel {n : Nat} {a : StepArgs} {q : Request}
    (h : StepChild n a (some q)) : q.fuel < n := by
  unfold StepChild selectedChild at h
  split at h
  · cases h
  · split at h
    all_goals repeat first | split at h | (cases h)
    all_goals simp_all [Request.fuel] <;> omega

/-- Z acceptance supplies every operand used in actual recursive dispatch. -/
theorem accepted_arity (a : StepArgs) :
    (δ a.op).getD 0 ≤ a.mid.stack.length := by
  rw [Z_ok_stack a.guard]
  exact ReturnedGas.accepted_stack a.guard

/-- Canonical actual stack decompositions, so operand defaults cannot hide a child. -/
theorem stack3_shape (s : Stack UInt256) (h : 3 ≤ s.length) :
    s = s.getD 0 ⟨0⟩ :: s.getD 1 ⟨0⟩ :: s.getD 2 ⟨0⟩ :: s.drop 3 := by
  rcases s with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, rest⟩⟩⟩ <;> simp_all

theorem stack4_shape (s : Stack UInt256) (h : 4 ≤ s.length) :
    s = s.getD 0 ⟨0⟩ :: s.getD 1 ⟨0⟩ :: s.getD 2 ⟨0⟩ :: s.getD 3 ⟨0⟩ :: s.drop 4 := by
  rcases s with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, rest⟩⟩⟩⟩ <;> simp_all

theorem stack6_shape (s : Stack UInt256) (h : 6 ≤ s.length) :
    s = s.getD 0 ⟨0⟩ :: s.getD 1 ⟨0⟩ :: s.getD 2 ⟨0⟩ :: s.getD 3 ⟨0⟩ ::
      s.getD 4 ⟨0⟩ :: s.getD 5 ⟨0⟩ :: s.drop 6 := by
  rcases s with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, rest⟩⟩⟩⟩⟩⟩ <;> simp_all

theorem stack7_shape (s : Stack UInt256) (h : 7 ≤ s.length) :
    s = s.getD 0 ⟨0⟩ :: s.getD 1 ⟨0⟩ :: s.getD 2 ⟨0⟩ :: s.getD 3 ⟨0⟩ ::
      s.getD 4 ⟨0⟩ :: s.getD 5 ⟨0⟩ :: s.getD 6 ⟨0⟩ :: s.drop 7 := by
  rcases s with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, rest⟩⟩⟩⟩⟩⟩⟩ <;> simp_all

theorem call_stack (a : StepArgs) (hop : a.op = .CALL) :
    a.mid.stack = operand a 0 :: operand a 1 :: operand a 2 :: operand a 3 ::
      operand a 4 :: operand a 5 :: operand a 6 :: a.mid.stack.drop 7 := by
  exact stack7_shape _ (by simpa only [hop, δ, Option.getD_some] using accepted_arity a)

def familyValue (k : CallFamilyGas.Variant) (a : StepArgs) : UInt256 :=
  match k with | .callcode => operand a 2 | _ => ⟨0⟩
def familyInOff (k : CallFamilyGas.Variant) (a : StepArgs) : UInt256 :=
  match k with | .callcode => operand a 3 | _ => operand a 2
def familyInLen (k : CallFamilyGas.Variant) (a : StepArgs) : UInt256 :=
  match k with | .callcode => operand a 4 | _ => operand a 3
def familyOutOff (k : CallFamilyGas.Variant) (a : StepArgs) : UInt256 :=
  match k with | .callcode => operand a 5 | _ => operand a 4
def familyOutLen (k : CallFamilyGas.Variant) (a : StepArgs) : UInt256 :=
  match k with | .callcode => operand a 6 | _ => operand a 5
def familyRest (k : CallFamilyGas.Variant) (a : StepArgs) : Stack UInt256 :=
  a.mid.stack.drop (match k with | .callcode => 7 | _ => 6)

theorem family_stack (k : CallFamilyGas.Variant) (a : StepArgs)
    (hop : a.op = CallFamilyGas.opcode k) :
    a.mid.stack = CallFamilyGas.stack k (operand a 0) (operand a 1) (familyValue k a)
      (familyInOff k a) (familyInLen k a) (familyOutOff k a) (familyOutLen k a) (familyRest k a) := by
  have h := accepted_arity a
  rw [hop] at h
  cases k with
  | callcode => exact stack7_shape _ (by simpa only [CallFamilyGas.opcode, δ, Option.getD_some] using h)
  | delegatecall => exact stack6_shape _ (by simpa only [CallFamilyGas.opcode, δ, Option.getD_some] using h)
  | staticcall => exact stack6_shape _ (by simpa only [CallFamilyGas.opcode, δ, Option.getD_some] using h)

def creationSalt (k : CreationGas.Variant) (a : StepArgs) : UInt256 :=
  match k with | .create => ⟨0⟩ | .create2 => operand a 3
def creationRest (k : CreationGas.Variant) (a : StepArgs) : Stack UInt256 :=
  a.mid.stack.drop (match k with | .create => 3 | .create2 => 4)

theorem creation_stack (k : CreationGas.Variant) (a : StepArgs)
    (hop : a.op = CreationGas.opcode k) :
    a.mid.stack = CreationGas.stack k (operand a 0) (operand a 1) (operand a 2)
      (creationSalt k a) (creationRest k a) := by
  have h := accepted_arity a
  rw [hop] at h
  cases k with
  | create => exact stack3_shape _ (by simpa only [CreationGas.opcode, δ, Option.getD_some] using h)
  | create2 => exact stack4_shape _ (by simpa only [CreationGas.opcode, δ, Option.getD_some] using h)

theorem selectedChild_call (n : Nat) (a : StepArgs) (hop : a.op = .CALL) :
    selectedChild (n+2) a =
      if CallOutcome.Gate a.mid (operand a 2) then
        some (.theta n (dispatchCallArgs a.mid (operand a 0) (operand a 1)
          (operand a 2) (operand a 3) (operand a 4))) else none := by
  simp only [selectedChild, hop]

theorem selectedChild_family (k : CallFamilyGas.Variant) (n : Nat) (a : StepArgs)
    (hop : a.op = CallFamilyGas.opcode k) :
    selectedChild (n+2) a =
      if CallFamilyGas.gate k a.mid (familyValue k a) then
        some (.theta n (familyArgs k a.mid (operand a 0) (operand a 1)
          (familyValue k a) (familyInOff k a) (familyInLen k a))) else none := by
  cases k <;> simp only [selectedChild, hop, CallFamilyGas.opcode, familyValue, familyInOff, familyInLen]

theorem selectedChild_creation (k : CreationGas.Variant) (n : Nat) (a : StepArgs)
    (hop : a.op = CreationGas.opcode k) :
    selectedChild (n+1) a =
      if CreationGas.nonceAllowed a.mid ∧ CreationGas.gate a.mid (operand a 0) (operand a 1) (operand a 2) then
        some (.lambda n (creationArgs k a.cost a.mid (operand a 0) (operand a 1)
          (operand a 2) (creationSalt k a))) else none := by
  cases k <;> simp only [selectedChild, hop, CreationGas.opcode, creationSalt]

/-- These literal all-outcome dispatcher equations use the canonical actual
stack. They do not require StepOk or a successful final CREATE guard. -/
theorem call_step_equation (n : Nat) (a : StepArgs) (hop : a.op = .CALL) :
    (Request.step (n+2) a).eval = CallOutcome.finish (a.mid.stack.drop 7)
      (CallDispatchGas.helper n a.cost a.mid (operand a 0) (operand a 1) (operand a 2)
        (operand a 3) (operand a 4) (operand a 5) (operand a 6)) := by
  change EVM.step (n+2) a.cost (some (a.op,a.arg)) a.mid = _
  rw [hop]
  exact CallOutcome.step_call_equation n a.cost a.mid a.arg _ _ _ _ _ _ _ _ (call_stack a hop)

theorem family_step_equation (k : CallFamilyGas.Variant) (n : Nat) (a : StepArgs)
    (hop : a.op = CallFamilyGas.opcode k) :
    (Request.step (n+2) a).eval = CallOutcome.finish (familyRest k a)
      (CallFamilyGas.helper k n a.cost a.mid (operand a 0) (operand a 1) (familyValue k a)
        (familyInOff k a) (familyInLen k a) (familyOutOff k a) (familyOutLen k a)) := by
  change EVM.step (n+2) a.cost (some (a.op,a.arg)) a.mid = _
  rw [hop]
  exact CallOutcome.step_family_equation k n a.cost a.mid a.arg _ _ _ _ _ _ _ _ (family_stack k a hop)

theorem creation_step_admitted (k : CreationGas.Variant) (n : Nat) (a : StepArgs)
    (hop : a.op = CreationGas.opcode k) (hn : CreationGas.nonceAllowed a.mid)
    (hg : CreationGas.gate a.mid (operand a 0) (operand a 1) (operand a 2)) :
    (Request.step (n+1) a).eval =
      CreationOutcome.settle a.cost a.mid (operand a 0) (operand a 1) (operand a 2) (creationRest k a)
        (Request.lambda n (creationArgs k a.cost a.mid (operand a 0) (operand a 1)
          (operand a 2) (creationSalt k a))).eval := by
  change EVM.step (n+1) a.cost (some (a.op,a.arg)) a.mid = _
  rw [hop]
  exact CreationOutcome.admitted_equation k n a.cost a.mid a.arg _ _ _ _ _ (creation_stack k a hop) hn hg

theorem creation_step_denied (k : CreationGas.Variant) (n : Nat) (a : StepArgs)
    (hop : a.op = CreationGas.opcode k)
    (hg : ¬ CreationGas.nonceAllowed a.mid ∨
      ¬ CreationGas.gate a.mid (operand a 0) (operand a 1) (operand a 2)) :
    (Request.step (n+1) a).eval =
      CreationOutcome.finish a.cost a.mid (operand a 0) (operand a 1) (operand a 2) (creationRest k a)
        (0,stepPre a.cost a.mid,UInt256.ofNat (CreationGas.allowance a.cost a.mid),false,.empty) := by
  change EVM.step (n+1) a.cost (some (a.op,a.arg)) a.mid = _
  rw [hop]
  exact CreationOutcome.denied_equation k n a.cost a.mid a.arg _ _ _ _ _ (creation_stack k a hop) hg

#print axioms stepChild_total
#print axioms stepChild_unique
#print axioms stepChild_fuel
#print axioms accepted_arity
#print axioms callArgs_eval
#print axioms familyArgs_eval
#print axioms creationArgs_eval
#print axioms call_step_equation
#print axioms family_step_equation
#print axioms creation_step_admitted
#print axioms creation_step_denied
end Eip8282.Audit.Integrator.NestedEvents
