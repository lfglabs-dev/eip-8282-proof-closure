import Eip8282.Audit.EvmRunner

/-!
The real message-call boundary in the pinned EVMYulLean semantics is `Θ`.
`Ξ` alone neither transfers call value nor returns a world on REVERT.
This module exposes Θ's input world, its exact value-transfer order, and its
failure results. Interpreter OutOfFuel remains an error, not an EVM failure.
These are semantic transport lemmas, not protocol authorization, sufficient
funds, transaction-fee accounting, or a proof of any predeploy path.
-/
namespace Eip8282.Audit.Integrator.MessageCall

open EvmYul EvmYul.EVM

/-- Inputs to the code branch of Θ. Original transaction state `originalWorld`
is distinct from the pre-call journal `world`. Actual and apparent value are
separate inputs in Θ; ordinary calls must bind them at the consumer. -/
structure Context where
  fuel : Nat
  created : Std.TreeSet AccountAddress compare
  genesis : BlockHeader
  blocks : ProcessedBlocks
  world : AccountMap .EVM
  originalWorld : AccountMap .EVM
  substate : Substate
  caller : AccountAddress
  origin : AccountAddress
  target : AccountAddress
  code : ByteArray
  gas : UInt256
  gasPrice : UInt256
  value : UInt256
  apparentValue : UInt256
  calldata : ByteArray
  depth : Nat
  header : BlockHeader
  permission : Bool
  blobHashes : List ByteArray

/-- First credit the recipient, then debit the sender, exactly as Θ does.
In particular, the second lookup uses the already credited map. -/
def Context.entryWorld (c : Context) : AccountMap .EVM :=
  let credited := match c.world.get? c.target with
    | none => if c.value != UInt256.ofNat 0 then
        c.world.insert c.target { (default : Account .EVM) with balance := c.value }
      else c.world
    | some acc => c.world.insert c.target { acc with balance := acc.balance + c.value }
  match credited.get? c.caller with
  | none => credited
  | some acc => credited.insert c.caller { acc with balance := acc.balance - c.value }

def Context.environment (c : Context) : ExecutionEnv .EVM :=
  { codeOwner := c.target, sender := c.origin, source := c.caller,
    weiValue := c.apparentValue, calldata := c.calldata, code := c.code,
    gasPrice := c.gasPrice.toNat, header := c.header, depth := c.depth,
    perm := c.permission, blobVersionedHashes := c.blobHashes }

def Context.execution (c : Context) : EvmRunner.RunResult :=
  Ξ c.fuel c.created c.genesis c.blocks c.entryWorld c.originalWorld
    c.gas c.substate c.environment

def Context.result (c : Context) :=
  Θ (c.fuel + 1) c.blobHashes c.created c.genesis c.blocks c.world
    c.originalWorld c.substate c.caller c.origin c.target (.Code c.code)
    c.gas c.gasPrice c.value c.apparentValue c.calldata c.depth c.header c.permission

/-- Exact Θ settlement, including the upstream empty-world fallback on success.
This fallback is kept visible rather than claiming unconditional world identity
between successful Ξ and successful Θ. -/
def Context.settle (c : Context) (res : EvmRunner.RunResult) :
    Except ExecutionException
      (Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray) :=
  match res with
  | .error e => if e == ExecutionException.OutOfFuel then .error .OutOfFuel
      else .ok (c.created, c.world, UInt256.ofNat 0, c.substate, false, ByteArray.empty)
  | .ok (.revert gas out) =>
      .ok (c.created, c.world, gas, c.substate, false, out)
  | .ok (.success (created, world, gas, substate) out) =>
      .ok (created, if world == ∅ then c.world else world, gas,
        if world == ∅ then c.substate else substate, true, out)

theorem result_eq_settle (c : Context) : c.result = c.settle c.execution := by
  unfold Context.result Θ
  change (do
    let (created, success, world, gas, substate, out) ←
      match c.execution with
      | .error e =>
          if e == ExecutionException.OutOfFuel then
            Except.error ExecutionException.OutOfFuel
          else
            Except.ok (c.created, false, c.world, UInt256.ofNat 0, c.substate, ByteArray.empty)
      | .ok (.revert gas out) => pure (c.created, false, c.world, gas, c.substate, out)
      | .ok (.success (created, world, gas, substate) out) =>
          pure (created, true, world, gas, substate, out)
    pure (created, if world == ∅ then c.world else world, gas,
      if world == ∅ then c.substate else substate, success, out)) = _
  cases h : c.execution with
  | error e =>
    by_cases he : (e == ExecutionException.OutOfFuel) = true
    · simp [Context.settle, h, he]
    · simp [Context.settle, h, he]
  | ok res =>
    cases res with
    | revert gas out =>
      simp only [Context.settle, h, Bind.bind, Except.bind, pure, Except.pure]
      split <;> rfl
    | success post out =>
      rcases post with ⟨created, world, gas, substate⟩
      rfl

theorem revert_restores_world (c : Context) (gas : UInt256) (out : ByteArray)
    (h : c.execution = .ok (.revert gas out)) :
    c.result = .ok (c.created, c.world, gas, c.substate, false, out) := by
  rw [result_eq_settle, h]
  rfl

theorem exceptional_halt_restores_world (c : Context) (e : ExecutionException)
    (h : c.execution = .error e) (hf : (e == ExecutionException.OutOfFuel) = false) :
    c.result = .ok (c.created, c.world, UInt256.ofNat 0, c.substate, false,
      ByteArray.empty) := by
  rw [result_eq_settle, h]
  simp [Context.settle, hf]

theorem evaluation_exhaustion_is_error (c : Context)
    (h : c.execution = .error .OutOfFuel) : c.result = .error .OutOfFuel := by
  rw [result_eq_settle, h]
  rfl

theorem success_commits_world (c : Context)
    (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (substate : Substate) (out : ByteArray)
    (h : c.execution = .ok (.success (created, world, gas, substate) out))
    (hne : (world == ∅) = false) :
    c.result = .ok (created, world, gas, substate, true, out) := by
  rw [result_eq_settle, h]
  simp [Context.settle, hne]

/-- Every returned failure rolls back the complete journal, without requiring
the consumer to identify which instruction or exceptional halt caused it. -/
theorem failure_restores_journal (c : Context)
    (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (substate : Substate) (out : ByteArray)
    (h : c.result = .ok (created, world, gas, substate, false, out)) :
    world = c.world ∧ substate = c.substate ∧ created = c.created := by
  rw [result_eq_settle] at h
  cases he : c.execution with
  | error err =>
      by_cases hf : (err == ExecutionException.OutOfFuel) = true
      · simp [Context.settle, he, hf] at h
      · simp [Context.settle, he, hf] at h
        obtain ⟨hc, hw, _, hs, _⟩ := h
        exact ⟨hw.symm, hs.symm, hc.symm⟩
  | ok result =>
      cases result with
      | revert g o =>
          simp only [Context.settle, he, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨hc, hw, _, hs, _, _⟩ := h
          exact ⟨hw.symm, hs.symm, hc.symm⟩
      | success post o =>
          rcases post with ⟨cs, ws, gs, ss⟩
          simp [Context.settle, he] at h

#print axioms failure_restores_journal
#print axioms result_eq_settle
#print axioms revert_restores_world
#print axioms exceptional_halt_restores_world
#print axioms evaluation_exhaustion_is_error
#print axioms success_commits_world

end Eip8282.Audit.Integrator.MessageCall
