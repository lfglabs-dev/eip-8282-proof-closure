import Eip8282.Audit.Integrator.ActualAppendGas

/-!
# Gas debits of actual ordinary instructions

Ordinary excludes precisely the six recursive CALL/CREATE instructions. Raw
instruction semantics may read gas (GAS) but do not change its field. The actual
EVM dispatcher charges opcode cost, and accepted Z supplies every no-wrap fact.
-/
namespace Eip8282.Audit.Integrator.OrdinaryGas

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open SuccessInversion

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- All instructions except those which invoke child evaluators. -/
def Ordinary (op : Operation .EVM) : Prop :=
  op.isCall = false ∧ op.isCreate = false

instance (op : Operation .EVM) : Decidable (Ordinary op) :=
  inferInstanceAs (Decidable (op.isCall = false ∧ op.isCreate = false))

private theorem dup_gas (n : Nat) {pre post : EVM.State}
    (h : EvmYul.dup n pre = .ok post) : post.gasAvailable = pre.gasAvailable := by
  unfold EvmYul.dup at h
  dsimp only at h
  split at h
  · cases h; rfl
  · cases h

private theorem swap_gas (n : Nat) {pre post : EVM.State}
    (h : EvmYul.swap n pre = .ok post) : post.gasAvailable = pre.gasAvailable := by
  unfold EvmYul.swap at h
  dsimp only at h
  split at h
  · cases h; rfl
  · cases h

private theorem selfdestruct_gas {arg : Option (UInt256 × Nat)}
    {pre post : EVM.State} (h : EvmYul.step (τ := .EVM) .SELFDESTRUCT arg pre = .ok post) :
    post.gasAvailable = pre.gasAvailable := by
  obtain ⟨sh, pc, stk, ex⟩ := pre
  cases stk with
  | nil => cases h
  | cons dest stk =>
    change (if sh.createdAccounts.contains sh.executionEnv.codeOwner then
      Except.ok _ else Except.ok _) = Except.ok post at h
    split at h <;> cases h <;> rfl

/-- Raw opcode execution preserves the gas field, including GAS, which reads
that field to produce a stack value. Recursive operations are handled separately
by EVM.step and are not covered by this raw helper's application. -/
theorem raw_gas {op : Operation .EVM} (hop : Ordinary op) (hvalid : op ≠ .INVALID)
    {arg : Option (UInt256 × Nat)}
    {pre post : EVM.State} (h : EvmYul.step op arg pre = .ok post) :
    post.gasAvailable = pre.gasAvailable := by
  cases op <;> rename_i op <;> cases op
  all_goals first
    | exact False.elim (hvalid rfl)
    | (simp only [Ordinary, Operation.isCall, Operation.isCreate, Bool.true_eq_false, false_and, and_false] at hop; done)
    | exact ActualAppendGas.opcode_preserves_gas (by decide) h
    | exact selfdestruct_gas h
    | exact dup_gas _ h
    | exact swap_gas _ h
    | skip
  all_goals
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases arg with _ | ⟨v,n⟩
    all_goals rcases stk with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, tail⟩⟩⟩⟩⟩⟩
    all_goals first
      | (cases h <;> rfl)


/-- Exact dispatch identity for every nonrecursive opcode. Unlike the narrower
symbolic theorem, this includes GAS, all copy/log operations and SELFDESTRUCT. -/
theorem dispatch {op : Operation .EVM} (hop : Ordinary op) (fuel cost : Nat)
    (arg : Option (UInt256 × Nat)) (pre : EVM.State) :
    EVM.step (fuel+1) cost (some (op,arg)) pre =
      EvmYul.step op arg (stepPre cost pre) := by
  cases op <;> rename_i op <;> cases op
  all_goals first
    | rfl
    | (simp only [Ordinary, Operation.isCall, Operation.isCreate,
        Bool.true_eq_false, false_and, and_false] at hop)

/-- INVALID cannot pass the actual Z guard; no raw-opcode behavior is assumed. -/
theorem accepted_valid {vj : Array UInt256} {op : Operation .EVM}
    {pre mid : EVM.State} {cost : Nat} (hz : Z vj op pre = .ok (mid,cost)) :
    op ≠ .INVALID := by
  intro he
  subst op
  simp only [Z, Bind.bind, Except.bind, pure, Except.pure] at hz
  replace hz := elim_guard hz
  replace hz := elim_guard hz
  simp only [δ, ↓reduceIte] at hz
  cases hz

/-- Actual step gas settlement. Validity is derived from Z by the consumer. -/
theorem step_gas {op : Operation .EVM} (hop : Ordinary op) (hv : op ≠ .INVALID)
    {arg : Option (UInt256 × Nat)} {pre post : EVM.State} {fuel cost : Nat}
    (h : StepOk fuel cost (op,arg) pre post) :
    post.gasAvailable = pre.gasAvailable - UInt256.ofNat cost := by
  cases fuel with
  | zero => change Except.error ExecutionException.OutOfFuel = Except.ok post at h; cases h
  | succ fuel =>
    change EVM.step (fuel+1) cost (some (op,arg)) pre = .ok post at h
    rw [dispatch hop] at h
    exact raw_gas hop hv h

/-- Exact natural debit. Memory and opcode costs and all word-fit facts come
from actual accepted Z and actual execution, without a predicted post-state. -/
theorem accepted_step_debit {vj : Array UInt256} {op : Operation .EVM}
    (hop : Ordinary op) {arg : Option (UInt256 × Nat)}
    {pre mid post : EVM.State} {fuel cost : Nat}
    (hz : Z vj op pre = .ok (mid,cost)) (hs : StepOk fuel cost (op,arg) mid post) :
    post.gasAvailable.toNat + memoryExpansionCost pre op + cost = pre.gasAvailable.toNat := by
  obtain ⟨hm, he, hc, _⟩ := ActualAppendGas.accepted_gas hz
  have hp := step_gas hop (accepted_valid hz) hs
  have hn : post.gasAvailable.toNat = mid.gasAvailable.toNat - cost := by
    rw [hp]
    exact toNat_sub_ofNat hc
  omega

theorem accepted_step_nonincrease {vj : Array UInt256} {op : Operation .EVM}
    (hop : Ordinary op) {arg : Option (UInt256 × Nat)}
    {pre mid post : EVM.State} {fuel cost : Nat}
    (hz : Z vj op pre = .ok (mid,cost)) (hs : StepOk fuel cost (op,arg) mid post) :
    post.gasAvailable.toNat ≤ pre.gasAvailable.toNat := by
  have hd := accepted_step_debit hop hz hs
  omega

/-- Ordinary covers exactly the complement of the six child-frame opcodes. -/
theorem ordinary_iff (op : Operation .EVM) : Ordinary op ↔
    op ≠ .CALL ∧ op ≠ .CALLCODE ∧ op ≠ .DELEGATECALL ∧ op ≠ .STATICCALL ∧
    op ≠ .CREATE ∧ op ≠ .CREATE2 := by
  cases op <;> rename_i op <;> cases op <;> decide

/-- Actual nonhalting ordinary steps pay their labelled opcode charge. -/
theorem xstep_debit {vj : Array UInt256} {fuel cost : Nat} {pre post : EVM.State}
    (hop : Ordinary (decodeAt pre).1) (h : XStepAt vj fuel cost pre post) :
    post.gasAvailable.toNat + cost ≤ pre.gasAvailable.toNat := by
  obtain ⟨mid, hz, hs, _⟩ := h
  have hd := accepted_step_debit hop hz hs
  omega

/-- Syntactic support of the existing evaluator trace, not another execution model. -/
def Supported (trace : List Labelled) : Prop := ∀ step ∈ trace, Ordinary step.2.2.1

/-- Debit of any actual ordinary prefix, irrespective of whether later execution
succeeds, reverts, or raises an exception. Charges belong to the real XRuns labels. -/
theorem xruns_debit {vj : Array UInt256} {fuel rest : Nat} {pre post : EVM.State}
    {trace : List Labelled} (h : XRuns vj fuel pre trace rest post) (hop : Supported trace) :
    post.gasAvailable.toNat + ActualAppendGas.opcodeCharges trace ≤ pre.gasAvailable.toNat := by
  induction h with
  | refl => simp [ActualAppendGas.opcodeCharges]
  | @cons fuel cost rest pre mid post trace hs ht ih =>
      have hh : Ordinary (decodeAt pre).1 := hop (fuel, cost, decodeAt pre) (by simp)
      have hd := xstep_debit hh hs
      have htail : Supported trace := fun x hx => hop x (by simp [hx])
      have hi := ih htail
      simp only [ActualAppendGas.opcodeCharges, List.map_cons, List.sum_cons]
      change post.gasAvailable.toNat + (cost + ActualAppendGas.opcodeCharges trace) ≤ _
      omega

/-- The actual final successful halt also pays its Z/step debit. -/
theorem success_final_step_nonincrease {fuel : Nat} {vj : Array UInt256}
    {pre final : EVM.State} {out : ByteArray}
    (hop : Ordinary (decodeAt pre).1) (hh : Halting (decodeAt pre).1 = true)
    (h : X fuel vj pre = .ok (.success final out)) :
    final.gasAvailable.toNat ≤ pre.gasAvailable.toNat := by
  obtain ⟨rest, cost, op, arg, mid, post, _, hd, hz, hs, hc⟩ := success_step h
  have hm : Ordinary op := by rw [hd] at hop; exact hop
  have hg := accepted_step_debit hm hz hs
  rcases hc with ⟨hn, _⟩ | ⟨_, _, he⟩
  · have hn' := H_eq_none_iff.mp hn
    rw [hd] at hh
    change Halting op = true at hh
    rw [hn'] at hh
    cases hh
  · subst post
    omega

#print axioms raw_gas
#print axioms dispatch
#print axioms accepted_valid
#print axioms accepted_step_debit
#print axioms accepted_step_nonincrease
#print axioms ordinary_iff
#print axioms xruns_debit
#print axioms success_final_step_nonincrease
end Eip8282.Audit.Integrator.OrdinaryGas
