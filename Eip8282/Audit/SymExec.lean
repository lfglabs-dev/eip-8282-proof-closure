import Eip8282.Audit.Execution.Symbolic
import EvmYul.EVM.Proof.Block
import EvmYul.EVM.Proof.MemoryStep
import Eip8282.Audit.Correspondence

/-!
# Symbolic execution of the pinned runtimes under `EvmYul.EVM.X`

Every `∀` result about a whole `Ξ` call has to walk the pinned bytes instruction
by instruction, and `Eip8282.Audit.XiTransport` shows what that costs when each
instruction is a hand-written lemma: a dozen lines per opcode site. The two
runtimes have 642 sites. This module makes a straight-line stretch of code one
theorem application instead.

The idea is to let EVMYulLean's own instruction semantics do the work. `symStep`
runs `EvmYul.step` — the *same* function `EvmYul.EVM.step` dispatches to — on
the current machine, after checking the finitely decidable parts of `X`'s
exceptional-halting predicate `Z` (stack depth, stack overflow, a listed
`JUMP` destination). Gas is deliberately not charged by `symStep`: the charge
is symbolic (`SLOAD` is warm or cold depending on the transaction's access
list) and no theorem downstream reads it, so `xRuns_symBlock` re-attaches it as
an existential bounded below, and `EvmYul.step` never reads it
(`step_stepPre_eq_map_bump`). Everything else — the program counter, the stack,
storage reads, the `JUMP` target — is computed by `EvmYul.step` itself, so a
block lemma is `rfl` on the explicit machine it starts from.

`xRuns_symBlock` is the one-time soundness proof: a listed block whose sites
are kernel-checked against the pinned image (`sitesOk`, `decide +kernel`),
starting at its first site with enough gas for the whole block, is an `XRuns`
of exactly that many `X` iterations onto `symBlock`'s answer, with gas charged.
It takes no `native_decide`, no axiom and no premise about the model.

The instructions the two pinned runtimes use outside their effectful sites are
`blockOps`; the effectful ones — `JUMPI`, `SSTORE`, `MSTORE`, `MSTORE8`,
`CALLDATACOPY`, `LOG0` and the three halts — get individual lemmas at the end
of this module, in the same shape, so that a whole path composes through
`Reaches`.
-/

namespace Eip8282.Audit.SymExec

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Jumpdests (opcodeAt)

/-! ## Sites and the block opcode set -/











/-! ## The symbolic step -/















/-! ## `Z` accepts every block opcode -/

theorem elim_guard_ok {α ε : Type} {c : Prop} [Decidable c] {e : ε} {rest : Except ε α}
    (h : ¬ c) : (if c then Except.error e else rest) = rest := if_neg h







/-! ## Facts about the block opcodes, by enumeration -/





























@[simp] theorem stack_withGE (t : EVM.State) (g : UInt256) (e : Nat) :
    (withGE t g e).stack = t.stack := rfl

@[simp] theorem toState_withGE (t : EVM.State) (g : UInt256) (e : Nat) :
    (withGE t g e).toState = t.toState := rfl
@[simp] theorem gas_withGE (t : EVM.State) (g : UInt256) (e : Nat) :
    (withGE t g e).gasAvailable = g := rfl
@[simp] theorem execLength_withGE (t : EVM.State) (g : UInt256) (e : Nat) :
    (withGE t g e).execLength = e := rfl
@[simp] theorem memory_withGE (t : EVM.State) (g : UInt256) (e : Nat) :
    (withGE t g e).memory = t.memory := rfl










/-! ## Soundness of one symbolic step -/

theorem toOption_eq_some {ε α : Type} {x : Except ε α} {a : α} (h : x.toOption = some a) :
    x = .ok a := by
  cases x with
  | error e => simp [Except.toOption] at h
  | ok b => simp [Except.toOption] at h; rw [h]

















/-! ## What a symbolic step leaves alone, and where it puts the `pc` -/







/-- Every block opcode leaves the memory, the account map and the log series
alone; `SLOAD` touches only the accessed-keys set. -/
theorem memory_step {w : Operation .EVM} (h : w ∈ blockOps) {arg : Option (UInt256 × Nat)}
    {s t : EVM.State} (hstep : EvmYul.step (τ := .EVM) w arg s = .ok t) :
    t.memory = s.memory ∧ t.activeWords = s.activeWords ∧ t.returnData = s.returnData ∧
      t.H_return = s.H_return ∧ t.accountMap = s.accountMap ∧
      t.substate.logSeries = s.substate.logSeries := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  block_ops_cases h <;> rcases arg with _ | ⟨v, n⟩ <;> stack_split stk <;> cases hstep <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! ## Word arithmetic for `pc` and gas -/







/-! ## Soundness of a listed block -/











theorem toOption_map {ε α β : Type} (x : Except ε α) (f : α → β) :
    (x.map f).toOption = x.toOption.map f := by
  cases x <;> rfl









/-- The environment survives a symbolic block: in particular the code. -/
theorem executionEnv_symBlock {vjNats : List Nat} {ops : List Instruction} {s s' : EVM.State}
    (h : symBlock vjNats ops s = some s') : s'.executionEnv = s.executionEnv := by
  induction ops generalizing s with
  | nil =>
    simp only [symBlock, Option.some.injEq] at h
    rw [h]
  | cons i rest ih =>
    rw [symBlock_cons] at h
    cases hs : symStep vjNats i s with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some s₁ =>
      rw [hs] at h
      obtain ⟨hg, hstep⟩ := guardOk_of_symStep hs
      rw [ih h, executionEnv_step (List.mem_append_left _ (mem_blockOps_of_guardOk hg)) hstep]




/-! ## The effectful sites

`JUMPI`, `SSTORE`, the memory writers and the three halts are not in
`blockOps`: their `Z` charge depends on the machine (memory expansion, the
storage refund schedule), or their next `pc` depends on a stack word. Each gets
its `Z` acceptance from `Z_of_facts` and its post-state from `EvmYul.step`
directly, so a block lemma can step through them one at a time. -/





/-! ### `JUMPI` -/





















/-! ### `SSTORE` -/













/-! ### The memory writers: `MSTORE`, `MSTORE8`, `CALLDATACOPY`, `LOG0`

Their `Z` charge is the memory expansion `Cₘ (M aw off len) - Cₘ aw`, which
depends on the machine. The lemmas here take that charge symbolically, so that
a caller supplies one bound on it per site. -/











theorem C'_REVERT (s : EVM.State) : C' s .REVERT = 0 := by
  simp +decide [C', GasConstants.Gzero]

















theorem step_REVERT {s : EVM.State} {off len : UInt256} {r : Stack UInt256}
    (hs : s.stack = off :: len :: r) :
    EvmYul.step (τ := .EVM) .REVERT none s
      = .ok (({ s with toMachineState := s.toMachineState.evmRevert off len } : EVM.State).replaceStackAndIncrPC r) := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  simp only at hs
  subst hs
  rfl



/-! ### The halting instruction, for `RunUntil.X_success` / `X_revert`

A halt is the one iteration `X` does not continue through. What the
composition lemmas need is `Z`'s acceptance and the `StepOk` of the halt, in
the form `EvmYul.EVM.Proof.RunUntil.X_success` consumes. -/



/-! ## Fuel-polymorphic reachability

`XRuns vj (f + 1 + k) s tr (f + 1) s'` says `X` gets from `s` to `s'` in `k`
iterations, leaving `f + 1` units of fuel. Nothing along a straight path depends
on `f`, so the natural statement is for all `f` at once; that is what composes
across blocks, and it is instantiated at the very end with the call's fuel. -/



theorem Reaches.refl (vj : Array UInt256) (s : EVM.State) : Reaches vj 0 s s :=
  fun f => ⟨[], XRuns.refl (f + 1) s⟩







/-- Instantiating the fuel: a call with at least `k + 1` units of fuel runs the
whole path and stops with fuel to spare. -/
theorem Reaches.xRuns_of_fuel {vj : Array UInt256} {k : Nat} {s s' : EVM.State}
    (h : Reaches vj k s s') {fuel : Nat} (hfuel : k + 1 ≤ fuel) :
    ∃ tr rem, XRuns vj fuel s tr (rem + 1) s' := by
  obtain ⟨tr, hrun⟩ := h (fuel - k - 1)
  rw [show fuel - k - 1 + 1 + k = fuel by omega] at hrun
  exact ⟨tr, fuel - k - 1, hrun⟩

/-! ## Jump tables as `Nat` lists -/



end Eip8282.Audit.SymExec
