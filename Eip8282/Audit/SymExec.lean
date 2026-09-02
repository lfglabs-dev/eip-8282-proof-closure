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

/-- A decoded instruction with the byte offset it sits at in the image. -/
abbrev Site := Nat × Instruction

/-- Width of a `PUSH` immediate, as `decode` reports it; zero otherwise. -/
def immWidth (i : Instruction) : Nat := argOnNBytesOfInstr i.1

/-- The opcodes `symStep` runs. Exactly the instructions the two pinned runtimes
execute outside their effectful sites: pure stack and arithmetic work, the
environment reads, `SLOAD`, and an unconditional `JUMP` to a listed target. -/
def blockOps : List (Operation .EVM) :=
  [.JUMPDEST, .POP, .CALLER, .CALLVALUE, .CALLDATASIZE, .CALLDATALOAD,
   .ADD, .MUL, .SUB, .DIV, .LT, .GT, .EQ, .ISZERO, .AND, .SHL, .SHR,
   .PUSH0, .PUSH1, .PUSH2, .PUSH4, .PUSH8, .PUSH20, .PUSH32,
   .DUP1, .DUP2, .DUP3, .DUP4, .DUP5,
   .SWAP1, .SWAP2, .SWAP3, .SWAP4,
   .SLOAD, .JUMP]

/-- An upper bound on what `X` charges for one block opcode. Exact for every
constant-cost instruction; `SLOAD` is bounded by its cold cost. -/
def costBound : Operation .EVM → Nat
  | .JUMPDEST => GasConstants.Gjumpdest
  | .POP | .CALLER | .CALLVALUE | .CALLDATASIZE | .PUSH0 => GasConstants.Gbase
  | .MUL | .DIV => GasConstants.Glow
  | .JUMP => GasConstants.Gmid
  | .SLOAD => GasConstants.Gcoldsload
  | _ => GasConstants.Gverylow

/-- Gas bound for a whole listed block. -/
def blockBound (sites : List Site) : Nat :=
  (sites.map fun p => costBound p.2.1).sum

/-! ## The symbolic step -/

/-- The part of `Z` a block opcode needs decided on the spot: it is a block
opcode, and a `JUMP` lands on one of the listed destinations. Operand depth is
checked by `pureStep`'s own patterns; the stack-overflow guard is discharged
from a block-level bound, so that a block may be stated over a stack whose
tail is symbolic. -/
def guardOk (vjNats : List Nat) (i : Instruction) (s : EVM.State) : Bool :=
  blockOps.contains i.1 &&
    (match i.1, s.stack with
      | .JUMP, d :: _ => vjNats.contains d.toNat
      | .JUMP, [] => false
      | _, _ => true)

/-- **The block opcodes, computed directly.** A compact table of what each block
opcode does to the program counter, the stack and — for `SLOAD` — the state,
written so that it reduces on a machine whose stack is a list literal. It is
validated against EVMYulLean's own semantics case by case in `pureStep_sound`:
whenever it answers, `EvmYul.step` answers the same. Running `EvmYul.step`
directly would be correct too, but its dispatch is large enough that unfolding
it once per site makes a block lemma time out; this table is what `rfl` sees. -/
def pureStep (i : Instruction) (s : EVM.State) : Option EVM.State :=
  match i.1, i.2, s.stack with
  | .JUMPDEST, _, _ => some s.incrPC
  | .POP, _, _ :: r => some (s.replaceStackAndIncrPC r)
  | .CALLER, _, r =>
      some (s.replaceStackAndIncrPC (UInt256.ofNat s.executionEnv.source.val :: r))
  | .CALLVALUE, _, r => some (s.replaceStackAndIncrPC (s.executionEnv.weiValue :: r))
  | .CALLDATASIZE, _, r =>
      some (s.replaceStackAndIncrPC (UInt256.ofNat s.executionEnv.calldata.size :: r))
  | .CALLDATALOAD, _, a :: r => some (s.replaceStackAndIncrPC (s.toState.calldataload a :: r))
  | .ADD, _, a :: b :: r => some (s.replaceStackAndIncrPC (UInt256.add a b :: r))
  | .MUL, _, a :: b :: r => some (s.replaceStackAndIncrPC (UInt256.mul a b :: r))
  | .SUB, _, a :: b :: r => some (s.replaceStackAndIncrPC (UInt256.sub a b :: r))
  | .DIV, _, a :: b :: r => some (s.replaceStackAndIncrPC (UInt256.div a b :: r))
  | .LT, _, a :: b :: r => some (s.replaceStackAndIncrPC (UInt256.lt a b :: r))
  | .GT, _, a :: b :: r => some (s.replaceStackAndIncrPC (UInt256.gt a b :: r))
  | .EQ, _, a :: b :: r => some (s.replaceStackAndIncrPC (UInt256.eq a b :: r))
  | .ISZERO, _, a :: r => some (s.replaceStackAndIncrPC (UInt256.isZero a :: r))
  | .AND, _, a :: b :: r => some (s.replaceStackAndIncrPC (UInt256.land a b :: r))
  | .SHL, _, a :: b :: r => some (s.replaceStackAndIncrPC (UInt256.shiftLeft b a :: r))
  | .SHR, _, a :: b :: r => some (s.replaceStackAndIncrPC (UInt256.shiftRight b a :: r))
  | .PUSH0, _, r => some (s.replaceStackAndIncrPC (⟨0⟩ :: r))
  | .Push _, some (v, n), r => some (s.replaceStackAndIncrPC (v :: r) (n + 1))
  | .Push _, none, _ => none
  | .DUP1, _, a :: r => some (s.replaceStackAndIncrPC (a :: a :: r))
  | .DUP2, _, a :: b :: r => some (s.replaceStackAndIncrPC (b :: a :: b :: r))
  | .DUP3, _, a :: b :: c :: r => some (s.replaceStackAndIncrPC (c :: a :: b :: c :: r))
  | .DUP4, _, a :: b :: c :: d :: r => some (s.replaceStackAndIncrPC (d :: a :: b :: c :: d :: r))
  | .DUP5, _, a :: b :: c :: d :: e :: r =>
      some (s.replaceStackAndIncrPC (e :: a :: b :: c :: d :: e :: r))
  | .SWAP1, _, a :: b :: r => some (s.replaceStackAndIncrPC (b :: a :: r))
  | .SWAP2, _, a :: b :: c :: r => some (s.replaceStackAndIncrPC (c :: b :: a :: r))
  | .SWAP3, _, a :: b :: c :: d :: r => some (s.replaceStackAndIncrPC (d :: b :: c :: a :: r))
  | .SWAP4, _, a :: b :: c :: d :: e :: r =>
      some (s.replaceStackAndIncrPC (e :: b :: c :: d :: a :: r))
  | .SLOAD, _, k :: r =>
      some (({ s with toState := (s.toState.sload k).1 } : EVM.State).replaceStackAndIncrPC
        ((s.toState.sload k).2 :: r))
  | .JUMP, _, d :: r => some { s with pc := d, stack := r }
  | _, _, _ => none

/-- One instruction, with gas left untouched. -/
def symStep (vjNats : List Nat) (i : Instruction) (s : EVM.State) : Option EVM.State :=
  if guardOk vjNats i s then pureStep i s else none

/-- A listed straight-line block. -/
def symBlock (vjNats : List Nat) : List Instruction → EVM.State → Option EVM.State
  | [], s => some s
  | i :: rest, s => symStep vjNats i s >>= symBlock vjNats rest

/-- The sites of a block decode to the listed instructions in `code`, sit at
consecutive offsets, and only the last may be a `JUMP`. Kernel-decidable over
the pinned images. -/
def sitesOk (code : ByteArray) : List Site → Bool
  | [] => true
  | [(pc, i)] => decide (opcodeAt code pc = some i)
  | (pc, i) :: (pc', i') :: rest =>
      decide (opcodeAt code pc = some i) && decide (pc' = pc + 1 + immWidth i) &&
        decide (i.1 ≠ .JUMP) && sitesOk code ((pc', i') :: rest)

/-- Re-attach a gas charge and the instruction count to a symbolic post-state. -/
def withGE (t : EVM.State) (g : UInt256) (e : Nat) : EVM.State :=
  { t with gasAvailable := g, execLength := e }

/-- The post-state of a real step: the symbolic post-state with `pre`'s gas
charged and `pre`'s instruction count bumped. -/
abbrev bump (g : Nat) (pre t : EVM.State) : EVM.State :=
  withGE t (pre.gasAvailable - UInt256.ofNat g) (pre.execLength + 1)

/-! ## `Z` accepts every block opcode -/

theorem elim_guard_ok {α ε : Type} {c : Prop} [Decidable c] {e : ε} {rest : Except ε α}
    (h : ¬ c) : (if c then Except.error e else rest) = rest := if_neg h

/-- The state `Z` hands to `step`: the pre-state with this instruction's memory
expansion charged. Definitionally `EvmYul.EVM.Proof.zMid`. -/
abbrev charged (pre : EVM.State) (w : Operation .EVM) : EVM.State :=
  { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat (memoryExpansionCost pre w) }

/-- **`Z` accepts, from named facts.** Every guard `Z` runs is discharged from a
hypothesis, so acceptance is stated once for every instruction this module
steps rather than once per opcode. -/
theorem Z_of_facts (validJumps : Array UInt256) (w : Operation .EVM) (pre : EVM.State)
    {d a : Nat}
    (hgas₁ : memoryExpansionCost pre w ≤ pre.gasAvailable.toNat)
    (hgas₂ : C' (charged pre w) w ≤ (charged pre w).gasAvailable.toNat)
    (hδ : δ w = some d) (hα : α w = some a)
    (hlen : d ≤ pre.stack.length)
    (hover : pre.stack.length - d + a ≤ 1024)
    (hjump : w = .JUMP → X.notIn pre.stack[0]? validJumps = false)
    (hjumpi : w = .JUMPI → pre.stack[1]? ≠ some ⟨0⟩ → X.notIn pre.stack[0]? validJumps = false)
    (hrdc : w ≠ .RETURNDATACOPY)
    (hW : pre.executionEnv.perm = false → W w pre.stack = false)
    (hss : w = .SSTORE → GasConstants.Gcallstipend < (charged pre w).gasAvailable.toNat)
    (hcr : w.isCreate = false) :
    Z validJumps w pre = .ok (charged pre w, C' (charged pre w) w) := by
  simp only [Z, Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg (Nat.not_lt.mpr hgas₁)]
  rw [if_neg (Nat.not_lt.mpr hgas₂)]
  simp only [hδ, hα, reduceCtorEq, if_false, Option.getD_some]
  rw [if_neg (Nat.not_lt.mpr hlen)]
  rw [if_neg (by
    rintro ⟨rfl, hbad⟩
    rw [hjump rfl] at hbad
    exact Bool.false_ne_true hbad)]
  rw [if_neg (by
    rintro ⟨rfl, hne, hbad⟩
    rw [hjumpi rfl hne] at hbad
    exact Bool.false_ne_true hbad)]
  rw [if_neg (fun h => hrdc h.1)]
  rw [if_neg (Nat.not_lt.mpr hover)]
  rw [if_neg (fun h => by
    have hp : pre.executionEnv.perm = false := by
      cases hperm : pre.executionEnv.perm
      · rfl
      · exact absurd hperm h.1
    rw [hW hp] at h
    exact Bool.false_ne_true h.2)]
  rw [if_neg (fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hss h.1) h.2))]
  rw [if_neg (fun h => by rw [hcr] at h; exact Bool.false_ne_true h.1)]

/-- A charge-free instruction leaves `Z`'s state at the pre-state. -/
theorem charged_eq_self {pre : EVM.State} {w : Operation .EVM}
    (hmem : memoryExpansionCost pre w = 0) : charged pre w = pre := by
  have hsub : pre.gasAvailable - UInt256.ofNat 0 = pre.gasAvailable := by
    cases pre.gasAvailable with | mk v =>
    show (⟨v - (UInt256.ofNat 0).val⟩ : UInt256) = ⟨v⟩
    have h : (UInt256.ofNat 0).val = 0 := rfl
    rw [h, sub_zero]
  show ({pre with gasAvailable := pre.gasAvailable - UInt256.ofNat (memoryExpansionCost pre w)} :
    EVM.State) = pre
  rw [hmem, hsub]

/-! ## Facts about the block opcodes, by enumeration -/

/-- The instructions any lemma in this module steps: the block opcodes plus the
effectful sites that get individual lemmas below. -/
def allOps : List (Operation .EVM) :=
  blockOps ++ [.JUMPI, .SSTORE, .MSTORE, .MSTORE8, .CALLDATACOPY, .LOG0, .RETURN, .REVERT, .STOP]

set_option hygiene false in
/-- Unfold membership in `blockOps` into its 35 cases. -/
macro "block_ops_cases" h:ident : tactic =>
  `(tactic| (simp only [blockOps, List.mem_cons, List.not_mem_nil, or_false] at $h:ident
             rcases $h:ident with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl))

set_option hygiene false in
/-- Unfold membership in `allOps` into its 44 cases. -/
macro "all_ops_cases" h:ident : tactic =>
  `(tactic| (simp only [allOps, blockOps, List.mem_cons, List.mem_append, List.not_mem_nil,
               or_false, or_assoc] at $h:ident
             rcases $h:ident with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl))

/-- No block opcode touches memory, so none expands it. -/
theorem memcost_zero {w : Operation .EVM} (h : w ∈ blockOps) (s : EVM.State) :
    memoryExpansionCost s w = 0 := by
  block_ops_cases h <;> simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

/-- `X` never charges a block opcode more than `costBound`. -/
theorem C'_le_costBound {w : Operation .EVM} (h : w ∈ blockOps) (s : EVM.State) :
    C' s w ≤ costBound w := by
  block_ops_cases h
  all_goals first
    | (simp +decide [C', costBound]; done)
    | (show Csload s.stack s.substate s.executionEnv ≤ GasConstants.Gcoldsload
       unfold Csload
       split <;> decide)

/-- Every block opcode has a stack signature. -/
theorem δ_block {w : Operation .EVM} (h : w ∈ blockOps) : δ w = some ((δ w).getD 0) := by
  block_ops_cases h <;> rfl

theorem α_block {w : Operation .EVM} (h : w ∈ blockOps) : α w = some ((α w).getD 0) := by
  block_ops_cases h <;> rfl

/-- No block opcode is a static-mode violation. -/
theorem W_block {w : Operation .EVM} (h : w ∈ blockOps) (stk : Stack UInt256) :
    W w stk = false := by
  block_ops_cases h <;> simp +decide [W]

theorem not_halting_block {w : Operation .EVM} (h : w ∈ blockOps) : Halting w = false := by
  block_ops_cases h <;> decide

theorem block_ne_JUMPI {w : Operation .EVM} (h : w ∈ blockOps) : w ≠ .JUMPI := by
  block_ops_cases h <;> decide

theorem block_ne_RETURNDATACOPY {w : Operation .EVM} (h : w ∈ blockOps) : w ≠ .RETURNDATACOPY := by
  block_ops_cases h <;> decide

theorem block_ne_SSTORE {w : Operation .EVM} (h : w ∈ blockOps) : w ≠ .SSTORE := by
  block_ops_cases h <;> decide

theorem block_not_create {w : Operation .EVM} (h : w ∈ blockOps) : w.isCreate = false := by
  block_ops_cases h <;> decide

/-- None of the stepped instructions re-enters `X` on a child frame, so
`EvmYul.EVM.step` hands each of them straight to `EvmYul.step` on `stepPre`. -/
theorem EVM_step_eq_step {w : Operation .EVM} (h : w ∈ allOps) (f g : Nat)
    (arg : Option (UInt256 × Nat)) (s : EVM.State) :
    EvmYul.EVM.step (f + 1) g (some (w, arg)) s = EvmYul.step (τ := .EVM) w arg (stepPre g s) := by
  all_ops_cases h <;> rfl

@[simp] theorem stack_withGE (t : EVM.State) (g : UInt256) (e : Nat) :
    (withGE t g e).stack = t.stack := rfl
@[simp] theorem pc_withGE (t : EVM.State) (g : UInt256) (e : Nat) :
    (withGE t g e).pc = t.pc := rfl
@[simp] theorem toState_withGE (t : EVM.State) (g : UInt256) (e : Nat) :
    (withGE t g e).toState = t.toState := rfl
@[simp] theorem gas_withGE (t : EVM.State) (g : UInt256) (e : Nat) :
    (withGE t g e).gasAvailable = g := rfl
@[simp] theorem execLength_withGE (t : EVM.State) (g : UInt256) (e : Nat) :
    (withGE t g e).execLength = e := rfl
@[simp] theorem memory_withGE (t : EVM.State) (g : UInt256) (e : Nat) :
    (withGE t g e).memory = t.memory := rfl
@[simp] theorem executionEnv_withGE (t : EVM.State) (g : UInt256) (e : Nat) :
    (withGE t g e).executionEnv = t.executionEnv := rfl

theorem withGE_withGE (t : EVM.State) (g g' : UInt256) (e e' : Nat) :
    withGE (withGE t g e) g' e' = withGE t g' e' := rfl

theorem stepPre_eq_withGE (g : Nat) (s : EVM.State) :
    stepPre g s = withGE s (s.gasAvailable - UInt256.ofNat g) (s.execLength + 1) := rfl

set_option hygiene false in
/-- Split a stack variable five levels deep, so that every operand pattern the
stepped opcodes match on is a constructor. -/
macro "stack_split" stk:ident : tactic =>
  `(tactic| (rcases $stk:ident with _ | ⟨a₀, _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, _ | ⟨a₄, r₅⟩⟩⟩⟩⟩))

/-- **`EvmYul.step` never reads gas or the instruction count.** Running an
instruction on the machine with gas `g` and count `e` is running it on the
machine as it was and then setting gas `g` and count `e`. This is what lets the
symbolic step leave the charge to the soundness theorem. -/
theorem step_withGE {w : Operation .EVM} (h : w ∈ allOps) (arg : Option (UInt256 × Nat))
    (s : EVM.State) (g : UInt256) (e : Nat) :
    EvmYul.step (τ := .EVM) w arg (withGE s g e)
      = (EvmYul.step (τ := .EVM) w arg s).map (fun t => withGE t g e) := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  all_ops_cases h <;> rcases arg with _ | ⟨v, n⟩ <;> stack_split stk <;> rfl

/-! ## Soundness of one symbolic step -/

theorem toOption_eq_some {ε α : Type} {x : Except ε α} {a : α} (h : x.toOption = some a) :
    x = .ok a := by
  cases x with
  | error e => simp [Except.toOption] at h
  | ok b => simp [Except.toOption] at h; rw [h]

/-- `decodeAt` is a function of the code and the `pc`. -/
theorem decodeAt_of_code_pc {st : EVM.State} {code : ByteArray} {n : Nat} {i : Instruction}
    (hcode : st.executionEnv.code = code) (hpc : st.pc = UInt256.ofNat n)
    (hop : opcodeAt code n = some i) : decodeAt st = i := by
  show (decode st.toState.executionEnv.code st.pc).getD (.STOP, .none) = _
  have hcode' : st.toState.executionEnv.code = code := hcode
  rw [hcode', hpc]
  show (opcodeAt code n).getD (.STOP, .none) = _
  rw [hop]
  rfl

theorem mem_blockOps_of_guardOk {vjNats : List Nat} {i : Instruction} {s : EVM.State}
    (h : guardOk vjNats i s = true) : i.1 ∈ blockOps := by
  unfold guardOk at h
  simp only [Bool.and_eq_true] at h
  exact List.contains_iff_mem.mp h.1

/-- **The table agrees with EVMYulLean.** Every answer of `pureStep` on a block
opcode is `EvmYul.step`'s answer, for every argument and every stack. -/
theorem pureStep_sound {w : Operation .EVM} (h : w ∈ blockOps) {arg : Option (UInt256 × Nat)}
    {s s' : EVM.State} (hps : pureStep (w, arg) s = some s') :
    EvmYul.step (τ := .EVM) w arg s = .ok s' := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  block_ops_cases h <;> rcases arg with _ | ⟨v, n⟩ <;> stack_split stk <;> cases hps <;> rfl

theorem guardOk_of_symStep {vjNats : List Nat} {i : Instruction} {s s' : EVM.State}
    (h : symStep vjNats i s = some s') :
    guardOk vjNats i s = true ∧ EvmYul.step (τ := .EVM) i.1 i.2 s = .ok s' := by
  unfold symStep at h
  split at h
  · rename_i hg
    exact ⟨hg, pureStep_sound (mem_blockOps_of_guardOk hg) h⟩
  · exact absurd h (by simp)

/-- Whenever the table answers, the operands were there, and the stack grew by
at most one word. -/
theorem pureStep_stack_ok {w : Operation .EVM} (h : w ∈ blockOps) {arg : Option (UInt256 × Nat)}
    {s s' : EVM.State} (hps : pureStep (w, arg) s = some s') :
    (δ w).getD 0 ≤ s.stack.length ∧ s'.stack.length ≤ s.stack.length + 1 := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  block_ops_cases h <;> rcases arg with _ | ⟨v, n⟩ <;> stack_split stk <;> cases hps <;>
    simp [δ, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]

/-- No block opcode pushes more than one word beyond what it pops. -/
theorem α_le_δ_succ {w : Operation .EVM} (h : w ∈ blockOps) :
    (α w).getD 0 ≤ (δ w).getD 0 + 1 := by
  block_ops_cases h <;> decide

theorem jump_of_guardOk {vj : Array UInt256} {vjNats : List Nat}
    (hvj : ∀ n ∈ vjNats, vj.contains (UInt256.ofNat n) = true)
    {i : Instruction} {s : EVM.State} (h : guardOk vjNats i s = true) :
    i.1 = .JUMP → X.notIn s.stack[0]? vj = false := by
  intro hj
  unfold guardOk at h
  simp only [Bool.and_eq_true] at h
  have h4 := h.2
  rw [hj] at h4
  cases hs : s.stack with
  | nil => rw [hs] at h4; exact absurd h4 (by simp)
  | cons d rest =>
    rw [hs] at h4
    simp only at h4
    have hmem : d.toNat ∈ vjNats := List.contains_iff_mem.mp h4
    have hc := hvj d.toNat hmem
    have hd : UInt256.ofNat d.toNat = d := by
      have h : (UInt256.ofNat d.toNat).val = d.val := by
        apply Fin.ext
        show d.toNat % UInt256.size = d.val.val
        exact Nat.mod_eq_of_lt d.val.isLt
      cases hx : UInt256.ofNat d.toNat
      cases hy : d
      simp_all
    rw [hd] at hc
    simp [X.notIn, X.belongs, hc]

/-- **One symbolic step is one non-halting `X` iteration**, charging exactly
what `X` charges for it. The gas bound is the only hypothesis `symStep` could
not decide for itself. -/
theorem xStepAt_symStep {vj : Array UInt256} {vjNats : List Nat}
    (hvj : ∀ n ∈ vjNats, vj.contains (UInt256.ofNat n) = true)
    {f : Nat} {i : Instruction} {s s' : EVM.State}
    (hdec : decodeAt s = i) (hsym : symStep vjNats i s = some s')
    (hgas : costBound i.1 ≤ s.gasAvailable.toNat) (hover : s.stack.length < 1024) :
    XStepAt vj (f + 1) (C' s i.1) s (bump (C' s i.1) s s') := by
  obtain ⟨hguard, hstep⟩ := guardOk_of_symStep hsym
  have hmem := mem_blockOps_of_guardOk hguard
  have hps : pureStep i s = some s' := by
    unfold symStep at hsym; rw [if_pos hguard] at hsym; exact hsym
  have hbounds : (δ i.1).getD 0 ≤ s.stack.length ∧
      s.stack.length - (δ i.1).getD 0 + (α i.1).getD 0 ≤ 1024 := by
    obtain ⟨h1, _⟩ := pureStep_stack_ok hmem (arg := i.2) hps
    have h3 := α_le_δ_succ hmem
    exact ⟨h1, by omega⟩
  have hch : charged s i.1 = s := charged_eq_self (memcost_zero hmem s)
  have hZ : Z vj i.1 s = .ok (s, C' s i.1) := by
    have h := Z_of_facts vj i.1 s (d := (δ i.1).getD 0) (a := (α i.1).getD 0)
      (by rw [memcost_zero hmem s]; exact Nat.zero_le _)
      (by rw [hch]; exact Nat.le_trans (C'_le_costBound hmem s) hgas)
      (δ_block hmem) (α_block hmem) hbounds.1 hbounds.2 (jump_of_guardOk hvj hguard)
      (fun h => absurd h (block_ne_JUMPI hmem)) (block_ne_RETURNDATACOPY hmem)
      (fun _ => W_block hmem s.stack)
      (fun h => absurd h (block_ne_SSTORE hmem)) (block_not_create hmem)
    rwa [hch] at h
  refine ⟨s, ?_, ?_, ?_⟩
  · rw [hdec]; exact hZ
  · rw [hdec]
    show EvmYul.EVM.step (f + 1) (C' s i.1) (some (i.1, i.2)) s = .ok _
    rw [EVM_step_eq_step (List.mem_append_left _ hmem), stepPre_eq_withGE,
      step_withGE (List.mem_append_left _ hmem), hstep]
    rfl
  · rw [hdec]
    exact H_eq_none_of_not_halting (not_halting_block hmem)

/-! ## What a symbolic step leaves alone, and where it puts the `pc` -/

/-- `sstore` rewrites the account map and the substate; the environment is
untouched whether or not the executing account exists. -/
theorem executionEnv_sstore (st : EvmYul.State .EVM) (k v : UInt256) :
    (st.sstore k v).executionEnv = st.executionEnv := by
  unfold EvmYul.State.sstore
  dsimp only
  rcases hacc : Std.TreeMap.get! st.accountMap st.executionEnv.codeOwner with ⟨⟨nonce, bal, sto, code⟩, tst⟩
  cases st.lookupAccount st.executionEnv.codeOwner <;> rfl

theorem executionEnv_step {w : Operation .EVM} (h : w ∈ allOps) {arg : Option (UInt256 × Nat)}
    {s t : EVM.State} (hstep : EvmYul.step (τ := .EVM) w arg s = .ok t) :
    t.executionEnv = s.executionEnv := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  all_ops_cases h <;> rcases arg with _ | ⟨v, n⟩ <;> stack_split stk <;> cases hstep <;>
    first
      | rfl
      | exact executionEnv_sstore _ _ _

/-- The straight-line `pc` update of every block opcode other than `JUMP`: one
byte for the opcode itself plus its immediate. `harg` is what `decode` always
delivers — a `PUSH` immediate carries its own width. -/
theorem pc_step {w : Operation .EVM} (h : w ∈ blockOps) (hne : w ≠ .JUMP)
    {arg : Option (UInt256 × Nat)} (harg : ∀ v n, arg = some (v, n) → n = argOnNBytesOfInstr w)
    {s t : EVM.State} (hstep : EvmYul.step (τ := .EVM) w arg s = .ok t) :
    t.pc = s.pc + UInt256.ofNat (argOnNBytesOfInstr w + 1) := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  block_ops_cases h <;> rcases arg with _ | ⟨v, n⟩ <;> stack_split stk <;>
    first
      | exact absurd rfl hne
      | (cases hstep <;> first | rfl | (rw [harg v n rfl]; rfl))

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

theorem ofNat_add_ofNat (m n : Nat) :
    UInt256.ofNat m + UInt256.ofNat n = UInt256.ofNat (m + n) := by
  have h : ((UInt256.ofNat m + UInt256.ofNat n).val : Fin UInt256.size)
      = (UInt256.ofNat (m + n)).val := by
    apply Fin.ext
    show (m % UInt256.size + n % UInt256.size) % UInt256.size = (m + n) % UInt256.size
    exact (Nat.add_mod m n UInt256.size).symm
  cases hx : UInt256.ofNat m + UInt256.ofNat n
  cases hy : UInt256.ofNat (m + n)
  simp_all

/-- Gas decreases by exactly the charge when the charge is affordable. -/
theorem toNat_sub_ofNat {a : UInt256} {k : Nat} (h : k ≤ a.toNat) :
    (a - UInt256.ofNat k).toNat = a.toNat - k := by
  have hlt : a.val.val < UInt256.size := a.val.isLt
  have h' : k ≤ a.val.val := h
  have hk : k < UInt256.size := Nat.lt_of_le_of_lt h' hlt
  have hv : ((UInt256.ofNat k).val : Fin UInt256.size).val = k := Nat.mod_eq_of_lt hk
  show (a.val - (UInt256.ofNat k).val).val = a.val.val - k
  rw [Fin.sub_def, hv]
  show (UInt256.size - k + a.val.val) % UInt256.size = a.val.val - k
  have key : UInt256.size - k + a.val.val = UInt256.size + (a.val.val - k) := by omega
  rw [key, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

theorem toNat_ofNat_of_lt {n : Nat} (h : n < UInt256.size) : (UInt256.ofNat n).toNat = n :=
  Nat.mod_eq_of_lt h

/-! ## Soundness of a listed block -/

/-- The offset of a block's first site. -/
def headPc : List Site → Nat
  | [] => 0
  | (pc, _) :: _ => pc

/-- `decode` never invents an immediate width: a `PUSH` argument carries exactly
the width `argOnNBytesOfInstr` assigns to its opcode. -/
theorem arg_width_of_opcodeAt {code : ByteArray} {pc : Nat} {w : Operation .EVM}
    {arg : Option (UInt256 × Nat)} (h : opcodeAt code pc = some (w, arg)) :
    ∀ v n, arg = some (v, n) → n = argOnNBytesOfInstr w := by
  intro v n hn
  unfold opcodeAt decode at h
  simp only [Bind.bind, Option.bind] at h
  split at h
  · exact absurd h (by simp)
  · rename_i instr hinstr
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, harg⟩ := h
    rw [← harg] at hn
    split at hn
    · exact absurd hn (by simp)
    · simp only [Option.some.injEq, Prod.mk.injEq] at hn
      exact hn.2.symm

theorem sitesOk_cons {code : ByteArray} {pc : Nat} {i : Instruction} {rest : List Site}
    (h : sitesOk code ((pc, i) :: rest) = true) :
    opcodeAt code pc = some i ∧
      (rest = [] ∨
        (headPc rest = pc + 1 + immWidth i ∧ i.1 ≠ .JUMP ∧ sitesOk code rest = true)) := by
  cases rest with
  | nil =>
    simp only [sitesOk, decide_eq_true_eq] at h
    exact ⟨h, Or.inl rfl⟩
  | cons site rest' =>
    obtain ⟨pc', i'⟩ := site
    simp only [sitesOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1, Or.inr ⟨h.1.1.2, h.1.2, h.2⟩⟩

theorem blockBound_cons (site : Site) (rest : List Site) :
    blockBound (site :: rest) = costBound site.2.1 + blockBound rest := by
  simp [blockBound]

theorem symBlock_cons (vjNats : List Nat) (i : Instruction) (rest : List Instruction)
    (s : EVM.State) :
    symBlock vjNats (i :: rest) s = symStep vjNats i s >>= symBlock vjNats rest := rfl

theorem toOption_map {ε α β : Type} (x : Except ε α) (f : α → β) :
    (x.map f).toOption = x.toOption.map f := by
  cases x <;> rfl

theorem guardOk_withGE (vjNats : List Nat) (i : Instruction) (s : EVM.State) (g : UInt256)
    (e : Nat) : guardOk vjNats i (withGE s g e) = guardOk vjNats i s := rfl

/-- The table never reads gas or the instruction count either. -/
theorem pureStep_withGE (i : Instruction) (s : EVM.State) (g : UInt256) (e : Nat) :
    pureStep i (withGE s g e) = (pureStep i s).map (fun t => withGE t g e) := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  obtain ⟨w, arg⟩ := i
  unfold pureStep
  cases w <;> rename_i op <;> cases op <;> rcases arg with _ | ⟨v, n⟩ <;> stack_split stk <;> rfl

theorem symStep_withGE (vjNats : List Nat) (i : Instruction) (s : EVM.State) (g : UInt256)
    (e : Nat) :
    symStep vjNats i (withGE s g e) = (symStep vjNats i s).map (fun t => withGE t g e) := by
  unfold symStep
  rw [guardOk_withGE]
  split
  · exact pureStep_withGE i s g e
  · rfl

theorem symBlock_withGE (vjNats : List Nat) (ops : List Instruction) (s : EVM.State)
    (g : UInt256) (e : Nat) :
    symBlock vjNats ops (withGE s g e) = (symBlock vjNats ops s).map (fun t => withGE t g e) := by
  induction ops generalizing s with
  | nil => rfl
  | cons i rest ih =>
    rw [symBlock_cons, symBlock_cons, symStep_withGE]
    cases symStep vjNats i s with
    | none => rfl
    | some s₁ =>
      show symBlock vjNats rest (withGE s₁ g e) = _
      rw [ih]
      rfl

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

/-- **A listed block is an `XRuns`.** From a machine sitting at the block's
first site, with the block's gas bound in hand, `X` takes exactly one iteration
per site and lands on the symbolic answer with some gas left, bounded below.

The fuel is left free: whatever `X` has to spare after the block, it had that
plus one unit per site before it. The run must end with at least one unit
unspent, because `X` refuses to *start* an instruction at fuel zero. -/
theorem xRuns_symBlock {vj : Array UInt256} {vjNats : List Nat}
    (hvj : ∀ n ∈ vjNats, vj.contains (UInt256.ofNat n) = true)
    {code : ByteArray} (sites : List Site) (hsites : sitesOk code sites = true)
    {s s' : EVM.State}
    (hcode : s.executionEnv.code = code) (hpc : s.pc = UInt256.ofNat (headPc sites))
    (hgas : blockBound sites ≤ s.gasAvailable.toNat)
    (hlen : s.stack.length + sites.length ≤ 1024)
    (hsym : symBlock vjNats (sites.map Prod.snd) s = some s') :
    ∃ g' e', s.gasAvailable.toNat - blockBound sites ≤ g'.toNat ∧
      ∀ f, ∃ tr, XRuns vj (f + 1 + sites.length) s tr (f + 1) (withGE s' g' e') := by
  induction sites generalizing s s' with
  | nil =>
    simp only [List.map_nil, symBlock, Option.some.injEq] at hsym
    subst hsym
    exact ⟨s.gasAvailable, s.execLength, by omega, fun f => ⟨[], XRuns.refl (f + 1) s⟩⟩
  | cons site rest ih =>
    obtain ⟨pc, i⟩ := site
    obtain ⟨hop, hrest⟩ := sitesOk_cons hsites
    rw [List.map_cons, symBlock_cons] at hsym
    cases hs₁ : symStep vjNats i s with
    | none => rw [hs₁] at hsym; exact absurd hsym (by simp)
    | some s₁ =>
    rw [hs₁] at hsym
    change symBlock vjNats (rest.map Prod.snd) s₁ = some s' at hsym
    obtain ⟨hguard, hstep₁⟩ := guardOk_of_symStep hs₁
    have hmem := mem_blockOps_of_guardOk hguard
    have hps : pureStep i s = some s₁ := by
      unfold symStep at hs₁; rw [if_pos hguard] at hs₁; exact hs₁
    have hgrow := (pureStep_stack_ok hmem (arg := i.2) hps).2
    have hlen' : s.stack.length + (rest.length + 1) ≤ 1024 := hlen
    have hover : s.stack.length < 1024 := by omega
    have hdec : decodeAt s = i := decodeAt_of_code_pc hcode hpc hop
    rw [blockBound_cons] at hgas
    have hgas' : costBound i.1 + blockBound rest ≤ s.gasAvailable.toNat := hgas
    have hcost : costBound i.1 ≤ s.gasAvailable.toNat := by omega
    have hC := C'_le_costBound hmem s
    have hg₁ : (s.gasAvailable - UInt256.ofNat (C' s i.1)).toNat
        = s.gasAvailable.toNat - C' s i.1 := toNat_sub_ofNat (by omega)
    rcases hrest with rfl | ⟨hhead, hne, hrest⟩
    · change some s₁ = some s' at hsym
      obtain rfl := Option.some.inj hsym
      refine ⟨_, _, ?_, fun f => ⟨_,
        XRuns.cons (xStepAt_symStep hvj (f := f) hdec hs₁ hcost hover) (XRuns.refl (f + 1) _)⟩⟩
      change s.gasAvailable.toNat - (costBound i.1 + blockBound []) ≤
        (s.gasAvailable - UInt256.ofNat (C' s i.1)).toNat
      rw [hg₁]
      simp only [blockBound, List.map_nil, List.sum_nil]
      omega
    · have hcode₁ : (bump (C' s i.1) s s₁).executionEnv.code = code := by
        show s₁.executionEnv.code = code
        rw [executionEnv_step (List.mem_append_left _ hmem) hstep₁, hcode]
      have hpc₁ : (bump (C' s i.1) s s₁).pc = UInt256.ofNat (headPc rest) := by
        show s₁.pc = _
        rw [pc_step hmem hne (arg_width_of_opcodeAt hop) hstep₁, hpc, ofNat_add_ofNat, hhead]
        show UInt256.ofNat (pc + (argOnNBytesOfInstr i.1 + 1))
          = UInt256.ofNat (pc + 1 + argOnNBytesOfInstr i.1)
        congr 1
        omega
      have hgas₁ : blockBound rest ≤ (bump (C' s i.1) s s₁).gasAvailable.toNat := by
        change blockBound rest ≤ (s.gasAvailable - UInt256.ofNat (C' s i.1)).toNat
        rw [hg₁]; omega
      have hsym₁ : symBlock vjNats (rest.map Prod.snd) (bump (C' s i.1) s s₁)
          = some (withGE s' (s.gasAvailable - UInt256.ofNat (C' s i.1)) (s.execLength + 1)) := by
        show symBlock vjNats (rest.map Prod.snd) (withGE s₁ _ _) = _
        rw [symBlock_withGE, hsym]
        rfl
      have hlen₁ : (bump (C' s i.1) s s₁).stack.length + rest.length ≤ 1024 := by
        show s₁.stack.length + rest.length ≤ 1024
        omega
      obtain ⟨g', e', hbound, hrun⟩ := ih hrest hcode₁ hpc₁ hgas₁ hlen₁ hsym₁
      refine ⟨g', e', ?_, fun f => ?_⟩
      · change (s.gasAvailable - UInt256.ofNat (C' s i.1)).toNat - blockBound rest ≤ g'.toNat
          at hbound
        rw [hg₁] at hbound
        rw [blockBound_cons]
        change s.gasAvailable.toNat - (costBound i.1 + blockBound rest) ≤ g'.toNat
        omega
      · obtain ⟨tr, hrun⟩ := hrun f
        rw [withGE_withGE] at hrun
        have hx := xStepAt_symStep hvj (f := f + rest.length) hdec hs₁ hcost hover
        rw [show f + rest.length + 1 = f + 1 + rest.length by omega] at hx
        exact ⟨_, XRuns.cons hx hrun⟩


/-! ## The effectful sites

`JUMPI`, `SSTORE`, the memory writers and the three halts are not in
`blockOps`: their `Z` charge depends on the machine (memory expansion, the
storage refund schedule), or their next `pc` depends on a stack word. Each gets
its `Z` acceptance from `Z_of_facts` and its post-state from `EvmYul.step`
directly, so a block lemma can step through them one at a time. -/

/-- **One effectful iteration of `X`.** `Z` accepts with the memory charge
applied, the instruction does not halt, and `EvmYul.step` answers `t`: then the
iteration lands on `t` with both charges applied and the count bumped. -/
theorem xStepAt_of_step {vj : Array UInt256} {f : Nat} {w : Operation .EVM}
    {arg : Option (UInt256 × Nat)} {s t : EVM.State}
    (hmem : w ∈ allOps) (hhalt : Halting w = false)
    (hdec : decodeAt s = (w, arg))
    (hZ : Z vj w s = .ok (charged s w, C' (charged s w) w))
    (hstep : EvmYul.step (τ := .EVM) w arg s = .ok t) :
    XStepAt vj (f + 1) (C' (charged s w) w) s
      (withGE t
        (s.gasAvailable - UInt256.ofNat (memoryExpansionCost s w)
          - UInt256.ofNat (C' (charged s w) w))
        (s.execLength + 1)) := by
  refine ⟨charged s w, ?_, ?_, ?_⟩
  · rw [hdec]; exact hZ
  · rw [hdec]
    show EvmYul.EVM.step (f + 1) (C' (charged s w) w) (some (w, arg)) (charged s w) = .ok _
    rw [EVM_step_eq_step hmem, stepPre_eq_withGE]
    show EvmYul.step (τ := .EVM) w arg (withGE s _ _) = _
    rw [step_withGE hmem, hstep]
    rfl
  · rw [hdec]
    exact H_eq_none_of_not_halting hhalt

/-- The same iteration when the instruction expands no memory. -/
theorem xStepAt_of_step_nomem {vj : Array UInt256} {f : Nat} {w : Operation .EVM}
    {arg : Option (UInt256 × Nat)} {s t : EVM.State}
    (hmem : w ∈ allOps) (hhalt : Halting w = false)
    (hdec : decodeAt s = (w, arg)) (hmc : memoryExpansionCost s w = 0)
    (hZ : Z vj w s = .ok (s, C' s w))
    (hstep : EvmYul.step (τ := .EVM) w arg s = .ok t) :
    XStepAt vj (f + 1) (C' s w) s
      (withGE t (s.gasAvailable - UInt256.ofNat (C' s w)) (s.execLength + 1)) := by
  have hch := charged_eq_self hmc
  have h := xStepAt_of_step (f := f) hmem hhalt hdec (by rw [hch]; exact hZ) hstep
  rw [hch, hmc] at h
  have hsub : s.gasAvailable - UInt256.ofNat 0 = s.gasAvailable := by
    cases s.gasAvailable with | mk v =>
    show (⟨v - (UInt256.ofNat 0).val⟩ : UInt256) = ⟨v⟩
    have h : (UInt256.ofNat 0).val = 0 := rfl
    rw [h, sub_zero]
  rwa [hsub] at h

/-! ### `JUMPI` -/

@[simp] theorem memcost_JUMPI (s : EVM.State) : memoryExpansionCost s .JUMPI = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

@[simp] theorem C'_JUMPI (s : EVM.State) : C' s .JUMPI = GasConstants.Ghigh := by
  simp +decide [C']

theorem Z_JUMPI {vj : Array UInt256} {s : EVM.State} {d c : UInt256} {r : Stack UInt256}
    (hs : s.stack = d :: c :: r) (hgas : GasConstants.Ghigh ≤ s.gasAvailable.toNat)
    (hlen : r.length ≤ 1024)
    (hdest : c ≠ ⟨0⟩ → vj.contains d = true) :
    Z vj .JUMPI s = .ok (s, GasConstants.Ghigh) := by
  have hch : charged s .JUMPI = s := charged_eq_self (memcost_JUMPI s)
  have h := Z_of_facts vj .JUMPI s (d := 2) (a := 0)
    (by rw [memcost_JUMPI]; exact Nat.zero_le _)
    (by rw [hch, C'_JUMPI]; exact hgas) rfl rfl (by rw [hs]; simp)
    (by rw [hs]; simp only [List.length_cons]; omega)
    (fun h => absurd h (by decide))
    (fun _ hne => by
      rw [hs] at hne ⊢
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, ne_eq, Option.some.injEq] at hne
      simp [X.notIn, X.belongs, hdest hne])
    (by decide) (fun _ => by simp +decide [W]) (fun h => absurd h (by decide)) (by decide)
  rwa [hch, C'_JUMPI] at h

theorem step_JUMPI {s : EVM.State} {d c : UInt256} {r : Stack UInt256}
    (hs : s.stack = d :: c :: r) :
    EvmYul.step (τ := .EVM) .JUMPI none s
      = .ok { s with pc := if (c != ⟨0⟩) = true then d else s.pc + ⟨1⟩, stack := r } := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  simp only at hs
  subst hs
  rfl

/-- The derived `BEq` on `UInt256` is not registered as lawful; these two are
the facts the `JUMPI` branch needs. -/
theorem bne_zero_true (c : UInt256) (hc : c ≠ ⟨0⟩) : (c != ⟨0⟩) = true := by
  cases c with | mk v =>
  have hv : v ≠ (0 : Fin UInt256.size) := fun h => hc (by rw [h])
  show (!(v == (0 : Fin UInt256.size))) = true
  simp [hv]

theorem bne_zero_false (c : UInt256) (hc : c = ⟨0⟩) : (c != ⟨0⟩) = false := by
  subst hc
  show (!((0 : Fin UInt256.size) == (0 : Fin UInt256.size))) = false
  simp

theorem step_JUMPI_taken {s : EVM.State} {d c : UInt256} {r : Stack UInt256}
    (hs : s.stack = d :: c :: r) (hc : c ≠ ⟨0⟩) :
    EvmYul.step (τ := .EVM) .JUMPI none s = .ok { s with pc := d, stack := r } := by
  rw [step_JUMPI hs, if_pos (bne_zero_true c hc)]

theorem step_JUMPI_untaken {s : EVM.State} {d c : UInt256} {r : Stack UInt256}
    (hs : s.stack = d :: c :: r) (hc : c = ⟨0⟩) :
    EvmYul.step (τ := .EVM) .JUMPI none s = .ok { s with pc := s.pc + ⟨1⟩, stack := r } := by
  rw [step_JUMPI hs, if_neg (by rw [bne_zero_false c hc]; exact Bool.false_ne_true)]

/-- A taken `JUMPI`, as one `X` iteration. -/
theorem xStepAt_JUMPI_taken {vj : Array UInt256} {f : Nat} {s : EVM.State} {d c : UInt256}
    {r : Stack UInt256}
    (hdec : decodeAt s = (.JUMPI, none)) (hs : s.stack = d :: c :: r)
    (hc : c ≠ ⟨0⟩) (hdest : vj.contains d = true)
    (hgas : GasConstants.Ghigh ≤ s.gasAvailable.toNat) (hlen : r.length ≤ 1024) :
    XStepAt vj (f + 1) GasConstants.Ghigh s
      (withGE { s with pc := d, stack := r } (s.gasAvailable - UInt256.ofNat GasConstants.Ghigh)
        (s.execLength + 1)) := by
  have h := xStepAt_of_step_nomem (f := f) (by decide) (by decide) hdec (memcost_JUMPI s)
    (by rw [C'_JUMPI]; exact Z_JUMPI hs hgas hlen (fun _ => hdest)) (step_JUMPI_taken hs hc)
  rwa [C'_JUMPI] at h

/-- An untaken `JUMPI`, as one `X` iteration; no destination check is needed. -/
theorem xStepAt_JUMPI_untaken {vj : Array UInt256} {f : Nat} {s : EVM.State} {d c : UInt256}
    {r : Stack UInt256}
    (hdec : decodeAt s = (.JUMPI, none)) (hs : s.stack = d :: c :: r)
    (hc : c = ⟨0⟩)
    (hgas : GasConstants.Ghigh ≤ s.gasAvailable.toNat) (hlen : r.length ≤ 1024) :
    XStepAt vj (f + 1) GasConstants.Ghigh s
      (withGE { s with pc := s.pc + ⟨1⟩, stack := r }
        (s.gasAvailable - UInt256.ofNat GasConstants.Ghigh) (s.execLength + 1)) := by
  have h := xStepAt_of_step_nomem (vj := vj) (f := f) (by decide) (by decide) hdec (memcost_JUMPI s)
    (by rw [C'_JUMPI]; exact Z_JUMPI hs hgas hlen (fun h => absurd hc h))
    (step_JUMPI_untaken hs hc)
  rwa [C'_JUMPI] at h

/-! ### `SSTORE` -/

@[simp] theorem memcost_SSTORE (s : EVM.State) : memoryExpansionCost s .SSTORE = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

theorem C'_SSTORE (s : EVM.State) : C' s .SSTORE = Csstore s := rfl

/-- `SSTORE` never costs more than a cold store of a fresh nonzero value. -/
theorem Csstore_le (s : EVM.State) :
    Csstore s ≤ GasConstants.Gcoldsload + GasConstants.Gsset := by
  unfold Csstore
  obtain ⟨sh, pc, stk, ex⟩ := s
  dsimp only
  rcases hacc : Std.TreeMap.get! sh.accountMap sh.executionEnv.codeOwner with ⟨⟨nonce, bal, sto, code⟩, tst⟩
  dsimp only
  split <;> split_ifs <;>
    simp only [GasConstants.Gcoldsload, GasConstants.Gsset, GasConstants.Gwarmaccess,
      GasConstants.Gsreset] <;> omega

theorem Z_SSTORE {vj : Array UInt256} {s : EVM.State} {k v : UInt256} {r : Stack UInt256}
    (hs : s.stack = k :: v :: r) (hperm : s.executionEnv.perm = true)
    (hgas : GasConstants.Gcoldsload + GasConstants.Gsset ≤ s.gasAvailable.toNat)
    (hlen : r.length ≤ 1024) :
    Z vj .SSTORE s = .ok (s, Csstore s) := by
  have hch : charged s .SSTORE = s := charged_eq_self (memcost_SSTORE s)
  have hle := Csstore_le s
  have h := Z_of_facts vj .SSTORE s (d := 2) (a := 0)
    (by rw [memcost_SSTORE]; exact Nat.zero_le _)
    (by rw [hch, C'_SSTORE]; omega) rfl rfl (by rw [hs]; simp)
    (by rw [hs]; simp only [List.length_cons]; omega)
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (by decide) (fun h => absurd (h.symm.trans hperm) (by decide))
    (fun _ => by
      rw [hch]
      simp only [GasConstants.Gcallstipend, GasConstants.Gcoldsload, GasConstants.Gsset] at hgas ⊢
      omega)
    (by decide)
  rwa [hch, C'_SSTORE] at h

theorem step_SSTORE {s : EVM.State} {k v : UInt256} {r : Stack UInt256}
    (hs : s.stack = k :: v :: r) :
    EvmYul.step (τ := .EVM) .SSTORE none s
      = .ok (({ s with toState := s.toState.sstore k v } : EVM.State).replaceStackAndIncrPC r) := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  simp only at hs
  subst hs
  rfl

/-- One `SSTORE`, as one `X` iteration. Write permission is required: `X`
raises `StaticModeViolation` otherwise. -/
theorem xStepAt_SSTORE {vj : Array UInt256} {f : Nat} {s : EVM.State} {k v : UInt256}
    {r : Stack UInt256}
    (hdec : decodeAt s = (.SSTORE, none)) (hs : s.stack = k :: v :: r)
    (hperm : s.executionEnv.perm = true)
    (hgas : GasConstants.Gcoldsload + GasConstants.Gsset ≤ s.gasAvailable.toNat)
    (hlen : r.length ≤ 1024) :
    XStepAt vj (f + 1) (Csstore s) s
      (withGE (({ s with toState := s.toState.sstore k v } : EVM.State).replaceStackAndIncrPC r)
        (s.gasAvailable - UInt256.ofNat (Csstore s)) (s.execLength + 1)) :=
  xStepAt_of_step_nomem (f := f) (by decide) (by decide) hdec (memcost_SSTORE s)
    (Z_SSTORE hs hperm hgas hlen) (step_SSTORE hs)

/-! ### The memory writers: `MSTORE`, `MSTORE8`, `CALLDATACOPY`, `LOG0`

Their `Z` charge is the memory expansion `Cₘ (M aw off len) - Cₘ aw`, which
depends on the machine. The lemmas here take that charge symbolically, so that
a caller supplies one bound on it per site. -/

theorem C'_MSTORE (s : EVM.State) : C' s .MSTORE = GasConstants.Gverylow := by
  simp +decide [C']

theorem C'_MSTORE8 (s : EVM.State) : C' s .MSTORE8 = GasConstants.Gverylow := by
  simp +decide [C']

theorem C'_CALLDATACOPY (s : EVM.State) :
    C' s .CALLDATACOPY
      = GasConstants.Gverylow + GasConstants.Gcopy * (((s.stack[2]?.getD default).toNat + 31) / 32) := by
  simp +decide [C']

theorem C'_LOG0 (s : EVM.State) :
    C' s .LOG0 = GasConstants.Glog + GasConstants.Glogdata * (s.stack[1]?.getD default).toNat := by
  simp +decide [C']

theorem C'_RETURN (s : EVM.State) : C' s .RETURN = 0 := by
  simp +decide [C', GasConstants.Gzero]

theorem C'_REVERT (s : EVM.State) : C' s .REVERT = 0 := by
  simp +decide [C', GasConstants.Gzero]

theorem C'_STOP (s : EVM.State) : C' s .STOP = 0 := by
  simp +decide [C', GasConstants.Gzero]

@[simp] theorem memcost_STOP (s : EVM.State) : memoryExpansionCost s .STOP = 0 := by
  simp [memoryExpansionCost, memoryExpansionCost.μᵢ']

/-- The memory writers and the halts: `Z` accepts as soon as the two charges
are affordable, since none of them is a jump, a static-mode violation (except
`LOG0`, which needs permission) or a store. -/
theorem Z_memop {vj : Array UInt256} {w : Operation .EVM} {s : EVM.State} {d : Nat}
    (hw : w = .MSTORE ∨ w = .MSTORE8 ∨ w = .CALLDATACOPY ∨ w = .LOG0 ∨ w = .RETURN ∨ w = .REVERT)
    (hδ : δ w = some d) (hα : α w = some 0)
    (hlen : d ≤ s.stack.length) (hover : s.stack.length - d ≤ 1024)
    (hgas : memoryExpansionCost s w + C' (charged s w) w ≤ s.gasAvailable.toNat)
    (hperm : w = .LOG0 → s.executionEnv.perm = true) :
    Z vj w s = .ok (charged s w, C' (charged s w) w) := by
  have hg₁ : (charged s w).gasAvailable.toNat = s.gasAvailable.toNat - memoryExpansionCost s w :=
    toNat_sub_ofNat (by omega)
  refine Z_of_facts vj w s (d := d) (a := 0) (by omega) (by rw [hg₁]; omega) hδ hα hlen (by omega)
    ?_ ?_ ?_ ?_ ?_ ?_
  · rintro rfl; rcases hw with h | h | h | h | h | h <;> cases h
  · rintro rfl; rcases hw with h | h | h | h | h | h <;> cases h
  · rintro rfl; rcases hw with h | h | h | h | h | h <;> cases h
  · intro hp
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · simp +decide [W]
    · simp +decide [W]
    · simp +decide [W]
    · exact absurd (hp.symm.trans (hperm rfl)) (by decide)
    · simp +decide [W]
    · simp +decide [W]
  · rintro rfl; rcases hw with h | h | h | h | h | h <;> cases h
  · rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem step_MSTORE {s : EVM.State} {off v : UInt256} {r : Stack UInt256}
    (hs : s.stack = off :: v :: r) :
    EvmYul.step (τ := .EVM) .MSTORE none s
      = .ok (({ s with toMachineState := s.toMachineState.mstore off v } : EVM.State).replaceStackAndIncrPC r) := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  simp only at hs
  subst hs
  rfl

theorem step_MSTORE8 {s : EVM.State} {off v : UInt256} {r : Stack UInt256}
    (hs : s.stack = off :: v :: r) :
    EvmYul.step (τ := .EVM) .MSTORE8 none s
      = .ok (({ s with toMachineState := s.toMachineState.mstore8 off v } : EVM.State).replaceStackAndIncrPC r) := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  simp only at hs
  subst hs
  rfl

theorem step_CALLDATACOPY {s : EVM.State} {dst src len : UInt256} {r : Stack UInt256}
    (hs : s.stack = dst :: src :: len :: r) :
    EvmYul.step (τ := .EVM) .CALLDATACOPY none s
      = .ok (({ s with toSharedState := s.toSharedState.calldatacopy dst src len } : EVM.State).replaceStackAndIncrPC r) := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  simp only at hs
  subst hs
  rfl

theorem step_LOG0 {s : EVM.State} {off len : UInt256} {r : Stack UInt256}
    (hs : s.stack = off :: len :: r) :
    EvmYul.step (τ := .EVM) .LOG0 none s
      = .ok (({ s with toSharedState := SharedState.logOp off len #[] s.toSharedState } : EVM.State).replaceStackAndIncrPC r) := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  simp only at hs
  subst hs
  rfl

theorem step_RETURN {s : EVM.State} {off len : UInt256} {r : Stack UInt256}
    (hs : s.stack = off :: len :: r) :
    EvmYul.step (τ := .EVM) .RETURN none s
      = .ok (({ s with toMachineState := s.toMachineState.evmReturn off len } : EVM.State).replaceStackAndIncrPC r) := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  simp only at hs
  subst hs
  rfl

theorem step_REVERT {s : EVM.State} {off len : UInt256} {r : Stack UInt256}
    (hs : s.stack = off :: len :: r) :
    EvmYul.step (τ := .EVM) .REVERT none s
      = .ok (({ s with toMachineState := s.toMachineState.evmRevert off len } : EVM.State).replaceStackAndIncrPC r) := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  simp only at hs
  subst hs
  rfl

theorem step_STOP (s : EVM.State) :
    EvmYul.step (τ := .EVM) .STOP none s
      = .ok { s with toMachineState := s.toMachineState.setReturnData .empty } := rfl

/-! ### The halting instruction, for `RunUntil.X_success` / `X_revert`

A halt is the one iteration `X` does not continue through. What the
composition lemmas need is `Z`'s acceptance and the `StepOk` of the halt, in
the form `EvmYul.EVM.Proof.RunUntil.X_success` consumes. -/

/-- The halting step, at any fuel `f + 1`, from `Z`'s charged state. -/
theorem stepOk_halt {f : Nat} {w : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {s t : EVM.State} (hmem : w ∈ allOps)
    (hstep : EvmYul.step (τ := .EVM) w arg s = .ok t) :
    StepOk (f + 1) (C' (charged s w) w) (w, arg) (charged s w)
      (withGE t
        (s.gasAvailable - UInt256.ofNat (memoryExpansionCost s w)
          - UInt256.ofNat (C' (charged s w) w))
        (s.execLength + 1)) := by
  show EvmYul.EVM.step (f + 1) (C' (charged s w) w) (some (w, arg)) (charged s w) = .ok _
  rw [EVM_step_eq_step hmem, stepPre_eq_withGE]
  show EvmYul.step (τ := .EVM) w arg (withGE s _ _) = _
  rw [step_withGE hmem, hstep]
  rfl

/-! ## Fuel-polymorphic reachability

`XRuns vj (f + 1 + k) s tr (f + 1) s'` says `X` gets from `s` to `s'` in `k`
iterations, leaving `f + 1` units of fuel. Nothing along a straight path depends
on `f`, so the natural statement is for all `f` at once; that is what composes
across blocks, and it is instantiated at the very end with the call's fuel. -/

def Reaches (vj : Array UInt256) (k : Nat) (s s' : EVM.State) : Prop :=
  ∀ f, ∃ tr, XRuns vj (f + 1 + k) s tr (f + 1) s'

theorem Reaches.refl (vj : Array UInt256) (s : EVM.State) : Reaches vj 0 s s :=
  fun f => ⟨[], XRuns.refl (f + 1) s⟩

theorem Reaches.trans {vj : Array UInt256} {k k' : Nat} {s s' s'' : EVM.State}
    (h₁ : Reaches vj k s s') (h₂ : Reaches vj k' s' s'') : Reaches vj (k + k') s s'' := by
  intro f
  obtain ⟨tr₂, h₂⟩ := h₂ f
  obtain ⟨tr₁, h₁⟩ := h₁ (f + k')
  rw [show f + k' + 1 + k = f + 1 + (k + k') by omega,
    show f + k' + 1 = f + 1 + k' by omega] at h₁
  exact ⟨_, h₁.trans h₂⟩

theorem Reaches.of_stepAt {vj : Array UInt256} {c : Nat} {s s' : EVM.State}
    (h : ∀ f, XStepAt vj (f + 1) c s s') : Reaches vj 1 s s' :=
  fun f => ⟨_, XRuns.cons (h f) (XRuns.refl (f + 1) s')⟩

/-- A listed block, as a `Reaches`. -/
theorem Reaches.of_symBlock {vj : Array UInt256} {vjNats : List Nat}
    (hvj : ∀ n ∈ vjNats, vj.contains (UInt256.ofNat n) = true)
    {code : ByteArray} (sites : List Site) (hsites : sitesOk code sites = true)
    {s s' : EVM.State}
    (hcode : s.executionEnv.code = code) (hpc : s.pc = UInt256.ofNat (headPc sites))
    (hgas : blockBound sites ≤ s.gasAvailable.toNat)
    (hlen : s.stack.length + sites.length ≤ 1024)
    (hsym : symBlock vjNats (sites.map Prod.snd) s = some s') :
    ∃ g' e', s.gasAvailable.toNat - blockBound sites ≤ g'.toNat ∧
      Reaches vj sites.length s (withGE s' g' e') :=
  xRuns_symBlock hvj sites hsites hcode hpc hgas hlen hsym

/-- Instantiating the fuel: a call with at least `k + 1` units of fuel runs the
whole path and stops with fuel to spare. -/
theorem Reaches.xRuns_of_fuel {vj : Array UInt256} {k : Nat} {s s' : EVM.State}
    (h : Reaches vj k s s') {fuel : Nat} (hfuel : k + 1 ≤ fuel) :
    ∃ tr rem, XRuns vj fuel s tr (rem + 1) s' := by
  obtain ⟨tr, hrun⟩ := h (fuel - k - 1)
  rw [show fuel - k - 1 + 1 + k = fuel by omega] at hrun
  exact ⟨tr, fuel - k - 1, hrun⟩

/-! ## Jump tables as `Nat` lists -/

theorem beq_self_uint (x : UInt256) : (x == x) = true := by
  cases x with | mk v => exact beq_self_eq_true v

end Eip8282.Audit.SymExec
