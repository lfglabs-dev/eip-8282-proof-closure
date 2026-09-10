import Eip8282.Audit.Integrator.ReferenceMeterRollback

/-! Source-shaped child meters at protected-runtime boundaries, independent of
any claimed equivalence of foreign bytecode interpreters. EL commit
0cc100eb190b64b23baba72dac0165652eaec252: vm/__init__.py:193-249
SHA664702bc483736fca3c4ac4bb9e459a24c83f5365b495485c4674d5c41fbe993;
vm/interpreter.py:455-474 SHA8281535f92be8cfe663033716baf9418ffc37b6c8861f70ac357e41fb6cf4c82;
vm/gas.py:629-674 SHA41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c.
Full bodies are archived in audit/receipts/direct-reference-memory-control-sources-20260910.json
and direct-reference-admission-sources-20260910.json. Source snapshot/journal,
actual grants (including CALL stipend), admission and frame extraction remain
separate obligations. The arithmetic below is audited transcription, not Python
execution. No parent/child grant conservation is assumed or claimed. -/
namespace Eip8282.Audit.Integrator.ReferenceChildMeter
open ReferenceMeterRollback
set_option autoImplicit false

def init (execution reservoir : Nat) : Meter :=
  {execution := execution
   reservoir := reservoir
   baseline := reservoir
   spill := 0
   committedSpill := 0
   refund := 0}

inductive Outcome where
  | success | reverted | exceptional
  deriving DecidableEq, Repr

/-- Exceptional execution forfeiture follows ordinary state-gas restoration.
Its source spill=0 assertion is discharged by restore, never omitted as input. -/
def settle : Outcome → Meter → Meter
  | .success, m => m
  | .reverted, m => restore m
  | .exceptional, m => {restore m with execution := 0}

def repay (m : Meter) : Meter :=
  let paid := min m.reservoir m.spill
  {m with
    execution := m.execution+paid
    reservoir := m.reservoir-paid
    spill := m.spill-paid}

def absorb (parent child : Meter) : Meter :=
  {parent with
    execution := parent.execution+child.execution
    reservoir := parent.reservoir+child.reservoir
    spill := parent.spill+child.spill
    refund := parent.refund+child.refund}

/-- Literal assertions precede the unconditional core-meter absorption.
Only a successful child triggers repayment of outstanding parent spill. -/
def incorporate (parent child : Meter) (failed : Bool) : Option Meter :=
  if child.committedSpill = 0 ∧
      (failed = true → child.spill = 0 ∧ child.refund = 0 ∧ child.reservoir = child.baseline) then
    some (if failed then absorb parent child else repay (absorb parent child))
  else none

theorem init_fields (execution reservoir : Nat) :
    (init execution reservoir).baseline = reservoir ∧
    (init execution reservoir).spill = 0 ∧
    (init execution reservoir).committedSpill = 0 ∧
    (init execution reservoir).refund = 0 ∧
    netUsed reservoir (init execution reservoir) = 0 := by
  simp [init,netUsed]

theorem settled_failure_guards (m : Meter) (outcome : Outcome)
    (failed : outcome ≠ .success) (committed : m.committedSpill = 0) :
    (settle outcome m).committedSpill = 0 ∧
    (settle outcome m).spill = 0 ∧ (settle outcome m).refund = 0 ∧
    (settle outcome m).reservoir = (settle outcome m).baseline ∧
    (outcome = .exceptional → (settle outcome m).execution = 0) := by
  cases outcome <;> simp_all [settle,restore]

/-- The exceptional forfeiture precondition follows from the preceding restore. -/
theorem exceptional_order (m : Meter) :
    (restore m).spill = 0 ∧
    settle .exceptional m = {restore m with execution := 0} := ⟨rfl,rfl⟩

/-- Successful-child repayment moves gas between pools, preserving their sum
and signed state usage. The source post-assertion is derived from min. -/
theorem repay_accounting (m : Meter) (grant : Nat) :
    pools (repay m) = pools m ∧ netUsed grant (repay m) = netUsed grant m ∧
    ((repay m).reservoir = 0 ∨ (repay m).spill = 0) ∧
    (repay m).baseline = m.baseline ∧
    (repay m).committedSpill = m.committedSpill ∧ (repay m).refund = m.refund := by
  simp [repay,pools,netUsed]
  omega

/-- Exact successful incorporation, with the child assertions exposed again
as consequences. The signed child term is not an assumed grant split. -/
theorem incorporate_accounting {parent child post : Meter} {failed : Bool}
    (h : incorporate parent child failed = some post) (grant : Nat) :
    child.committedSpill = 0 ∧
    (failed = true → child.spill = 0 ∧ child.refund = 0 ∧ child.reservoir = child.baseline) ∧
    pools post = pools parent+pools child ∧
    netUsed grant post-netUsed grant parent = netUsed 0 child ∧
    post.baseline = parent.baseline ∧ post.committedSpill = parent.committedSpill ∧
    post.refund = parent.refund+child.refund := by
  unfold incorporate at h
  split at h
  · rename_i guard
    refine ⟨guard.1,guard.2,?_⟩
    cases failed with
    | true =>
      simp only [↓reduceIte,Option.some.injEq] at h
      subst post
      simp [absorb,pools,netUsed,guard.1]
      omega
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte,Option.some.injEq] at h
      subst post
      have hp := repay_accounting (absorb parent child) grant
      simp only [absorb,pools,netUsed] at hp ⊢
      simp only [guard.1] at hp ⊢
      omega
  · contradiction

/-- A failed child is absorbed without successful-child spill repayment. -/
theorem failed_incorporation (parent child : Meter)
    (committed : child.committedSpill = 0) (spill : child.spill = 0)
    (refund : child.refund = 0) (baseline : child.reservoir = child.baseline) :
    incorporate parent child true = some (absorb parent child) ∧
    (absorb parent child).spill = parent.spill ∧
    (absorb parent child).refund = parent.refund := by
  simp [incorporate,absorb,committed,spill,refund,baseline]

#print axioms init_fields
#print axioms settled_failure_guards
#print axioms exceptional_order
#print axioms repay_accounting
#print axioms incorporate_accounting
#print axioms failed_incorporation
end Eip8282.Audit.Integrator.ReferenceChildMeter
