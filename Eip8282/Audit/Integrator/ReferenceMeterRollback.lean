import Eip8282.Audit.Integrator.ReferenceStorageGas

/-! Literal source-shaped frame meter and rollback accounting. Amsterdam EL
0cc100eb190b64b23baba72dac0165652eaec252 vm/gas.py:270-337,469-601,
SHA256 41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c,
archived in audit/receipts/direct-reference-admission-sources-20260910.json.
Source assertions are explicit Option guards. State quantities are nonnegative
unbounded Uint values; signed net usage is deliberately not truncated.
This is arithmetic of an audited transcription, not a Python execution proof
or a relation to an actual nested frame, storage snapshot or refund provenance.
The existing simplified payment Meter is unchanged. -/
namespace Eip8282.Audit.Integrator.ReferenceMeterRollback
set_option autoImplicit false

structure Meter where
  execution : Nat
  reservoir : Nat
  baseline : Nat
  spill : Nat
  committedSpill : Nat
  refund : Int
  deriving DecidableEq, Repr

def pools (m : Meter) : Int := (m.execution : Int)+m.reservoir

/-- The expression returned by tx_state_gas_used, before its baseline assertion. -/
def netUsed (grant : Nat) (m : Meter) : Int :=
  (grant : Int)-m.reservoir+m.spill+m.committedSpill

def checkedNetUsed (grant : Nat) (m : Meter) : Option Int :=
  if m.baseline ≤ grant then some (netUsed grant m) else none

def commit (m : Meter) : Option Meter :=
  if m.reservoir ≤ m.baseline then
    some {m with
      committedSpill := m.committedSpill+m.spill
      baseline := m.reservoir
      spill := 0}
  else none

def restore (m : Meter) : Meter :=
  {m with
    execution := m.execution+m.spill
    spill := 0
    reservoir := m.baseline
    refund := 0}

def restoreToEntry (grant : Nat) (m : Meter) : Option Meter :=
  if m.baseline ≤ grant ∧ m.refund = 0 then
    some {m with
      execution := m.execution+m.spill+m.committedSpill
      spill := 0
      committedSpill := 0
      reservoir := grant
      baseline := grant}
  else none

/-- Source commit guards preserve signed usage, both spendable pools and refund.
The committed amount remains charged by ordinary rollback. -/
theorem commit_accounting (m : Meter) (grant : Nat)
    (guard : m.reservoir ≤ m.baseline) :
    ∃ post, commit m = some post ∧
      netUsed grant post = netUsed grant m ∧ pools post = pools m ∧
      post.baseline ≤ m.baseline ∧ post.committedSpill = m.committedSpill+m.spill ∧
      post.spill = 0 ∧ post.refund = m.refund := by
  refine ⟨_,if_pos guard,?_,rfl,guard,rfl,rfl,rfl⟩
  simp only [netUsed]
  omega

/-- Ordinary rollback restores only state gas since the baseline. The signed
pool change is exact even for hypothetical inputs whose reservoir exceeds it. -/
theorem restore_accounting (m : Meter) (grant : Nat) :
    netUsed grant (restore m) = (grant : Int)-m.baseline+m.committedSpill ∧
    pools (restore m)-pools m = netUsed grant m-netUsed grant (restore m) ∧
    (restore m).execution = m.execution+m.spill ∧
    (restore m).reservoir = m.baseline ∧ (restore m).spill = 0 ∧
    (restore m).committedSpill = m.committedSpill ∧ (restore m).refund = 0 := by
  simp [restore,netUsed,pools]
  omega

/-- The baseline guard gives nonnegative usage after ordinary rollback;
nonnegativity of arbitrary pre-rollback frames is not asserted. -/
theorem restore_nonnegative (m : Meter) (grant : Nat) (guard : m.baseline ≤ grant) :
    checkedNetUsed grant (restore m) = some (netUsed grant (restore m)) ∧
    0 ≤ netUsed grant (restore m) := by
  constructor
  · exact if_pos guard
  · have h := (restore_accounting m grant).1
    omega

/-- Predispatch rollback also undoes committed state gas. Its source assertion
that no refund accrued is retained, not inferred from a desired final state. -/
theorem entry_accounting (m : Meter) (grant : Nat)
    (baseline : m.baseline ≤ grant) (refund : m.refund = 0) :
    ∃ post, restoreToEntry grant m = some post ∧
      checkedNetUsed grant post = some 0 ∧
      pools post-pools m = netUsed grant m ∧
      post.execution = m.execution+m.spill+m.committedSpill ∧
      post.reservoir = grant ∧ post.baseline = grant ∧
      post.spill = 0 ∧ post.committedSpill = 0 ∧ post.refund = 0 := by
  refine ⟨_,if_pos ⟨baseline,refund⟩,?_,?_,rfl,rfl,rfl,rfl,rfl,refund⟩
  · simp [checkedNetUsed,netUsed]
  · simp only [pools,netUsed]
    omega

#print axioms commit_accounting
#print axioms restore_accounting
#print axioms restore_nonnegative
#print axioms entry_accounting
end Eip8282.Audit.Integrator.ReferenceMeterRollback
