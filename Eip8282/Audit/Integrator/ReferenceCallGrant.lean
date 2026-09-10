import Eip8282.Audit.Integrator.ReferenceMeterBoundary

/-! Amsterdam CALL gas is split AFTER access/value/memory/delegation execution
charges and any new-account state charge. EL0cc100eb gas.py809-872 and
instructions/system.py480-566 (archived pinned source bodies). The value stipend
is explicit; a grant split alone does not conserve execution gas. This module
transcribes resource operations, not source state reads or an outer call trace. -/
namespace Eip8282.Audit.Integrator.ReferenceCallGrant
open EvmYul ReferenceMeterRollback ReferenceMeterBoundary
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Source max_message_call_gas: retain one sixty-fourth, rounded down. -/
def maximum (gas : Nat) : Nat := gas-gas/64

def stipend (hasValue : Bool) : Nat := if hasValue then 2300 else 0

def executionCost (cold delegated delegationCold hasValue : Bool) (memoryCost : Nat) : Nat :=
  (if cold then 3000 else 100)+(if hasValue then 11300 else 0)+memoryCost+
    (if delegated then (if delegationCold then 3000 else 100) else 0)

def stateCost (hasValue deadRecipient : Bool) : Nat :=
  if hasValue && deadRecipient then 183600 else 0

/-- Literal ordered payments. Source checks before state reads and creation
predicate extraction must still be supplied by the outer operational adapter. -/
def prepare (cold delegated delegationCold hasValue deadRecipient : Bool)
    (memoryCost : Nat) (m : Meter) : Option Meter :=
  ((ReferenceStorageGas.chargeExecution (core m)
      (executionCost cold delegated delegationCold hasValue memoryCost)).bind
    (fun charged => ReferenceStorageGas.chargeState charged (stateCost hasValue deadRecipient))).map (update m)

structure Split where
  parent : Meter
  childExecution : Nat
  childState : Nat
  withheld : Nat

/-- The whole remaining state reservoir goes to the child. Its execution
stipend is included in the grant but not in the withheld share. -/
def split (hasValue : Bool) (requested : UInt256) (charged : Meter) : Split :=
  let withheld := min requested.toNat (maximum charged.execution)
  {parent := {charged with execution := charged.execution-withheld,reservoir := 0},
   childExecution := withheld+stipend hasValue,
   childState := charged.reservoir,
   withheld := withheld}

theorem split_accounting (hasValue : Bool) (requested : UInt256) (charged : Meter) :
    (split hasValue requested charged).withheld ≤ charged.execution ∧
    (split hasValue requested charged).parent.execution ≥ charged.execution/64 ∧
    (split hasValue requested charged).parent.reservoir = 0 ∧
    (split hasValue requested charged).childState = charged.reservoir ∧
    pools (split hasValue requested charged).parent+
      (split hasValue requested charged).childExecution+(split hasValue requested charged).childState =
      pools charged+stipend hasValue := by
  simp [split,maximum,pools]
  omega

private theorem prepared_cost {cold delegated delegationCold hasValue deadRecipient : Bool}
    {memoryCost : Nat} {pre post : Meter}
    (h : prepare cold delegated delegationCold hasValue deadRecipient memoryCost pre = some post) :
    pools pre-pools post = (executionCost cold delegated delegationCold hasValue memoryCost : Int)+
      stateCost hasValue deadRecipient := by
  unfold prepare at h
  cases he : ReferenceStorageGas.chargeExecution (core pre)
      (executionCost cold delegated delegationCold hasValue memoryCost) with
  | none => simp only [he,Option.bind_none,Option.map_none] at h; contradiction
  | some middle =>
    simp only [he,Option.bind_some] at h
    unfold ReferenceStorageGas.chargeExecution at he
    split at he
    · cases he
      unfold ReferenceStorageGas.chargeState at h
      split at h
      · simp only [Option.map_some,Option.some.injEq] at h
        subst post
        simp only [pools,core,update] at *
        omega
      · split at h
        · simp only [Option.map_some,Option.some.injEq] at h
          subst post
          simp only [pools,core,update] at *
          omega
        · contradiction
    · contradiction

/-- Prior CALL_VALUE includes 9000 execution gas plus the 2300 stipend.
Even after the stipend is handed to a child, that complete opcode prefix
cannot increase available pools. Actual source grant values are input-computed. -/
theorem charged_split {cold delegated delegationCold hasValue deadRecipient : Bool}
    {memoryCost : Nat} {pre charged : Meter}
    (h : prepare cold delegated delegationCold hasValue deadRecipient memoryCost pre = some charged)
    (requested : UInt256) :
    pools pre-(pools (split hasValue requested charged).parent+
      (split hasValue requested charged).childExecution+(split hasValue requested charged).childState) =
      (executionCost cold delegated delegationCold hasValue memoryCost : Int)+stateCost hasValue deadRecipient-
        stipend hasValue ∧
    pools (split hasValue requested charged).parent+
      (split hasValue requested charged).childExecution+(split hasValue requested charged).childState ≤ pools pre := by
  have paid := prepared_cost h
  have granted := (split_accounting hasValue requested charged).2.2.2.2
  have cost : stipend hasValue ≤ executionCost cold delegated delegationCold hasValue memoryCost := by
    cases hasValue <;> simp only [stipend,executionCost,Bool.false_eq_true,↓reduceIte] <;> omega
  omega

#print axioms split_accounting
#print axioms charged_split
end Eip8282.Audit.Integrator.ReferenceCallGrant
