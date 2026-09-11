import Eip8282.Audit.Integrator.ProtocolCreditEnvelope

/-! Source-transcribed Amsterdam SSTORE gas classification, EL commit
0cc100eb190b64b23baba72dac0165652eaec252. Cached vm/instructions/storage.py
SHA256 d355855a1c50212a4e4753abb533c338919103635755da13bc1e154fcb3ed11b,
lines80-170; vm/gas.py SHA256
41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c,
lines49-113,389-447,604-626. Signed refunds and state-refund order are retained.
This audited transcription is not an equation with an actual Python evaluator.
Stack pops, state reads/writes and access-set mutation require separate adapters.
No reference trace, global progress or protocol adoption is asserted. -/
namespace Eip8282.Audit.Integrator.ReferenceStorageGas
open EvmYul
set_option autoImplicit false

structure Charge where
  access : Nat
  sentry : Nat
  execution : Nat
  state : Nat
  refundDelta : Int
  stateRefund : Nat
  deriving DecidableEq, Repr

def classify (warm : Bool) (original current new : UInt256) : Charge :=
  let access := if warm then 100 else 2100
  let first := original = current ∧ current ≠ new
  let changed := current ≠ new
  { access := access, sentry := max access 2301,
    execution := access + (if first then 10000 else 0),
    state := if first ∧ original = ⟨0⟩ then 97920 else 0,
    refundDelta :=
      (if changed ∧ original ≠ ⟨0⟩ ∧ current ≠ ⟨0⟩ ∧ new = ⟨0⟩ then 11616 else 0) -
      (if changed ∧ original ≠ ⟨0⟩ ∧ current = ⟨0⟩ then 11616 else 0) +
      (if changed ∧ original = new then 10000 else 0),
    stateRefund := if changed ∧ original = new ∧ original = ⟨0⟩ then 97920 else 0 }

theorem charge_bounds (warm : Bool) (original current new : UInt256) :
    (classify warm original current new).execution ≤ 12100 ∧
    (classify warm original current new).state ≤ 97920 ∧
    (classify warm original current new).sentry = 2301 := by
  cases warm <;> simp only [classify, Bool.false_eq_true, ↓reduceIte]
  all_goals split <;> split <;> norm_num

structure Meter where
  execution : Nat
  reservoir : Nat
  spill : Nat
  refund : Int
  deriving DecidableEq, Repr

/-- Source LIFO state refund: execution spill is restored first. -/
def creditState (m : Meter) (amount : Nat) : Meter :=
  let restored := min amount m.spill
  { m with
    execution := m.execution + restored
    spill := m.spill - restored
    reservoir := m.reservoir + (amount-restored) }

def chargeExecution (m : Meter) (amount : Nat) : Option Meter :=
  if amount ≤ m.execution then some {m with execution := m.execution-amount} else none

/-- Reservoir first, then execution spill; includes the actual exhaustion branch. -/
def chargeState (m : Meter) (amount : Nat) : Option Meter :=
  if amount ≤ m.reservoir then some {m with reservoir := m.reservoir-amount}
  else if amount ≤ m.reservoir+m.execution then
    some {m with
      reservoir := 0
      execution := m.execution-(amount-m.reservoir)
      spill := m.spill+(amount-m.reservoir)}
  else none

/-- The source's static rejection and sentry precede state-dependent pricing.
Input original/current values represent subsequent reads, not pre-sentry effects. -/
def storageCharge (isStatic warm : Bool) (original current new : UInt256)
    (m : Meter) : Option Meter :=
  let c := classify warm original current new
  if isStatic then none
  else if c.sentry ≤ m.execution then
    let credited := creditState {m with refund := m.refund+c.refundDelta} c.stateRefund
    (chargeExecution credited c.execution).bind (fun charged => chargeState charged c.state)
  else none

/-- A per-class resource condition proves success in the literal charge order.
No state refund or execution-refund credit is needed in these hypotheses. -/
theorem funded_success (warm : Bool) (original current new : UInt256) (m : Meter)
    (hs : (classify warm original current new).sentry ≤ m.execution)
    (he : (classify warm original current new).execution ≤ m.execution)
    (hr : (classify warm original current new).state ≤ m.reservoir) :
    ∃ post, storageCharge false warm original current new m = some post ∧
      m.execution-(classify warm original current new).execution ≤ post.execution ∧
      m.reservoir-(classify warm original current new).state ≤ post.reservoir := by
  unfold storageCharge
  simp only [Bool.false_eq_true, ↓reduceIte, hs]
  unfold creditState chargeExecution
  rw [if_pos (by dsimp; omega)]
  simp only [Option.bind_some]
  unfold chargeState
  rw [if_pos (by dsimp; omega)]
  exact ⟨_,rfl,by dsimp; omega,by dsimp; omega⟩

theorem conservative_success (warm : Bool) (original current new : UInt256) (m : Meter)
    (he : 12100 ≤ m.execution) (hr : 97920 ≤ m.reservoir) :
    ∃ post, storageCharge false warm original current new m = some post ∧
      m.execution-12100 ≤ post.execution ∧ m.reservoir-97920 ≤ post.reservoir := by
  obtain ⟨hb,hst,hse⟩ := charge_bounds warm original current new
  obtain ⟨post,hp,hpe,hpr⟩ := funded_success warm original current new m
    (by omega) (by omega) (by omega)
  exact ⟨post,hp,by omega,by omega⟩

theorem static_rejects (warm : Bool) (original current new : UInt256) (m : Meter) :
    storageCharge true warm original current new m = none := rfl

#print axioms charge_bounds
#print axioms funded_success
#print axioms conservative_success
#print axioms static_rejects
end Eip8282.Audit.Integrator.ReferenceStorageGas
