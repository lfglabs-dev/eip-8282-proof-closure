import Eip8282.Audit.Integrator.EndpointState
import Eip8282.Audit.Integrator.CallBridge
import Eip8282.Audit.EntryReach.FeeQuote
import Eip8282.Audit.EntryReach.Words

/-!
# Complete message-call fee getters

These conditional success theorems consume a completed operational fee quote
and explicit gas/fuel bounds. They do not assume a successful call or a
post-state agreement. They publish the actual quoted word as 32 bytes and
preserve every account lookup and the existing logs across Θ, including its
value-transfer layer and empty-world fallback. Existence of a completed word
quote and protocol resource bounds remain separate obligations.
-/

namespace Eip8282.Audit.Integrator.GetterCall

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport
open Eip8282.Audit.Correspondence (runtimeCode)
open Eip8282.Audit.Integrator.MessageCall
open Eip8282.Audit.Integrator.CallBridge

private theorem word_add_zero (w : UInt256) : w + UInt256.ofNat 0 = w := by
  cases w with
  | mk v =>
      change UInt256.mk (v + 0) = UInt256.mk v
      rw [add_zero]

private theorem word_sub_zero (w : UInt256) : w - UInt256.ofNat 0 = w := by
  cases w with
  | mk v =>
      change UInt256.mk (v - 0) = UInt256.mk v
      rw [sub_zero]

private theorem credit_zero (a : Account .EVM) :
    { a with balance := a.balance + UInt256.ofNat 0 } = a := by
  rw [word_add_zero]

private theorem debit_zero (a : Account .EVM) :
    { a with balance := a.balance - UInt256.ofNat 0 } = a := by
  rw [word_sub_zero]

/-- Reinserting an existing value need not produce the same tree shape, but
it preserves every observable account lookup. -/
private theorem lookup_insert_same {world : AccountMap .EVM}
    {key : AccountAddress} {a : Account .EVM}
    (h : world.get? key = some a) (address : AccountAddress) :
    (world.insert key a).get? address = world.get? address := by
  change (world.insert key a)[address]? = world[address]?
  rw [Std.TreeMap.getElem?_insert]
  by_cases he : compare key address = .eq
  · have hk : key = address := Std.LawfulEqOrd.compare_eq_iff_eq.mp he
    subst address
    simpa using h.symm
  · simp only [he, ↓reduceIte]

private def reinsert (world : AccountMap .EVM) (key : AccountAddress) : AccountMap .EVM :=
  match world.get? key with
  | none => world
  | some a => world.insert key a

private theorem lookup_reinsert (world : AccountMap .EVM) (key address : AccountAddress) :
    (reinsert world key).get? address = world.get? address := by
  unfold reinsert
  cases h : world.get? key with
  | none => rfl
  | some a => exact lookup_insert_same h address

/-- Θ's actual credit-then-debit operation with zero value preserves all
account observations, including the caller=target and missing-account cases. -/
theorem entryWorld_zero_lookup (c : Context) (hv : c.value = UInt256.ofNat 0)
    (address : AccountAddress) : c.entryWorld.get? address = c.world.get? address := by
  have he : c.entryWorld = reinsert (reinsert c.world c.target) c.caller := by
    unfold Context.entryWorld reinsert
    rw [hv]
    simp only [credit_zero, debit_zero,
      show (UInt256.ofNat 0 != UInt256.ofNat 0) = false by decide,
      Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [he]
  exact (lookup_reinsert _ _ _).trans (lookup_reinsert _ _ _)

/-- Exact byte encoding of the operational price, independent of prior memory. -/
theorem getter_bytes (memory : ByteArray) (price : UInt256) :
    (mstoreMem memory (UInt256.ofNat 0) price).readWithPadding 0 32 = price.toByteArray := by
  unfold mstoreMem
  change (ByteArray.write price.toByteArray 0 memory 0 32).readWithPadding 0 32 = _
  rw [ByteArray.readWithPadding_write_self_of_pad _ _ _ _ (by norm_num) (by norm_num)
    (UInt256.size_toByteArray price) (by simp)]

/-- Observable success of a quote: exact 32-byte price, unchanged account
lookups (therefore balances, code, storage and transient storage), unchanged
created accounts and log series. Gas and access bookkeeping may change. -/
def ReturnsQuote (c : Context) (price : UInt256) : Prop :=
  ∃ (world : AccountMap .EVM) (gas : UInt256) (substate : Substate),
    c.result = .ok (c.created, world, gas, substate, true, price.toByteArray) ∧
    (∀ address, world.get? address = c.world.get? address) ∧
    substate.logSeries = c.substate.logSeries

/-- Settlement preserves a zero-value getter's observations in either branch
of Θ's empty-world fallback. No nonempty-world premise is necessary. -/
theorem settles_getter (c : Context) {kind : Model.Kind}
    (hcode : c.code = runtimeCode kind) (steps : Nat) (hf : c.fuel = steps + 1)
    (hv : c.value = UInt256.ofNat 0) (price gas : UInt256) (substate : Substate)
    (hr : (codeCall c hcode steps).result =
      .ok (.success (c.created, c.entryWorld, gas, substate) price.toByteArray))
    (hlogs : substate.logSeries = c.substate.logSeries) : ReturnsQuote c price := by
  have h := result_eq_codeCall_settlement c hcode steps hf
  rw [hr] at h
  by_cases he : (c.entryWorld == ∅) = true
  · refine ⟨c.world, gas, c.substate, ?_, fun _ => rfl, rfl⟩
    simpa only [Context.settle, he, Bool.false_eq_true, ↓reduceIte] using h
  · refine ⟨c.entryWorld, gas, substate, ?_, entryWorld_zero_lookup c hv, hlogs⟩
    simpa only [Context.settle, he, Bool.false_eq_true, ↓reduceIte] using h

private theorem quote_initial (X : UInt256) (n : Nat) :
    feeExit X n (UInt256.ofNat 0) (UInt256.ofNat 17 * UInt256.ofNat 1)
      (UInt256.ofNat 1) = feeExit X n ⟨0⟩ (UInt256.ofNat 17) (UInt256.ofNat 1) := by
  rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
    show UInt256.ofNat 17 * UInt256.ofNat 1 = UInt256.ofNat 17 by decide]

/-- Deposit getter through actual Θ settlement, with the completed word price
and explicit sufficient resources. No mathematical-fee or success premise. -/
theorem deposit_getter (c : Context) (hcode : c.code = runtimeCode .deposit)
    (steps : Nat) (hf : c.fuel = steps + 1)
    (huser : c.caller ≠ EvmRunner.sysAddr)
    (hen : Deposit.excessWord (codeCall c hcode steps) ≠ INH)
    (hv : c.value = UInt256.ofNat 0) (hactual : c.apparentValue = c.value)
    (hdata : c.calldata.size = 0) {n : Nat} {price : UInt256}
    (hq : quoteWithin (Deposit.effExcess (codeCall c hcode steps)) n = some price)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) (hsteps : 24 * n + 82 ≤ steps) :
    ReturnsQuote c price := by
  let q := codeCall c hcode steps
  obtain ⟨o, i, hloop, hprice⟩ := quoteWithin_eq_some_iff.mp hq
  have hfee : Deposit.FeeLoopEnds q n o i := by
    simpa only [Deposit.FeeLoopEnds, quote_initial] using hloop
  have hu : Deposit.callerWord q ≠ sysW := by
    intro h
    exact huser ((callerW_eq_sysW_iff q).mp h)
  have hsize : Deposit.cdsizeWord q = ⟨0⟩ := by
    change UInt256.ofNat c.calldata.size = _
    rw [hdata]
    rfl
  have hval : Deposit.valueWord q = ⟨0⟩ := by
    change c.apparentValue = _
    rw [hactual, hv]
    rfl
  obtain ⟨gas, substate, hr, hl⟩ :=
    EndpointState.deposit_getter_preserves_state q hu hen hfee hsize hval hg hsteps
  change price = Deposit.feeWord o at hprice
  rw [getter_bytes, ← hprice] at hr
  exact settles_getter c hcode steps hf hv price gas substate hr hl

/-- The same complete-message-call result for the exit getter. -/
theorem exit_getter (c : Context) (hcode : c.code = runtimeCode .exit)
    (steps : Nat) (hf : c.fuel = steps + 1)
    (huser : c.caller ≠ EvmRunner.sysAddr)
    (hen : Exit.excessWord (codeCall c hcode steps) ≠ INH)
    (hv : c.value = UInt256.ofNat 0) (hactual : c.apparentValue = c.value)
    (hdata : c.calldata.size = 0) {n : Nat} {price : UInt256}
    (hq : quoteWithin (Exit.effExcess (codeCall c hcode steps)) n = some price)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) (hsteps : 24 * n + 82 ≤ steps) :
    ReturnsQuote c price := by
  let q := codeCall c hcode steps
  obtain ⟨o, i, hloop, hprice⟩ := quoteWithin_eq_some_iff.mp hq
  have hfee : Exit.FeeLoopEnds q n o i := by
    simpa only [Exit.FeeLoopEnds, quote_initial] using hloop
  have hu : Exit.callerWord q ≠ sysW := by
    intro h
    exact huser ((callerW_eq_sysW_iff q).mp h)
  have hsize : Exit.cdsizeWord q = ⟨0⟩ := by
    change UInt256.ofNat c.calldata.size = _
    rw [hdata]
    rfl
  have hval : Exit.valueWord q = ⟨0⟩ := by
    change c.apparentValue = _
    rw [hactual, hv]
    rfl
  obtain ⟨gas, substate, hr, hl⟩ :=
    EndpointState.exit_getter_preserves_state q hu hen hfee hsize hval hg hsteps
  change price = Exit.feeWord o at hprice
  rw [getter_bytes, ← hprice] at hr
  exact settles_getter c hcode steps hf hv price gas substate hr hl

#print axioms entryWorld_zero_lookup
#print axioms settles_getter
#print axioms deposit_getter
#print axioms exit_getter

end Eip8282.Audit.Integrator.GetterCall
