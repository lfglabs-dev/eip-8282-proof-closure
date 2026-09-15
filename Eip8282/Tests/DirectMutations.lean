import Eip8282.Tests.MutationReceipts
import Eip8282.Audit.Integrator.SystemSpec

/-! Read an existing finite receipt's actual published storage. -/
namespace Eip8282.Tests.DirectMutations
open EvmYul EvmYul.EVM
open Eip8282.Audit.EvmRunner
open Eip8282.Audit.Integrator.SystemSpec (worldSlot)

private theorem word_eq_of_beq {a b : UInt256} (h : (a == b) = true) : a = b := by
  cases a with | mk a =>
  cases b with | mk b =>
  have he : a = b := beq_iff_eq.mp h
  cases he
  rfl

/-- The old Boolean storage observation reads the actual published world; this
bridge does not replace a missing world with a constructed expected one. -/
theorem worldSlot_of_receipt {r : RunResult} {created world gas substate out}
    (hr : r = .ok (.success (created, world, gas, substate) out))
    {owner : AccountAddress} {q value : UInt256}
    (h : storageSlotIs r owner q value = true) : worldSlot world owner q = value := by
  rw [hr] at h
  unfold storageSlotIs storageSlotAfter at h
  change (match (world.get? owner).map (fun acc => acc.lookupStorage q) with
    | some v => v == value
    | none => false) = true at h
  cases ha : world.get? owner with
  | none => rw [ha] at h; cases h
  | some acc =>
    simp only [ha, Option.map_some] at h
    have he : acc.lookupStorage q = value := word_eq_of_beq h
    simp only [worldSlot, ha, Option.map_some, Option.getD_some]
    exact he

end Eip8282.Tests.DirectMutations
