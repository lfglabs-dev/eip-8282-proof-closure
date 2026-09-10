import Eip8282.Audit.Integrator.FinalizationWorldFrame
import Eip8282.Audit.Integrator.TransferFunding

/-! Literal debit-then-credit transfer, including absent zero-balance senders.
Reference: audit/receipts/direct-reference-migration-deployment-sources-20260910.json,
EL 0cc100eb190b64b23baba72dac0165652eaec252,
dao_fork/dao.py:367-369 and state_tracker.py:491-522. The recipient is
read from the UPDATED world, so sender=recipient is handled in execution order.
Reference checked-U256 and state-diff correspondence remain OPEN; this module
proves the pinned word update, not a Python overflow or canonical DAO theorem. -/
namespace Eip8282.Audit.Integrator.ProtocolTransfer
open EvmYul EvmYul.EVM
open TransferFunding
open Eip8282.Audit.EntryReach
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def debit (world : AccountMap .EVM) (sender : AccountAddress) (amount : UInt256) : AccountMap .EVM :=
  let old := (world.get? sender).getD default
  world.insert sender {old with balance := old.balance-amount}

def transfer (world : AccountMap .EVM) (sender recipient : AccountAddress) (amount : UInt256) :
    AccountMap .EVM := (debit world sender amount).increaseBalance .EVM recipient amount

private theorem default_balance (world : AccountMap .EVM) (sender : AccountAddress) :
    ((world.get? sender).getD (default : Account .EVM)).balance.toNat = worldBalance world sender := by
  unfold worldBalance
  cases world.get? sender <;> rfl

theorem debit_funds (world : AccountMap .EVM) (sender : AccountAddress) (amount : UInt256)
    (funded : amount.toNat ≤ worldBalance world sender) :
    worldFunds (debit world sender amount) + amount.toNat = worldFunds world := by
  have hd := default_balance world sender
  have hs := toNat_sub_of_le ((world.get? sender).getD (default : Account .EVM)).balance amount (by omega)
  have hi := funds_insert world sender
    {((world.get? sender).getD (default : Account .EVM)) with balance :=
      ((world.get? sender).getD (default : Account .EVM)).balance-amount}
  change worldFunds (debit world sender amount) + worldBalance world sender =
    worldFunds world + (((world.get? sender).getD (default : Account .EVM)).balance-amount).toNat at hi
  rw [hs] at hi
  omega

theorem funds (world : AccountMap .EVM) (sender recipient : AccountAddress) (amount : UInt256)
    (funded : amount.toNat ≤ worldBalance world sender) :
    worldFunds (transfer world sender recipient amount) ≤ worldFunds world := by
  have hd := debit_funds world sender amount funded
  have hc := FinalizationFunding.credit_le (debit world sender amount) recipient amount
  exact le_trans hc (le_of_eq hd)

theorem debit_frame (world : AccountMap .EVM) (sender protectedAddr : AccountAddress) (amount : UInt256) :
    CodeStorageFrame.Frame world (debit world sender amount) protectedAddr := by
  have hl : (debit world sender amount).get? protectedAddr =
      if sender = protectedAddr then some {((world.get? sender).getD (default : Account .EVM)) with
        balance := ((world.get? sender).getD (default : Account .EVM)).balance-amount}
      else world.get? protectedAddr := by
    exact (Std.TreeMap.getElem?_insert (t := world) (k := sender) (a := protectedAddr)
      (v := {((world.get? sender).getD (default : Account .EVM)) with
        balance := ((world.get? sender).getD (default : Account .EVM)).balance-amount})).trans
      (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)
  by_cases he : sender = protectedAddr
  · subst sender
    constructor
    · intro old ho
      refine ⟨{old with balance := old.balance-amount},?_,rfl⟩
      rw [hl,if_pos rfl,ho]
      rfl
    · intro slot
      simp only [SystemSpec.worldSlot,hl]
      cases world.get? protectedAddr <;> rfl
  · constructor
    · intro old ho
      exact ⟨old,by rw [hl,if_neg he]; exact ho,rfl⟩
    · intro slot
      simp only [SystemSpec.worldSlot,hl,if_neg he]

theorem frame (world : AccountMap .EVM) (sender recipient protectedAddr : AccountAddress) (amount : UInt256) :
    CodeStorageFrame.Frame world (transfer world sender recipient amount) protectedAddr :=
  CodeStorageFrame.trans (debit_frame world sender protectedAddr amount)
    (FinalizationWorldFrame.credit_frame _ recipient protectedAddr amount)

#print axioms debit_funds
#print axioms funds
#print axioms debit_frame
#print axioms frame
end Eip8282.Audit.Integrator.ProtocolTransfer
