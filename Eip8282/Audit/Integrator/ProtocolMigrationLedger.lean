import Eip8282.Audit.Integrator.ProtocolCreditEnvelope

/-! A literal full-balance migration sweep creates no external credit.
Reference: audit/receipts/direct-reference-migration-deployment-sources-20260910.json,
DAO apply_dao and sequential move_ether. Every source balance is read from the
current world. Duplicate sources, recovery aliases and absent accounts are
allowed. Python state-diff and canonical DAO-list correspondence remain OPEN.
The optional checked-addition bound is derived from the pre-world sum, which
must itself be supplied by the independently justified funding ledger. -/
namespace Eip8282.Audit.Integrator.ProtocolMigrationLedger
open EvmYul EvmYul.EVM
open TransferFunding ProtocolCreditEnvelope
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def currentBalance (world : AccountMap .EVM) (source : AccountAddress) : UInt256 :=
  ((world.get? source).getD (default : Account .EVM)).balance

theorem current_balance (world : AccountMap .EVM) (source : AccountAddress) :
    (currentBalance world source).toNat = worldBalance world source := by
  unfold currentBalance worldBalance
  cases world.get? source <;> rfl

def sweep (recovery : AccountAddress) : List AccountAddress → AccountMap .EVM → AccountMap .EVM
  | [], world => world
  | source::rest, world => sweep recovery rest
      (ProtocolTransfer.transfer world source recovery (currentBalance world source))

theorem ledger {initial world : AccountMap .EVM} {p w s c : Nat}
    (prior : Ledger initial p w s c world) (sources : List AccountAddress) (recovery : AccountAddress) :
    Ledger initial p w s c (sweep recovery sources world) := by
  induction sources generalizing world with
  | nil => exact prior
  | cons source rest ih =>
    apply ih
    exact Ledger.conserving prior (.transfer world source recovery (currentBalance world source)
      (by rw [current_balance]))

theorem funding {initial world : AccountMap .EVM} {credits : Nat}
    (prior : FundingHistory.Trace initial credits world)
    (sources : List AccountAddress) (recovery : AccountAddress) :
    FundingHistory.Trace initial credits (sweep recovery sources world) := by
  induction sources generalizing world with
  | nil => exact prior
  | cons source rest ih =>
    apply ih
    simpa only [Nat.add_zero] using FundingHistory.Trace.next prior
      (.transfer world source recovery (currentBalance world source) (by rw [current_balance]))

theorem frame (world : AccountMap .EVM) (sources : List AccountAddress)
    (recovery protectedAddr : AccountAddress) :
    CodeStorageFrame.Frame world (sweep recovery sources world) protectedAddr := by
  induction sources generalizing world with
  | nil => exact CodeStorageFrame.refl _ _
  | cons source rest ih =>
    exact CodeStorageFrame.trans (ProtocolTransfer.frame world source recovery protectedAddr _)
      (ih _)

/-- The recipient is read after debit. Thus aliases satisfy the same bound. -/
theorem recipient_add_bound (world : AccountMap .EVM) (source recipient : AccountAddress)
    (amount : UInt256) (funded : amount.toNat ≤ worldBalance world source) :
    worldBalance (ProtocolTransfer.debit world source amount) recipient + amount.toNat ≤
      worldFunds world := by
  have hd := ProtocolTransfer.debit_funds world source amount funded
  have hr := balance_le_funds (ProtocolTransfer.debit world source amount) recipient
  omega

theorem checked_add_fits (world : AccountMap .EVM) (source recipient : AccountAddress)
    (amount : UInt256) (funded : amount.toNat ≤ worldBalance world source)
    (total : worldFunds world < UInt256.size) :
    (currentBalance (ProtocolTransfer.debit world source amount) recipient).toNat + amount.toNat < UInt256.size := by
  rw [current_balance]
  exact lt_of_le_of_lt (recipient_add_bound world source recipient amount funded) total

#print axioms ledger
#print axioms funding
#print axioms frame
#print axioms recipient_add_bound
#print axioms checked_add_fits
end Eip8282.Audit.Integrator.ProtocolMigrationLedger
