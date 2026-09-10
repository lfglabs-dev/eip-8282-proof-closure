import Eip8282.Audit.Integrator.ReferenceSourceBalanceTransport
import Eip8282.Audit.Integrator.ReferenceSourceFundedGuarantees
import Eip8282.Audit.Integrator.ReferenceSourceFundedFailure

/-! Balance observations of the same account-aware execution used by the three
checked guarantees. An internal endpoint retains the entry transfer even when
its outcome will revert; settlement instead restores the pre-transfer balances.
This does not identify the replay post-world, source frame construction, gas or
ancestor settlement with the source evaluator. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceBalanceOutcome
open EvmYul EvmYul.EVM
open ReferenceSourceValueTransfer ReferenceSourceTransferFunding
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceCheckedDispatch ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- Reads, code/storage writes and transient state do not change account balance
observations when the account write overlay is unchanged. -/
theorem same_writes {Hash : Type} (emptyHash : Hash) (parent : Parent Hash)
    (before after : Tx Hash) (world : AccountMap .EVM)
    (related : BalancesRelated emptyHash parent before world)
    (writes : after.accounts.writes = before.accounts.writes) :
    BalancesRelated emptyHash parent after world := by
  intro address
  change ((ReferenceAccountLookup.peek parent after.accounts address).getD (empty emptyHash)).balance.toNat = _
  unfold ReferenceAccountLookup.peek
  rw [writes]
  exact related address

/-- Same finite completed evaluation as the guarantee consumers: its internal
account balances match the transferred entry world. This is deliberately a
pre-settlement observation, including failed and reverted outcomes. -/
theorem evaluated {deposit exit : TransactionAppendBudget.Receipt} {Hash LoadError : Type} [DecidableEq Hash]
    (emptyHash : Hash) (accountsParent : Parent Hash) (before : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError)
    (c : MessageCall.Context) (shouldTransfer : Bool)
    (history : ReleaseCandidate.History deposit exit c.world)
    (balances : BalancesRelated emptyHash accountsParent before c.world)
    (funded : c.value.toNat ≤ TransferFunding.worldBalance c.world c.caller)
    (mode : shouldTransfer = true ∨ c.value = ⟨0⟩)
    {destinations : List Nat} {parent : ReferenceStorageView.Parent} {output : ByteArray}
    {fuel : Nat} {v : View} {warm : Warm} {meter : Meter} {events : List Event} {result : Outcome}
    {finalAccounts : ReferenceAccountLookup.Tx (Account Hash)}
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent output fuel
      (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts v warm meter =
      some ((events,result),finalAccounts)) :
    BalancesRelated emptyHash accountsParent
      {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts} c.entryWorld := by
  have fetchedBalances : BalancesRelated emptyHash accountsParent
      (fetched emptyHash accountsParent before codeParent c.target) c.world := balances
  have transported := ReferenceSourceBalanceTransport.after_history emptyHash accountsParent
    (fetched emptyHash accountsParent before codeParent c.target) c shouldTransfer history fetchedBalances funded mode
  exact same_writes emptyHash accountsParent _ _ _ transported (ReferenceCheckedAccountEvaluator.writes actual)

/-- Frame restoration recovers the pre-transfer balances while retaining live
read metadata. Ancestor commit/rollback is a separate operation. -/
theorem restored {Hash : Type} (emptyHash : Hash) (parent : Parent Hash)
    (live before : Tx Hash) (world : AccountMap .EVM)
    (balances : BalancesRelated emptyHash parent before world) :
    BalancesRelated emptyHash parent (restore live before) world :=
  same_writes emptyHash parent before (restore live before) world balances rfl

#print axioms same_writes
#print axioms evaluated
#print axioms restored
end Eip8282.Audit.Integrator.ReferenceSourceBalanceOutcome
