import Eip8282.Audit.Integrator.ReferenceSourceValueTransfer
import Eip8282.Audit.Integrator.ReferenceValueTransfer
import Eip8282.Audit.Integrator.ReleaseCandidate

/-! Discharge source transfer success using the independently observed initial
balances and an initialized ledger. The relation below compares pre-transfer
balance reads, not a successful transfer or desired post-state. Its concrete
source/world producer is still required for Ethereum application. Empty-account
cleanup is retained: deletion of a zero balance is observationally zero, which
is enough for the debit/credit arithmetic without asserting account identity.
-/
namespace Eip8282.Audit.Integrator.ReferenceSourceTransferFunding
open EvmYul EvmYul.EVM
open ReferenceSourceValueTransfer
open TransferFunding
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def BalancesRelated {Hash : Type} (emptyHash : Hash) (parent : Parent Hash) (tx : Tx Hash)
    (world : AccountMap .EVM) : Prop :=
  ∀ address, (account emptyHash parent tx address).balance.toNat = worldBalance world address

private theorem account_write {Hash : Type} (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (key address : AccountAddress) (value : Option (ReferenceSourceValueTransfer.Account Hash)) :
    account emptyHash parent (writeAccount tx key value) address =
      if address = key then value.getD (empty emptyHash) else account emptyHash parent tx address := by
  classical
  by_cases same : address = key <;>
    simp [account,writeAccount,ReferenceAccountLookup.peek,same]

theorem modify_balance {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (key address : AccountAddress) (balance : UInt256) :
    (account emptyHash parent (modifyBalance emptyHash parent tx key balance) address).balance =
      if address = key then balance else (account emptyHash parent tx address).balance := by
  classical
  unfold modifyBalance
  dsimp only
  split
  · rename_i deleted
    rw [account_write]
    by_cases same : address = key
    · simp only [if_pos same]
      exact deleted.2.2.symm
    · simp only [if_neg same]
      rfl
  · rw [account_write]
    by_cases same : address = key <;> simp only [same,if_true,if_false,Option.getD_some]
    rfl

private theorem world_debit_balance (world : AccountMap .EVM) (sender address : AccountAddress)
    (amount : UInt256) (funded : amount.toNat ≤ worldBalance world sender) :
    worldBalance (ProtocolTransfer.debit world sender amount) address =
      if address = sender then worldBalance world sender - amount.toNat else worldBalance world address := by
  have read : ((world.get? sender).getD (default : EvmYul.Account .EVM)).balance.toNat = worldBalance world sender := by
    unfold worldBalance
    cases world.get? sender <;> rfl
  have fits := Eip8282.Audit.EntryReach.toNat_sub_of_le ((world.get? sender).getD (default : EvmYul.Account .EVM)).balance amount (by omega)
  have lookup : (ProtocolTransfer.debit world sender amount).get? address =
      if sender = address then some {((world.get? sender).getD (default : EvmYul.Account .EVM)) with
        balance := ((world.get? sender).getD (default : EvmYul.Account .EVM)).balance-amount}
      else world.get? address := by
    exact (Std.TreeMap.getElem?_insert (t := world) (k := sender) (a := address)
      (v := {((world.get? sender).getD (default : EvmYul.Account .EVM)) with
        balance := ((world.get? sender).getD (default : EvmYul.Account .EVM)).balance-amount})).trans
      (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)
  unfold worldBalance
  rw [lookup]
  by_cases same : address = sender
  · subst address
    simp only [if_true,Option.map_some,Option.getD_some]
    exact fits.trans (congrArg (fun n => n-amount.toNat) read)
  · simp [same,Ne.symm same]

/-- Pointwise debit-balance agreement even if source empty cleanup removes
an account while the old map retains its zero-balance account object. -/
theorem debit_balance {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (world : AccountMap .EVM) (sender address : AccountAddress) (value : UInt256)
    (related : BalancesRelated emptyHash parent tx world)
    (funded : value.toNat ≤ worldBalance world sender) :
    (account emptyHash parent (modifyBalance emptyHash parent
      {tx with accounts := ReferenceAccountLookup.tracked tx.accounts sender} sender
      (UInt256.ofNat ((account emptyHash parent tx sender).balance.toNat-value.toNat))) address).balance.toNat =
    worldBalance (ProtocolTransfer.debit world sender value) address := by
  rw [modify_balance,world_debit_balance world sender address value funded]
  by_cases same : address = sender
  · simp only [if_pos same]
    have bound : (account emptyHash parent tx sender).balance.toNat-value.toNat < UInt256.size :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (account emptyHash parent tx sender).balance.val.isLt
    have valueFit : (UInt256.ofNat ((account emptyHash parent tx sender).balance.toNat-value.toNat)).toNat =
        (account emptyHash parent tx sender).balance.toNat-value.toNat := by
      change (_ % UInt256.size) = _
      exact Nat.mod_eq_of_lt bound
    rw [valueFit,related sender]
  · simp only [if_neg same]
    exact related address

theorem enter_success {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (c : MessageCall.Context) (shouldTransfer : Bool)
    (related : BalancesRelated emptyHash parent tx c.world)
    (funded : c.value.toNat ≤ worldBalance c.world c.caller)
    (total : worldFunds c.world < UInt256.size) :
    (enter emptyHash parent tx c.caller c.target c.value shouldTransfer).1 = .ok () := by
  unfold enter
  split
  · unfold move
    dsimp only
    have senderFit : c.value.toNat ≤ (account emptyHash parent tx c.caller).balance.toNat := by rwa [related c.caller]
    rw [if_pos senderFit]
    have recipientFit : (account emptyHash parent (modifyBalance emptyHash parent
      {tx with accounts := ReferenceAccountLookup.tracked tx.accounts c.caller} c.caller
      (UInt256.ofNat ((account emptyHash parent tx c.caller).balance.toNat-c.value.toNat))) c.target).balance.toNat+c.value.toNat < UInt256.size := by
      rw [debit_balance emptyHash parent tx c.world c.caller c.target c.value related funded]
      exact (ProtocolMigrationLedger.recipient_add_bound c.world c.caller c.target c.value funded).trans_lt total
    split
    · rfl
    · rename_i overflow
      exact False.elim (overflow recipientFit)
  · rfl

/-- Initialized history supplies the global numerical bound; no chosen maximum
wealth, post-debit recipient bound, or transfer-success premise is supplied. -/
theorem after_history {deposit exit : TransactionAppendBudget.Receipt} {Hash : Type} [DecidableEq Hash]
    (emptyHash : Hash) (parent : Parent Hash) (tx : Tx Hash) (c : MessageCall.Context) (shouldTransfer : Bool)
    (history : ReleaseCandidate.History deposit exit c.world)
    (related : BalancesRelated emptyHash parent tx c.world)
    (funded : c.value.toNat ≤ worldBalance c.world c.caller) :
    (enter emptyHash parent tx c.caller c.target c.value shouldTransfer).1 = .ok () := by
  have total := FundingHistory.trace_funds (ProtocolCreditEnvelope.ledger_bound history.ledger).1
  exact enter_success emptyHash parent tx c shouldTransfer related funded
    (total.trans_lt (LedgerCreditSafety.genesis_budget history.ledger history.counts))


/-- Literal account-field image of an existing old world. This constructs a
source-shaped pre-state representation for replay; it is not a claim that an
arbitrary Python PreState has this image or that code hashes are collision-free. -/
def representedParent {Hash : Type} (codeHash : ByteArray → Hash) (world : AccountMap .EVM) : Parent Hash :=
  ⟨fun _ => none,fun address => (world.get? address).map (fun a => ⟨a.nonce.toNat,a.balance,codeHash a.code⟩)⟩

def representedTx {Hash : Type} (storage : ReferenceStorageView.Tx)
    (codeWrites : Hash → Option ByteArray) (transient : AccountAddress → ByteArray → Option UInt256) : Tx Hash :=
  ⟨⟨fun _ => none,∅⟩,storage,codeWrites,transient⟩

theorem represented_balances {Hash : Type} (codeHash : ByteArray → Hash) (world : AccountMap .EVM)
    (storage : ReferenceStorageView.Tx) (codeWrites : Hash → Option ByteArray)
    (transient : AccountAddress → ByteArray → Option UInt256) :
    BalancesRelated (codeHash ByteArray.empty) (representedParent codeHash world)
      (representedTx storage codeWrites transient) world := by
  intro address
  unfold account ReferenceAccountLookup.peek ReferenceAccountLookup.parentRead worldBalance representedParent representedTx
  dsimp only
  cases world.get? address <;> rfl

/-- An initialized history has a concrete source balance representation whose
transfer succeeds. This representation witness is distinct from establishing
canonical source-world identity at a transaction or nested frame. -/
theorem represented_success {deposit exit : TransactionAppendBudget.Receipt} {Hash : Type} [DecidableEq Hash]
    (codeHash : ByteArray → Hash) (storage : ReferenceStorageView.Tx)
    (codeWrites : Hash → Option ByteArray) (transient : AccountAddress → ByteArray → Option UInt256)
    (c : MessageCall.Context) (shouldTransfer : Bool) (history : ReleaseCandidate.History deposit exit c.world)
    (funded : c.value.toNat ≤ worldBalance c.world c.caller) :
    (enter (codeHash ByteArray.empty) (representedParent codeHash c.world) (representedTx storage codeWrites transient)
      c.caller c.target c.value shouldTransfer).1 = .ok () :=
  after_history _ _ _ c shouldTransfer history (represented_balances codeHash c.world storage codeWrites transient) funded

#print axioms represented_balances
#print axioms represented_success

#print axioms modify_balance
#print axioms debit_balance
#print axioms enter_success
#print axioms after_history
end Eip8282.Audit.Integrator.ReferenceSourceTransferFunding
