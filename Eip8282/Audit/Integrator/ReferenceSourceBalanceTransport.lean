import Eip8282.Audit.Integrator.ReferenceSourceTransferFunding

/-! The initial balance representation is preserved through the actual checked
source transfer. This is the balance-field consumer of source funding, not
optional-account/world equality: source empty cleanup may erase an account.
It connects source entry to the existing old receipt without identifying gas,
logs, account presence or source frame construction. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceBalanceTransport
open EvmYul EvmYul.EVM
open ReferenceSourceValueTransfer ReferenceSourceTransferFunding TransferFunding
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem lookup_insert (world : AccountMap .EVM) (key address : AccountAddress)
    (a : EvmYul.Account .EVM) :
    (world.insert key a).get? address = if key = address then some a else world.get? address := by
  exact (Std.TreeMap.getElem?_insert (t := world) (k := key) (a := address) (v := a)).trans
    (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)

private theorem credit_balance (world : AccountMap .EVM) (recipient address : AccountAddress) (amount : UInt256)
    (fit : worldBalance world recipient + amount.toNat < UInt256.size) :
    worldBalance (world.increaseBalance .EVM recipient amount) address =
      if address = recipient then worldBalance world recipient + amount.toNat else worldBalance world address := by
  unfold AccountMap.increaseBalance
  cases found : world.get? recipient with
  | none =>
    unfold worldBalance
    rw [lookup_insert]
    by_cases same : address = recipient
    · subst address
      simp only [if_true,found,Option.map_none,Option.getD_none,Option.map_some,Option.getD_some,Nat.zero_add]
    · simp [same,Ne.symm same]
  | some previous =>
    have previousFit : previous.balance.toNat+amount.toNat < UInt256.size := by
      simpa only [worldBalance,found,Option.map_some,Option.getD_some] using fit
    have add : (previous.balance+amount).toNat = previous.balance.toNat+amount.toNat := by
      change (_ % UInt256.size) = _
      exact Nat.mod_eq_of_lt previousFit
    unfold worldBalance
    rw [lookup_insert]
    by_cases same : address = recipient
    · subst address
      simpa only [if_true,found,Option.map_some,Option.getD_some] using add
    · simp [same,Ne.symm same]

/-- The same checked debit/credit operation preserves balance correspondence;
no successful-entry or post-balance equation is assumed. -/
theorem move_balances {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (world : AccountMap .EVM) (sender recipient : AccountAddress) (value : UInt256)
    (related : BalancesRelated emptyHash parent tx world)
    (funded : value.toNat ≤ worldBalance world sender)
    (total : worldFunds world < UInt256.size) :
    BalancesRelated emptyHash parent (move emptyHash parent tx sender recipient value).2
      (ProtocolTransfer.transfer world sender recipient value) := by
  let mid := modifyBalance emptyHash parent {tx with accounts := ReferenceAccountLookup.tracked tx.accounts sender} sender
    (UInt256.ofNat ((account emptyHash parent tx sender).balance.toNat-value.toNat))
  have midRelated : BalancesRelated emptyHash parent mid (ProtocolTransfer.debit world sender value) := by
    intro address
    exact debit_balance emptyHash parent tx world sender address value related funded
  have senderFit : value.toNat ≤ (account emptyHash parent tx sender).balance.toNat := by rw [related sender]; exact funded
  have oldFit := (ProtocolMigrationLedger.recipient_add_bound world sender recipient value funded).trans_lt total
  have recipientFit : (account emptyHash parent mid recipient).balance.toNat+value.toNat < UInt256.size := by
    rw [midRelated recipient]
    exact oldFit
  intro address
  unfold move
  dsimp only
  rw [if_pos senderFit]
  change (account emptyHash parent (if (account emptyHash parent mid recipient).balance.toNat+value.toNat < UInt256.size then
    (Except.ok (),modifyBalance emptyHash parent {mid with accounts := ReferenceAccountLookup.tracked mid.accounts recipient} recipient
      (UInt256.ofNat ((account emptyHash parent mid recipient).balance.toNat+value.toNat)))
    else (Except.error Error.creditOverflow,{mid with accounts := ReferenceAccountLookup.tracked mid.accounts recipient})).2 address).balance.toNat = _
  rw [if_pos recipientFit]
  dsimp only
  rw [modify_balance]
  change _ = worldBalance ((ProtocolTransfer.debit world sender value).increaseBalance .EVM recipient value) address
  rw [credit_balance _ recipient address value oldFit]
  by_cases same : address = recipient
  · simp only [if_pos same]
    have val : (UInt256.ofNat ((account emptyHash parent mid recipient).balance.toNat+value.toNat)).toNat =
        (account emptyHash parent mid recipient).balance.toNat+value.toNat := by
      change (_ % UInt256.size) = _
      exact Nat.mod_eq_of_lt recipientFit
    rw [val,midRelated recipient]
  · simp only [if_neg same]
    exact midRelated address

/-- Ordinary transfer mode agrees with Theta's value movement at the balance
observation, even though its internal debit/credit order differs. Disabling
transfer with nonzero actual value is deliberately not included. -/
theorem enter_balances {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (c : MessageCall.Context) (shouldTransfer : Bool)
    (related : BalancesRelated emptyHash parent tx c.world)
    (funded : c.value.toNat ≤ worldBalance c.world c.caller)
    (total : worldFunds c.world < UInt256.size)
    (mode : shouldTransfer = true ∨ c.value = ⟨0⟩) :
    BalancesRelated emptyHash parent (enter emptyHash parent tx c.caller c.target c.value shouldTransfer).2 c.entryWorld := by
  have same (address : AccountAddress) : worldBalance c.entryWorld address =
      worldBalance (ReferenceValueTransfer.referenceEntry c) address := by
    unfold worldBalance
    rw [ReferenceValueTransfer.entry_lookup c funded address]
  by_cases zero : c.value = ⟨0⟩
  · intro address
    rw [same]
    simpa [enter,zero,ReferenceValueTransfer.referenceEntry,show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl] using related address
  · have yes : shouldTransfer = true := mode.resolve_right zero
    have moved := move_balances emptyHash parent tx c.world c.caller c.target c.value related funded total
    intro address
    rw [same]
    simpa [enter,yes,zero,ReferenceValueTransfer.referenceEntry,show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl] using moved address

/-- Initialized funding supplies the numeric domain of balance transport. -/
theorem after_history {deposit exit : TransactionAppendBudget.Receipt} {Hash : Type} [DecidableEq Hash]
    (emptyHash : Hash) (parent : Parent Hash) (tx : Tx Hash) (c : MessageCall.Context) (shouldTransfer : Bool)
    (history : ReleaseCandidate.History deposit exit c.world)
    (related : BalancesRelated emptyHash parent tx c.world)
    (funded : c.value.toNat ≤ worldBalance c.world c.caller)
    (mode : shouldTransfer = true ∨ c.value = ⟨0⟩) :
    BalancesRelated emptyHash parent (enter emptyHash parent tx c.caller c.target c.value shouldTransfer).2 c.entryWorld := by
  have total := FundingHistory.trace_funds (ProtocolCreditEnvelope.ledger_bound history.ledger).1
  exact enter_balances emptyHash parent tx c shouldTransfer related funded
    (total.trans_lt (LedgerCreditSafety.genesis_budget history.ledger history.counts)) mode

#print axioms after_history

#print axioms move_balances
#print axioms enter_balances
end Eip8282.Audit.Integrator.ReferenceSourceBalanceTransport
