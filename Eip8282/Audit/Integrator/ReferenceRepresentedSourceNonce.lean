import Eip8282.Audit.Integrator.ReferenceSourceTransferFunding

/-! Source nonce derivation from the represented-parent overlay.

The two public consumers `ReferenceFullFeeBlockTotal.verified` and
`ReferenceCheckedSystemBlock.verified` currently take the read-nonce equality
`(ReferenceSourceValueTransfer.account emptyHash parent tx tx.sender).nonce =
sender.nonce.toNat` as a separate explicit premise, alongside a `found` lookup
identity and a balance-only coherence `BalancesRelated`. The balance-only
coherence does not force any nonce equality, and the abstract `parent : Parent
Hash` has no imposed shape, so read-nonce is a genuinely independent premise in
the current abstract framing.

This module records the elementary derivation: when the parent overlay is
literally the represented image of a source world (`representedParent codeHash
world`) and the transaction accounts journal writes nothing at the address of
interest (fresh journal at that address), the read-nonce equality follows
directly from `world.get? address = some a` alone. The lemma exposes the
condition under which the read-nonce premise is derivable — the represented
parent shape — and is a proven step-(a) building block toward eliminating the
sourceNonce premise from the public consumers by threading a `parent =
representedParent codeHash tx.world` constraint through the downstream
`ReferenceFullFeeBlockNonce` / `ReferenceFullFeeBlockReceipt` chain.

No public consumer signature is changed by this module; it registers the
derivation as a reusable, whitelist-clean lemma. -/
namespace Eip8282.Audit.Integrator.ReferenceRepresentedSourceNonce

open EvmYul
open ReferenceSourceValueTransfer (Account Tx account empty)
open ReferenceSourceTransferFunding (representedParent BalancesRelated)
open TransferFunding (worldBalance)

set_option autoImplicit false

/-- Read-nonce equality holds automatically when the parent overlay is the
    represented image of a world and the transaction accounts journal does not
    override the address under consideration. Requires only the world lookup
    identity `found`; no balance coherence, no code-hash choice, and no
    nonce premise. -/
theorem sourceNonce_of_represented {Hash : Type} (codeHash : ByteArray → Hash)
    (world : AccountMap .EVM) (tx : Tx Hash) (emptyHash : Hash)
    (address : AccountAddress) (a : EvmYul.Account .EVM)
    (freshAccountsAt : tx.accounts.writes address = none)
    (found : world.get? address = some a) :
    (account emptyHash (representedParent codeHash world) tx address).nonce =
      a.nonce.toNat := by
  unfold account ReferenceAccountLookup.peek ReferenceAccountLookup.parentRead representedParent
  dsimp only
  rw [freshAccountsAt, Option.getD_none, Option.getD_none, found]
  rfl

#print axioms sourceNonce_of_represented

/-- The globally-fresh accounts journal case: `tx.accounts.writes = fun _ => none`
    delivers the pointwise `freshAccountsAt` for any address. Convenience form. -/
theorem sourceNonce_of_represented_freshAll {Hash : Type} (codeHash : ByteArray → Hash)
    (world : AccountMap .EVM) (tx : Tx Hash) (emptyHash : Hash)
    (address : AccountAddress) (a : EvmYul.Account .EVM)
    (freshAccounts : tx.accounts.writes = fun _ => none)
    (found : world.get? address = some a) :
    (account emptyHash (representedParent codeHash world) tx address).nonce =
      a.nonce.toNat :=
  sourceNonce_of_represented codeHash world tx emptyHash address a
    (by rw [freshAccounts])
    found

#print axioms sourceNonce_of_represented_freshAll

/-- Balance-coherence identity at a single address, under `parent =
    representedParent codeHash world` and pointwise-fresh accounts journal.
    This is the balance analog of `sourceNonce_of_represented`, generalizing
    `ReferenceSourceTransferFunding.represented_balances` in that it drops the
    `tx = representedTx …` shape requirement — only `tx.accounts.writes address
    = none` is needed, independent of `tx.storage`, `tx.codeWrites`, and
    `tx.transient`. -/
theorem sourceBalance_of_represented {Hash : Type} (codeHash : ByteArray → Hash)
    (world : AccountMap .EVM) (tx : Tx Hash) (emptyHash : Hash)
    (address : AccountAddress)
    (freshAccountsAt : tx.accounts.writes address = none) :
    (account emptyHash (representedParent codeHash world) tx address).balance.toNat =
      worldBalance world address := by
  unfold account ReferenceAccountLookup.peek ReferenceAccountLookup.parentRead worldBalance
    representedParent
  dsimp only
  rw [freshAccountsAt, Option.getD_none, Option.getD_none]
  cases world.get? address <;> rfl

#print axioms sourceBalance_of_represented

/-- `BalancesRelated` follows from the represented-parent shape and a globally
    fresh accounts journal, for any `tx.storage`, `tx.codeWrites`, and
    `tx.transient`. This drops the `tx = representedTx …` requirement of
    `ReferenceSourceTransferFunding.represented_balances`, since `BalancesRelated`
    only reads `tx.accounts`. Composed with `sourceNonce_of_represented_freshAll`,
    it proves that both `balances` and `sourceNonce` premises of the public
    consumers are simultaneously derivable from a single `parent =
    representedParent codeHash tx.world` overlay assumption together with fresh
    accounts, world lookup, and — for nonce — the found witness. -/
theorem BalancesRelated_of_represented_freshAll {Hash : Type}
    (codeHash : ByteArray → Hash) (world : AccountMap .EVM) (tx : Tx Hash)
    (emptyHash : Hash) (freshAccounts : tx.accounts.writes = fun _ => none) :
    BalancesRelated emptyHash (representedParent codeHash world) tx world :=
  fun address => sourceBalance_of_represented codeHash world tx emptyHash address
    (by rw [freshAccounts])

#print axioms BalancesRelated_of_represented_freshAll

end Eip8282.Audit.Integrator.ReferenceRepresentedSourceNonce
