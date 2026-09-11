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
open ReferenceSourceTransferFunding (representedParent)

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

end Eip8282.Audit.Integrator.ReferenceRepresentedSourceNonce
