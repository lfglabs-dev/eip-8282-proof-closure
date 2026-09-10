import Eip8282.Audit.Integrator.ReferenceSourceTransferFunding

/-! Literal create_ether / modify_state credit, including zero credits, source
checked U256 addition and read effects preceding overflow. This is consumed by
the ordered source fee disbursement, not an external funding-history credit. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceFeeCredit
open EvmYul ReferenceSourceValueTransfer
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

noncomputable def credit {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (address : AccountAddress) (amount : UInt256) :
    Except Unit Unit × Tx Hash :=
  let old := account emptyHash parent tx address
  let read := {tx with accounts := ReferenceAccountLookup.tracked tx.accounts address}
  if old.balance.toNat + amount.toNat < UInt256.size then
    (.ok (),modifyBalance emptyHash parent read address
      (UInt256.ofNat (old.balance.toNat + amount.toNat)))
  else (.error (),read)

theorem successful {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (key : AccountAddress) (amount : UInt256)
    (fits : (account emptyHash parent tx key).balance.toNat + amount.toNat < UInt256.size) :
    (credit emptyHash parent tx key amount).1 = .ok () ∧
    ∀ address, (account emptyHash parent (credit emptyHash parent tx key amount).2 address).balance.toNat =
      (account emptyHash parent tx address).balance.toNat + (if address = key then amount.toNat else 0) := by
  unfold credit
  rw [if_pos fits]
  refine ⟨rfl,?_⟩
  intro address
  rw [ReferenceSourceTransferFunding.modify_balance]
  by_cases same : address = key
  · subst address
    simp only [if_true]
    change (_ % UInt256.size) = _
    exact Nat.mod_eq_of_lt fits
  · simp only [if_neg same,Nat.add_zero]
    rfl

theorem hash {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (key address : AccountAddress) (amount : UInt256) :
    hashAt emptyHash parent (credit emptyHash parent tx key amount).2 address = hashAt emptyHash parent tx address := by
  unfold credit
  dsimp only
  split
  · rw [modify_hash]
    rfl
  · rfl

theorem protected_storage {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (key address : AccountAddress) (amount : UInt256)
    (nonempty : hashAt emptyHash parent tx address ≠ emptyHash)
    (storageParent : ReferenceStorageView.Parent) (slot : ByteArray) :
    ReferenceStorageView.current storageParent (credit emptyHash parent tx key amount).2.storage address slot =
      ReferenceStorageView.current storageParent tx.storage address slot := by
  unfold credit
  dsimp only
  split
  · exact modify_protected_storage emptyHash parent
      {tx with accounts := ReferenceAccountLookup.tracked tx.accounts key}
      key address _ nonempty storageParent slot
  · rfl

theorem fields {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (key : AccountAddress) (amount : UInt256) :
    (credit emptyHash parent tx key amount).2.codeWrites = tx.codeWrites ∧
    (credit emptyHash parent tx key amount).2.transient = tx.transient ∧
    (credit emptyHash parent tx key amount).2.accounts.reads = insert key tx.accounts.reads := by
  unfold credit
  dsimp only
  split
  · unfold modifyBalance
    dsimp only
    split <;> simp [writeAccount,ReferenceAccountLookup.tracked]
  · exact ⟨rfl,rfl,rfl⟩

#print axioms successful
#print axioms hash
#print axioms protected_storage
#print axioms fields
end Eip8282.Audit.Integrator.ReferenceSourceFeeCredit
