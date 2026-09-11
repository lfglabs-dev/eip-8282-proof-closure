import Eip8282.Audit.Integrator.ReferenceCheckedStateGas

/-! Fresh transaction storage is preserved by prepayment, account dispatch
reads and source value entry, including their partial failure states. This is
an initial journal condition, not an assumption about a final gas balance.
Consumer: same-run transaction gas settlement. Python construction/canonical
applicability of the represented fresh journal remain external. -/
namespace Eip8282.Audit.Integrator.ReferenceFreshStorageEntry
open EvmYul EvmYul.EVM ReferenceSourceValueTransfer
open ReferenceRuntimeStateBalance (emptyTx)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private theorem erase_empty (address : AccountAddress) : eraseStorage emptyTx address = emptyTx := by
  simp [eraseStorage,emptyTx]

private theorem modify_empty {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (address : AccountAddress) (balance : UInt256) (fresh : tx.storage = emptyTx) :
    (modifyBalance emptyHash parent tx address balance).storage = emptyTx := by
  unfold modifyBalance
  dsimp only
  split <;> simp only [writeAccount,fresh,erase_empty]

private theorem move_empty {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender recipient : AccountAddress) (value : UInt256) (fresh : tx.storage = emptyTx) :
    (move emptyHash parent tx sender recipient value).2.storage = emptyTx := by
  unfold move
  dsimp only
  split
  · have debit := modify_empty emptyHash parent {tx with accounts := ReferenceAccountLookup.tracked tx.accounts sender} sender
      (UInt256.ofNat ((account emptyHash parent tx sender).balance.toNat-value.toNat)) fresh
    split
    · apply modify_empty
      exact debit
    · exact debit
  · exact fresh

theorem enter {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender recipient : AccountAddress) (value : UInt256) (mode : Bool) (fresh : tx.storage = emptyTx) :
    (ReferenceSourceValueTransfer.enter emptyHash parent tx sender recipient value mode).2.storage = emptyTx := by
  unfold ReferenceSourceValueTransfer.enter
  split
  · exact move_empty emptyHash parent tx sender recipient value fresh
  · exact fresh

theorem probe {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (before : Tx Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (target : AccountAddress) (value : UInt256) :
    (ReferenceSourceDispatch.probe emptyHash parent before codeParent target value).2.storage = before.storage := by
  simp only [ReferenceSourceDispatch.probe,ReferenceSourceDispatch.readTarget]
  repeat' (split <;> try rfl)

theorem allocated {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (before : Tx Hash) (tx : RefundAccounting.Context) (kind : ReachableCalls.Contract)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (fresh : before.storage = emptyTx) :
    (ReferenceAllocatedEntry.entered emptyHash parent before tx kind codeParent).2.storage = emptyTx := by
  apply enter
  rw [probe,(ReferenceSourcePrepaidCheckpoint.fields emptyHash parent before tx).1,fresh]

#print axioms enter
#print axioms probe
#print axioms allocated
end Eip8282.Audit.Integrator.ReferenceFreshStorageEntry
