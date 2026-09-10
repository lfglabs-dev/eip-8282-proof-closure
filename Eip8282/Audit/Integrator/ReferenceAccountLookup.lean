import Eip8282.Audit.Integrator.ReferenceStorageView

/-! Literal optional-account read chain from the pinned Amsterdam
state_tracker.py: transaction writes, then block writes, then PreState.
An explicit deletion (some none) masks older accounts; an empty account is
still present. Reads are recorded even when lookup returns none and survive
rollback. Payload is generic: no account-field or whole-world correspondence
is assumed by this lookup projection. Initial deployment/presence and concrete
source dictionary bindings remain source-context producers.
-/
namespace Eip8282.Audit.Integrator.ReferenceAccountLookup
open EvmYul
set_option autoImplicit false

abbrev Overlay (Account : Type) := AccountAddress → Option (Option Account)

structure Parent (Account : Type) where
  writes : Overlay Account
  pre : AccountAddress → Option Account

structure Tx (Account : Type) where
  writes : Overlay Account
  reads : Set AccountAddress

def parentRead {Account : Type} (p : Parent Account) (a : AccountAddress) : Option Account :=
  (p.writes a).getD (p.pre a)

/-- Pure observation of the chain; getOptional below records the source read. -/
def peek {Account : Type} (p : Parent Account) (tx : Tx Account) (a : AccountAddress) : Option Account :=
  (tx.writes a).getD (parentRead p a)

def tracked {Account : Type} (tx : Tx Account) (a : AccountAddress) : Tx Account :=
  {tx with reads := insert a tx.reads}

def getOptional {Account : Type} (p : Parent Account) (tx : Tx Account) (a : AccountAddress) :
    Option Account × Tx Account := (peek p tx a,tracked tx a)

/-- Actual restore_tx_state resets the write dictionary, retaining shared reads. -/
def rollback {Account : Type} (tx snapshot : Tx Account) : Tx Account :=
  {tx with writes := snapshot.writes}

theorem tracked_peek {Account : Type} (p : Parent Account) (tx : Tx Account) (a b : AccountAddress) :
    peek p (tracked tx a) b = peek p tx b := rfl

theorem deletion_masks {Account : Type} (p : Parent Account) (tx : Tx Account) (a : AccountAddress)
    (deleted : tx.writes a = some none) : peek p tx a = none := by
  simp only [peek,deleted,Option.getD_some]

theorem read_recorded {Account : Type} (p : Parent Account) (tx : Tx Account) (a : AccountAddress) :
    a ∈ (getOptional p tx a).2.reads := Set.mem_insert a _

theorem rollback_lookup {Account : Type} (p : Parent Account) (tx snapshot : Tx Account) (a : AccountAddress) :
    peek p (rollback tx snapshot) a = peek p snapshot a ∧
    (rollback tx snapshot).reads = tx.reads := ⟨rfl,rfl⟩

#print axioms tracked_peek
#print axioms deletion_masks
#print axioms read_recorded
#print axioms rollback_lookup
end Eip8282.Audit.Integrator.ReferenceAccountLookup
