import Eip8282.Audit.Integrator.ReferenceTransferredFailure
import Eip8282.Audit.Integrator.Topics.Reference5

/-! Source call-dispatch prefix for the represented no-authorization domain.
EL0cc100eb interpreter.py124-237: inspect optional target account only for a
positive value; load target code to resolve delegation; load the resolved code
again. This prefix reports continuations requiring a state charge or delegated
resolution rather than falsely calling them EVM errors. For pinned nonempty,
nondelegating code both charged continuations are excluded from actual reads.
The ready branch has unchanged meter and only accumulated account reads.
Python extraction, no-authorization binding and full frame construction remain
external. Consumers: allocated initialized terminal/EOF/failure guarantees. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceDispatch
open EvmYul EvmYul.EVM
open ReferenceSourceValueTransfer
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def Alive {Hash : Type} (emptyHash : Hash) (parent : Parent Hash) (tx : Tx Hash)
    (target : AccountAddress) : Prop :=
  match ReferenceAccountLookup.peek parent tx.accounts target with
  | none => False
  | some a => a.nonce ≠ 0 ∨ a.codeHash ≠ emptyHash ∨ a.balance ≠ ⟨0⟩

/-- Exact length and marker tests of source is_valid_delegation. -/
def delegation (bytes : ByteArray) : Bool :=
  bytes.size == 23 && bytes.extract 0 3 == (⟨#[0xef,0x01,0x00]⟩ : ByteArray)

inductive Next (Error : Type) where
  | stateChargeRequired
  | delegatedResolution (designation : ByteArray)
  | loadError (error : Error)
  | ready (code : ByteArray)

noncomputable def readTarget {Hash : Type} (tx : Tx Hash) (target : AccountAddress) : Tx Hash :=
  {tx with accounts := ReferenceAccountLookup.tracked tx.accounts target}

noncomputable def fetchCode {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (before : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (target : AccountAddress) : Except Error ByteArray :=
  (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash parent before.accounts codeParent before.codeWrites target).1

/-- Stops before charged continuations outside the ready domain. It does not
silently drop their gas cost or treat them as a failed transaction. -/
noncomputable def probe {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (before : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (target : AccountAddress) (value : UInt256) : Next Error × Tx Hash := by
  classical
  exact
    let inspected := if 0 < value.toNat then readTarget before target else before
    if 0 < value.toNat ∧ ¬ Alive emptyHash parent before target then
      (.stateChargeRequired,inspected)
    else
      let first := fetchCode emptyHash parent inspected codeParent target
      let resolved := readTarget inspected target
      match first with
      | .error e => (.loadError e,resolved)
      | .ok bytes =>
        if delegation bytes then (.delegatedResolution bytes,resolved)
        else
          let second := fetchCode emptyHash parent resolved codeParent target
          let final := readTarget resolved target
          match second with
          | .error e => (.loadError e,final)
          | .ok bytes => (.ready bytes,final)

theorem loaded_alive {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (before : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (target : AccountAddress) {bytes : ByteArray}
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash parent before.accounts codeParent before.codeWrites target).1 = .ok bytes)
    (nonempty : bytes ≠ ByteArray.empty) : Alive emptyHash parent before target := by
  have hn := loaded_nonempty_hash emptyHash parent before codeParent target loaded nonempty
  obtain ⟨a,found⟩ := ReferenceCodeAccountPresence.nonempty_present ReferenceSourceValueTransfer.Account.codeHash emptyHash parent before.accounts codeParent before.codeWrites target loaded nonempty
  simp only [Alive,found]
  right; left
  simpa only [hashAt,account,found,Option.getD_some] using hn

private theorem read_idempotent {Hash : Type} (before : Tx Hash) (target : AccountAddress) :
    readTarget (readTarget before target) target = readTarget before target := by
  simp [readTarget,ReferenceAccountLookup.tracked,Set.insert_eq_of_mem (Set.mem_insert _ _)]

private theorem fetch_read {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (before : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (target : AccountAddress) :
    fetchCode emptyHash parent (readTarget before target) codeParent target =
      fetchCode emptyHash parent before codeParent target := rfl

theorem ready {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (before : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (target : AccountAddress) (value : UInt256) {bytes : ByteArray}
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash parent before.accounts codeParent before.codeWrites target).1 = .ok bytes)
    (nonempty : bytes ≠ ByteArray.empty) (ordinary : delegation bytes = false) :
    probe emptyHash parent before codeParent target value =
      (.ready bytes,readTarget before target) := by
  have alive := loaded_alive emptyHash parent before codeParent target loaded nonempty
  have first : fetchCode emptyHash parent before codeParent target = .ok bytes := loaded
  by_cases positive : 0 < value.toNat <;>
    simp only [probe,positive,alive,not_true_eq_false,and_false,ite_false,ite_true,
      fetch_read,first,ordinary,Bool.false_eq_true,read_idempotent]

/-- Source branch tests, kernel-checked for both pinned runtime images. -/
theorem pinned_ordinary (kind : ReachableCalls.Contract) :
    ReachableCalls.runtime kind ≠ ByteArray.empty ∧ delegation (ReachableCalls.runtime kind) = false := by
  cases kind <;> decide +kernel

/-- Existing fetched entry already accumulates exactly these idempotent reads. -/
theorem ready_fetched {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (before : Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (kind : ReachableCalls.Contract) (value : UInt256)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash parent before.accounts codeParent before.codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    probe emptyHash parent before codeParent (ReachableCalls.address kind) value =
      (.ready (ReachableCalls.runtime kind),ReferenceTransferredFailure.fetched emptyHash parent before codeParent (ReachableCalls.address kind)) := by
  exact ready emptyHash parent before codeParent _ value loaded (pinned_ordinary kind).1 (pinned_ordinary kind).2

/-- Literal transaction allocation and fresh zero spill meter. This arithmetic
bound is not an assertion that arbitrary supplied meters arose from allocation. -/
theorem allocated_bound (txGas intrinsic : Nat) :
    ReferenceExecutionPotential.potential (ReferenceTransactionWork.initial txGas intrinsic) ≤ 16777216 := by
  simp only [ReferenceExecutionPotential.potential,ReferenceTransactionWork.initial,ReferenceChildMeter.init,
    ReferenceTransactionGas.allocate,Nat.add_zero]
  omega

#print axioms loaded_alive
#print axioms ready
#print axioms pinned_ordinary
#print axioms ready_fetched
#print axioms allocated_bound
end Eip8282.Audit.Integrator.ReferenceSourceDispatch
