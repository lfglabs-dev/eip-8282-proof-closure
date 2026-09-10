import Eip8282.Audit.Integrator.ReferenceAccountLookup

/-! Literal account-default and code-hash read chain from pinned Amsterdam
state_tracker.py. EMPTY_CODE_HASH is tested before any code overlay; an absent
account defaults to EMPTY_ACCOUNT and therefore loads empty code. A completed
nonempty fetch consequently witnesses a present account. The PreState callback
retains its possible error; neither code availability nor a successful fetch
is invented. Code addresses and current_target must be related by actual frame
construction (SYSTEM uses the same target; delegation/CALLCODE need care).
-/
namespace Eip8282.Audit.Integrator.ReferenceCodeAccountPresence
open EvmYul
set_option autoImplicit false

structure CodeParent (Hash Error : Type) where
  writes : Hash → Option ByteArray
  pre : Hash → Except Error ByteArray

/-- Source get_code special-cases the empty hash before the tx/block layers. -/
noncomputable def getCode {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash)
    (p : CodeParent Hash Error) (writes : Hash → Option ByteArray) (hash : Hash) : Except Error ByteArray :=
  if hash = emptyHash then .ok ByteArray.empty
  else match writes hash with
    | some code => .ok code
    | none => match p.writes hash with
      | some code => .ok code
      | none => p.pre hash

/-- get_account records the optional read, defaults absent accounts to
EMPTY_ACCOUNT, then passes its code_hash to get_code. Reads survive errors. -/
noncomputable def load {Account Hash Error : Type} [DecidableEq Hash]
    (codeHash : Account → Hash) (emptyHash : Hash)
    (accountsParent : ReferenceAccountLookup.Parent Account) (accounts : ReferenceAccountLookup.Tx Account)
    (codeParent : CodeParent Hash Error) (codeWrites : Hash → Option ByteArray) (address : AccountAddress) :
    Except Error ByteArray × ReferenceAccountLookup.Tx Account :=
  (getCode emptyHash codeParent codeWrites
    ((ReferenceAccountLookup.peek accountsParent accounts address).map codeHash |>.getD emptyHash),
   ReferenceAccountLookup.tracked accounts address)

theorem absent_empty {Account Hash Error : Type} [DecidableEq Hash]
    (codeHash : Account → Hash) (emptyHash : Hash)
    (accountsParent : ReferenceAccountLookup.Parent Account) (accounts : ReferenceAccountLookup.Tx Account)
    (codeParent : CodeParent Hash Error) (codeWrites : Hash → Option ByteArray) (address : AccountAddress)
    (absent : ReferenceAccountLookup.peek accountsParent accounts address = none) :
    (load codeHash emptyHash accountsParent accounts codeParent codeWrites address).1 = .ok ByteArray.empty := by
  simp only [load,absent,Option.map_none,Option.getD_none,getCode,if_true]

/-- Nonempty code proves presence at the *code address*. This does not equate
that address with a delegated or CALLCODE frame's storage owner by definition. -/
theorem nonempty_present {Account Hash Error : Type} [DecidableEq Hash]
    (codeHash : Account → Hash) (emptyHash : Hash)
    (accountsParent : ReferenceAccountLookup.Parent Account) (accounts : ReferenceAccountLookup.Tx Account)
    (codeParent : CodeParent Hash Error) (codeWrites : Hash → Option ByteArray) (address : AccountAddress)
    {code : ByteArray}
    (loaded : (load codeHash emptyHash accountsParent accounts codeParent codeWrites address).1 = .ok code)
    (nonempty : code ≠ ByteArray.empty) :
    ∃ account, ReferenceAccountLookup.peek accountsParent accounts address = some account := by
  cases found : ReferenceAccountLookup.peek accountsParent accounts address with
  | some account => exact ⟨account,rfl⟩
  | none =>
    have empty := absent_empty codeHash emptyHash accountsParent accounts codeParent codeWrites address found
    have same : code = ByteArray.empty := Except.ok.inj (loaded.symm.trans empty)
    exact False.elim (nonempty same)

/-- SYSTEM's code-probe transaction and execution transaction are fresh
siblings with the same block parent. Only their empty account write overlays
matter; the probe's read bookkeeping is not imported into the execution. -/
theorem fresh_system_owner {Account Hash Error : Type} [DecidableEq Hash]
    (codeHash : Account → Hash) (emptyHash : Hash)
    (accountsParent : ReferenceAccountLookup.Parent Account)
    (probe execution : ReferenceAccountLookup.Tx Account)
    (probeEmpty : ∀ a, probe.writes a = none) (executionEmpty : ∀ a, execution.writes a = none)
    (codeParent : CodeParent Hash Error) (codeWrites : Hash → Option ByteArray) (target : AccountAddress)
    {code : ByteArray}
    (loaded : (load codeHash emptyHash accountsParent probe codeParent codeWrites target).1 = .ok code)
    (nonempty : code ≠ ByteArray.empty) :
    (ReferenceAccountLookup.peek accountsParent execution target).isSome = true := by
  obtain ⟨account,present⟩ := nonempty_present codeHash emptyHash accountsParent probe codeParent codeWrites target loaded nonempty
  have same : ReferenceAccountLookup.peek accountsParent execution target =
      ReferenceAccountLookup.peek accountsParent probe target := by
    simp only [ReferenceAccountLookup.peek,probeEmpty,executionEmpty]
  rw [same,present]
  rfl

#print axioms absent_empty
#print axioms nonempty_present
#print axioms fresh_system_owner
end Eip8282.Audit.Integrator.ReferenceCodeAccountPresence
