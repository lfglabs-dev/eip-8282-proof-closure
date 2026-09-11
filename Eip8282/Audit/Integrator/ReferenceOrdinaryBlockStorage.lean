import Eip8282.Audit.Integrator.ReferenceOrdinaryBlockAccounts
import Eip8282.Audit.Integrator.ReferenceSystemBlockFootprint
import Eip8282.Audit.Integrator.ReferenceSystemBlockAccess

/-! Finite actual write support for ordinary successful and failed receipts.
Failure read metadata is retained as the actual set; this module does not
claim its enumeration, final BAL serialization or final block capacity.
Consumer: ordinary transaction block incorporation. -/
namespace Eip8282.Audit.Integrator.ReferenceOrdinaryBlockStorage
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceCheckedDispatch
open ReferenceStorageView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-- Only the final write dictionary, never executed append occurrences. -/
def Writes (owner : AccountAddress) (tx : Tx) (keys : List UInt256) : Prop :=
  ∀ a k value, tx.writes a k = some value → a = owner ∧ ∃ q ∈ keys, k = q.toByteArray

private theorem no_writes {owner : AccountAddress} {tx : Tx} {keys : List UInt256}
    (empty : tx.writes = fun _ _ => none) : Writes owner tx keys := by
  intro a k value written
  rw [empty] at written
  contradiction

/-- The same actual last dispatch and actual settlement yield finite writes.
A revert or caught fault uses the original fresh write overlay. -/
theorem receipt {kind : Eip8282.Audit.Model.Kind} {parent : Parent}
    {v finish : View} {warm finalWarm : Warm} {meter final : ReferenceMeterRollback.Meter}
    {events : List ReferenceMeterPath.Event} {destinations : List Nat} {ownerExists : Bool}
    {snapshot : Tx} {outcome : Outcome} {receipt : ReferenceCheckedFrameOutcome.Receipt}
    (trace : ReferenceCheckedRuntimeTrace.Run kind parent v warm meter finish finalWarm final events)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (fresh : v.storage = ReferenceRuntimeStateBalance.emptyTx)
    (snapshotFresh : snapshot.writes = fun _ _ => none)
    (last : run destinations ownerExists parent finish finalWarm final ByteArray.empty = outcome)
    (settled : ReferenceCheckedFrameOutcome.settle snapshot [] finalWarm outcome = .returned receipt) :
    ∃ keys, Writes v.env.codeOwner receipt.storage keys := by
  have support : ReferenceSystemBlockFootprint.Support v.env.codeOwner v.storage [] := by
    rw [fresh]
    exact ReferenceSystemBlockFootprint.empty _
  obtain ⟨env,keys,support⟩ := ReferenceSystemBlockFootprint.checked trace stack aligned support
  refine ⟨keys,?_⟩
  cases outcome with
  | continued v w m e => contradiction
  | unsupported t v w m o => contradiction
  | terminal ended =>
    obtain ⟨endedEnv,endedSupport⟩ := ReferenceSystemBlockFootprint.terminal last support
    simp only [ReferenceCheckedFrameOutcome.settle] at settled
    split at settled
    · cases settled
      exact no_writes snapshotFresh
    · cases settled
      simpa only [Writes,ReferenceCheckedFrameOutcome.success,List.append_nil,endedEnv,env] using endedSupport.writes
  | eof endView endWarm endMeter output =>
    have fields := ReferenceCheckedEOF.fields last
    cases settled
    simpa only [Writes,ReferenceCheckedFrameOutcome.success,List.append_nil,← fields.1,env] using support.writes
  | failed fault endView endWarm endMeter output =>
    simp only [ReferenceCheckedFrameOutcome.settle] at settled
    split at settled
    · cases settled
      exact no_writes snapshotFresh
    · contradiction

private theorem erased {owner : AccountAddress} {tx : Tx} {keys : List UInt256}
    (support : Writes owner tx keys) (address : AccountAddress) :
    Writes owner (ReferenceSourceValueTransfer.eraseStorage tx address) keys := by
  intro a k value written
  change (if a = address then none else tx.writes a k) = some value at written
  split at written
  · contradiction
  · exact support a k value written

private theorem modified {Hash : Type} [DecidableEq Hash]
    {owner : AccountAddress} {keys : List UInt256} (emptyHash : Hash)
    (parent : ReferenceSourceValueTransfer.Parent Hash) (tx : ReferenceSourceValueTransfer.Tx Hash)
    (address : AccountAddress) (balance : UInt256) (support : Writes owner tx.storage keys) :
    Writes owner (ReferenceSourceValueTransfer.modifyBalance emptyHash parent tx address balance).storage keys := by
  unfold ReferenceSourceValueTransfer.modifyBalance
  dsimp only
  split
  · exact erased support address
  · exact support

private theorem credited {Hash : Type} [DecidableEq Hash]
    {owner : AccountAddress} {keys : List UInt256} (emptyHash : Hash)
    (parent : ReferenceSourceValueTransfer.Parent Hash) (tx : ReferenceSourceValueTransfer.Tx Hash)
    (address : AccountAddress) (amount : UInt256) (support : Writes owner tx.storage keys) :
    Writes owner (ReferenceSourceFeeCredit.credit emptyHash parent tx address amount).2.storage keys := by
  unfold ReferenceSourceFeeCredit.credit
  dsimp only
  split
  · exact modified emptyHash parent _ address _ support
  · exact support

/-- Ordered fee credits can remove writes during empty cleanup, but cannot
introduce a foreign or untyped storage write. -/
theorem fees {Hash : Type} [DecidableEq Hash]
    {owner : AccountAddress} {keys : List UInt256} (emptyHash : Hash)
    (parent : ReferenceSourceValueTransfer.Parent Hash) (tx : ReferenceSourceValueTransfer.Tx Hash)
    (payer beneficiary : AccountAddress) (price base : Nat) (gas : ReferenceTransactionGas.Settlement)
    (support : Writes owner tx.storage keys) :
    Writes owner (ReferenceSourceFeeDisbursement.run emptyHash parent tx payer beneficiary price base gas).2.storage keys := by
  unfold ReferenceSourceFeeDisbursement.run
  dsimp only
  split
  · split
    · split
      · exact credited emptyHash parent tx payer _ support
      · split
        · split <;> exact credited emptyHash parent _ beneficiary _ (credited emptyHash parent tx payer _ support)
        · exact credited emptyHash parent tx payer _ support
    · exact support
  · exact support

/-- All enumerated entries are actual writes, with unique keys; every actual
write is covered. Key conversion is already proved for the typed source keys. -/
theorem complete {owner : AccountAddress} {tx : Tx} {keys : List UInt256} (support : Writes owner tx keys) :
    ((ReferenceSystemBlockAccess.entries owner tx keys).map Prod.fst).Nodup ∧
    (∀ pair ∈ ReferenceSystemBlockAccess.entries owner tx keys, tx.writes owner pair.1 = some pair.2) ∧
    ∀ a k value, tx.writes a k = some value → a = owner ∧ (k,value) ∈ ReferenceSystemBlockAccess.entries owner tx keys := by
  refine ⟨ReferenceSystemBlockAccess.entries_unique _ _ _,ReferenceSystemBlockAccess.entries_sound _ _ _,?_⟩
  intro a k value written
  obtain ⟨rfl,q,member,rfl⟩ := support a k value written
  refine ⟨rfl,List.mem_filterMap.mpr ⟨q,?_,?_⟩⟩
  · simpa only [List.mem_dedup] using member
  · simp only [written,Option.map_some]

#print axioms receipt
#print axioms fees
#print axioms complete
end Eip8282.Audit.Integrator.ReferenceOrdinaryBlockStorage
