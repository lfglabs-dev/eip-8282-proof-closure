import Eip8282.Audit.Integrator.ReferenceFullFeeBlockTotal

/-! Injected functional journals/builders, not canonical histories or a
counterexample to the existing FullFeeTotal theorem. These witnesses expose
why balance-only observations do not supply nonce admission, and kill wrong
BAL merge order, nonce replacement and transaction/frame rollback boundaries. -/
namespace Eip8282.Tests.ReferenceOrdinaryBlock
open EvmYul EvmYul.EVM Eip8282.Audit.Integrator
open ReferenceSourceValueTransfer ReferenceOrdinaryBlockNonce
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private def blank : Tx Bool := ReferenceCheckedSystemEntry.before Bool
private noncomputable def parent (a : AccountAddress) (nonce : Nat) : Parent Bool := by
  classical
  exact ⟨fun _ => none,fun x => if x = a then some ⟨nonce,⟨0⟩,false⟩ else none⟩

/-- Even fully fresh source journals with equal balance observations can
read arbitrary different nonces. This is a projection counterexample only. -/
theorem balances_do_not_bind_nonce (a : AccountAddress) (n m : Nat) :
    (∀ x, (account false (parent a n) blank x).balance = (account false (parent a m) blank x).balance) ∧
    (account false (parent a n) blank a).nonce = n ∧
    (account false (parent a m) blank a).nonce = m := by
  classical
  simp [account,blank,ReferenceCheckedSystemEntry.before,ReferenceAccountLookup.peek,
    ReferenceAccountLookup.parentRead,parent,empty]
  intro x
  by_cases same : x = a <;> simp only [same,if_true,if_false,Option.getD_some,Option.getD_none]

/-- An injected source nonce at U64.MAX survives zero prepayment as MAX+1,
then fails source U64 conversion. Balance agreement alone cannot forbid it. -/
theorem unbound_nonce_conversion_fails (a : AccountAddress) :
    (ReferenceSourcePrepayment.pay false (parent a (2^64-1)) blank a 0 0).1 = .ok () ∧
    checkedNonce (account false (parent a (2^64-1))
      (ReferenceSourcePrepayment.pay false (parent a (2^64-1)) blank a 0 0).2 a).nonce = none := by
  have paid := ReferenceSourcePrepayment.successful_account false (parent a (2^64-1)) blank a a 0 0 (by omega)
  refine ⟨paid.1,?_⟩
  rw [paid.2]
  simp [account,blank,ReferenceCheckedSystemEntry.before,ReferenceAccountLookup.peek,
    ReferenceAccountLookup.parentRead,parent,empty,checkedNonce]

/-- Largest admitted before-nonce is MAX-1, and increment reaches MAX
without truncation. Using ≤MAX in admission is killed by the preceding test. -/
theorem admitted_edge :
    checkedNonce ((2^64-2)+1) = some (UInt64.ofNat (2^64-1)) ∧
    (UInt64.ofNat ((2^64-2)+1)).toNat = 2^64-1 := by decide +kernel

/-- Failed frame restoration uses the prepaid transaction snapshot. Restoring
the pretransaction journal instead would lose the admitted nonce increment. -/
theorem frame_rollback_retains_nonce (a : AccountAddress) (r : ReferenceCheckedFrameOutcome.Receipt) :
    let paid := (ReferenceSourcePrepayment.pay false (parent a 6) blank a 0 0).2
    let live := writeAccount paid a (some ⟨99,⟨0⟩,false⟩)
    (account false (parent a 6) (ReferenceSettledAccountJournal.journal paid live live.accounts
      {r with error := some .reverted}) a).nonce = 7 := by
  dsimp only
  change (account false (parent a 6) (ReferenceSourcePrepayment.pay false (parent a 6) blank a 0 0).2 a).nonce = 7
  rw [(ReferenceSourcePrepayment.successful_account false (parent a 6) blank a a 0 0 (by omega)).2]
  simp [account,blank,ReferenceCheckedSystemEntry.before,ReferenceAccountLookup.peek,
    ReferenceAccountLookup.parentRead,parent,empty]

/-- Nonce history keeps the maximum at the first equal index. A generic
balance-style replacement would reduce 9 to 7 and is therefore incorrect. -/
theorem nonce_keeps_maximum :
    ReferenceOrdinaryBlockAccess.highest 3 7 [⟨2,4⟩,⟨3,9⟩,⟨3,1⟩] = [⟨2,4⟩,⟨3,9⟩,⟨3,1⟩] ∧
    ReferenceOrdinaryBlockAccess.replace 3 (7 : UInt64) [⟨2,4⟩,⟨3,9⟩,⟨3,1⟩] = [⟨2,4⟩,⟨3,7⟩,⟨3,1⟩] := by
  exact ⟨rfl,rfl⟩

/-- A larger nonce updates the first same-index item only, exactly as the
source loop returns after its first match. -/
theorem nonce_updates_first :
    ReferenceOrdinaryBlockAccess.highest 3 10 [⟨2,4⟩,⟨3,9⟩,⟨3,1⟩] = [⟨2,4⟩,⟨3,10⟩,⟨3,1⟩] := by
  rfl

/-- Candidate addresses can alias; the final dictionary entry is enumerated
once. This cardinality is not an executed or committed append count. -/
theorem account_alias_enumerated_once (a : AccountAddress) :
    ReferenceOrdinaryBlockAccess.entries (writeAccount blank a (some ⟨1,⟨2⟩,false⟩)).accounts [a,a,a] =
      [(a,some ⟨1,⟨2⟩,false⟩)] := by
  classical
  simp [ReferenceOrdinaryBlockAccess.entries,writeAccount]

private def builder : ReferenceOrdinaryBlockAccess.Builder :=
  ⟨⟨0,∅,fun _ _ => none⟩,fun _ => [],fun _ => [],fun _ => []⟩
private def codeParent : ReferenceCodeAccountPresence.CodeParent Bool Unit := ⟨fun _ => none,fun _ => .error ()⟩

/-- Merge-before-BAL loses the actual nonce increment, even though account
and storage dictionaries later look correct. The real composition uses old
parent comparisons and only merges after both BAL update phases succeed. -/
theorem account_merge_order (a : AccountAddress) :
    ((ReferenceOrdinaryBlockAccess.one false (parent a 6) codeParent (fun _ => none) a (some ⟨7,⟨0⟩,false⟩) builder).map
      (fun b => b.nonces a)) = some [⟨0,7⟩] ∧
    ((ReferenceOrdinaryBlockAccess.one false
      (ReferenceOrdinaryBlockSettlement.commitAccounts (parent a 6) (writeAccount blank a (some ⟨7,⟨0⟩,false⟩)))
      codeParent (fun _ => none) a (some ⟨7,⟨0⟩,false⟩) builder).map (fun b => b.nonces a)) = some [] := by
  classical
  simp [ReferenceOrdinaryBlockAccess.one,ReferenceAccountLookup.parentRead,parent,empty,checkedNonce,
    ReferenceOrdinaryBlockAccess.addNonce,ReferenceOrdinaryBlockAccess.highest,builder,
    ReferenceOrdinaryBlockSettlement.commitAccounts,writeAccount]

#print axioms account_merge_order
#print axioms balances_do_not_bind_nonce
#print axioms unbound_nonce_conversion_fails
#print axioms admitted_edge
#print axioms frame_rollback_retains_nonce
#print axioms nonce_keeps_maximum
#print axioms nonce_updates_first
#print axioms account_alias_enumerated_once
end Eip8282.Tests.ReferenceOrdinaryBlock
