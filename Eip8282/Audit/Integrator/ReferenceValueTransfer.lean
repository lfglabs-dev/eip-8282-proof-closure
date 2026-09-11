import Eip8282.Audit.Integrator.ProtocolTransfer
import Eip8282.Audit.Integrator.LedgerCreditSafety

/-! Actual pinned Θ credit-before-debit versus the source's debit-before-credit
value transfer. Reference EL0cc process_call skips zero value; move_ether reads
the recipient after debiting the sender. This proves account-map operation
parity, not Python state-diff representation or outer execution refinement. -/
namespace Eip8282.Audit.Integrator.ReferenceValueTransfer
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open TransferFunding
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

def referenceEntry (c : MessageCall.Context) : AccountMap .EVM :=
  if c.value = (UInt256.ofNat 0) then c.world else ProtocolTransfer.transfer c.world c.caller c.target c.value

private theorem lookup_insert (world : AccountMap .EVM) (key addr : AccountAddress)
    (account : Account .EVM) :
    (world.insert key account).get? addr = if key = addr then some account else world.get? addr := by
  exact (Std.TreeMap.getElem?_insert (t := world) (k := key) (a := addr) (v := account)).trans
    (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)

private theorem add_zero (a : UInt256) : a+(UInt256.ofNat 0) = a := by
  apply congrArg UInt256.mk
  apply Fin.ext
  change (a.toNat+0)%UInt256.size = a.toNat
  simp [Nat.mod_eq_of_lt (toNat_lt_size a)]

private theorem sub_zero (a : UInt256) : a-(UInt256.ofNat 0) = a := by
  apply congrArg UInt256.mk
  apply Fin.ext
  change (UInt256.size-0+a.toNat)%UInt256.size = a.toNat
  simp [Nat.mod_eq_of_lt (toNat_lt_size a)]

private theorem add_sub (a b : UInt256) : (a+b)-b = a := by
  apply congrArg UInt256.mk
  apply Fin.ext
  change (UInt256.size-b.toNat+(a.toNat+b.toNat)%UInt256.size)%UInt256.size = a.toNat
  have ha := toNat_lt_size a
  have hb := toNat_lt_size b
  unfold UInt256.size at *
  omega

private theorem sub_add (a b : UInt256) : (a-b)+b = a := by
  apply congrArg UInt256.mk
  apply Fin.ext
  change ((UInt256.size-b.toNat+a.toNat)%UInt256.size+b.toNat)%UInt256.size = a.toNat
  have ha := toNat_lt_size a
  have hb := toNat_lt_size b
  unfold UInt256.size at *
  omega

private theorem insert_same (world : AccountMap .EVM) (key addr : AccountAddress)
    (account : Account .EVM) (h : world.get? key = some account) :
    (world.insert key account).get? addr = world.get? addr := by
  rw [lookup_insert]
  split
  · rename_i he
    exact he ▸ h.symm
  · rfl

/-- Pointwise equality retains account presence, full account fields and
aliasing. No tree representation equality or supplied final balance is used. -/
theorem entry_lookup (c : MessageCall.Context)
    (funded : c.value.toNat ≤ worldBalance c.world c.caller) (addr : AccountAddress) :
    c.entryWorld.get? addr = (referenceEntry c).get? addr := by
  by_cases hz : c.value = (UInt256.ofNat 0)
  · simp only [referenceEntry,hz,if_true]
    unfold MessageCall.Context.entryWorld
    rw [hz]
    cases ht : c.world.get? c.target with
    | none =>
      simp only [show (((UInt256.ofNat 0) : UInt256) != (UInt256.ofNat 0)) = false from rfl,Bool.false_eq_true,if_false]
      cases hs : c.world.get? c.caller with
      | none => rfl
      | some sender =>
        simp only [sub_zero]
        exact insert_same c.world c.caller addr sender hs
    | some target =>
      simp only [add_zero]
      have hlookup := insert_same c.world c.target c.caller target ht
      rw [hlookup]
      cases hs : c.world.get? c.caller with
      | none => exact insert_same c.world c.target addr target ht
      | some sender =>
        simp only [sub_zero]
        rw [insert_same _ c.caller addr sender (hlookup.trans hs)]
        exact insert_same c.world c.target addr target ht
  · have hpositive : 0 < c.value.toNat := by
      by_contra h
      apply hz
      apply (eq_ofNat_iff_toNat c.value 0 (by decide)).mpr
      omega
    obtain ⟨sender,hs⟩ : ∃ sender, c.world.get? c.caller = some sender := by
      cases he : c.world.get? c.caller with
      | none =>
        have hf : c.value.toNat ≤ 0 := by
          simpa only [worldBalance,he,Option.map_none,Option.getD_none] using funded
        omega
      | some sender => exact ⟨sender,rfl⟩
    have hb : (c.value != ((UInt256.ofNat 0) : UInt256)) = true := by
      change (c.value.val != (UInt256.ofNat 0).val) = true
      apply bne_iff_ne.mpr
      intro he
      exact hz (congrArg UInt256.mk he)
    unfold referenceEntry
    rw [if_neg hz]
    unfold MessageCall.Context.entryWorld ProtocolTransfer.transfer ProtocolTransfer.debit AccountMap.increaseBalance
    by_cases he : c.caller = c.target
    · rw [he] at hs ⊢
      rw [hs]
      simp only [lookup_insert,if_true,Option.getD_some,add_sub,sub_add]
      by_cases haddr : c.target = addr <;> simp [haddr]
    · have he' : c.target ≠ c.caller := Ne.symm he
      cases ht : c.world.get? c.target with
      | none =>
        simp only [hb,if_true,lookup_insert,he,he',if_false,hs,ht,Option.getD_some]
        by_cases ha : c.caller = addr <;> by_cases ht' : c.target = addr <;> simp_all
      | some target =>
        simp only [lookup_insert,he,he',if_false,hs,ht,Option.getD_some]
        by_cases ha : c.caller = addr <;> by_cases ht' : c.target = addr <;> simp_all

/-- The checked reference subtraction and subsequent addition both fit.
The recipient is read after debit, so aliases need no extra exclusion. -/
theorem checked (c : MessageCall.Context)
    (funded : c.value.toNat ≤ worldBalance c.world c.caller)
    (total : worldFunds c.world < UInt256.size) :
    c.value.toNat ≤ worldBalance c.world c.caller ∧
      worldBalance (ProtocolTransfer.debit c.world c.caller c.value) c.target + c.value.toNat < UInt256.size ∧
      ∀ addr, c.entryWorld.get? addr = (referenceEntry c).get? addr := by
  exact ⟨funded,(ProtocolMigrationLedger.recipient_add_bound c.world c.caller c.target c.value funded).trans_lt total,
    entry_lookup c funded⟩

/-- Literal genesis/credit history supplies the sum bound used by the checked
reference transfer. Reference state-diff and canonical ledger extraction remain
separate; no chosen maximum recipient balance is an input. -/
theorem from_ledger (c : MessageCall.Context) {p w s credits : Nat}
    (ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world p w s credits c.world)
    (counts : ProtocolCreditEnvelope.Counts p w s)
    (funded : c.value.toNat ≤ worldBalance c.world c.caller) :
    worldBalance (ProtocolTransfer.debit c.world c.caller c.value) c.target + c.value.toNat < UInt256.size ∧
      ∀ addr, c.entryWorld.get? addr = (referenceEntry c).get? addr := by
  have ht := FundingHistory.trace_funds (ProtocolCreditEnvelope.ledger_bound ledger).1
  exact (checked c funded (ht.trans_lt (LedgerCreditSafety.genesis_budget ledger counts))).2

#print axioms entry_lookup
#print axioms checked
#print axioms from_ledger
end Eip8282.Audit.Integrator.ReferenceValueTransfer
