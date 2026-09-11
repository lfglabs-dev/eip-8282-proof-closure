import Eip8282.Audit.Integrator.CallBridge
import Eip8282.Audit.Integrator.SystemSpec
import Eip8282.Audit.Integrator.ReachableCalls

/-!
# Storage and installed code across Θ's actual value transfer

The credit precedes the debit, and the debit reads the credited map. These
proofs cover all values, caller=target, and absent accounts. Existing accounts
survive; balances are deliberately outside the preservation statement. A newly
created recipient has the default empty code and zero storage, so defaulted
storage/code observations are preserved even at previously absent addresses.
-/

namespace Eip8282.Audit.Integrator.TransferFrame

open EvmYul EvmYul.EVM
open MessageCall CallBridge
open Eip8282.Audit.EntryReach (entrySt slotW)
open Eip8282.Audit.Correspondence (runtimeCode)
open SystemSpec (HasOwner worldSlot)

set_option autoImplicit false

private def observed {α : Type} (world : AccountMap .EVM) (addr : AccountAddress)
    (f : Account .EVM → α) : α :=
  ((world.get? addr).map f).getD (f default)

private theorem lookup_insert (world : AccountMap .EVM) (key addr : AccountAddress)
    (account : Account .EVM) :
    (world.insert key account).get? addr = if key = addr then some account else world.get? addr := by
  exact (Std.TreeMap.getElem?_insert (t := world) (k := key) (a := addr) (v := account)).trans
    (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)

private theorem observed_insert {α : Type} (world : AccountMap .EVM)
    (key addr : AccountAddress) (account : Account .EVM) (f : Account .EVM → α)
    (h : f account = observed world key f) :
    observed (world.insert key account) addr f = observed world addr f := by
  by_cases he : key = addr
  · subst addr
    unfold observed
    rw [lookup_insert, if_pos rfl]
    exact h
  · unfold observed
    rw [lookup_insert, if_neg he]

private theorem insert_keeps_existing {world : AccountMap .EVM}
    (key : AccountAddress) (account : Account .EVM)
    {addr : AccountAddress} {old : Account .EVM} (h : world.get? addr = some old) :
    ∃ current, (world.insert key account).get? addr = some current := by
  by_cases he : key = addr
  · subst addr
    exact ⟨account, Std.TreeMap.getElem?_insert_self⟩
  · refine ⟨old, ?_⟩
    rw [lookup_insert, if_neg he]
    exact h

/-- This is the actual first half of Context.entryWorld, extracted for proof. -/
private def credited (c : Context) : AccountMap .EVM :=
  match c.world.get? c.target with
  | none => if c.value != UInt256.ofNat 0 then
      c.world.insert c.target { (default : Account .EVM) with balance := c.value }
    else c.world
  | some acc => c.world.insert c.target { acc with balance := acc.balance + c.value }

private theorem credited_observation {α : Type} (c : Context) (addr : AccountAddress)
    (f : Account .EVM → α)
    (hb : ∀ (account : Account .EVM) (balance : UInt256),
      f { account with balance := balance } = f account) :
    observed (credited c) addr f = observed c.world addr f := by
  unfold credited
  cases ha : c.world.get? c.target with
  | none =>
      dsimp only
      split
      · apply observed_insert
        rw [hb]
        simp only [observed, ha, Option.map_none, Option.getD_none]
      · rfl
  | some acc =>
      dsimp only
      apply observed_insert
      rw [hb]
      simp only [observed, ha, Option.map_some, Option.getD_some]

private theorem credited_keeps_existing (c : Context) {addr : AccountAddress}
    {old : Account .EVM} (h : c.world.get? addr = some old) :
    ∃ current, (credited c).get? addr = some current := by
  unfold credited
  cases ha : c.world.get? c.target with
  | none =>
      dsimp only
      split
      · exact insert_keeps_existing _ _ h
      · exact ⟨old, h⟩
  | some acc =>
      dsimp only
      exact insert_keeps_existing _ _ h

/-- Every account observation insensitive to balance survives both transfer
steps. This statement includes the default value at a missing account. -/
private theorem entry_observation {α : Type} (c : Context) (addr : AccountAddress)
    (f : Account .EVM → α)
    (hb : ∀ (account : Account .EVM) (balance : UInt256),
      f { account with balance := balance } = f account) :
    observed c.entryWorld addr f = observed c.world addr f := by
  change observed (match (credited c).get? c.caller with
    | none => credited c
    | some acc => (credited c).insert c.caller { acc with balance := acc.balance - c.value }) addr f = _
  cases ha : (credited c).get? c.caller with
  | none => exact credited_observation c addr f hb
  | some acc =>
      rw [observed_insert _ _ _ _ f (by
        rw [hb]
        simp only [observed, ha, Option.map_some, Option.getD_some])]
      exact credited_observation c addr f hb

/-- Any prior account exists after value transfer, including the target and
caller when they are equal. No nonzero-value or distinct-address premise. -/
theorem entry_keeps_existing (c : Context) {addr : AccountAddress} {old : Account .EVM}
    (h : c.world.get? addr = some old) :
    ∃ current, c.entryWorld.get? addr = some current := by
  obtain ⟨middle, hm⟩ := credited_keeps_existing c h
  change ∃ current, (match (credited c).get? c.caller with
    | none => credited c
    | some acc => (credited c).insert c.caller { acc with balance := acc.balance - c.value }).get? addr = some current
  cases (credited c).get? c.caller with
  | none => exact ⟨middle, hm⟩
  | some acc =>
      dsimp only
      exact insert_keeps_existing _ _ hm

/-- Storage reads are unchanged at every address and every word slot, including
zero default reads at an absent account that the credit creates. -/
theorem entry_storage (c : Context) (addr : AccountAddress) (q : UInt256) :
    worldSlot c.entryWorld addr q = worldSlot c.world addr q := by
  exact entry_observation c addr (fun acc => acc.lookupStorage q) (fun _ _ => rfl)

/-- Empty is the code observation for a missing account. -/
def worldCode (world : AccountMap .EVM) (addr : AccountAddress) : ByteArray :=
  ((world.get? addr).map (fun acc => acc.code)).getD .empty

/-- Value transfer cannot alter installed code. A new recipient has empty code. -/
theorem entry_code (c : Context) (addr : AccountAddress) :
    worldCode c.entryWorld addr = worldCode c.world addr :=
  entry_observation c addr (fun acc => acc.code) (fun _ _ => rfl)

/-- Lookup-based account preservation: the old account survives with precisely
the same code and all storage reads. Its balance may have changed. -/
theorem entry_existing_account (c : Context) {addr : AccountAddress} {old : Account .EVM}
    (h : c.world.get? addr = some old) :
    ∃ current, c.entryWorld.get? addr = some current ∧ current.code = old.code ∧
      ∀ q, current.lookupStorage q = old.lookupStorage q := by
  obtain ⟨current, hn⟩ := entry_keeps_existing c h
  refine ⟨current, hn, ?_, ?_⟩
  · have hc := entry_code c addr
    simpa only [worldCode, h, hn, Option.map_some, Option.getD_some] using hc
  · intro q
    have hs := entry_storage c addr q
    simpa only [worldSlot, h, hn, Option.map_some, Option.getD_some] using hs

/-- Direct bridge from the bytecode entry slots back to Θ's pre-transfer world. -/
theorem codeCall_storage (c : Context) {kind : Eip8282.Audit.Model.Kind}
    (hcode : c.code = runtimeCode kind) (steps : Nat) (q : UInt256) :
    slotW (entrySt (codeCall c hcode steps)) q = worldSlot c.world c.target q := by
  rw [← SystemSpec.worldSlot_state]
  exact entry_storage c c.target q

/-- Any storage-only invariant on the pre-transfer target transports to entry. -/
theorem codeCall_storage_invariant (c : Context) {kind : Eip8282.Audit.Model.Kind}
    (hcode : c.code = runtimeCode kind) (steps : Nat) (P : (UInt256 → UInt256) → Prop)
    (h : P (worldSlot c.world c.target)) :
    P (slotW (entrySt (codeCall c hcode steps))) := by
  have he : slotW (entrySt (codeCall c hcode steps)) = worldSlot c.world c.target :=
    funext (codeCall_storage c hcode steps)
  rwa [he]

/-- Installed target existence supplies the owner assumption at code entry. -/
theorem codeCall_hasOwner (c : Context) {kind : Eip8282.Audit.Model.Kind}
    (hcode : c.code = runtimeCode kind) (steps : Nat)
    (h : ∃ account, c.world.get? c.target = some account) :
    HasOwner (entrySt (codeCall c hcode steps)) := by
  obtain ⟨account, ha⟩ := h
  exact entry_keeps_existing c ha

/-- PinnedCall's installed-code witness survives the actual transfer. -/
theorem pinned_installed_at_entry (c : Context) {contract : ReachableCalls.Contract}
    (h : ReachableCalls.PinnedCall contract c) :
    ∃ account, c.entryWorld.get? c.target = some account ∧ account.code = c.code := by
  obtain ⟨old, ho, hc⟩ := h.installed
  obtain ⟨current, hn, hcode, _⟩ := entry_existing_account c ho
  exact ⟨current, hn, hcode.trans hc⟩

/-- PinnedCall discharges the existing direct proofs' owner assumption. The
runtime equality is their existing codeCall argument, not a new value premise. -/
theorem pinned_codeCall_hasOwner (c : Context) {contract : ReachableCalls.Contract}
    (h : ReachableCalls.PinnedCall contract c) {kind : Eip8282.Audit.Model.Kind}
    (hcode : c.code = runtimeCode kind) (steps : Nat) :
    HasOwner (entrySt (codeCall c hcode steps)) :=
  codeCall_hasOwner c hcode steps (by obtain ⟨account, ha, _⟩ := h.installed; exact ⟨account, ha⟩)

#print axioms entry_storage
#print axioms entry_existing_account
#print axioms codeCall_storage_invariant
#print axioms pinned_installed_at_entry
#print axioms pinned_codeCall_hasOwner

end Eip8282.Audit.Integrator.TransferFrame
