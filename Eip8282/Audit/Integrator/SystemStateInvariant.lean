import Eip8282.Audit.Integrator.SuccessfulSystem
import Eip8282.Audit.Integrator.AccountedState
import Eip8282.Audit.Integrator.FundedDomain
import Eip8282.Audit.Integrator.QueueInvariant

/-!
# Structural invariants across actual completed SYSTEM calls

Actual success consumes the natural capped queue prefix and returns its exact
bytes; actual failure restores the journal and consumes nothing. Both preserve
the same independent append budget and enabled mathematical-fee safe domain.
There are no execution-resource, permission, or assumed post-state premises.

The initial budget, fee safety, queue representation and exit source width are
explicit structural invariants, not claimed protocol-history facts. Control uses
the exact calldata-size word: no unrestricted natural nonempty-calldata latch
claim is made. Evaluator OutOfFuel is outside the completed Θ result premise.
-/
namespace Eip8282.Audit.Integrator.SystemStateInvariant

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall bytes)
open Eip8282.Audit.Correspondence (runtimeCode)
open MessageCall CallBridge AccountedState FundedDomain SystemSpec QueueInvariant

/-- Only successful completion consumes queue entries. -/
def consumed (success : Bool) (length cap : Nat) : Nat :=
  if success then min length cap else 0

/-- The independent expected map and output belong to the supplied actual Θ
result, even though the reused receipt packages its world existentially. -/
private theorem actual_storage (c : Context) (q : XiCall kind)
    (target drained cds : UInt256) (data : ByteArray)
    (hr : CommittedSystem.StorageResult c q target drained cds data)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,true,out)) :
    worldSlot world c.target = expectedSlot (entrySt q) target drained cds ∧ out = data := by
  obtain ⟨ew,cr,g,es,he,hs⟩ := hr
  have hh := h.symm.trans he
  simp only [Except.ok.injEq, Prod.mk.injEq] at hh
  obtain ⟨_,hw,_,_,_,hout⟩ := hh
  exact ⟨by rw [hw]; exact funext hs,hout⟩

private theorem map_preserves (q : XiCall kind) (target drained cds : UInt256)
    (budget : Nat) (hbudget : budget < 2^128)
    (hb : Bounded budget (slotW (entrySt q)))
    (hsafe : EnabledSafe target.toNat (slotW (entrySt q)))
    (htarget : target.toNat ≤ 8) (queue : List (Record kind))
    (hr : Represents kind (slotW (entrySt q)) queue) (hn : drained.toNat ≤ queue.length) :
    Bounded budget (expectedSlot (entrySt q) target drained cds) ∧
    EnabledSafe target.toNat (expectedSlot (entrySt q) target drained cds) ∧
    Represents kind (expectedSlot (entrySt q) target drained cds) (queue.drop drained.toNat) := by
  have hlen : queue.length = QueueArithmetic.length (entrySt q) := hr.length_eq
  exact ⟨AccountedState.system (entrySt q) target drained cds hb
      (hbudget.trans (by decide)) (by omega),
    expected_system_safe (entrySt q) target drained cds htarget hsafe,
    represents_drain (entrySt q) target drained cds queue hr hn⟩

/-- Every completed exit SYSTEM call preserves the structural invariants.
On success the exact returned bytes are the oldest capped prefix. On failure
there is no drain and no claim about returned bytes. -/
theorem exit_system (c : Context) (hcode : c.code = runtimeCode .exit)
    (hsys : c.caller = EvmRunner.sysAddr)
    (ho : ∃ account, c.world.get? c.target = some account)
    (budget : Nat) (hbudget : budget < 2^128)
    (hb : Bounded budget (worldSlot c.world c.target))
    (hsafe : EnabledSafe 2 (worldSlot c.world c.target))
    (queue : List (Record .exit)) (hr : Represents .exit (worldSlot c.world c.target) queue)
    (hsource : SourceWidth queue)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,success,out)) :
    Bounded budget (worldSlot world c.target) ∧
    EnabledSafe 2 (worldSlot world c.target) ∧
    Represents .exit (worldSlot world c.target) (queue.drop (consumed success queue.length 16)) ∧
    SourceWidth (queue.drop (consumed success queue.length 16)) ∧
    (success = true → bytes out = (queue.take (min queue.length 16)).flatMap exitBytes) := by
  cases success with
  | false =>
    have hw := (failure_restores_journal c created world gas substate out h).1
    simp only [hw, consumed, Bool.false_eq_true, ↓reduceIte, List.drop_zero]
    exact ⟨hb,hsafe,hr,hsource,by intro hh; cases hh⟩
  | true =>
    let q := codeCall c hcode (c.fuel-1)
    have hbq : Bounded budget (slotW (entrySt q)) :=
      TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1) (Bounded budget) hb
    have hsq : EnabledSafe 2 (slotW (entrySt q)) :=
      TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1) (EnabledSafe 2) hsafe
    have hrq : Represents .exit (slotW (entrySt q)) queue :=
      TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1) (fun read => Represents .exit read queue) hr
    have hc := QueueArithmetic.exit_count q hrq.ordered
    have hl : queue.length = QueueArithmetic.length (entrySt q) := hrq.length_eq
    rw [← hl] at hc
    have hn : (Exit.drainWord q).toNat ≤ queue.length := by rw [hc]; exact Nat.min_le_left _ _
    have hreceipt := SuccessfulSystem.exit_system c hcode hsys ho h
    obtain ⟨hread,hout⟩ := actual_storage c q _ _ _ _ hreceipt h
    obtain ⟨hbp,hsp,hrp⟩ := map_preserves q (UInt256.ofNat 2) _ _ budget hbudget hbq hsq
      (by decide) queue hrq hn
    simp only [consumed, ↓reduceIte]
    refine ⟨by rwa [hread],by rwa [hread],?_,source_width_drop queue _ hsource,?_⟩
    · rw [hread,← hc]
      exact hrp
    · intro _
      rw [hout,ExitDrain.exitData_bytes q (source_width_at (entrySt q) queue hrq hsource _ hn),
        exit_fifo_list (entrySt q) queue hrq _ hn,hc]

/-- Deposit counterpart, including the independent 184-byte record encoding
with each stored amount recoded to little endian in the returned prefix. -/
theorem deposit_system (c : Context) (hcode : c.code = runtimeCode .deposit)
    (hsys : c.caller = EvmRunner.sysAddr)
    (ho : ∃ account, c.world.get? c.target = some account)
    (budget : Nat) (hbudget : budget < 2^128)
    (hb : Bounded budget (worldSlot c.world c.target))
    (hsafe : EnabledSafe 8 (worldSlot c.world c.target))
    (queue : List (Record .deposit)) (hr : Represents .deposit (worldSlot c.world c.target) queue)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,success,out)) :
    Bounded budget (worldSlot world c.target) ∧
    EnabledSafe 8 (worldSlot world c.target) ∧
    Represents .deposit (worldSlot world c.target) (queue.drop (consumed success queue.length 64)) ∧
    (success = true → bytes out = (queue.take (min queue.length 64)).flatMap depositBytes) := by
  cases success with
  | false =>
    have hw := (failure_restores_journal c created world gas substate out h).1
    simp only [hw, consumed, Bool.false_eq_true, ↓reduceIte, List.drop_zero]
    exact ⟨hb,hsafe,hr,by intro hh; cases hh⟩
  | true =>
    let q := codeCall c hcode (c.fuel-1)
    have hbq : Bounded budget (slotW (entrySt q)) :=
      TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1) (Bounded budget) hb
    have hsq : EnabledSafe 8 (slotW (entrySt q)) :=
      TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1) (EnabledSafe 8) hsafe
    have hrq : Represents .deposit (slotW (entrySt q)) queue :=
      TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1) (fun read => Represents .deposit read queue) hr
    have hc := QueueArithmetic.deposit_count q hrq.ordered
    have hl : queue.length = QueueArithmetic.length (entrySt q) := hrq.length_eq
    rw [← hl] at hc
    have hn : (Deposit.drainWord q).toNat ≤ queue.length := by rw [hc]; exact Nat.min_le_left _ _
    have hreceipt := SuccessfulSystem.deposit_system c hcode hsys ho h
    obtain ⟨hread,hout⟩ := actual_storage c q _ _ _ _ hreceipt h
    obtain ⟨hbp,hsp,hrp⟩ := map_preserves q (UInt256.ofNat 8) _ _ budget hbudget hbq hsq
      (by decide) queue hrq hn
    simp only [consumed, ↓reduceIte]
    refine ⟨by rwa [hread],by rwa [hread],?_,?_⟩
    · rw [hread,← hc]
      exact hrp
    · intro _
      rw [hout,DepositDrain.depositData_bytes q,deposit_fifo_list (entrySt q) queue hrq _ hn,hc]

/-- Scalar history interface: no logical queue or source-width premise is
needed to preserve the independent budget and enabled fee safety. -/
theorem exit_state (c : Context) (hcode : c.code = runtimeCode .exit)
    (hsys : c.caller = EvmRunner.sysAddr)
    (ho : ∃ account, c.world.get? c.target = some account)
    (budget : Nat) (hbudget : budget < 2^128)
    (hb : Bounded budget (worldSlot c.world c.target))
    (hsafe : EnabledSafe 2 (worldSlot c.world c.target))
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,success,out)) :
    Bounded budget (worldSlot world c.target) ∧ EnabledSafe 2 (worldSlot world c.target) := by
  cases success with
  | false =>
    have hw := (failure_restores_journal c created world gas substate out h).1
    rw [hw]
    exact ⟨hb,hsafe⟩
  | true =>
    let q := codeCall c hcode (c.fuel-1)
    have hbq : Bounded budget (slotW (entrySt q)) :=
      TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1) (Bounded budget) hb
    have hsq : EnabledSafe 2 (slotW (entrySt q)) :=
      TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1) (EnabledSafe 2) hsafe
    have hc := QueueArithmetic.exit_count q hbq.ordered
    have hn : (Exit.drainWord q).toNat ≤ QueueArithmetic.length (entrySt q) := by
      rw [hc]
      exact Nat.min_le_left _ _
    have hreceipt := SuccessfulSystem.exit_system c hcode hsys ho h
    obtain ⟨hread,_⟩ := actual_storage c q _ _ _ _ hreceipt h
    rw [hread]
    exact ⟨AccountedState.system (entrySt q) (UInt256.ofNat 2) _ _ hbq
      (hbudget.trans (by decide)) hn,
      expected_system_safe (entrySt q) (UInt256.ofNat 2) _ _ (by decide) hsq⟩

/-- Scalar history interface: no logical queue or source-width premise is
needed to preserve the independent budget and enabled fee safety. -/
theorem deposit_state (c : Context) (hcode : c.code = runtimeCode .deposit)
    (hsys : c.caller = EvmRunner.sysAddr)
    (ho : ∃ account, c.world.get? c.target = some account)
    (budget : Nat) (hbudget : budget < 2^128)
    (hb : Bounded budget (worldSlot c.world c.target))
    (hsafe : EnabledSafe 8 (worldSlot c.world c.target))
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,success,out)) :
    Bounded budget (worldSlot world c.target) ∧ EnabledSafe 8 (worldSlot world c.target) := by
  cases success with
  | false =>
    have hw := (failure_restores_journal c created world gas substate out h).1
    rw [hw]
    exact ⟨hb,hsafe⟩
  | true =>
    let q := codeCall c hcode (c.fuel-1)
    have hbq : Bounded budget (slotW (entrySt q)) :=
      TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1) (Bounded budget) hb
    have hsq : EnabledSafe 8 (slotW (entrySt q)) :=
      TransferFrame.codeCall_storage_invariant c hcode (c.fuel-1) (EnabledSafe 8) hsafe
    have hc := QueueArithmetic.deposit_count q hbq.ordered
    have hn : (Deposit.drainWord q).toNat ≤ QueueArithmetic.length (entrySt q) := by
      rw [hc]
      exact Nat.min_le_left _ _
    have hreceipt := SuccessfulSystem.deposit_system c hcode hsys ho h
    obtain ⟨hread,_⟩ := actual_storage c q _ _ _ _ hreceipt h
    rw [hread]
    exact ⟨AccountedState.system (entrySt q) (UInt256.ofNat 8) _ _ hbq
      (hbudget.trans (by decide)) hn,
      expected_system_safe (entrySt q) (UInt256.ofNat 8) _ _ (by decide) hsq⟩

#print axioms exit_system
#print axioms deposit_system
#print axioms exit_state
#print axioms deposit_state

end Eip8282.Audit.Integrator.SystemStateInvariant
