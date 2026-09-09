import Eip8282.Audit.Integrator.ExitDrain

/-!
# Ordinary queue arithmetic under an explicit pointer invariant

These lemmas turn the actual word subtraction, cap and pointer branch into
natural FIFO arithmetic. They do not assume desired post-state equations.
Preservation and establishment of the entry invariant remain separate work.
-/
namespace Eip8282.Audit.Integrator.QueueArithmetic

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall)
open SystemSpec

/-- The pointers delimit a non-wrapped logical queue. -/
def Ordered (st : EvmYul.State .EVM) : Prop :=
  (slotW st (UInt256.ofNat 2)).toNat ≤ (slotW st (UInt256.ofNat 3)).toNat

def length (st : EvmYul.State .EVM) : Nat :=
  (slotW st (UInt256.ofNat 3)).toNat - (slotW st (UInt256.ofNat 2)).toNat

theorem capped_sub_toNat (head tail : UInt256) (cap : Nat)
    (hc : cap < UInt256.size) (hord : head.toNat ≤ tail.toNat) :
    (if tail-head < UInt256.ofNat cap then tail-head else UInt256.ofNat cap).toNat =
      min (tail.toNat-head.toNat) cap := by
  have hsub := toNat_sub_of_le tail head hord
  have hcap := toNat_ofNat_lit cap hc
  split
  · rename_i h
    have hn := (lt_iff_toNat _ _).mp h
    rw [hsub, hcap] at hn
    rw [hsub, Nat.min_eq_left (by omega)]
  · rename_i h
    have hn : ¬ (tail-head).toNat < (UInt256.ofNat cap).toNat := h
    rw [hsub, hcap] at hn
    rw [hcap, Nat.min_eq_right (by omega)]

theorem exit_count (q : XiCall .exit) (h : Ordered (entrySt q)) :
    (Exit.drainWord q).toNat = min (length (entrySt q)) 16 :=
  capped_sub_toNat _ _ 16 (by decide) h

theorem deposit_count (q : XiCall .deposit) (h : Ordered (entrySt q)) :
    (Deposit.drainWord q).toNat = min (length (entrySt q)) 64 :=
  capped_sub_toNat _ _ 64 (by decide) h

/-- No addition wrap is possible when the drain count is bounded by length. -/
theorem advanced_head (head tail count : UInt256) (hord : head.toNat ≤ tail.toNat)
    (hc : count.toNat ≤ tail.toNat-head.toNat) :
    (head+count).toNat = head.toNat+count.toNat :=
  toNat_add_of_lt _ _ (by have ht := toNat_lt_size tail; omega)

theorem full_iff (head tail count : UInt256) (hord : head.toNat ≤ tail.toNat)
    (hc : count.toNat ≤ tail.toNat-head.toNat) :
    tail = head+count ↔ count.toNat = tail.toNat-head.toNat := by
  have ha := advanced_head head tail count hord hc
  constructor
  · intro h
    have he := congrArg UInt256.toNat h
    rw [ha] at he
    omega
  · intro h
    have he : tail.toNat = (head+count).toNat := by rw [ha]; omega
    rw [← ofNat_toNat' tail, ← ofNat_toNat' (head+count), he]

/-- The actual slot formula gives exactly full-reset/partial-advance behavior. -/
theorem pointers (st : EvmYul.State .EVM) (target count cds : UInt256)
    (ho : Ordered st) (hc : count.toNat ≤ length st) :
    (expectedSlot st target count cds (UInt256.ofNat 2)).toNat =
      (if count.toNat = length st then 0 else (slotW st (UInt256.ofNat 2)).toNat+count.toNat) ∧
    (expectedSlot st target count cds (UInt256.ofNat 3)).toNat =
      (if count.toNat = length st then 0 else (slotW st (UInt256.ofNat 3)).toNat) := by
  rw [expectedSlot_head, expectedSlot_tail]
  have he := full_iff (slotW st (UInt256.ofNat 2)) (slotW st (UInt256.ofNat 3)) count ho hc
  change (_ ↔ count.toNat = length st) at he
  simp only [he]
  by_cases h : count.toNat = length st
  · simp [h]
  · simp only [h, ↓reduceIte]
    exact ⟨advanced_head _ _ _ ho hc, True.intro⟩

open MessageCall CallBridge CommittedSystem
open Eip8282.Audit.Correspondence (runtimeCode)

/-- Natural queue observations of the actual committed call. -/
def QueueResult (c : Context) (st : EvmYul.State .EVM) (n : Nat) : Prop :=
  ∃ created world gas substate out,
    c.result = .ok (created, world, gas, substate, true, out) ∧
    (worldSlot world c.target (UInt256.ofNat 2)).toNat =
      (if n = length st then 0 else (slotW st (UInt256.ofNat 2)).toNat+n) ∧
    (worldSlot world c.target (UInt256.ofNat 3)).toNat =
      (if n = length st then 0 else (slotW st (UInt256.ofNat 3)).toNat) ∧
    ∀ k, 4 ≤ k.toNat → worldSlot world c.target k = slotW st k

theorem queueResult_of_storage (c : Context) (q : XiCall kind)
    (target count cds : UInt256) (out : ByteArray) (ho : Ordered (entrySt q))
    (hc : count.toNat ≤ length (entrySt q))
    (hr : StorageResult c q target count cds out) : QueueResult c (entrySt q) count.toNat := by
  obtain ⟨world, created, gas, substate, hr, hs⟩ := hr
  obtain ⟨hh, ht⟩ := pointers (entrySt q) target count cds ho hc
  refine ⟨created, world, gas, substate, out, hr, ?_, ?_, ?_⟩
  · rw [hs]; exact hh
  · rw [hs]; exact ht
  · intro k hk
    rw [hs, expectedSlot_record _ _ _ _ _ hk]

theorem deposit_system_queue (c : Context)
    (hcode : c.code = runtimeCode .deposit) (steps : Nat) (hf : c.fuel = steps+1)
    (hsys : Deposit.callerWord (codeCall c hcode steps) = sysW)
    (hperm : c.permission = true) (hg : 2500000 ≤ c.gas.toNat) (hsteps : 8502 ≤ steps)
    (ho : HasOwner (entrySt (codeCall c hcode steps)))
    (hord : Ordered (entrySt (codeCall c hcode steps))) :
    QueueResult c (entrySt (codeCall c hcode steps))
      (min (length (entrySt (codeCall c hcode steps))) 64) := by
  have hr := deposit_system_commits c hcode steps hf hsys hperm hg hsteps ho
  have hn := deposit_count (codeCall c hcode steps) hord
  have res := queueResult_of_storage c (codeCall c hcode steps) _ _ _ _ hord
    (by rw [hn]; exact Nat.min_le_left _ _) hr
  rwa [hn] at res

theorem exit_system_queue (c : Context)
    (hcode : c.code = runtimeCode .exit) (steps : Nat) (hf : c.fuel = steps+1)
    (hsys : Exit.callerWord (codeCall c hcode steps) = sysW)
    (hperm : c.permission = true) (hg : 250000 ≤ c.gas.toNat) (hsteps : 802 ≤ steps)
    (ho : HasOwner (entrySt (codeCall c hcode steps)))
    (hord : Ordered (entrySt (codeCall c hcode steps))) :
    QueueResult c (entrySt (codeCall c hcode steps))
      (min (length (entrySt (codeCall c hcode steps))) 16) := by
  have hr := exit_system_commits c hcode steps hf hsys hperm hg hsteps ho
  have hn := exit_count (codeCall c hcode steps) hord
  have res := queueResult_of_storage c (codeCall c hcode steps) _ _ _ _ hord
    (by rw [hn]; exact Nat.min_le_left _ _) hr
  rwa [hn] at res

#print axioms deposit_system_queue
#print axioms exit_system_queue

#print axioms exit_count
#print axioms deposit_count
#print axioms pointers

end Eip8282.Audit.Integrator.QueueArithmetic
