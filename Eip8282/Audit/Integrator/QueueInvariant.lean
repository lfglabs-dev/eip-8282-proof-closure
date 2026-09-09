import Eip8282.Audit.Integrator.CommittedAppend
import Eip8282.Audit.Integrator.QueueArithmetic
import Eip8282.Audit.Integrator.DepositDrain

/-!
# A local FIFO invariant over physical word vectors

The small representation below relates an ordinary list to queue pointers and
storage slots. It carries explicit ordering and physical-window bounds. The
preservation lemmas do not establish those bounds from protocol histories.
-/
namespace Eip8282.Audit.Integrator.QueueInvariant

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Model (Kind)
open AppendStorage (stride AppendFits entryTail recordWord recordKey)
open SystemSpec (worldSlot HasOwner)

set_option maxHeartbeats 1200000

/-- A physical vector of six deposit words or three exit words. -/
abbrev Record (kind : Kind) := Fin (stride kind) → UInt256

def head (read : UInt256 → UInt256) := (read (UInt256.ofNat 2)).toNat
def tail (read : UInt256 → UInt256) := (read (UInt256.ofNat 3)).toNat

def key (kind : Kind) (index : Nat) (j : Fin (stride kind)) : UInt256 :=
  UInt256.ofNat (4 + stride kind * index + j.val)

structure Represents (kind : Kind) (read : UInt256 → UInt256) (queue : List (Record kind)) : Prop where
  ordered : head read ≤ tail read
  window : 4 + stride kind * tail read ≤ UInt256.size
  length_eq : queue.length = tail read - head read
  contents : ∀ (i : Nat) (hi : i < queue.length) (j : Fin (stride kind)),
    read (key kind (head read+i) j) = queue[i] j

/-- Zero pointers represent an empty queue, regardless of stale record slots. -/
theorem represents_empty (kind : Kind) (read : UInt256 → UInt256)
    (hh : head read = 0) (ht : tail read = 0) : Represents kind read [] := by
  constructor
  · rw [hh, ht]
  · simp only [ht, Nat.mul_zero, Nat.add_zero]; decide
  · simp [hh, ht]
  · intro i hi; simp at hi

theorem stride_pos (kind : Kind) : 0 < stride kind := by cases kind <;> decide

theorem address_lt (kind : Kind) {index limit : Nat} (hi : index < limit)
    (j : Fin (stride kind)) : 4 + stride kind * index + j.val < 4 + stride kind * limit := by
  have h := Nat.mul_le_mul_left (stride kind) (Nat.succ_le_iff.mpr hi)
  rw [Nat.mul_succ] at h
  have hj := j.isLt
  omega

theorem key_toNat (kind : Kind) {index limit : Nat} (hi : index < limit)
    (hw : 4+stride kind*limit ≤ UInt256.size) (j : Fin (stride kind)) :
    (key kind index j).toNat = 4+stride kind*index+j.val :=
  toNat_ofNat_lit _ ((address_lt kind hi j).trans_le hw)

/-- Every old physical record lies strictly below the append window. -/
theorem old_key_separated (c : XiCall kind) (hf : AppendFits c)
    {index : Nat} (hi : index < (entryTail c).toNat) (j k : Fin (stride kind)) :
    key kind index j ≠ recordKey c k.val := by
  have hw : 4+stride kind*(entryTail c).toNat ≤ UInt256.size := by have h := hf.1; omega
  intro he
  have he' := congrArg UInt256.toNat he
  rw [key_toNat kind hi hw, AppendStorage.recordKey_toNat c hf k.val k.isLt] at he'
  have ha := address_lt kind hi j
  omega

/-- The operational append preserves all words in every prior record, without
requiring those words to satisfy any record-format predicate. -/
theorem expected_prior (c : XiCall kind) (hf : AppendFits c)
    {index : Nat} (hi : index < (entryTail c).toNat) (j : Fin (stride kind)) :
    AppendStorage.expected c (key kind index j) = slotW (entrySt c) (key kind index j) := by
  have hw : 4+stride kind*(entryTail c).toNat ≤ UInt256.size := by have h := hf.1; omega
  have hk := key_toNat kind hi hw j
  apply AppendStorage.expected_outside c
  · intro he
    have hh := congrArg UInt256.toNat he
    rw [hk] at hh
    change 4+stride kind*index+j.val = 1 at hh
    omega
  · intro he
    have hh := congrArg UInt256.toNat he
    rw [hk] at hh
    change 4+stride kind*index+j.val = 3 at hh
    omega
  · intro i hi'
    exact old_key_separated c hf hi j ⟨i, hi'⟩

/-- The freshly appended physical record is determined solely by the input. -/
def appendedRecord (c : XiCall kind) : Record kind := fun j => recordWord c j.val

theorem new_key (c : XiCall kind) (hf : AppendFits c) (j : Fin (stride kind)) :
    key kind (entryTail c).toNat j = recordKey c j.val := by
  have ht := AppendStorage.recordKey_toNat c hf j.val j.isLt
  rw [← ofNat_toNat' (recordKey c j.val), ht]
  rfl

/-- Appending extends the represented FIFO by exactly one physical vector.
AppendFits is the explicit local capacity/counter condition from the bytecode proof. -/
theorem represents_append (c : XiCall kind) (hf : AppendFits c)
    (queue : List (Record kind)) (hr : Represents kind (slotW (entrySt c)) queue) :
    Represents kind (AppendStorage.expected c) (queue ++ [appendedRecord c]) := by
  have hh : head (AppendStorage.expected c) = head (slotW (entrySt c)) := by
    unfold head
    rw [AppendStorage.expected_head c hf]
  have ht : tail (AppendStorage.expected c) = tail (slotW (entrySt c))+1 :=
    AppendStorage.expected_tail_nat c hf
  have he : tail (slotW (entrySt c)) = (entryTail c).toNat := rfl
  constructor
  · rw [hh, ht]; have h := hr.ordered; omega
  · rw [ht, Nat.mul_succ, he]
    simpa only [Nat.add_assoc] using hf.1
  · rw [List.length_append, List.length_singleton, ht, hh, hr.length_eq]
    have h := hr.ordered
    omega
  · intro i hi j
    rw [hh]
    by_cases ho : i < queue.length
    · have hindex : head (slotW (entrySt c))+i < (entryTail c).toNat := by
        have h := hr.length_eq; rw [he] at h
        have horder := hr.ordered; rw [he] at horder
        omega
      rw [expected_prior c hf hindex j, List.getElem_append_left ho]
      exact hr.contents i ho j
    · have heq : i = queue.length := by simp at hi; omega
      subst i
      have hindex : head (slotW (entrySt c))+queue.length = (entryTail c).toNat := by
        have h := hr.length_eq; rw [he] at h
        have horder := hr.ordered; rw [he] at horder
        omega
      rw [hindex, new_key c hf j, AppendStorage.expected_record c hf j.isLt]
      simp [appendedRecord]

/-- Draining retains exactly the undrained list suffix. The empty case resets
both pointers; the partial case advances HEAD and reuses unchanged record slots. -/
theorem represents_drain (st : EvmYul.State .EVM) (target count cds : UInt256)
    (queue : List (Record kind)) (hr : Represents kind (slotW st) queue)
    (hc : count.toNat ≤ queue.length) :
    Represents kind (SystemSpec.expectedSlot st target count cds) (queue.drop count.toNat) := by
  have hl : queue.length = QueueArithmetic.length st := hr.length_eq
  have hp := QueueArithmetic.pointers st target count cds hr.ordered (by omega)
  change head (SystemSpec.expectedSlot st target count cds) = _ ∧
    tail (SystemSpec.expectedSlot st target count cds) = _ at hp
  have hh : head (SystemSpec.expectedSlot st target count cds) =
      if count.toNat = queue.length then 0 else head (slotW st)+count.toNat := by
    simpa only [← hl, head] using hp.1
  have ht : tail (SystemSpec.expectedSlot st target count cds) =
      if count.toNat = queue.length then 0 else tail (slotW st) := by
    simpa only [← hl, tail] using hp.2
  have hord := hr.ordered
  have hlen := hr.length_eq
  by_cases hfull : count.toNat = queue.length
  · have he : queue.drop count.toNat = [] := by rw [hfull]; exact List.drop_length
    rw [he]
    constructor
    · simp [hh, ht, hfull]
    · simp [ht, hfull]; decide
    · simp [hh, ht, hfull]
    · intro i hi; simp at hi
  · rw [if_neg hfull] at hh ht
    constructor
    · rw [hh, ht]; omega
    · rw [ht]; exact hr.window
    · rw [List.length_drop, hh, ht]; omega
    · intro i hi j
      have hi' : count.toNat+i < queue.length := by simp only [List.length_drop] at hi; omega
      have hindex : head (slotW st)+(count.toNat+i) < tail (slotW st) := by omega
      have hk := key_toNat kind hindex hr.window j
      rw [hh, Nat.add_assoc, SystemSpec.expectedSlot_record _ _ _ _ _ (by rw [hk]; omega)]
      rw [hr.contents (count.toNat+i) hi' j, List.getElem_drop]

open MessageCall CallBridge CommittedAppend
open Eip8282.Audit.Correspondence (runtimeCode)

/-- The represented queue concerns the actual world returned by Θ. -/
def QueueResult (c : Context) (kind : Kind) (queue : List (Record kind)) : Prop :=
  ∃ created world gas substate out,
    c.result = .ok (created, world, gas, substate, true, out) ∧
    Represents kind (worldSlot world c.target) queue

/-- Compose independently proved append execution with the representation lemma.
The execution premise is the existing concrete receipt, not a queue postcondition. -/
theorem append_queue_of_result (c : Context) (q : XiCall kind) (record : ByteArray)
    (queue : List (Record kind)) (hf : AppendFits q)
    (hr : Represents kind (slotW (entrySt q)) queue)
    (hcall : AppendResult c q record) : QueueResult c kind (queue ++ [appendedRecord q]) := by
  obtain ⟨created, world, gas, substate, he, _, hs, _⟩ := hcall
  refine ⟨created, world, gas, substate, .empty, he, ?_⟩
  have hread : worldSlot world c.target = AppendStorage.expected q := funext hs
  rw [hread]
  exact represents_append q hf queue hr

/-- Compose the actual SYSTEM receipt and all-slot result with list dropping. -/
theorem system_queue_of_result (c : Context) (q : XiCall kind)
    (target count cds : UInt256) (out : ByteArray) (queue : List (Record kind))
    (hr : Represents kind (slotW (entrySt q)) queue) (hc : count.toNat ≤ queue.length)
    (hcall : CommittedSystem.StorageResult c q target count cds out) :
    QueueResult c kind (queue.drop count.toNat) := by
  obtain ⟨world, created, gas, substate, he, hs⟩ := hcall
  refine ⟨created, world, gas, substate, out, he, ?_⟩
  have hread : worldSlot world c.target = SystemSpec.expectedSlot (entrySt q) target count cds := funext hs
  rw [hread]
  exact represents_drain (entrySt q) target count cds queue hr hc

/-- Actual deposit SYSTEM calls preserve the local queue invariant, with FIFO
consumption of min(length,64). Entry bounds are not claimed to be protocol-derived. -/
theorem deposit_system_queue (c : Context)
    (hcode : c.code = runtimeCode .deposit) (steps : Nat) (hf : c.fuel = steps+1)
    (hsys : Deposit.callerWord (codeCall c hcode steps) = sysW)
    (hperm : c.permission = true) (hg : 2500000 ≤ c.gas.toNat) (hsteps : 8502 ≤ steps)
    (ho : SystemSpec.HasOwner (entrySt (codeCall c hcode steps)))
    (queue : List (Record .deposit))
    (hr : Represents .deposit (slotW (entrySt (codeCall c hcode steps))) queue) :
    QueueResult c .deposit (queue.drop (min queue.length 64)) := by
  have hc := QueueArithmetic.deposit_count (codeCall c hcode steps) hr.ordered
  have hl : queue.length = QueueArithmetic.length (entrySt (codeCall c hcode steps)) := hr.length_eq
  rw [← hl] at hc
  have hcall := CommittedSystem.deposit_system_commits c hcode steps hf hsys hperm hg hsteps ho
  have hres := system_queue_of_result c (codeCall c hcode steps) _ _ _ _ queue hr
    (by rw [hc]; exact Nat.min_le_left _ _) hcall
  rwa [hc] at hres

theorem exit_system_queue (c : Context)
    (hcode : c.code = runtimeCode .exit) (steps : Nat) (hf : c.fuel = steps+1)
    (hsys : Exit.callerWord (codeCall c hcode steps) = sysW)
    (hperm : c.permission = true) (hg : 250000 ≤ c.gas.toNat) (hsteps : 802 ≤ steps)
    (ho : SystemSpec.HasOwner (entrySt (codeCall c hcode steps)))
    (queue : List (Record .exit))
    (hr : Represents .exit (slotW (entrySt (codeCall c hcode steps))) queue) :
    QueueResult c .exit (queue.drop (min queue.length 16)) := by
  have hc := QueueArithmetic.exit_count (codeCall c hcode steps) hr.ordered
  have hl : queue.length = QueueArithmetic.length (entrySt (codeCall c hcode steps)) := hr.length_eq
  rw [← hl] at hc
  have hcall := CommittedSystem.exit_system_commits c hcode steps hf hsys hperm hg hsteps ho
  have hres := system_queue_of_result c (codeCall c hcode steps) _ _ _ _ queue hr
    (by rw [hc]; exact Nat.min_le_left _ _) hcall
  rwa [hc] at hres


/-- The actual committed append extends the local physical FIFO by one record. -/
theorem deposit_append_queue (c : Context)
    (hcode : c.code = runtimeCode .deposit) (steps : Nat) (hf : c.fuel = steps + 1)
    (huser : Deposit.callerWord (codeCall c hcode steps) ≠ sysW)
    (hen : Deposit.excessWord (codeCall c hcode steps) ≠ INH)
    (hperm : c.permission = true) {n : Nat} {o i : UInt256}
    (hfee : Deposit.FeeLoopEnds (codeCall c hcode steps) n o i)
    (hsize : c.calldata.size = 184)
    (hpaid : ¬ Deposit.valueWord (codeCall c hcode steps) < Deposit.feeWord o)
    (hfloor : ¬ Deposit.amountWord (codeCall c hcode steps) < UInt256.ofNat 1000000000)
    (hstake : ¬ (Deposit.valueWord (codeCall c hcode steps) - Deposit.feeWord o) <
      UInt256.ofNat 1000000000 * Deposit.amountWord (codeCall c hcode steps))
    (hg : 87 * n + 190000 ≤ c.gas.toNat) (hsteps : 24 * n + 152 ≤ steps)
    (ho : HasOwner (entrySt (codeCall c hcode steps)))
    (hfit : AppendStorage.AppendFits (codeCall c hcode steps))
    (queue : List (Record .deposit))
    (hr : Represents .deposit (slotW (entrySt (codeCall c hcode steps))) queue) :
    QueueResult c .deposit (queue ++ [appendedRecord (codeCall c hcode steps)]) := by
  have hcall := CommittedAppend.deposit_append_commits c hcode steps hf huser hen hperm hfee hsize hpaid hfloor hstake hg hsteps ho hfit
  exact append_queue_of_result c (codeCall c hcode steps) _ queue hfit hr hcall

/-- The actual committed append extends the local physical FIFO by one record. -/
theorem exit_append_queue (c : Context)
    (hcode : c.code = runtimeCode .exit) (steps : Nat) (hf : c.fuel = steps + 1)
    (huser : Exit.callerWord (codeCall c hcode steps) ≠ sysW)
    (hen : Exit.excessWord (codeCall c hcode steps) ≠ INH)
    (hperm : c.permission = true) {n : Nat} {o i : UInt256}
    (hfee : Exit.FeeLoopEnds (codeCall c hcode steps) n o i)
    (hsize : c.calldata.size = 48)
    (hpaid : ¬ Exit.valueWord (codeCall c hcode steps) < Exit.feeWord o)
    (hg : 87 * n + 150000 ≤ c.gas.toNat) (hsteps : 24 * n + 122 ≤ steps)
    (ho : HasOwner (entrySt (codeCall c hcode steps)))
    (hfit : AppendStorage.AppendFits (codeCall c hcode steps))
    (queue : List (Record .exit))
    (hr : Represents .exit (slotW (entrySt (codeCall c hcode steps))) queue) :
    QueueResult c .exit (queue ++ [appendedRecord (codeCall c hcode steps)]) := by
  have hcall := CommittedAppend.exit_append_commits c hcode steps hf huser hen hperm hfee hsize hpaid hg hsteps ho hfit
  exact append_queue_of_result c (codeCall c hcode steps) _ queue hfit hr hcall

/-- An exit queue's stored source words represent actual 160-bit addresses. -/
def SourceWidth (queue : List (Record .exit)) : Prop :=
  ∀ r ∈ queue, (r ⟨0, by decide⟩).toNat < 2^160

theorem source_width_empty : SourceWidth [] := by simp [SourceWidth]

theorem source_width_append (q : XiCall .exit) (queue : List (Record .exit))
    (h : SourceWidth queue) : SourceWidth (queue ++ [appendedRecord q]) := by
  intro r hr
  rcases List.mem_append.mp hr with hold | hnew
  · exact h r hold
  · simp only [List.mem_singleton] at hnew
    subst r
    change (UInt256.ofNat q.env.source.val).toNat < 2^160
    have hsrc : q.env.source.val < 2^160 := q.env.source.isLt
    rw [toNat_ofNat_lit _ (hsrc.trans (by decide))]
    exact hsrc

theorem source_width_drop (queue : List (Record .exit)) (n : Nat)
    (h : SourceWidth queue) : SourceWidth (queue.drop n) :=
  fun r hr => h r (List.mem_of_mem_drop hr)

private theorem ofNat_mul (m n : Nat) :
    UInt256.ofNat m * UInt256.ofNat n = UInt256.ofNat (m*n) := by
  have h : (UInt256.ofNat m * UInt256.ofNat n).val = (UInt256.ofNat (m*n)).val := by
    apply Fin.ext
    change ((m % UInt256.size)*(n % UInt256.size)) % UInt256.size = (m*n) % UInt256.size
    exact (Nat.mul_mod m n UInt256.size).symm
  cases hx : UInt256.ofNat m * UInt256.ofNat n
  cases hy : UInt256.ofNat (m*n)
  simp_all

/-- The natural physical index is the same word index as the actual exit loop. -/
theorem key_exit (h : UInt256) (i : Nat) (j : Fin (stride .exit)) :
    key .exit (h.toNat+i) j = UInt256.ofNat j.val + Exit.base (UInt256.ofNat i) h := by
  conv_rhs => rw [← ofNat_toNat' h]
  simp only [key, stride, Exit.base, Eip8282.Audit.SymExec.ofNat_add_ofNat, ofNat_mul,
    Nat.add_comm]

theorem key_exit_source (h : UInt256) (i : Nat) :
    key .exit (h.toNat+i) ⟨0, by decide⟩ = Exit.base (UInt256.ofNat i) h := by
  conv_rhs => rw [← ofNat_toNat' h]
  simp only [key, stride, Exit.base, Eip8282.Audit.SymExec.ofNat_add_ofNat, ofNat_mul, Nat.zero_add,
    Nat.add_comm]

/-- The preserved list invariant supplies the operational drain's source-width
condition for every drained index. -/
theorem source_width_at (st : EvmYul.State .EVM) (queue : List (Record .exit))
    (hr : Represents .exit (slotW st) queue) (hs : SourceWidth queue)
    (n : Nat) (hn : n ≤ queue.length) :
    ∀ i, i < n →
      (slotW st (Exit.base (UInt256.ofNat i) (slotW st (UInt256.ofNat 2)))).toNat < 2^160 := by
  intro i hi
  have hi' : i < queue.length := by omega
  have hc := hr.contents i hi' ⟨0, by decide⟩
  unfold head at hc
  rw [key_exit_source] at hc
  rw [hc]
  exact hs queue[i] (List.getElem_mem hi')

/-- The independent byte format of one stored physical exit vector. -/
def exitBytes (r : Record .exit) : List Eip8282.Audit.Model.Byte :=
  ExitDrain.encodeWords (r ⟨0, by decide⟩) (r ⟨1, by decide⟩) (r ⟨2, by decide⟩)

theorem exit_recordAt (st : EvmYul.State .EVM) (queue : List (Record .exit))
    (hr : Represents .exit (slotW st) queue) (i : Nat) (hi : i < queue.length) :
    ExitDrain.recordAt st (slotW st (UInt256.ofNat 2)) i = exitBytes queue[i] := by
  have h0 := hr.contents i hi ⟨0, by decide⟩
  have h1 := hr.contents i hi ⟨1, by decide⟩
  have h2 := hr.contents i hi ⟨2, by decide⟩
  unfold head at h0 h1 h2
  rw [key_exit_source] at h0
  rw [key_exit] at h1 h2
  dsimp only [ExitDrain.recordAt, exitBytes]
  rw [h0, h1, h2]

/-- The actual word-indexed FIFO is the ordinary represented list prefix. -/
theorem exit_fifo_list (st : EvmYul.State .EVM) (queue : List (Record .exit))
    (hr : Represents .exit (slotW st) queue) (n : Nat) (hn : n ≤ queue.length) :
    ExitDrain.fifoBytes st (slotW st (UInt256.ofNat 2)) n =
      (queue.take n).flatMap exitBytes := by
  induction n with
  | zero => simp [ExitDrain.fifoBytes]
  | succ n ih =>
    rw [ExitDrain.fifoBytes_succ, ih (by omega), exit_recordAt st queue hr n (by omega),
      List.take_succ_eq_append_getElem (l := queue) (i := n) (by omega)]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The actual exit SYSTEM result returns the natural list prefix and preserves
both the queue representation and source-width invariant for its suffix. The
source-width premise is now structural and append/drop-preserved. -/
theorem exit_system_fifo (c : Context)
    (hcode : c.code = runtimeCode .exit) (steps : Nat) (hf : c.fuel = steps+1)
    (hsys : Exit.callerWord (codeCall c hcode steps) = sysW)
    (hperm : c.permission = true) (hg : 250000 ≤ c.gas.toNat) (hsteps : 802 ≤ steps)
    (ho : HasOwner (entrySt (codeCall c hcode steps)))
    (queue : List (Record .exit))
    (hr : Represents .exit (slotW (entrySt (codeCall c hcode steps))) queue)
    (hs : SourceWidth queue) :
    ∃ world created gas substate out,
      c.result = .ok (created, world, gas, substate, true, out) ∧
      Eip8282.Audit.XiTransport.bytes out = (queue.take (min queue.length 16)).flatMap exitBytes ∧
      Represents .exit (worldSlot world c.target) (queue.drop (min queue.length 16)) ∧
      SourceWidth (queue.drop (min queue.length 16)) := by
  let q := codeCall c hcode steps
  have hc := QueueArithmetic.exit_count q hr.ordered
  have hl : queue.length = QueueArithmetic.length (entrySt q) := hr.length_eq
  rw [← hl] at hc
  have hn : (Exit.drainWord q).toNat ≤ queue.length := by rw [hc]; exact Nat.min_le_left _ _
  have hsource := source_width_at (entrySt q) queue hr hs _ hn
  obtain ⟨world, created, gas, substate, out, hcall, hout, hslots⟩ :=
    ExitDrain.exit_system_fifo c hcode steps hf hsys hperm hg hsteps ho hsource
  refine ⟨world, created, gas, substate, out, hcall, ?_, ?_, source_width_drop queue _ hs⟩
  · rw [hout, exit_fifo_list (entrySt q) queue hr _ hn, hc]
  · have hread : worldSlot world c.target =
        SystemSpec.expectedSlot (entrySt q) (UInt256.ofNat 2) (Exit.drainWord q) (Exit.cdsizeWord q) :=
      funext hslots
    rw [hread, ← hc]
    exact represents_drain (entrySt q) _ _ _ queue hr hn

/-- Natural physical deposit indices agree with the actual six-word loop. -/
theorem key_deposit (h : UInt256) (i : Nat) (j : Fin (stride .deposit)) :
    key .deposit (h.toNat+i) j = UInt256.ofNat j.val + Deposit.base (UInt256.ofNat i) h := by
  conv_rhs => rw [← ofNat_toNat' h]
  simp only [key, stride, Deposit.base, Eip8282.Audit.SymExec.ofNat_add_ofNat, ofNat_mul,
    Nat.add_comm]

theorem key_deposit_first (h : UInt256) (i : Nat) :
    key .deposit (h.toNat+i) ⟨0, by decide⟩ = Deposit.base (UInt256.ofNat i) h := by
  conv_rhs => rw [← ofNat_toNat' h]
  simp only [key, stride, Deposit.base, Eip8282.Audit.SymExec.ofNat_add_ofNat, ofNat_mul,
    Nat.zero_add, Nat.add_comm]

/-- The independently encoded physical deposit vector includes the proved
BE-to-LE amount reversal from DepositDrain. -/
def depositBytes (r : Record .deposit) : List Eip8282.Audit.Model.Byte :=
  DepositDrain.encodeWords (r ⟨0, by decide⟩) (r ⟨1, by decide⟩) (r ⟨2, by decide⟩)
    (r ⟨3, by decide⟩) (r ⟨4, by decide⟩) (r ⟨5, by decide⟩)

theorem deposit_recordAt (st : EvmYul.State .EVM) (queue : List (Record .deposit))
    (hr : Represents .deposit (slotW st) queue) (i : Nat) (hi : i < queue.length) :
    DepositDrain.recordAt st (slotW st (UInt256.ofNat 2)) i = depositBytes queue[i] := by
  have h0 := hr.contents i hi ⟨0, by decide⟩
  have h1 := hr.contents i hi ⟨1, by decide⟩
  have h2 := hr.contents i hi ⟨2, by decide⟩
  have h3 := hr.contents i hi ⟨3, by decide⟩
  have h4 := hr.contents i hi ⟨4, by decide⟩
  have h5 := hr.contents i hi ⟨5, by decide⟩
  unfold head at h0 h1 h2 h3 h4 h5
  rw [key_deposit_first] at h0
  rw [key_deposit] at h1 h2 h3 h4 h5
  dsimp only [DepositDrain.recordAt, depositBytes]
  rw [h0, h1, h2, h3, h4, h5]

theorem deposit_fifo_list (st : EvmYul.State .EVM) (queue : List (Record .deposit))
    (hr : Represents .deposit (slotW st) queue) (n : Nat) (hn : n ≤ queue.length) :
    DepositDrain.fifoBytes st (slotW st (UInt256.ofNat 2)) n =
      (queue.take n).flatMap depositBytes := by
  induction n with
  | zero => simp [DepositDrain.fifoBytes]
  | succ n ih =>
    rw [DepositDrain.fifoBytes_succ, ih (by omega), deposit_recordAt st queue hr n (by omega),
      List.take_succ_eq_append_getElem (l := queue) (i := n) (by omega)]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- Actual Θ returns the natural deposit list prefix and preserves the queue
representation for its suffix. No record-encoding agreement is a premise. -/
theorem deposit_system_fifo (c : Context)
    (hcode : c.code = runtimeCode .deposit) (steps : Nat) (hf : c.fuel = steps+1)
    (hsys : Deposit.callerWord (codeCall c hcode steps) = sysW)
    (hperm : c.permission = true) (hg : 2500000 ≤ c.gas.toNat) (hsteps : 8502 ≤ steps)
    (ho : HasOwner (entrySt (codeCall c hcode steps)))
    (queue : List (Record .deposit))
    (hr : Represents .deposit (slotW (entrySt (codeCall c hcode steps))) queue) :
    ∃ world created gas substate out,
      c.result = .ok (created, world, gas, substate, true, out) ∧
      Eip8282.Audit.XiTransport.bytes out = (queue.take (min queue.length 64)).flatMap depositBytes ∧
      Represents .deposit (worldSlot world c.target) (queue.drop (min queue.length 64)) := by
  let q := codeCall c hcode steps
  have hc := QueueArithmetic.deposit_count q hr.ordered
  have hl : queue.length = QueueArithmetic.length (entrySt q) := hr.length_eq
  rw [← hl] at hc
  have hn : (Deposit.drainWord q).toNat ≤ queue.length := by rw [hc]; exact Nat.min_le_left _ _
  obtain ⟨world, created, gas, substate, out, hcall, hout, hslots⟩ :=
    DepositDrain.deposit_system_fifo c hcode steps hf hsys hperm hg hsteps ho
  refine ⟨world, created, gas, substate, out, hcall, ?_, ?_⟩
  · rw [hout, deposit_fifo_list (entrySt q) queue hr _ hn, hc]
  · have hread : worldSlot world c.target =
        SystemSpec.expectedSlot (entrySt q) (UInt256.ofNat 8) (Deposit.drainWord q) (Deposit.cdsizeWord q) :=
      funext hslots
    rw [hread, ← hc]
    exact represents_drain (entrySt q) _ _ _ queue hr hn

#print axioms represents_empty
#print axioms deposit_fifo_list
#print axioms deposit_system_fifo
#print axioms expected_prior
#print axioms represents_append
#print axioms represents_drain
#print axioms deposit_system_queue
#print axioms exit_system_queue
#print axioms deposit_append_queue
#print axioms exit_append_queue
#print axioms source_width_empty
#print axioms source_width_append
#print axioms source_width_drop
#print axioms exit_fifo_list
#print axioms source_width_at
#print axioms exit_system_fifo

end Eip8282.Audit.Integrator.QueueInvariant
