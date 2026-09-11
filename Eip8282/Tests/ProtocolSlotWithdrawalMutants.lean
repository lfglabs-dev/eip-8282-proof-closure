import Eip8282.Audit.Integrator.ProtocolWithdrawalExtraction

/-! Kill-lines for the slot/withdrawal extraction guards. These refute the
wrong uniqueness and counting claims a one-byte mutant of the archived
guards would license. They do not register a public parent and do not
edit sibling guarantee files.

Cited bodies (archived, rehashed): phase0 `process_slots` 1788-1796 /
`process_block_header` 2281-2297; Gloas `get_builder_withdrawals` 1805-1833;
Amsterdam `validate_header` fork.py:472; Capella LIMIT 16;
fork-choice.md:659-699 / 1096-1116; Electra `verify_and_notify_new_payload`
1307-1336. -/
namespace Eip8282.Tests.ProtocolSlotWithdrawalMutants
open EvmYul EvmYul.EVM
open Eip8282.Audit.Integrator
open ProtocolSlotExtraction ProtocolWithdrawalCount ProtocolWithdrawalExtraction
open ResourceBounds (U64)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 400000

def z : U64 := ⟨0, by decide⟩
def one : U64 := ⟨1, by decide⟩
def unit : Item := { recipient := default, gwei := z }

def emptyParent : Block where
  slot := z
  parentFull := false
  pending := []
  pendingPartial := []
  partialBound := by
    simp only [queueStage, List.length_nil]
    exact Nat.zero_le _
  builders := []
  validators := []
  validatorsGuard := GuardedAdds.nil (Nat.zero_le 16)

/-- phase0:1789 `assert state.slot < slot`. Equal current/target slots are
rejected; a `≤` mutant of that guard is not `ProcessSlots`. -/
theorem processSlots_rejects_equal {c d : Clock} : ¬ ProcessSlots c c.slot d := by
  intro h
  exact (lt_irrefl c.slot) h.advancing

/-- phase0:1767+2283: a block at the current slot cannot be a
`state_transition`. -/
theorem transition_requires_advance {c d : Clock} :
    ¬ StateTransition c c.slot d := by
  intro h
  exact (lt_irrefl c.slot) (transition_newer h).2.1

/-- Derived uniqueness: two identical accepted slots cannot arise from the
archived guards. This is the kill-line for dropping `block.slot >
state.latest_block_header.slot` (phase0:2285). -/
theorem duplicate_slots_rejected {pre post : Clock} {s : U64} :
    ¬ Accepted pre [s, s] post := by
  intro h
  exact accepted_ne h rfl

/-- Replacing the extracted `<` by `≤` would accept duplicates.
`accepted_pairwise` uses `<`, so this pair is pairwise-≤ and not Nodup. -/
theorem le_pair_is_not_nodup (s : U64) :
    [s, s].Pairwise (· ≤ ·) ∧ ¬ [s, s].Nodup := by
  refine ⟨?_, ?_⟩
  · refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
    · intro x hx
      have hx' : x = s := List.mem_singleton.mp hx
      exact hx' ▸ le_rfl
    · intro _ hx
      cases hx
  · simp [List.nodup_cons]

/-- fork.py:472 `header.number != parent_header.number + 1`. A repeated
parent number is not an appended EL sequence. -/
theorem el_rejects_parent {n last : Nat} : ¬ ElAppended n [n] last := by
  intro h
  exact el_not_parent h (List.mem_singleton.mpr rfl)

/-- Gloas:1810-1819 builder-pending break at 15. Twenty queued entries
produce fifteen credits, not twenty. -/
theorem queueStage_caps :
    (queueStage 15 0 (List.replicate 20 unit)).length = 15 := by
  have h := queueStage_length 15 0 (List.replicate 20 unit) (Nat.zero_le 15)
  simp only [List.length_replicate, Nat.min_eq_left (by decide : 15 ≤ 20)] at h
  exact h

/-- Capella LIMIT / Gloas MAX_WITHDRAWALS_PER_PAYLOAD = 16. A 17-item
list is not a `GuardedAdds 16 0` trace, so it cannot enter `gloasPayload`. -/
theorem seventeen_unguarded {xs : List Item} (h : xs.length = 17) :
    ¬ GuardedAdds 16 0 xs := by
  intro g
  have := guarded_length g
  omega

/-- Gloas:1999 early return: an empty parent contributes no computed item
at that block. A mutant that still concatenated `expected` would fail this. -/
theorem empty_parent_witness : items emptyParent = [] :=
  items_empty emptyParent rfl

/-- `process_slots` cannot close a loop that does not increment: a tick
that kept the same slot is not a `SlotTick`. -/
theorem tick_must_increment {c : Clock} : ¬ SlotTick c c := by
  intro h
  have : c.slot.val + 1 = c.slot.val := h.increased.symm
  exact (Nat.succ_ne_self c.slot.val) this

/-- fork-choice.md:685. A verified envelope cannot carry a different
EL `slot_number` than the beacon slot. -/
theorem envelope_slot_must_agree {b e : U64} (h : VerifiedEnvelopeSlot b e) :
    e = b :=
  envelope_slot h

def fullParent : Block where
  slot := one
  parentFull := true
  pending := [unit]
  pendingPartial := []
  partialBound := by
    simp only [queueStage, List.length_nil]
    decide
  builders := []
  validators := []
  validatorsGuard := GuardedAdds.nil (by decide : (1:Nat) ≤ 16)

/-- Gloas:1999 retains the cache: an empty parent mints the previous
expected list, which the computed-only `items` projection drops. -/
theorem empty_parent_retains_cache :
    cacheAfter (expected fullParent) emptyParent = expected fullParent ∧
      items emptyParent = [] ∧
      expected fullParent = [unit] := by
  refine ⟨cacheAfter_empty _ _ rfl, items_empty _ rfl, rfl⟩

/-- Electra:1318. A payload whose transactions contain an empty byte is
not engine-admitted. -/
theorem empty_tx_not_admitted {c : EngineChecks} (h : c.emptyTxByte = true) :
    ¬ EngineAdmitted c := by
  intro adm
  have := adm.admits
  rw [engine_rejects_empty_tx c h] at this
  cases this

/-- Electra:1331-1334. A false notify_new_payload is not admission. -/
theorem notify_false_not_admitted {c : EngineChecks} (h : c.notifyOk = false) :
    ¬ EngineAdmitted c := by
  intro adm
  have := adm.admits
  rw [engine_rejects_notify c h] at this
  cases this

/-- fork-choice.md:1104. An unknown beacon root is not
`on_execution_payload_envelope`. -/
theorem unknown_root_not_on_envelope {α : Type} {da : Bool} {b : Block}
    {cached listed : List Item} {cons : EnvelopeConsistency}
    {p : PayloadBinding α} {req : NewPayloadRequest} {eng : EngineChecks} :
    ¬ OnExecutionPayloadEnvelope false da b cached listed cons p req eng :=
  on_envelope_rejects_unknown

/-- Gloas:1999: an empty-parent flag is `latest ≠ bid`. -/
theorem empty_parent_hashes_unequal {α : Type} [DecidableEq α]
    {latest bid : α} (hf : ParentFullFromHashes emptyParent latest bid) :
    latest ≠ bid := by
  intro heq
  have h := hf.flag
  rw [decide_eq_true heq] at h
  cases h

/-- A `parentFull = true` block cannot witness `latest ≠ bid`. -/
theorem full_parent_rejects_unequal_hashes {α : Type} [DecidableEq α]
    {latest bid : α} (hne : latest ≠ bid) :
    ¬ ParentFullFromHashes fullParent latest bid := by
  intro hf
  have htrue : (true : Bool) = decide (latest = bid) := hf.flag
  have hfalse : decide (latest = bid) = false := decide_eq_false hne
  rw [hfalse] at htrue
  cases htrue

theorem empty_parent_retains_from_hashes {α : Type} [DecidableEq α]
    {latest bid : α} (hf : ParentFullFromHashes emptyParent latest bid) :
    cacheAfter (expected fullParent) emptyParent = expected fullParent :=
  cacheAfter_empty_of_hashes hf (empty_parent_hashes_unequal hf)

/-- Gloas:1999 + 688: an empty-parent verified envelope mints the retained
cache, not `expected`. -/
theorem hash_step_empty_mints_cache {α : Type} [DecidableEq α]
    {cached listed : List Item} {latest bid : α}
    (flag : ParentFullFromHashes emptyParent latest bid)
    (env : VerifiedEnvelope emptyParent cached listed) :
    listed = cached :=
  hash_step_listed_empty flag env (empty_parent_hashes_unequal flag)

/-- phase0:1280 / fork-choice.md:687. Duration 12s, not 13s: slot 1 after
genesis time 0 is timestamp 12. -/
theorem timestamp_rejects_off_by_one :
    ¬ EnvelopeTimestamp z one ⟨13, by decide⟩ := by
  intro h
  have hs := envelope_timestamp h
  exact (by decide : (13 : Nat) ≠ 12) hs

/-- `EnvelopeCredits.cons` requires `ApplyBodyWithdrawals`, not merely
store insertion after verify. -/
theorem envelope_cons_needs_apply {before after : AccountMap .EVM}
    {cached : List Item} {b : Block} {rest : List Block}
    (h : EnvelopeCredits before cached (b::rest) after) :
    ∃ mid listed, ApplyBodyWithdrawals before mid listed := by
  obtain ⟨mid, listed, _, here, _⟩ := envelopeCredits_cons_implies_apply h
  exact ⟨mid, listed, here⟩

#print axioms envelope_slot_must_agree
#print axioms empty_parent_retains_cache
#print axioms empty_tx_not_admitted
#print axioms notify_false_not_admitted
#print axioms unknown_root_not_on_envelope
#print axioms empty_parent_hashes_unequal
#print axioms full_parent_rejects_unequal_hashes
#print axioms empty_parent_retains_from_hashes
#print axioms hash_step_empty_mints_cache
#print axioms timestamp_rejects_off_by_one
#print axioms envelope_cons_needs_apply

#print axioms processSlots_rejects_equal
#print axioms transition_requires_advance
#print axioms duplicate_slots_rejected
#print axioms le_pair_is_not_nodup
#print axioms el_rejects_parent
#print axioms queueStage_caps
#print axioms seventeen_unguarded
#print axioms empty_parent_witness
#print axioms tick_must_increment
end Eip8282.Tests.ProtocolSlotWithdrawalMutants
