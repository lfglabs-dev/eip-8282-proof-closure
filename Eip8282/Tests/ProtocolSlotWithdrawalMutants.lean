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
def oneGwei : Item := { recipient := default, gwei := one }

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

/-- Electra:338 / 1366-1378. Twenty ripe pending-partials produce eight
credits, not twenty. -/
theorem electra_partials_cap :
    (electraPartials 0 (List.replicate 20 (electraRipe unit))).length = 8 := by
  have hripe := electraPartialLoop_ripe (electraPartialsLimit 0) 0
    (List.replicate 20 unit)
  have hlen := queueStage_length (electraPartialsLimit 0) 0
    (List.replicate 20 unit) (electraPartials_assert 0 (Nat.zero_le 15))
  simp only [electraPartials, List.map_replicate, hripe] at hlen ⊢
  simp only [List.length_replicate, electraPartialsLimit, MAX_PENDING_PARTIALS,
    MAX_WITHDRAWALS_PER_PAYLOAD, Nat.min_eq_left (by decide : 8 ≤ 15)] at hlen
  exact hlen.trans (Nat.min_eq_left (by decide : 8 ≤ 20))

/-- Electra:1416. A prior of 16 is not a legal validator-sweep start. -/
theorem electra_validators_need_room : ¬ (16 < MAX_WITHDRAWALS_PER_PAYLOAD) := by
  decide

/-- Electra:715. An exited validator is not eligible for a pending partial. -/
theorem exited_not_partial_eligible (v : ValidatorView) (balance : Nat)
    (h : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    isEligibleForPartial v balance = false :=
  isEligibleForPartial_rejects_exited h

/-- Electra:676. A zero-balance validator is not fully withdrawable. -/
theorem zero_balance_not_fully_withdrawable (v : ValidatorView) (epoch : Nat) :
    isFullyWithdrawable v 0 epoch = false :=
  isFullyWithdrawable_rejects_zero

/-- Electra:733-740. Compounding max is 2048e9, not 32e9. -/
theorem compounding_max_is_2048e9 (v : ValidatorView)
    (h : v.cred = .compounding) :
    maxEffectiveBalance v = 2048 * 10^9 ∧
      maxEffectiveBalance v ≠ 32 * 10^9 := by
  have hm := maxEffectiveBalance_compounding h
  refine ⟨hm, ?_⟩
  rw [hm]
  decide

/-- Electra:1378-1385. An ineligible mature pending-partial is skipped. -/
theorem ineligible_partial_is_skipped (item : Item) (rest : List ElectraPartial) :
    electraPartialLoop 8 0
        ({ item := item, mature := true, eligible := false }::rest) =
      electraPartialLoop 8 0 rest :=
  electraPartialLoop_skips_ineligible 8 0 _ rest rfl rfl
    (by decide : ¬ (8 : Nat) ≤ 0)

/-- Gloas 15-cap on the first three stages leaves the Electra reserved slot. -/
theorem fifteen_has_validator_room : 15 < MAX_WITHDRAWALS_PER_PAYLOAD := by
  decide

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

/-- Gloas:1578-1598 / phase0:1815-1825. `process_epoch` is not the +1
assignment: it keeps the slot. -/
theorem process_epoch_is_not_increment {pre post : Clock}
    (h : GloasProcessEpoch pre post)
    (hinc : post.slot.val = pre.slot.val + 1) : False := by
  have hs := gloas_process_epoch_same_slot h
  rw [hs] at hinc
  exact (Nat.succ_ne_self pre.slot.val) hinc.symm

/-- phase0:614 / 1793. Slot 31 is the last slot of an epoch; slot 32 is
not an epoch boundary. A 31-slot mutant fails this. -/
theorem epoch_boundary_is_32 :
    epochBoundary ⟨31, by decide⟩ = true ∧
      epochBoundary ⟨32, by decide⟩ = false := by
  constructor
  · simp [epochBoundary, SLOTS_PER_EPOCH]
  · simp [epochBoundary, SLOTS_PER_EPOCH]

/-- phase0:1792-1794. Off the boundary, `process_epoch` is skipped. -/
theorem non_boundary_skips_epoch (c : Clock)
    (h : (c.slot.val + 1) % SLOTS_PER_EPOCH ≠ 0) :
    OptionalEpoch c.slot c c :=
  OptionalEpoch.skip h

/-- Fulu:71. Lookahead is two epochs (64), not one (32). A
`MIN_SEED_LOOKAHEAD = 0` mutant collapses the Vector. -/
theorem lookahead_length_is_not_one_epoch :
    proposerLookaheadLength ≠ SLOTS_PER_EPOCH := by
  unfold proposerLookaheadLength MIN_SEED_LOOKAHEAD SLOTS_PER_EPOCH
  decide

/-- Fulu:481-489. The helper copies the clock; it is not the +1 of
`process_slots`. -/
theorem proposer_lookahead_is_not_increment (s : LookaheadFrame)
    (filled : ProposerIndices)
    (hinc : (applyProposerLookahead s filled).clock.slot.val =
      s.clock.slot.val + 1) : False := by
  have hs := applyProposerLookahead_clock s filled
  have hslot : (applyProposerLookahead s filled).clock.slot = s.clock.slot :=
    congrArg Clock.slot hs
  rw [hslot] at hinc
  exact (Nat.succ_ne_self s.clock.slot.val) hinc.symm

def sampleLookahead : ProposerLookahead where
  data := List.replicate 32 z ++ List.replicate 32 one
  length_ok := by decide

def sampleFilled : ProposerIndices where
  data := List.replicate 32 z
  length_ok := by decide

/-- Fulu:484. Dropping the first epoch is not the identity when the two
epochs differ. A no-shift mutant keeps `[0,0,…,1,1,…]`. -/
theorem lookahead_shift_is_not_identity :
    shiftAndFill sampleLookahead sampleFilled ≠ sampleLookahead.data := by
  intro h
  have h0 := congrArg (fun xs => xs[0]?) h
  have hL : (shiftAndFill sampleLookahead sampleFilled)[0]? = some one := by
    simp [shiftAndFill, sampleLookahead, sampleFilled, SLOTS_PER_EPOCH]
  have hR : sampleLookahead.data[0]? = some z := by
    simp [sampleLookahead]
  rw [hL, hR] at h0
  exact (by decide : ¬ (some one = some z)) h0

/-- Fulu:366. Slot 0 reads index 0 of the current-epoch prefix, which is
zero on the sample, not the next-epoch ones. -/
theorem proposerAt_reads_current_prefix :
    proposerAt sampleLookahead z = z := by
  simp [proposerAt, sampleLookahead, SLOTS_PER_EPOCH, z]

/-- phase0:1275. The maximal slot overflows `Uint64(genesis + slot*12)`
at genesis 0. A wrap-free mutant of `compute_time_at_slot` is false. -/
theorem timeFits_rejects_overflow : ¬ TimeFitsU64 z ⟨2 ^ 64 - 1, by decide⟩ :=
  timeFits_rejects_max_slot

/-- phase0:678. Mainnet `MIN_GENESIS_TIME` at slot 0 fits. -/
theorem timeFits_mainnet_genesis : TimeFitsU64 ⟨MIN_GENESIS_TIME, by decide⟩ z :=
  timeFits_min_genesis_zero

/-- Fulu:390-407. Fifteen callees, not the Gloas seventeen. -/
theorem fulu_epoch_is_not_increment {pre post : Clock}
    (h : FuluProcessEpoch pre post)
    (hinc : post.slot.val = pre.slot.val + 1) : False := by
  have hs := fulu_process_epoch_same_slot h
  rw [hs] at hinc
  exact (Nat.succ_ne_self pre.slot.val) hinc.symm

/-- Electra:1451. The last validator wraps to 0, not `n`. -/
theorem next_validator_wraps :
    nextValidatorIndex 3 2 = 0 ∧ nextValidatorIndex 3 2 ≠ 3 := by
  decide

/-- Electra:1413. A 20000-validator registry is still swept at 16384. -/
theorem sweep_limit_caps_large_registry :
    validatorsSweepLimit 20000 = 16384 := by
  decide

/-- Capella:520-522. A full 16-withdrawal payload restarts after the
last credited index, not `start + 16384`. -/
theorem full_payload_follows_last :
    updateNextWithdrawalValidatorIndex 100 0 (List.range 16) =
      nextValidatorIndex 100 15 := by
  have hlen : (List.range 16).length = MAX_WITHDRAWALS_PER_PAYLOAD := by
    simp [MAX_WITHDRAWALS_PER_PAYLOAD, List.length_range]
  have hlast : (List.range 16).getLast? = some 15 := by decide
  exact updateNext_full hlen hlast

theorem full_payload_not_plus_sweep :
    updateNextWithdrawalValidatorIndex 100 0 (List.range 16) ≠
      (0 + MAX_VALIDATORS_PER_SWEEP) % 100 := by
  rw [full_payload_follows_last]
  decide

/-- Capella:525-528. A short payload advances by the sweep cap from
the original start, not `last + 1`. -/
theorem partial_payload_advances_sweep :
    updateNextWithdrawalValidatorIndex 100 7 [3] = (7 + 16384) % 100 := by
  have hlen : ([3] : List Nat).length ≠ 16 := by decide
  simpa [MAX_VALIDATORS_PER_SWEEP] using
    updateNext_partial (n := 100) (start := 7) hlen

/-- Electra:1421-1451. The archived fuel is at most the registry, so
the walk is Nodup; a repeated pair is not an Electra sweep. -/
theorem electra_sweep_is_nodup :
    (visitRing 4 1 (validatorsSweepLimit 4)).Nodup :=
  electraVisit_nodup ⟨by decide, by decide⟩

/-- phase0:1610-1613. Excess `decrease_balance` saturates at 0, not a
`Uint64` wrap. -/
theorem decrease_saturates_excess : decreaseBalance 5 7 = 0 := by
  decide

/-- Gloas:1033-1034. Index 0 does not carry `BUILDER_INDEX_FLAG`. -/
theorem zero_is_not_builder_index :
    isBuilderIndex 0 = false :=
  isBuilderIndex_zero

/-- Gloas:555/1034. The flag itself is a builder index. -/
theorem flag_is_builder_index :
    isBuilderIndex BUILDER_INDEX_FLAG = true :=
  isBuilderIndex_flag

/-- Gloas:1134-1135. Converting the flag yields builder index 0. -/
theorem convert_flag_clears :
    toBuilderIndex BUILDER_INDEX_FLAG = 0 :=
  toBuilderIndex_flag

/-- Gloas:1127-1128. `| FLAG` is classified as a builder index. -/
theorem tagged_builder_is_builder :
    isBuilderIndex (toValidatorIndex 3) = true :=
  toValidatorIndex_is_builder 3

/-- Gloas:1926-1931. The archived predicate still saturates. -/
theorem apply_from_builder_index_saturates :
    applyOneFromIndex BUILDER_INDEX_FLAG 5 7 = 0 :=
  applyOneFromIndex_eq_sub BUILDER_INDEX_FLAG 5 7

def sampleBalances : DualBalances where
  validators := fun _ => 32
  builders := fun _ => 100

/-- Gloas:1926-1929. A builder-tagged index does not write `balances`. -/
theorem builder_withdrawal_keeps_validators :
    (applyOneWithdrawal sampleBalances BUILDER_INDEX_FLAG 7).validators 0 = 32 := by
  rw [applyOneWithdrawal_builder_keeps_validators sampleBalances BUILDER_INDEX_FLAG 7
    isBuilderIndex_flag]
  rfl

/-- Gloas:1931. A validator index does not write `builders`. -/
theorem validator_withdrawal_keeps_builders :
    (applyOneWithdrawal sampleBalances 3 7).builders 0 = 100 := by
  have h : isBuilderIndex 3 = false := by decide
  rw [applyOneWithdrawal_validator_keeps_builders sampleBalances 3 7 h]
  rfl

/-- Gloas:1927. The flag converts to builder index 0 and saturates. -/
theorem builder_flag_writes_index_zero :
    (applyOneWithdrawal sampleBalances BUILDER_INDEX_FLAG 7).builders 0 = 93 := by
  have h := applyOneWithdrawal_builder_written sampleBalances BUILDER_INDEX_FLAG 7
    isBuilderIndex_flag
  rw [toBuilderIndex_flag] at h
  exact h

/-- Gloas:1924. The empty for-loop is the identity. -/
theorem tagged_nil_is_identity :
    applyTagged sampleBalances [] = sampleBalances :=
  applyTagged_nil sampleBalances

theorem decrease_not_u64_wrap : decreaseBalance 5 7 ≠ 2 ^ 64 - 2 := by
  decide

/-- Capella:481 / 411-421. An empty prior is the original balance; the
named wrap is discharged. -/
theorem empty_prior_is_original :
    balanceAfterWithdrawals 42 3 [] = 42 :=
  balanceAfter_nil 42 3

/-- Capella:498-500. Applying no withdrawals is the identity. -/
theorem apply_nil_identity (b : Nat → Nat) (i : Nat) :
    applyWithdrawals b [] i = b i :=
  applyWithdrawals_nil b i

/-- Gloas:1929 and phase0:1613 agree: both branches are `Nat.sub`. -/
theorem builder_and_validator_agree (balance amt : Nat) :
    applyOne true balance amt = applyOne false balance amt := by
  simp [applyOne_eq_sub]

/-- Capella:411-421 vs 498-500. Under `BalanceAfterFits` the fold matches
the sum-then-subtract read. -/
theorem apply_agrees_on_empty (b : Nat → Nat) (idx : Nat) :
    applyWithdrawals b [] idx = balanceAfterWithdrawals (b idx) idx [] :=
  apply_eq_balanceAfter (balanceAfterFits_nil (b idx) idx)

/-- A full withdrawal of the original Gwei zeros the remainder. -/
theorem full_withdrawal_zeros :
    balanceAfterWithdrawals 32 0 [(0, 32)] = 0 :=
  balanceAfter_full

/-- Capella:452/458. Assigned indices increment; a repeated index is
not an `indexSeq`. -/
theorem indexSeq_rejects_repeat :
    indexSeq 3 2 ≠ [3, 3] := by
  decide

/-- Capella:506-510. Empty withdrawals keep the cursor. -/
theorem empty_withdrawals_keep_index :
    updateNextWithdrawalIndex 9 [] = 9 :=
  updateNextWithdrawalIndex_empty 9

/-- Capella:510. A singleton updates to last+1, not last. -/
theorem singleton_index_is_successor :
    updateNextWithdrawalIndex 0 [7] = 8 :=
  updateNextWithdrawalIndex_singleton 0 7

/-- Capella:510 then 480. Two payloads starting at 4 of lengths 2 and 3
are `[4,5] ++ [6,7,8]`, unique. -/
theorem paired_payload_indices_unique :
    (indexSeq 4 2 ++ indexSeq (updateNextWithdrawalIndex 4 (indexSeq 4 2)) 3).Nodup :=
  indexSeq_pair_nodup 4 2 3

/-- fork.py:120/1118. Zero Gwei is zero Wei, not 10^9. -/
theorem zero_gwei_is_zero_wei :
    (⟨default, z⟩ : Item).amount.toNat = 0 :=
  create_ether_zero_wei _ rfl

/-- Capella:452/458. The credited list is tagged with the running
index; a repeated index is not `indexedWithdrawals`. -/
theorem indexed_rejects_repeat_index :
    (indexedWithdrawals 3 [unit, unit]).map (fun w => w.index) ≠ [3, 3] := by
  decide

/-- Capella:508 / Gloas:1999. An empty credited list keeps the cursor. -/
theorem empty_items_keep_index_cursor :
    nextIndexAfter 9 (items emptyParent) = 9 := by
  have h : items emptyParent = [] := items_empty emptyParent rfl
  rw [h]
  exact nextIndexAfter_nil 9

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

/-- Capella:510 then 480. Two singleton payloads starting at 4 are
indices `[4, 5]`, unique. -/
theorem chained_payload_indices_unique :
    ((indexedChain 4 [fullParent, fullParent]).map (fun w => w.index)).Nodup :=
  indexedChain_nodup 4 _

/-- The indexed items are the credited `items`, not a filtered copy. -/
theorem indexed_items_are_credited :
    (indexedChain 0 [fullParent]).map (fun w => w.item) = items fullParent := by
  simp [indexedChain_items, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- Gloas:1999. An empty parent remints the cached indices, it does not
assign a fresh successor. -/
theorem empty_parent_remints_cached_indices :
    indexedCacheAfter 7 (indexedWithdrawals 7 [unit]) emptyParent =
      indexedWithdrawals 7 [unit] :=
  indexedCacheAfter_empty (b := emptyParent) rfl

/-- Gloas:1999. The cursor stays when the parent is empty. -/
theorem empty_parent_cache_cursor_stays :
    nextIndexAfterCache 7 emptyParent = 7 :=
  nextIndexAfterCache_empty (b := emptyParent) rfl

/-- A full parent stamps `expected` from the running cursor. -/
theorem full_parent_cache_stamps_expected :
    (indexedCacheAfter 4 [] fullParent).map (fun w => w.index) = [4] := by
  have hf : fullParent.parentFull = true := rfl
  have he : expected fullParent = [unit] := rfl
  simp [indexedCacheAfter, hf, he, indexedWithdrawals]

/-- Empty parent adds no new index to the unique computed chain. -/
theorem empty_parent_drops_from_indexed_chain :
    indexedChain 3 [emptyParent, fullParent] = indexedChain 3 [fullParent] :=
  indexedChain_empty_step 3 emptyParent [fullParent] rfl

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

/-- A verified envelope on an empty parent mints the retained cache. -/
theorem verified_empty_mints_cache {α : Type} [DecidableEq α]
    {cached listed : List Item} {cons : EnvelopeConsistency}
    {p : PayloadBinding α} {req : NewPayloadRequest} {eng : EngineChecks}
    (s : VerifiedHashStep emptyParent cached listed cons p req eng) :
    listed = cached :=
  verifiedHashStep_empty s (empty_parent_hashes_unequal s.flag)

/-- fork-choice.md:1096-1116: storing an empty-parent envelope still mints
the retained cache, not `expected`. -/
theorem on_envelope_empty_mints_cache {α : Type} [DecidableEq α]
    {rootKnown da : Bool} {cached listed : List Item}
    {cons : EnvelopeConsistency} {p : PayloadBinding α}
    {req : NewPayloadRequest} {eng : EngineChecks}
    (s : OnEnvelopeHashStep rootKnown da emptyParent cached listed cons p req eng) :
    listed = cached :=
  onEnvelopeHashStep_empty s (empty_parent_hashes_unequal s.flag)

/-- fork.py:120/1118. The credited Wei is Gwei * 10^9, not 10^18. -/
theorem create_ether_wei_is_gwei_times_1e9 (item : Item) :
    item.amount.toNat = item.gwei.val * 10^9 :=
  create_ether_wei item

/-- state_tracker.py:188-211 / 642. A missing recipient is inserted at the
credited Wei, not left absent. -/
theorem create_ether_missing_inserts {before after : AccountMap .EVM} {item : Item}
    (hacc : before.get? item.recipient = none)
    (h : CreateEther before item after) :
    after.get? item.recipient =
      some {(default : Account .EVM) with balance := item.amount} :=
  createEther_missing hacc h

/-- fork.py:120/1118. A 1 Gwei credit is 10^9 Wei, hence nonzero. -/
theorem one_gwei_is_nonzero_wei :
    oneGwei.amount.toNat ≠ 0 :=
  create_ether_gwei_nonzero oneGwei (by decide : (1 : Nat) ≠ 0)

/-- state_tracker.py:385. A missing recipient credited 1 Gwei is not
`account_exists_and_is_empty` on the balance conjunct. -/
theorem missing_one_gwei_not_empty {before after : AccountMap .EVM}
    {acc' : Account .EVM}
    (hacc : before.get? oneGwei.recipient = none)
    (h : CreateEther before oneGwei after)
    (hlook : after.get? oneGwei.recipient = some acc') :
    ¬ AccountNonceBalanceEmpty acc' :=
  createEther_missing_not_empty hacc h (by decide : (1 : Nat) ≠ 0) hlook

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
#print axioms verified_empty_mints_cache
#print axioms on_envelope_empty_mints_cache
#print axioms create_ether_wei_is_gwei_times_1e9
#print axioms create_ether_missing_inserts
#print axioms one_gwei_is_nonzero_wei
#print axioms missing_one_gwei_not_empty
#print axioms timestamp_rejects_off_by_one
#print axioms envelope_cons_needs_apply

#print axioms processSlots_rejects_equal
#print axioms transition_requires_advance
#print axioms duplicate_slots_rejected
#print axioms le_pair_is_not_nodup
#print axioms el_rejects_parent
#print axioms queueStage_caps
#print axioms electra_partials_cap
#print axioms electra_validators_need_room
#print axioms exited_not_partial_eligible
#print axioms zero_balance_not_fully_withdrawable
#print axioms compounding_max_is_2048e9
#print axioms ineligible_partial_is_skipped
#print axioms fifteen_has_validator_room
#print axioms seventeen_unguarded
#print axioms empty_parent_witness
#print axioms tick_must_increment
#print axioms process_epoch_is_not_increment
#print axioms epoch_boundary_is_32
#print axioms non_boundary_skips_epoch
#print axioms lookahead_length_is_not_one_epoch
#print axioms proposer_lookahead_is_not_increment
#print axioms lookahead_shift_is_not_identity
#print axioms proposerAt_reads_current_prefix
#print axioms timeFits_rejects_overflow
#print axioms timeFits_mainnet_genesis
#print axioms fulu_epoch_is_not_increment
#print axioms next_validator_wraps
#print axioms sweep_limit_caps_large_registry
#print axioms full_payload_follows_last
#print axioms full_payload_not_plus_sweep
#print axioms partial_payload_advances_sweep
#print axioms electra_sweep_is_nodup
#print axioms decrease_saturates_excess
#print axioms zero_is_not_builder_index
#print axioms flag_is_builder_index
#print axioms convert_flag_clears
#print axioms tagged_builder_is_builder
#print axioms apply_from_builder_index_saturates
#print axioms builder_withdrawal_keeps_validators
#print axioms validator_withdrawal_keeps_builders
#print axioms builder_flag_writes_index_zero
#print axioms tagged_nil_is_identity
#print axioms decrease_not_u64_wrap
#print axioms empty_prior_is_original
#print axioms apply_nil_identity
#print axioms builder_and_validator_agree
#print axioms apply_agrees_on_empty
#print axioms full_withdrawal_zeros
#print axioms indexSeq_rejects_repeat
#print axioms empty_withdrawals_keep_index
#print axioms singleton_index_is_successor
#print axioms paired_payload_indices_unique
#print axioms zero_gwei_is_zero_wei
#print axioms indexed_rejects_repeat_index
#print axioms empty_items_keep_index_cursor
#print axioms chained_payload_indices_unique
#print axioms indexed_items_are_credited
#print axioms empty_parent_remints_cached_indices
#print axioms empty_parent_cache_cursor_stays
#print axioms full_parent_cache_stamps_expected
#print axioms empty_parent_drops_from_indexed_chain
end Eip8282.Tests.ProtocolSlotWithdrawalMutants
