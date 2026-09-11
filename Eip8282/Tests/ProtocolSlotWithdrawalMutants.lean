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

/-- fork.py:323/472. `validate_header` admits a repeated `slot_number`. -/
theorem validate_header_admits_duplicate_slots :
    ElHeadersAppended 0 sampleElDupSlots 2 ∧
      ¬ (elSlotNumbers sampleElDupSlots).Nodup :=
  ⟨sampleEl_appended, by
    unfold sampleElDupSlots elSlotNumbers
    exact (by decide : ¬ ([7, 7] : List Nat).Nodup)⟩

/-- Relabeling `slot_number` keeps the same `number` walk. -/
theorem validate_header_ignores_slot_relabel :
    ElHeadersAppended 0 sampleElRelabeled 2 ∧
      elNumbers sampleElDupSlots = elNumbers sampleElRelabeled ∧
      elSlotNumbers sampleElDupSlots ≠ elSlotNumbers sampleElRelabeled :=
  ⟨sampleEl_relabeled_appended, sampleEl_same_numbers, sampleEl_different_slots⟩

/-- A `slot_number` Nodup mutant of `validate_header` is false. -/
theorem validate_header_is_not_slot_nodup :
    ¬ ∀ (hs : List ElHeader) (parent last : Nat),
      ElHeadersAppended parent hs last → (elSlotNumbers hs).Nodup :=
  validate_header_slots_not_nodup

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

/-- phase0:554 / Electra:285. Archived first bytes are 0x01 and 0x02. -/
theorem eth1_prefix_is_one_compounding_is_two :
    ETH1_ADDRESS_WITHDRAWAL_PREFIX = 1 ∧
      COMPOUNDING_WITHDRAWAL_PREFIX = 2 ∧
      BLS_WITHDRAWAL_PREFIX = 0 :=
  ⟨eth1_prefix_byte, compounding_prefix_byte, bls_prefix_byte⟩

/-- Capella:317. Empty credentials are not 0x01. -/
theorem empty_cred_is_not_eth1 : hasEth1Bytes [] = false :=
  hasEth1Bytes_nil

/-- Electra:651-658. BLS 0x00 is not an execution credential. -/
theorem bls_prefix_is_not_execution (rest : List Nat) :
    hasExecutionBytes (BLS_WITHDRAWAL_PREFIX :: rest) = false :=
  hasExecutionBytes_bls rest

/-- Electra:737-740. Swapping 0x01 and 0x02 flips the max effective. -/
theorem prefix_swap_flips_max :
    maxEffectiveBalance (viewWithByte ETH1_ADDRESS_WITHDRAWAL_PREFIX 0 0 0) ≠
      maxEffectiveBalance (viewWithByte COMPOUNDING_WITHDRAWAL_PREFIX 0 0 0) :=
  prefix_swap_changes_max 0 0 0

/-- Capella:317 vs Electra:635. The tag follows the first byte. -/
theorem first_byte_selects_tag :
    hasExecutionCredential (viewWithByte ETH1_ADDRESS_WITHDRAWAL_PREFIX 0 0 0) =
      true ∧
      hasExecutionCredential (viewWithByte COMPOUNDING_WITHDRAWAL_PREFIX 0 0 0) =
        true ∧
      hasExecutionCredential (viewWithByte BLS_WITHDRAWAL_PREFIX 0 0 0) =
        false := by
  simp [hasExecutionCredential_of_byte, hasExecutionBytes_eth1,
    hasExecutionBytes_compounding, hasExecutionBytes_bls]

/-- Capella:454/639. Address is `credentials[12:]`, not `[:20]`. -/
theorem cred_address_is_not_first_twenty :
    credAddressBytes (eth1Credential sampleExecutionAddr) ≠
      (eth1Credential sampleExecutionAddr).take 20 :=
  cred_address_is_not_take20

/-- Capella:639. ETH1 credential is still 0x01 in front. -/
theorem eth1_layout_keeps_prefix :
    hasEth1Bytes (eth1Credential sampleExecutionAddr) = true :=
  eth1Credential_hasEth1 sampleExecutionAddr

/-- fork.py:1118. EL fields ignore `validator_index`. -/
theorem el_fields_ignore_validator_index (w : SszWithdrawal) :
    sszElFields { w with validatorIndex := w.validatorIndex + 1 } =
      sszElFields w :=
  sszEl_ignores_validator w (w.validatorIndex + 1)

/-- A mutant that credits `validator_index` as the address. -/
theorem el_address_is_not_validator_index :
    sszElFields
        { index := 0, validatorIndex := 7, addressBytes := [9], amount := 1 } ≠
      ([7], 1) :=
  sszEl_ne_validator_as_address (by decide)

/-- Capella:156 / Wheels.lean. Execution address is 160 bits, not 256. -/
theorem execution_address_is_not_uint256 :
    AccountAddress.size ≠ UInt256.size :=
  accountAddress_size_ne_u256

/-- Capella:454. Little-endian `[1,0,…,0]` is 1, not `256^19`. -/
theorem execution_address_is_big_endian :
    bytesBeToNat sampleBeAddr ≠ bytesLeToNat sampleBeAddr :=
  execution_be_ne_le

/-- The 20-byte slice is not the 32-byte credential. -/
theorem execution_width_is_not_credential :
    EXECUTION_ADDRESS_BYTES ≠ CREDENTIAL_BYTES :=
  execution_width_ne_credential

/-- `AccountAddress` wrap of `2^160` is 0. -/
theorem account_address_wraps_two_pow_160 :
    (AccountAddress.ofNat (2 ^ 160)).val = 0 :=
  accountAddress_two_pow_wraps

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

/-- phase0:1296-1300. Epoch `2^59` wraps `Slot(epoch)*32` to 0. -/
theorem start_slot_two_pow_59_wraps_to_zero :
    startSlotAtEpochU64 (2 ^ 59) = 0 ∧
      startSlotAtEpoch (2 ^ 59) ≠ startSlotAtEpochU64 (2 ^ 59) :=
  ⟨startSlot_two_pow_59_wraps, startSlot_two_pow_59_ne_wrap⟩

/-- phase0:547 / 1028. Big-endian `uint_to_bytes` is not the archived
`ENDIANNESS`. -/
theorem uint_to_bytes_is_little_endian :
    uintToBytes8 1 ≠ uintToBytes8Be 1 :=
  uint_to_bytes_is_not_be

/-- Fulu:350. A no-offset mutant of `start_slot + i` repeats one
preimage 32 times. -/
theorem proposer_seeds_need_slot_offset (seed : List Nat) (start : Nat) :
    ¬ (constantSlotPreimages seed start).Nodup :=
  constantSlotPreimages_not_nodup seed start

/-- Fulu:350. 32 consecutive Uint64 slots stay unique across the wrap. -/
theorem proposer_seed_slots_wrap_still_unique :
    (seedSlotU64s (2 ^ 64 - 16)).Nodup :=
  seedSlotU64s_wrap_nodup

/-- Fulu:350. Seed list is one epoch (32), not the 64-slot lookahead. -/
theorem proposer_seeds_length_is_not_lookahead (seed : List Nat) (epoch : Nat) :
    (computeProposerSeedInputs seed epoch).length ≠ proposerLookaheadLength := by
  rw [computeProposerSeedInputs_length]
  unfold proposerLookaheadLength MIN_SEED_LOOKAHEAD SLOTS_PER_EPOCH
  decide

/-- Fulu:350. Concatenation is `seed ++ slot`, not the reverse. -/
theorem proposer_preimage_is_seed_then_slot :
    proposerSeedPreimage [9] 0 0 ≠ uintToBytes8 (seedSlotU64 0 0) ++ [9] :=
  proposerSeedPreimage_ne_reversed

/-- phase0:560-561 / 1452. Attester domain is not the proposer seed. -/
theorem get_seed_uses_proposer_domain :
    getSeedPreimage DOMAIN_BEACON_PROPOSER 0 [7] ≠
      getSeedPreimage DOMAIN_BEACON_ATTESTER 0 [7] :=
  getSeedPreimage_uses_proposer

/-- Fulu:351. Fill length is derived from the 32-seed loop. -/
theorem proposer_fill_from_seeds_is_32
    (hash : List Nat → List Nat) (choose : List Nat → U64)
    (seed : List Nat) (epoch : Nat) :
    (proposerIndicesOfSeeds hash choose seed epoch).data.length = 32 := by
  simpa [SLOTS_PER_EPOCH] using
    proposerIndicesOfSeeds_length hash choose seed epoch

/-- phase0:1449-1451. Genesis mix is 65534, not randao_mixes[0]. -/
theorem get_seed_mix_is_not_current_epoch :
    getSeedMixIndex 0 ≠ getRandaoMixIndex 0 :=
  getSeedMix_ne_current_genesis

/-- phase0:1451. Dropping `+ VECTOR` underflows to 0 at genesis. -/
theorem get_seed_mix_needs_historical_vector :
    getSeedMixEpoch 0 ≠ getSeedMixEpochNoVector 0 :=
  getSeedMix_needs_vector

/-- phase0:615 / 1450. `MIN_SEED_LOOKAHEAD = 0` reads 65535. -/
theorem get_seed_mix_uses_lookahead :
    getSeedMixIndex 0 ≠
      getRandaoMixIndex (getSeedMixEpochNoLookahead 0) :=
  getSeedMix_uses_lookahead

/-- phase0:1414 / 1450. Epoch 2 wraps the mix ring to index 0. -/
theorem get_seed_mix_wraps_at_epoch_two :
    getSeedMixIndex 2 = 0 :=
  getSeedMixIndex_epoch_two

/-- phase0:1410-1414 / 1707. Genesis mixes are a splat: every epoch
reads `eth1_block_hash`. -/
theorem get_randao_mix_genesis_is_eth1 :
    getRandaoMix (genesisRandaoMixes sampleMixOne) 7
      (genesisRandaoMixes_length _) = sampleMixOne :=
  getRandaoMix_genesis _ _

/-- phase0:1414. The mix is the stored VECTOR entry, not
`uint_to_bytes(epoch)`. -/
theorem get_randao_mix_is_not_epoch_bytes :
    getRandaoMix (genesisRandaoMixes sampleMixOne) 3
      (genesisRandaoMixes_length _) ≠ uintToBytes8 3 :=
  getRandaoMix_genesis_ne_epoch_bytes

/-- phase0:1414. `epoch + VECTOR` aliases slot 0. -/
theorem get_randao_mix_wraps_vector :
    getRandaoMix (sampleMixes sampleMixOne) EPOCHS_PER_HISTORICAL_VECTOR
      (sampleMixes_length _) =
      getRandaoMix (sampleMixes sampleMixOne) 0 (sampleMixes_length _) :=
  getRandaoMix_sample_wraps

/-- phase0:1449-1451 / 1414. Genesis `get_seed` does not read
`randao_mixes[0]` when the VECTOR is not a splat. -/
theorem get_seed_mix_is_not_slot_zero :
    getRandaoMix (sampleMixes sampleMixOne) (getSeedMixEpoch 0)
      (sampleMixes_length _) ≠
      getRandaoMixAtZero (sampleMixes sampleMixOne) (sampleMixes_length _) :=
  getRandaoMix_seed_ne_zero_slot

/-- phase0:1452. A different VECTOR head at the looked-up index
changes the seed preimage. -/
theorem get_seed_preimage_tracks_mix :
    getSeedPreimageFromMixes DOMAIN_BEACON_PROPOSER 2
      (sampleMixes sampleMixOne) (sampleMixes_length _) ≠
      getSeedPreimageFromMixes DOMAIN_BEACON_PROPOSER 2
        (sampleMixes sampleMixZero) (sampleMixes_length _) :=
  getSeedPreimage_tracks_mix_head

/-- phase0:2237-2243. Reset copies the current mix into the next slot. -/
theorem get_randao_reset_copies_current :
    getRandaoMix
      (processRandaoMixesReset (sampleMixes sampleMixOne) 0
        (sampleMixes_length _)) 1
      (processRandaoMixesReset_length _ 0 (sampleMixes_length _)) =
      getRandaoMix (sampleMixes sampleMixOne) 0 (sampleMixes_length _) :=
  processRandaoMixesReset_next _ 0 _

/-- phase0:1707 / 2237-2243. Genesis splat makes that copy a no-op. -/
theorem get_randao_reset_genesis_noop :
    processRandaoMixesReset (genesisRandaoMixes sampleMixOne) 0
      (genesisRandaoMixes_length _) = genesisRandaoMixes sampleMixOne :=
  processRandaoMixesReset_genesis _ _

/-- phase0:1006. Lean `zipWith` truncates; Python `zip(..., strict=True)`
raises. -/
theorem xor_truncates_unequal_lengths :
    bytesXor [1, 2] [3] = [Nat.xor 1 3] :=
  bytesXor_truncates

/-- phase0:2314-2315. Genesis zeros xor the sample digest writes that
digest at the current epoch. -/
theorem process_randao_writes_xor :
    getRandaoMix
      (processRandao samplePivotHash (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _))
      0
      (processRandao_length samplePivotHash (genesisRandaoMixes sampleMixZero)
        0 [] (genesisRandaoMixes_length _)) = samplePivotDigest :=
  processRandao_genesis_current

/-- phase0:2314. The xor is not a copy of the old mix. -/
theorem process_randao_is_not_copy :
    getRandaoMix
      (processRandao samplePivotHash (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _))
      0
      (processRandao_length samplePivotHash (genesisRandaoMixes sampleMixZero)
        0 [] (genesisRandaoMixes_length _)) ≠
      getRandaoMix (genesisRandaoMixes sampleMixZero) 0
        (genesisRandaoMixes_length _) :=
  processRandao_not_copy

/-- phase0:2315 vs 2241. Current-epoch write leaves the next slot. -/
theorem process_randao_leaves_next :
    getRandaoMix
      (processRandao samplePivotHash (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _))
      1
      (processRandao_length samplePivotHash (genesisRandaoMixes sampleMixZero)
        0 [] (genesisRandaoMixes_length _)) =
      getRandaoMix (genesisRandaoMixes sampleMixZero) 1
        (genesisRandaoMixes_length _) :=
  processRandao_next_unchanged

/-- phase0:2314-2315 vs 2237-2243. Not the epoch-boundary copy. -/
theorem process_randao_is_not_reset :
    getRandaoMix
      (processRandao samplePivotHash (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _))
      0
      (processRandao_length samplePivotHash (genesisRandaoMixes sampleMixZero)
        0 [] (genesisRandaoMixes_length _)) ≠
      getRandaoMix
        (processRandaoMixesReset (genesisRandaoMixes sampleMixZero) 0
          (genesisRandaoMixes_length _))
        0 (processRandaoMixesReset_length _ 0 (genesisRandaoMixes_length _)) :=
  processRandao_ne_reset

/-- phase0:2314. A copy mutant of the write is not xor. -/
theorem process_randao_is_not_copy_mutant :
    getRandaoMix
      (processRandao samplePivotHash (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _))
      0
      (processRandao_length samplePivotHash (genesisRandaoMixes sampleMixZero)
        0 [] (genesisRandaoMixes_length _)) ≠
      getRandaoMix
        (processRandaoCopy (genesisRandaoMixes sampleMixZero) 0
          (genesisRandaoMixes_length _))
        0 (processRandaoCopy_length _ 0 (genesisRandaoMixes_length _)) :=
  processRandao_ne_copy_mutant

/-- phase0:2273 then 1823. After xor+reset, next epoch reads the xor. -/
theorem process_randao_then_reset_next_is_xor :
    getRandaoMix
      (processRandaoThenReset samplePivotHash
        (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _))
      1
      (processRandaoThenReset_length samplePivotHash
        (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _)) = samplePivotDigest :=
  processRandaoThenReset_genesis_next

/-- phase0:2273 then 1823, not reset-then-xor. Next epoch differs. -/
theorem process_randao_then_reset_not_swapped :
    getRandaoMix
      (processRandaoThenReset samplePivotHash
        (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _))
      1
      (processRandaoThenReset_length samplePivotHash
        (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _)) ≠
      getRandaoMix
        (processResetThenRandao samplePivotHash
          (genesisRandaoMixes sampleMixZero) 0 []
          (genesisRandaoMixes_length _))
        1
        (processResetThenRandao_length samplePivotHash
          (genesisRandaoMixes sampleMixZero) 0 []
          (genesisRandaoMixes_length _)) :=
  processRandaoThenReset_ne_swapped

/-- phase0:2273 then 1823. Current epoch still holds the xor. -/
theorem process_randao_then_reset_keeps_current :
    getRandaoMix
      (processRandaoThenReset samplePivotHash
        (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _))
      0
      (processRandaoThenReset_length samplePivotHash
        (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _)) = samplePivotDigest :=
  processRandaoThenReset_genesis_current

/-- phase0:1286-1290. Epoch is `slot // 32`, not the slot itself. -/
theorem epoch_at_slot_is_floor_div :
    computeEpochAtSlot ⟨31, by decide⟩ = 0 ∧
      computeEpochAtSlot ⟨32, by decide⟩ = 1 := by
  constructor
  · simp [computeEpochAtSlot, SLOTS_PER_EPOCH]
  · simp [computeEpochAtSlot, SLOTS_PER_EPOCH]

/-- phase0:1368-1372. `get_current_epoch` reads `state.slot` only. -/
theorem get_current_epoch_reads_slot :
    getCurrentEpoch { slot := ⟨32, by decide⟩, header := z } = 1 := by
  simp [getCurrentEpoch, computeEpochAtSlot, SLOTS_PER_EPOCH]

/-- phase0:2202. Epoch 0 does not clear votes; a always-clear mutant does. -/
theorem eth1_reset_keeps_off_boundary :
    processEth1DataReset [7] 0 = [7] ∧
      processEth1DataResetAlways [7] 0 = [] :=
  ⟨processEth1DataReset_epoch_zero [7], rfl⟩

/-- phase0:2202. `next_epoch = 64` clears. -/
theorem eth1_reset_clears_on_boundary :
    processEth1DataReset [7] 63 = [] :=
  processEth1DataReset_epoch_sixty_three [7]

/-- The always-clear mutant is not the archived helper. -/
theorem eth1_reset_not_always_clear :
    processEth1DataReset [7] 0 ≠ processEth1DataResetAlways [7] 0 := by
  simp [processEth1DataReset_epoch_zero, processEth1DataResetAlways]

/-- phase0:626 vs 625. Slashings ring is 8192, not the randao VECTOR. -/
theorem slashings_vector_is_not_randao :
    EPOCHS_PER_SLASHINGS_VECTOR ≠ EPOCHS_PER_HISTORICAL_VECTOR :=
  slashingsVector_ne_historical

/-- phase0:2231. Reset writes 0 at next, not a copy of current. -/
theorem slashings_reset_writes_zero_not_copy :
    (processSlashingsReset (sampleSlashings 7) 0
        (sampleSlashings_length 7))[getSlashingsIndex (0 + 1)]'(by
          rw [processSlashingsReset_length (sampleSlashings 7) 0
            (sampleSlashings_length 7)]
          exact getSlashingsIndex_lt (0 + 1)) = 0 ∧
      (processSlashingsResetCopy (sampleSlashings 7) 0
        (sampleSlashings_length 7))[getSlashingsIndex (0 + 1)]'(by
          rw [processSlashingsResetCopy_length (sampleSlashings 7) 0
            (sampleSlashings_length 7)]
          exact getSlashingsIndex_lt (0 + 1)) = 7 :=
  processSlashingsReset_ne_copy

/-- Gloas:1578-1598. `process_epoch` cannot accept a withdrawal payload. -/
theorem process_epoch_cannot_accept_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  gloas_process_epoch_not_accepted hep hacc

/-- Same-clock acceptance of a singleton is impossible. -/
theorem same_clock_cannot_accept {c : Clock} {b : Block}
    (h : AcceptedBlocks c [b] c) : False :=
  accepted_singleton_advances h

/-- phase0:2252. Historical period is 256, not the 8192-slot vector. -/
theorem historical_period_is_256 :
    HISTORICAL_PERIOD = 256 ∧
      HISTORICAL_PERIOD ≠ SLOTS_PER_HISTORICAL_ROOT :=
  ⟨historicalPeriod_eq, by decide⟩

/-- Forgetting `// 32` misses the epoch-255 append. -/
theorem historical_uses_period_not_slots :
    processHistoricalRootsUpdate ([] : List Nat) 255 7 = [7] ∧
      processHistoricalRootsUpdateNoDiv ([] : List Nat) 255 7 = [] := by
  refine ⟨processHistoricalRootsUpdate_epoch_255 [] 7, ?_⟩
  simp [processHistoricalRootsUpdateNoDiv, SLOTS_PER_HISTORICAL_ROOT]

/-- Capella:379-387. Summaries use the same 256-epoch guard. -/
theorem historical_summaries_keep_off_boundary
    (s : HistoricalSummary) :
    processHistoricalSummariesUpdate [] 0 s = [] :=
  processHistoricalSummariesUpdate_epoch_zero s

/-- phase0:2262-2265. Participation always rotates; historical does not
append at epoch 0. -/
theorem participation_rotates_off_historical_boundary :
    processParticipationRecordUpdates [1] = ([1], []) ∧
      processHistoricalRootsUpdate [9] 0 7 = [9] :=
  participation_rotates_when_historical_keeps [1] [9] 7

/-- Altair:824-828. Current flags become previous; current is zeros. -/
theorem participation_flags_clear_current :
    processParticipationFlagUpdates [1, 2] 2 = ([1, 2], [0, 0]) := by
  simp [processParticipationFlagUpdates]

/-- A historical append is not an accepted withdrawal payload. -/
theorem historical_append_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  historical_append_not_accepted hep hacc

/-- phase0:2213-2221. The hysteresis band is not symmetric. -/
theorem hysteresis_thresholds_are_asymmetric :
    downwardThreshold = 250000000 ∧ upwardThreshold = 1250000000 ∧
      downwardThreshold ≠ upwardThreshold :=
  ⟨downwardThreshold_eq, upwardThreshold_eq, hysteresis_band_asymmetric⟩

/-- In-band 31.8e9 vs 32e9 stays 32e9; always-update floors to 31e9. -/
theorem effective_balance_keeps_in_band :
    processEffectiveBalanceUpdate (318 * 10 ^ 8) (32 * 10 ^ 9)
        MAX_EFFECTIVE_BALANCE = 32 * 10 ^ 9 ∧
      processEffectiveBalanceUpdateAlways (318 * 10 ^ 8) (32 * 10 ^ 9)
        MAX_EFFECTIVE_BALANCE = 31 * 10 ^ 9 :=
  ⟨processEffectiveBalanceUpdate_in_band_keeps,
    processEffectiveBalanceUpdateAlways_in_band_floors⟩

theorem effective_balance_not_always_update :
    processEffectiveBalanceUpdate (318 * 10 ^ 8) (32 * 10 ^ 9)
      MAX_EFFECTIVE_BALANCE ≠
    processEffectiveBalanceUpdateAlways (318 * 10 ^ 8) (32 * 10 ^ 9)
      MAX_EFFECTIVE_BALANCE :=
  processEffectiveBalanceUpdate_ne_always

/-- Electra:733-740 / 1228-1244. Compounding 40e9 is not capped at 32e9. -/
theorem electra_compounding_keeps_40e9 :
    processEffectiveBalanceUpdateElectra (40 * 10 ^ 9) compoundingAt32 =
      40 * 10 ^ 9 ∧
      processEffectiveBalanceUpdate (40 * 10 ^ 9) (32 * 10 ^ 9)
        MAX_EFFECTIVE_BALANCE = MAX_EFFECTIVE_BALANCE :=
  ⟨processEffectiveBalanceUpdateElectra_compounding_40e9,
    processEffectiveBalanceUpdate_phase0_caps⟩

theorem electra_compounding_ne_phase0_cap :
    processEffectiveBalanceUpdateElectra (40 * 10 ^ 9) compoundingAt32 ≠
      processEffectiveBalanceUpdate (40 * 10 ^ 9) (32 * 10 ^ 9)
        MAX_EFFECTIVE_BALANCE :=
  processEffectiveBalanceUpdateElectra_ne_phase0_cap

/-- Altair:836-840. Epoch 0 keeps; epoch 255 rotates `fresh`. -/
theorem sync_committee_keeps_off_boundary :
    processSyncCommitteeUpdates (0 : Nat) 1 0 2 = (0, 1) :=
  processSyncCommitteeUpdates_epoch_zero 0 1 2

theorem sync_committee_rotates_on_boundary :
    processSyncCommitteeUpdates (0 : Nat) 1 255 2 = (1, 2) :=
  processSyncCommitteeUpdates_epoch_255 0 1 2

theorem sync_committee_not_always_rotate :
    processSyncCommitteeUpdates (0 : Nat) 1 0 2 ≠
      processSyncCommitteeUpdatesAlways 0 1 0 2 :=
  processSyncCommitteeUpdates_ne_always

/-- Effective-balance / sync-committee helpers accept no payload. -/
theorem effective_balance_update_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  effective_balance_update_not_accepted hep hacc

theorem sync_committee_update_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  sync_committee_update_not_accepted hep hacc

/-- Electra:344 / Gloas:1621. Index 16 stops before the next deposit. -/
theorem pending_deposits_cap_at_sixteen (d : PendingDepositView)
    (rest : List PendingDepositView) :
    takePendingDeposits 0 MAX_PENDING_DEPOSITS_PER_EPOCH (d :: rest) = [] :=
  takePendingDeposits_caps_at_sixteen d 0 rest

/-- Gloas dropped Electra:1140-1148. A post-genesis request still walks. -/
theorem gloas_pending_deposits_drop_eth1_bridge
    (d : PendingDepositView) (hs : d.slot ≤ 10)
    (hgen : GENESIS_SLOT.val < d.slot) :
    takePendingDeposits 10 0 [d] = [d] ∧
      takePendingDepositsElectra 10 0 1 0 [d] = [] :=
  takePendingDeposits_gloas_drops_eth1_bridge d 10 hs hgen

/-- Gloas:1658-1661. Missed churn clears leftover; always-keep is a mutant. -/
theorem deposit_churn_clears_when_not_hit :
    depositBalanceToConsume false 5 1 ≠
      depositBalanceToConsumeAlways 5 1 :=
  depositBalanceToConsume_ne_always

/-- Gloas:1669. Second-window weight is not credited. -/
theorem builder_payments_ignore_next_window :
    creditedBuilderWeights (List.replicate 32 0 ++ [7]) 1 ≠
      creditedBuilderWeightsAll (List.replicate 32 0 ++ [7]) 1 :=
  creditedBuilderWeights_ne_all

/-- Gloas:1416-1422. Quorum is 6/10 of the per-slot balance. -/
theorem builder_quorum_uses_per_slot :
    builderPaymentQuorum (32 * 10) ≠ builderPaymentQuorumNoSlot (32 * 10) :=
  builderPaymentQuorum_ne_noSlot

/-- Electra:620-628. Compounding 40e9 is queue-eligible; phase0 equality is not. -/
theorem electra_activation_queue_accepts_40e9 :
    isEligibleForActivationQueueElectra FAR_FUTURE_EPOCH (40 * 10 ^ 9) ≠
      isEligibleForActivationQueuePhase0 FAR_FUTURE_EPOCH (40 * 10 ^ 9) :=
  isEligibleForActivationQueue_electra_ne_phase0_40e9

theorem pending_deposits_are_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  pending_deposits_not_accepted hep hacc

theorem builder_pending_payments_are_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  builder_pending_payments_not_accepted hep hacc

/-- phase0:1306-1310. Effect epoch is +5, not +1. -/
theorem activation_exit_epoch_uses_lookahead :
    computeActivationExitEpoch 0 ≠
      computeActivationExitEpochNoLookahead 0 :=
  computeActivationExitEpoch_ne_noLookahead

/-- phase0:1077-1083. Active on `[activation, exit)`, not closed. -/
theorem active_validator_is_half_open :
    isActiveValidator 0 5 5 ≠ isActiveValidatorClosed 0 5 5 :=
  isActiveValidator_ne_closed

/-- Electra:1203-1205. A slashed source is skipped, not transferred. -/
theorem consolidation_skips_slashed :
    consolidationStep slashedUnwithdrawable 2 ≠
      consolidationStepTransferSlashed slashedUnwithdrawable 2 :=
  consolidationStep_ne_transferSlashed

/-- Electra:1206-1207. An unwithdrawable source stops the walk. -/
theorem consolidation_stops_before_later :
    consumedPendingConsolidations 2 [blockedUnslashed, readyUnslashed] = 0 :=
  consumedPendingConsolidations_stops

/-- Electra:857-860. Already-exiting is a no-op. -/
theorem initiate_exit_is_noop_if_exiting :
    initiateValidatorExit alreadyExiting 99 ≠
      initiateValidatorExitAlways alreadyExiting 99 :=
  initiateValidatorExit_ne_always

/-- phase0:1637. Withdrawable is exit + 256, not +1. -/
theorem initiate_exit_uses_256_delay :
    initiateValidatorExit notYetExiting 7 ≠
      initiateValidatorExitShort notYetExiting 7 :=
  initiateValidatorExit_ne_short

/-- Electra:1052-1062. Queue eligibility wins over ejection. -/
theorem registry_prefers_queue_to_eject :
    registryActionElectra true true false ≠
      registryActionEjectFirst true true false :=
  registryActionElectra_ne_ejectFirst

/-- phase0:696. Ejection is 16e9, not 32e9. -/
theorem ejection_balance_is_not_max_eb :
    EJECTION_BALANCE ≠ MAX_EFFECTIVE_BALANCE :=
  ejectionBalance_ne_maxEB

theorem pending_consolidations_are_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  pending_consolidations_not_accepted hep hacc

theorem registry_updates_are_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  registry_updates_not_accepted hep hacc

/-- Electra:924-926. Overflow epochs use ceil, not floor. -/
theorem exit_overflow_epochs_ceil :
    additionalExitEpochs 150 100 ≠ additionalExitEpochsFloor 150 100 :=
  additionalExitEpochs_ne_floor

/-- Electra:917-920. A new earliest epoch resets leftover. -/
theorem exit_churn_resets_on_new_epoch :
    computeExitEpochAndUpdateChurn
        { earliestExitEpoch := 0, exitBalanceToConsume := 999 } 0 40 100 ≠
      computeExitEpochAndUpdateChurnKeep
        { earliestExitEpoch := 0, exitBalanceToConsume := 999 } 0 40 100 :=
  computeExitEpochAndUpdateChurn_ne_keep

/-- Gloas:626 vs phase0:698. Exit churn uses 2^15, not 2^16. -/
theorem gloas_exit_churn_uses_half_quotient :
    exitChurnLimitGloas (CHURN_LIMIT_QUOTIENT * (200 * 10 ^ 9)) ≠
      balanceChurnLimit (CHURN_LIMIT_QUOTIENT * (200 * 10 ^ 9)) :=
  exitChurnLimitGloas_ne_electra_quotient

/-- Electra:1076. Penalty window is +4096, not +8192. -/
theorem slashing_penalty_is_mid_vector :
    appliesSlashingPenalty true 0 4096 ≠
      appliesSlashingPenaltyFull true 0 4096 :=
  appliesSlashingPenalty_ne_full

/-- Electra:1079-1086 vs phase0:2188-2193. Increment formulas differ. -/
theorem electra_slashing_penalty_ne_phase0 :
    slashingPenaltyElectra (32 * 10 ^ 9) (321 * 10 ^ 8) (32 * 10 ^ 9) ≠
      slashingPenaltyPhase0 (32 * 10 ^ 9) (321 * 10 ^ 8) (32 * 10 ^ 9) :=
  slashingPenaltyElectra_ne_phase0

theorem exit_churn_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  exit_churn_not_accepted hep hacc

theorem process_slashings_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  process_slashings_not_accepted hep hacc

/-- phase0:1889 vs Altair:754. Epoch 1 skips FFG, not inactivity. -/
theorem justification_skips_epoch_one_not_inactivity :
    skipsJustification 1 ≠ skipsInactivityUpdates 1 :=
  skipsJustification_ne_inactivity_at_one

/-- phase0:1933. Exact 2/3 justifies; a `>` mutant rejects it. -/
theorem justification_threshold_is_ge :
    justifiesSupermajority 2 3 ≠ justifiesSupermajorityStrict 2 3 :=
  justifiesSupermajority_ne_strict

/-- phase0:1928-1930. Bit 0 is cleared; a reverse rotate disagrees. -/
theorem justification_bits_shift_left_insert_false :
    shiftJustificationBits [true, true, false, true] ≠
      shiftJustificationBitsRev [true, true, false, true] :=
  shiftJustificationBits_ne_rev

/-- phase0:1971. Delay 4 is not a leak; delay 5 is. -/
theorem inactivity_leak_is_strictly_above_four :
    isInInactivityLeak 5 1 = false ∧ isInInactivityLeak 6 1 = true :=
  ⟨isInInactivityLeak_at_four, isInInactivityLeak_at_five⟩

/-- Altair:768-775. Recovery does not run during a leak. -/
theorem inactivity_score_does_not_recover_in_leak :
    inactivityScoreStep 10 false true ≠
      inactivityScoreStepAlwaysRecover 10 false :=
  inactivityScoreStep_ne_alwaysRecover

/-- Altair:481-482. Missing HEAD has no flag penalty. -/
theorem head_miss_has_no_flag_penalty :
    flagMissPenalty TIMELY_HEAD_FLAG_INDEX TIMELY_HEAD_WEIGHT 64 = 0 ∧
      flagMissPenalty TIMELY_TARGET_FLAG_INDEX TIMELY_TARGET_WEIGHT 64 ≠ 0 :=
  ⟨flagMissPenalty_head_zero, flagMissPenalty_target_nonzero⟩

theorem justification_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  justification_not_accepted hep hacc

theorem inactivity_updates_are_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  inactivity_updates_not_accepted hep hacc

theorem rewards_and_penalties_are_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  rewards_and_penalties_not_accepted hep hacc

/-- phase0:1934. k=3 uses `+ 2`, not the k=4 `+ 3`. -/
theorem finalize_k3_is_plus_two :
    finalizeK3 [false, true, true, false] 0 3 ≠
      finalizeK3AsK4 [false, true, true, false] 0 3 :=
  finalizeK3_ne_asK4

/-- phase0:1937. k=2 source is old current, not old previous. -/
theorem finalize_k2_source_is_old_current :
    finalizeK2FromOldCurr [true, true, true, false] 0 2 ≠
      finalizeK2FromOldPrev [true, true, true, false] 1 2 :=
  finalizeK2FromOldCurr_ne_oldPrev

/-- phase0:1940. Latest window does not require bits[2]. -/
theorem finalize_k2_recent_does_not_need_third_bit :
    finalizeK2Recent [true, true, false, false] 5 6 ≠
      finalizeK2FromOldCurr [true, true, false, false] 5 6 :=
  finalizeK2Recent_ne_requiresThird

/-- phase0:1931-1941. Windows are independent `if`s; later overwrites. -/
theorem finalize_windows_are_independent_ifs :
    finalizedEpochSource [true, true, true, true] 0 1 3 ≠
      finalizedEpochSourceElif [true, true, true, true] 0 1 3 :=
  finalizedEpochSource_ne_elif

/-- Altair:477-478. Leak zeros the flag reward. -/
theorem flag_reward_is_zero_in_leak :
    flagReward 64 TIMELY_TARGET_WEIGHT 32 32 true ≠
      flagRewardAlwaysPay 64 TIMELY_TARGET_WEIGHT 32 32 :=
  flagReward_ne_alwaysPay

/-- Bellatrix:302 vs Altair:504. Gloas inherits Bellatrix. -/
theorem inactivity_penalty_inherited_is_bellatrix :
    inactivityPenaltyBellatrix (32 * 10 ^ 9) 1 ≠
      inactivityPenaltyAltair (32 * 10 ^ 9) 1 :=
  inactivityPenalty_inherited_ne_altair

/-- Altair:390-391. Increments, not raw EB. -/
theorem base_reward_uses_increments :
    baseReward (32 * 10 ^ 9) 64 ≠
      baseRewardNoIncrement (32 * 10 ^ 9) 64 :=
  baseReward_ne_noIncrement

theorem weigh_finalization_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  weigh_finalization_not_accepted hep hacc

theorem flag_index_deltas_are_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  flag_index_deltas_not_accepted hep hacc

theorem inactivity_penalty_deltas_are_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  inactivity_penalty_deltas_not_accepted hep hacc

theorem get_base_reward_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  get_base_reward_not_accepted hep hacc

/-- phase0:985. `integer_squareroot(10) = 3`, not the identity. -/
theorem integer_squareroot_is_not_identity :
    integerSquareRoot 10 ≠ 10 :=
  integerSquareRoot_ne_identity

/-- Altair:369-373. Per-increment uses `integer_squareroot`, not raw total. -/
theorem base_reward_per_increment_uses_sqrt :
    baseRewardPerIncrement 4 ≠ baseRewardPerIncrementNoSqrt 4 :=
  baseRewardPerIncrement_ne_noSqrt

/-- phase0:1511. Empty indices still credit the increment minimum. -/
theorem total_balance_empty_is_not_zero :
    totalBalance [] ≠ totalBalanceNoMin [] :=
  totalBalance_ne_noMin

/-- phase0:1981-1982. Slashed-and-withdrawing is eligible. -/
theorem eligible_includes_slashed_withdrawing :
    isEligibleValidator exitedSlashedWithdrawing 5 ≠
      isEligibleValidatorActiveOnly exitedSlashedWithdrawing 5 :=
  isEligibleValidator_ne_activeOnly

theorem integer_squareroot_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  integer_squareroot_not_accepted hep hacc

theorem total_balance_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  total_balance_not_accepted hep hacc

theorem eligible_validator_indices_are_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  eligible_validator_indices_not_accepted hep hacc

theorem base_reward_per_increment_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  base_reward_per_increment_not_accepted hep hacc

/-- Altair:284 vs XOR. Adding a set bit is OR, not a toggle. -/
theorem add_flag_is_or_not_xor :
    addFlag 1 TIMELY_SOURCE_FLAG_INDEX ≠
      addFlagXor 1 TIMELY_SOURCE_FLAG_INDEX :=
  addFlag_ne_xor

/-- Altair:295. Extra bits do not clear `has_flag`. -/
theorem has_flag_allows_other_bits :
    hasFlag 7 TIMELY_TARGET_FLAG_INDEX ≠
      hasFlagExact 7 TIMELY_TARGET_FLAG_INDEX :=
  hasFlag_ne_exact

/-- phase0:1424-1425. Inactive registry entries are dropped. -/
theorem active_indices_drop_inactive :
    activeValidatorIndices [activatingLater, activeNow] 3 ≠
      allValidatorIndices [activatingLater, activeNow] :=
  activeValidatorIndices_ne_all

/-- Altair:404-407. Previous epoch reads the previous buffer. -/
theorem participation_buffer_is_not_always_current :
    participationBuffer [1] [2] 4 5 ≠
      participationBufferAlwaysCurrent [1] [2] 4 5 :=
  participationBuffer_ne_alwaysCurrent

/-- Altair:412. Slashed participating indices are dropped. -/
theorem unslashed_participating_drops_slashed :
    isUnslashedParticipating slashedTarget TIMELY_TARGET_FLAG_INDEX ≠
      isParticipatingKeepSlashed slashedTarget TIMELY_TARGET_FLAG_INDEX :=
  isUnslashedParticipating_ne_keepSlashed

theorem has_flag_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  has_flag_not_accepted hep hacc

theorem add_flag_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  add_flag_not_accepted hep hacc

theorem active_validator_indices_are_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  active_validator_indices_not_accepted hep hacc

theorem unslashed_participating_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  unslashed_participating_not_accepted hep hacc

/-- phase0:1403. The current slot is not in the historical window. -/
theorem block_root_rejects_current_slot :
    blockRootSlotOk 10 10 ≠ blockRootSlotOkClosed 10 10 :=
  blockRootSlotOk_ne_closed

/-- phase0:1404. Index is `% 8192`, not `/ 8192`. -/
theorem block_root_index_is_mod :
    blockRootIndex SLOTS_PER_HISTORICAL_ROOT ≠
      blockRootIndexDiv SLOTS_PER_HISTORICAL_ROOT :=
  blockRootIndex_ne_div

/-- phase0:1393. Epoch root is the start slot, not the last. -/
theorem block_root_epoch_uses_start_slot :
    blockRootEpochSlot 1 ≠ blockRootEpochSlotLast 1 :=
  blockRootEpochSlot_ne_last

/-- phase0:1849. Matching target filters on the epoch block root. -/
theorem matching_target_requires_epoch_root :
    matchingTarget [(0, 1), (1, 9)] 1 ≠
      matchingTargetNoRoot [(0, 1), (1, 9)] 1 :=
  matchingTarget_ne_noRoot

/-- Gloas:1367 vs Altair:446. Gloas target has no delay bound. -/
theorem gloas_target_flag_has_no_delay :
    participationFlagsAltair true true true 33 ≠
      participationFlagsGloas true true true 33 :=
  participationFlags_gloas_target_no_delay

/-- Gloas:1360. Head requires payload availability. -/
theorem gloas_head_needs_payload :
    isMatchingHeadGloas true true false ≠
      isMatchingHeadAltair true true :=
  isMatchingHead_gloas_needs_payload

/-- Gloas:1074. Same-slot requires the root to differ from the previous slot. -/
theorem same_slot_rejects_equal_prev_root :
    isAttestationSameSlot 5 7 7 7 ≠
      isAttestationSameSlotNoPrev 5 7 7 :=
  isAttestationSameSlot_ne_noPrev

theorem block_root_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  block_root_not_accepted hep hacc

theorem matching_target_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  matching_target_not_accepted hep hacc

theorem attestation_participation_flags_are_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  attestation_participation_flags_not_accepted hep hacc

theorem attestation_same_slot_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  attestation_same_slot_not_accepted hep hacc

/-- Electra:1652 vs Altair:571. Electra drops the `+ SLOTS_PER_EPOCH` cap. -/
theorem electra_inclusion_drops_upper_bound :
    attestationInclusionOkPhase0 0 33 ≠
      attestationInclusionOkElectra 0 33 :=
  attestationInclusion_electra_drops_upper

/-- Gloas:2331 vs Electra:1655. Gloas allows `data.index = 1`. -/
theorem gloas_attestation_index_allows_payload_bit :
    attestationIndexOkElectra 1 ≠ attestationIndexOkGloas 1 :=
  attestationIndex_electra_ne_gloas

/-- phase0:1575. Aggregation bits select the committee, not the whole set. -/
theorem attesting_indices_honor_bits :
    attestingIndicesPhase0 [10, 11, 12] [true, false, true] ≠
      attestingIndicesAll [10, 11, 12] [true, false, true] :=
  attestingIndices_ne_all

/-- Electra:798-807. Offset walks every selected committee. -/
theorem electra_attesting_indices_use_offset :
    attestingIndicesElectra [true, false, false, true] [[10, 11], [20, 21]] 0 ≠
      attestingIndicesPhase0 [10, 11] [true, false, false, true] :=
  attestingIndices_electra_ne_phase0_first

/-- phase0:1345. Domain is type ++ fork_root[:28], not the full root. -/
theorem compute_domain_takes_28 :
    computeDomain DOMAIN_BEACON_ATTESTER dummyForkRoot ≠
      computeDomainFullFork DOMAIN_BEACON_ATTESTER dummyForkRoot :=
  computeDomain_ne_full

theorem process_attestation_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  process_attestation_not_accepted hep hacc

theorem attesting_indices_are_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  attesting_indices_not_accepted hep hacc

theorem compute_signing_root_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  compute_signing_root_not_accepted hep hacc

/-- phase0:1466-1468. Count divides by `TARGET_COMMITTEE_SIZE`, not only by slots. -/
theorem committee_count_uses_target_size :
    committeeCountPerSlot (SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE) ≠
      committeeCountPerSlotNoTarget (SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE) :=
  committeeCount_ne_noTarget

/-- phase0:1265-1269. Last committee keeps the remainder. -/
theorem committee_slice_keeps_remainder :
    committeeSlice 10 2 3 ≠ committeeSliceEqual 10 2 3 :=
  committeeSlice_ne_equal

/-- phase0:1487. Committee index uses `slot % 32`. -/
theorem beacon_committee_index_mods_slot :
    beaconCommitteeIndex 33 1 2 ≠
      beaconCommitteeIndexNoMod 33 1 2 :=
  beaconCommitteeIndex_ne_noMod

/-- Electra:727. Only set bits are selected committee indices. -/
theorem committee_indices_honor_bits :
    committeeIndices [false, true, false, true] ≠
      committeeIndicesAll [false, true, false, true] :=
  committeeIndices_ne_all

theorem committee_count_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  committee_count_not_accepted hep hacc

theorem compute_committee_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  compute_committee_not_accepted hep hacc

theorem beacon_committee_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  beacon_committee_not_accepted hep hacc

theorem committee_indices_are_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  committee_indices_not_accepted hep hacc

/-- phase0:1500. Outer proposer seed suffixes `uint_to_bytes(slot)`, not epoch. -/
theorem beacon_proposer_seed_uses_slot_not_epoch :
    beaconProposerSeedPreimage [9] 33 ≠
      beaconProposerSeedPreimageEpoch [9] 33 :=
  beaconProposerSeed_ne_epoch

/-- phase0:1500 vs 1486. Bare committee seed omits the slot suffix. -/
theorem beacon_proposer_seed_is_not_bare (epochSeed : List Nat) :
    beaconProposerSeedPreimage epochSeed 1 ≠ epochSeed :=
  beaconProposerSeed_has_slot epochSeed

/-- Fulu:366. Lookahead index is `slot % 32`, not the raw slot. -/
theorem fulu_proposer_index_mods_slot :
    fuluProposerLookaheadIndex 33 ≠ fuluProposerLookaheadIndexNoMod 33 :=
  fuluProposerLookaheadIndex_ne_raw

/-- Electra:598. Sampling width is 16 bits, not a byte. -/
theorem electra_random_is_not_byte :
    MAX_RANDOM_VALUE ≠ MAX_RANDOM_BYTE :=
  maxRandomValue_ne_byte

/-- Electra:604. Preimage uses `i // 16`, not phase0 `i // 32`. -/
theorem electra_random_preimage_uses_div16 :
    electraRandomPreimage [9] 16 ≠ randomBytePreimage [9] 16 :=
  electraRandomPreimage_ne_phase0 [9]

/-- Electra:605. Offset is `i % 16 * 2`, not `i % 32`. -/
theorem electra_random_offset_is_pairs :
    electraRandomOffset 1 ≠ randomByteOffset 1 :=
  electraRandomOffset_ne_phase0

/-- Electra:609. 32e9 at max 16-bit random fails the 2048e9 cap. -/
theorem electra_accept_uses_2048e9 :
    electraProposerAccepts (32 * 10 ^ 9) MAX_RANDOM_VALUE ≠
      electraProposerAcceptsPhase0Cap (32 * 10 ^ 9) MAX_RANDOM_VALUE :=
  electraProposerAccepts_ne_phase0Cap

/-- Gloas:1285-1289. Slashed actives are dropped from proposer indices. -/
theorem gloas_proposer_indices_drop_slashed :
    unslashedActive [0, 1, 2] (fun i => decide (i = 1)) ≠
      unslashedActiveAll [0, 1, 2] (fun i => decide (i = 1)) :=
  unslashedActive_ne_all

/-- Gloas:562 / 1257. PTC seed domain is not the proposer domain. -/
theorem ptc_seed_uses_ptc_domain :
    getSeedPreimage DOMAIN_PTC_ATTESTER 0 [7] ≠
      getSeedPreimage DOMAIN_BEACON_PROPOSER 0 [7] :=
  ptcSeed_uses_ptc_domain

theorem beacon_proposer_seed_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  beacon_proposer_seed_not_accepted hep hacc

theorem electra_proposer_sample_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  electra_proposer_sample_not_accepted hep hacc

theorem fulu_proposer_index_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  fulu_proposer_index_not_accepted hep hacc

theorem gloas_proposer_unslashed_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  gloas_proposer_unslashed_not_accepted hep hacc

theorem ptc_seed_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  ptc_seed_not_accepted hep hacc

/-- Gloas:1199. Empty candidate list is not a sampling domain. -/
theorem balance_weighted_rejects_empty_indices :
    ¬ BalanceWeightedNonempty [] :=
  balanceWeighted_rejects_empty

/-- Gloas:1204-1206. Digest refresh is only at `offset == 0`, not every `i`. -/
theorem balance_weighted_refresh_is_chunked :
    balanceWeightedRefresh 1 ≠ balanceWeightedRefreshAlways 1 :=
  balanceWeightedRefresh_ne_always

/-- Gloas:1266 vs 1241. PTC does not shuffle; proposers do. -/
theorem ptc_does_not_shuffle :
    gloasPtcShuffle ≠ gloasProposerShuffle :=
  ptc_ne_proposer_shuffle

/-- Gloas:599 / 1241. PTC size is 512, not a singleton proposer draw. -/
theorem ptc_size_is_not_one :
    PTC_SIZE ≠ gloasProposerSelectionSize :=
  ptc_ne_proposer_size

/-- Gloas:1258-1263. Committees are concatenated in index order. -/
theorem ptc_committees_keep_order :
    concatCommittees [[1, 2], [3]] ≠ concatCommitteesRev [[1, 2], [3]] :=
  concatCommittees_ne_rev

/-- Gloas:1261-1263. Every committee in the slot is included. -/
theorem ptc_committees_are_not_first_only :
    concatCommittees [[1, 2], [3]] ≠ concatCommitteesFirst [[1, 2], [3]] :=
  concatCommittees_ne_first

/-- Gloas:1305. Next sync committee is sampled at `epoch + 1`. -/
theorem next_sync_committee_uses_next_epoch :
    nextSyncCommitteeEpoch 7 ≠ 7 :=
  nextSyncCommitteeEpoch_ne_current

theorem balance_weighted_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  balance_weighted_not_accepted hep hacc

theorem compute_ptc_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  compute_ptc_not_accepted hep hacc

theorem next_sync_committee_indices_are_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  next_sync_committee_indices_not_accepted hep hacc

/-- Electra:1111-1113. An existing pubkey is credited without a signature check. -/
theorem apply_pending_deposit_existing_skips_sig :
    applyPendingDeposit true false ≠
      applyPendingDepositSigAlways true false :=
  applyPendingDeposit_ne_sigAlways

/-- Electra:1110 vs 1770. Pending adds `amount`; Eth1 apply adds `Gwei(0)`. -/
theorem electra_pending_adds_amount_not_zero :
    electraNewValidatorAmount true 32 ≠ electraNewValidatorAmount false 32 :=
  electraNewValidatorAmount_ne

/-- Electra:1727-1728. Compounding 40e9 is not the phase0 32e9 cap. -/
theorem validator_from_deposit_uses_max_eb :
    validatorFromDepositEB (40 * 10 ^ 9) electraProposerMaxEb ≠
      validatorFromDepositEB (40 * 10 ^ 9) MAX_EFFECTIVE_BALANCE :=
  validatorFromDeposit_ne_phase0_cap

/-- Electra:1822. `eth1_deposit_index` advances even if the signature fails. -/
theorem process_deposit_index_always_advances :
    processDepositIndexAfter false 7 ≠
      processDepositIndexAfterOnlyIfValid false 7 :=
  processDepositIndex_always_advances

/-- phase0:2489. Merkle depth includes the list-length mix-in. -/
theorem deposit_proof_depth_includes_mixin :
    depositProofDepth 32 ≠ 32 :=
  depositProofDepth_includes_mixin

/-- Electra:1793-1797. Signed object is DepositMessage, not DepositData. -/
theorem deposit_message_omits_signature :
    depositMessageFields ≠ depositDataFields :=
  depositMessage_omits_signature

/-- Electra:1799. Deposit domain is DOMAIN_DEPOSIT, not attester. -/
theorem deposit_domain_is_not_attester :
    computeDomain DOMAIN_DEPOSIT dummyForkRoot ≠
      computeDomain DOMAIN_BEACON_ATTESTER dummyForkRoot :=
  depositDomain_uses_deposit_type

theorem apply_pending_deposit_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  apply_pending_deposit_not_accepted hep hacc

theorem apply_deposit_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  apply_deposit_not_accepted hep hacc

theorem is_valid_deposit_signature_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  is_valid_deposit_signature_not_accepted hep hacc

theorem get_validator_from_deposit_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  get_validator_from_deposit_not_accepted hep hacc

theorem process_deposit_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  process_deposit_not_accepted hep hacc

/-- phase0:1171. Sibling side uses `index // 2^i`, not `index % 2`. -/
theorem merkle_sibling_uses_level :
    merkleSiblingOnLeft 2 1 ≠ merkleSiblingOnLeftNoShift 2 1 :=
  merkleSibling_uses_level

/-- phase0:1172. Left pairing is sibling ++ value, not value ++ sibling. -/
theorem merkle_pair_left_is_not_always_right :
    merklePairPreimage [1] [2] true ≠
      merklePairAlwaysRight [1] [2] true :=
  merklePair_ne_always_right

/-- Electra:1947 vs Fulu:206. Fulu drops the UNSET start-index latch. -/
theorem fulu_drops_electra_start_latch :
    fuluDepositRequestStart UNSET_DEPOSIT_REQUESTS_START_INDEX 7 ≠
      electraDepositRequestStart UNSET_DEPOSIT_REQUESTS_START_INDEX 7 :=
  fulu_drops_start_latch

/-- Electra:1956. Request pending slot is `state.slot`, not GENESIS_SLOT. -/
theorem deposit_request_slot_is_not_genesis :
    depositRequestPendingSlot 5 ≠ GENESIS_SLOT.val :=
  depositRequest_slot_ne_eth1

/-- Electra:1956 vs 409. Pending slot is not `deposit_request.index`. -/
theorem deposit_request_slot_is_not_index :
    depositRequestPendingSlot 9 ≠ depositRequestPendingIndexMutant 9 3 :=
  depositRequest_slot_ne_index

/-- Fulu:180. Former `body.deposits` must be empty. -/
theorem fulu_rejects_legacy_deposits :
    fuluDepositsMustBeEmpty 1 = false :=
  fuluDeposits_rejects_nonempty

/-- Electra:291-292. Deposit and withdrawal request type tags differ. -/
theorem deposit_request_type_is_not_withdrawal :
    DEPOSIT_REQUEST_TYPE ≠ WITHDRAWAL_REQUEST_TYPE :=
  deposit_request_type_ne_withdrawal

theorem merkle_branch_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  merkle_branch_not_accepted hep hacc

theorem process_deposit_request_is_not_payload {pre post : Clock} {b : Block}
    (hep : GloasProcessEpoch pre post)
    (hacc : AcceptedBlocks pre [b] post) : False :=
  process_deposit_request_not_accepted hep hacc

/-- phase0:1243. Empty `indices` is not a sampling domain. -/
theorem compute_proposer_index_rejects_empty :
    ¬ ProposerIndicesNonempty [] :=
  empty_proposer_indices

/-- phase0:1251. Max effective balance accepts the max random byte.
A `>` mutant rejects that equality. -/
theorem proposer_accept_is_ge_not_gt :
    proposerAccepts MAX_EFFECTIVE_BALANCE MAX_RANDOM_BYTE ≠
      proposerAcceptsStrict MAX_EFFECTIVE_BALANCE MAX_RANDOM_BYTE :=
  proposerAccepts_ge_not_gt

/-- phase0:1251. Zero effective balance rejects a nonzero byte. -/
theorem proposer_zero_balance_rejects_nonzero :
    proposerAccepts 0 1 = false :=
  proposerAccepts_zero_pos (by decide : 0 < 1)

/-- phase0:1249. `i // 32` is not `i % 32`. -/
theorem proposer_random_byte_uses_div :
    randomBytePreimage [9] 32 ≠ randomBytePreimageMod [9] 32 :=
  random_byte_uses_div_not_mod [9]

/-- phase0:1249. i=0 and i=32 hash different `uint_to_bytes` inputs. -/
theorem proposer_random_byte_chunk_steps :
    randomBytePreimage [9] 0 ≠ randomBytePreimage [9] 32 :=
  randomBytePreimage_zero_ne_thirtytwo [9]

/-- phase0:1230. `index == index_count` is not a shuffled index. -/
theorem shuffled_index_rejects_equal_count :
    ¬ ShuffledIndexOk 7 7 :=
  shuffled_index_rejects_eq 7

/-- phase0:588. Shuffle is 90 rounds, not a 32-byte hash width. -/
theorem shuffle_rounds_are_not_hash32 :
    SHUFFLE_ROUND_COUNT ≠ HASH32_BYTES :=
  shuffleRoundCount_ne_hash32

/-- phase0:1205. Round tag is Uint8, not Uint64. -/
theorem shuffle_round_bytes_are_uint8 :
    uintToBytes 1 5 ≠ uintToBytes 8 5 :=
  round_bytes_is_not_u64

/-- phase0:1214. Bucket tag is Uint32, not Uint64. -/
theorem shuffle_bucket_bytes_are_uint32 :
    uintToBytes 4 1 ≠ uintToBytes 8 1 :=
  bucket_bytes_is_not_u64

/-- phase0:1203 / 1231. Zero rounds would be the identity. -/
theorem shuffled_index_identity_before_rounds :
    shuffledIndexOf (identityPerm 4) 2 = some 2 :=
  shuffledIndexOf_identity (by decide : 2 < 4)

/-- phase0:1209. The flip partner is an involution. -/
theorem shuffle_flip_is_involution :
    shuffleFlip 3 8 1 = 2 ∧ shuffleFlip 3 8 2 = 1 :=
  shuffleFlip_sample

/-- phase0:1206. Pivot is little-endian take-8, not big-endian. -/
theorem shuffle_pivot_is_little_endian :
    shufflePivot samplePivotHash [] 0 8 ≠
      shufflePivotBe samplePivotHash [] 0 8 :=
  shufflePivot_uses_le_not_be

/-- phase0:1217. The swap bit is indexed by `position`, not the loop index. -/
theorem shuffle_bit_uses_position :
    shuffleBitByteIndex (shufflePosition 0 8) ≠ shuffleBitByteIndex 0 :=
  shuffle_bit_uses_position_not_index

/-- phase0:1219. Bit 1 swaps; a swap-on-zero mutant disagrees. -/
theorem shuffle_swap_on_bit_one :
    shuffleSwapOrNot 3 5 1 ≠ shuffleSwapOrNotOnZero 3 5 1 :=
  shuffle_swap_is_not_on_zero

/-- phase0:1204. The walk is 90 rounds, not the empty fold. -/
theorem shuffle_is_not_zero_rounds :
    shuffleRounds ≠ [] :=
  shuffleRounds_ne_empty

/-- phase0:1210. A value and its flip share `position`. -/
theorem shuffle_flip_shares_position :
    shufflePosition 1 (shuffleFlip 3 8 1) =
      shufflePosition 2 (shuffleFlip 3 8 2) :=
  shuffleFlip_sample_shares_position

/-- phase0:1217. Indexing the bit by `idx` instead of `position` collides. -/
theorem shuffle_bit_at_index_collides :
    shuffleStepAtIndex samplePairHash [] 0 8 1 =
      shuffleStepAtIndex samplePairHash [] 0 8 2 ∧ 1 ≠ 2 :=
  shuffleStep_at_index_collides

/-- phase0:1210-1219. The archived position-max step does not collide. -/
theorem shuffle_step_partners_distinct :
    shuffleStep samplePairHash [] 0 8 1 ≠
      shuffleStep samplePairHash [] 0 8 2 :=
  shuffleStep_partners_distinct

/-- phase0:1203. A value ≥ n is not a permutation of `range(n)`. -/
theorem shuffle_perm_rejects_out_of_range :
    ¬ List.Perm [0, 2] (identityPerm 2) :=
  out_of_range_not_identity_perm

/-- phase0:1203. A shorter list is not a permutation of `range(n)`. -/
theorem shuffle_perm_rejects_short :
    ¬ List.Perm [0] (identityPerm 2) :=
  short_not_identity_perm

/-- phase0:1231. The returned slot is the 90-round walk, not the identity. -/
theorem shuffled_index_is_the_walk :
    shuffledIndexOf (shufflePermutation samplePairHash [] 2) 1 =
      some (shuffleIndexWalk samplePairHash [] 2 1) :=
  shuffledIndexOf_walk (by decide : 1 < 2)

/-- phase0:1211. Positions 0 and 255 share a bucket; 256 starts the next. -/
theorem shuffle_bucket_is_256_window :
    shuffleBucket 0 = shuffleBucket 255 ∧
      shuffleBucket 255 ≠ shuffleBucket 256 :=
  ⟨shuffleBucket_window_zero, shuffleBucket_next_window⟩

/-- phase0:1214. The cache hashes `position // 256`, not `position`. -/
theorem shuffle_source_uses_bucket_not_position :
    shuffleBucketPreimage [] 0 (shuffleBucket 256) ≠
      [] ++ shuffleRoundBytes 0 ++ uintToBytes 4 256 :=
  source_preimage_uses_bucket []

/-- phase0:1207-1216. A second lookup of the same bucket is a hit. -/
theorem shuffle_source_cache_hits_again :
    (sourceCacheStep samplePairHash [] 0
        (sourceCacheStep samplePairHash [] 0 [] 1).2 1).1 =
      (sourceCacheStep samplePairHash [] 0 [] 1).1 ∧
      (sourceCacheStep samplePairHash [] 0
          (sourceCacheStep samplePairHash [] 0 [] 1).2 1).2 =
        (sourceCacheStep samplePairHash [] 0 [] 1).2 :=
  (sourceCache_empty_then_hit samplePairHash [] 0 1).2

/-- phase0:1217. Same bucket, different source byte (positions 0 and 8). -/
theorem shuffle_same_bucket_distinct_byte :
    shuffleBucket 0 = shuffleBucket 8 ∧
      shuffleBitByteIndex 0 ≠ shuffleBitByteIndex 8 :=
  same_bucket_distinct_byte

/-- phase0:1217. `position // 8` is not `(position % 256) // 8`. -/
theorem shuffle_bit_byte_uses_mod_256 :
    shuffleBitByteIndex 256 ≠ shuffleBitByteIndexRaw 256 :=
  bit_byte_uses_mod_256

/-- phase0:1217-1218. One bit per bucket is not the archived offset. -/
theorem shuffle_bit_uses_offset_not_bucket :
    shuffleBitOf samplePairDigest 8 ≠
      shuffleBitOfBucket samplePairDigest 8 :=
  bit_uses_offset_not_bucket_only

/-- phase0:1213-1219. `shuffleStep` consumes the cached bucket bit. -/
theorem shuffle_step_uses_cached_bit :
    shuffleStep echoByteHash [] 0 512 256 =
      shuffleSwapOrNot 256
        (shuffleFlip (shufflePivot echoByteHash [] 0 512) 512 256)
        (shuffleStepBit echoByteHash [] 0 512 256) :=
  shuffleStep_uses_cached_bit echoByteHash [] 0 512 256

/-- phase0:1213-1217. Hashing `Uint32(position)` is not `source_by_bucket`. -/
theorem shuffle_bit_uses_bucket_not_position :
    shuffleBitOf (sourceByBucket echoByteHash [] 0 (shuffleBucket 256)) 256 ≠
      shuffleBitAtPosition echoByteHash [] 0 256 :=
  cached_bit_ne_position_bit

/-- phase0:1213-1215. Dropping `Uint8(round)` is not the archived preimage. -/
theorem shuffle_preimage_uses_round :
    shuffleBucketPreimage [] 1 0 ≠ [] ++ uintToBytes 4 0 :=
  source_preimage_uses_round [] 0

/-- phase0:1213-1215. Round 0 and round 1 do not share a preimage. -/
theorem shuffle_preimage_rounds_distinct :
    shuffleBucketPreimage [] 0 0 ≠ shuffleBucketPreimage [] 1 0 :=
  sourceByBucket_rounds_0_1 [] 0

/-- phase0:1204. The 90 Uint8 round encodings are Nodup. -/
theorem shuffle_rounds_uint8_distinct :
    (shuffleRounds.map shuffleRoundBytes).Nodup :=
  shuffleRounds_map_bytes_nodup

/-- phase0:588 / 1205. A 256-round mutant wraps `Uint8(256)` onto 0. -/
theorem shuffle_uint8_256_collides_zero :
    shuffleRoundBytes 256 = shuffleRoundBytes 0 :=
  uint8_round_256_collides_zero

/-- phase0:1207. A fresh dict is well-formed for every round. -/
theorem shuffle_cache_starts_empty_each_round :
    BucketCacheOk echoHeadHash [] 0 [] ∧
      BucketCacheOk echoHeadHash [] 1 [] :=
  each_round_starts_empty echoHeadHash [] 0 1

/-- phase0:1207. A cache filled at round 0 is not well-formed at round 1. -/
theorem shuffle_cache_not_reused_across_rounds :
    BucketCacheOk echoHeadHash [] 0
        [(0, sourceByBucket echoHeadHash [] 0 0)] ∧
      ¬ BucketCacheOk echoHeadHash [] 1
        [(0, sourceByBucket echoHeadHash [] 0 0)] :=
  BucketCacheOk_echo_round_0_not_1

/-- phase0:1207-1216. Reusing the previous dict returns a stale digest. -/
theorem shuffle_stale_cache_hit_is_wrong_round :
    (sourceCacheStep echoHeadHash [] 1
        [(0, sourceByBucket echoHeadHash [] 0 0)] 0).1 =
      sourceByBucket echoHeadHash [] 0 0 ∧
      sourceByBucket echoHeadHash [] 0 0 ≠
        sourceByBucket echoHeadHash [] 1 0 :=
  sourceCacheStep_stale_round_hit

/-- phase0:1207. Each step is an empty-cache lookup of that round. -/
theorem shuffle_step_eq_empty_cache :
    shuffleStep echoSplatHash [] 1 255 0 =
      shuffleSwapOrNot 0
        (shuffleFlip (shufflePivot echoSplatHash [] 1 255) 255 0)
        (shuffleBitOf
          (sourceCacheStep echoSplatHash [] 1 []
            (shuffleBucket (shufflePosition 0
              (shuffleFlip (shufflePivot echoSplatHash [] 1 255) 255 0)))).1
          (shufflePosition 0
            (shuffleFlip (shufflePivot echoSplatHash [] 1 255) 255 0))) :=
  shuffleStep_eq_empty_cache echoSplatHash [] 1 255 0

/-- phase0:1204-1207. Reusing round 0 for the second step is a mutant. -/
theorem shuffle_walk_not_fixed_round :
    [0, 1].foldl (fun acc r => shuffleStep echoSplatHash [] r 255 acc) 0 ≠
      [0, 1].foldl (fun acc _r => shuffleStep echoSplatHash [] 0 255 acc) 0 :=
  two_rounds_not_fixed_round

/-- phase0:1206 vs 1213-1215. The pivot preimage omits `Uint32(bucket)`. -/
theorem shuffle_pivot_preimage_omits_bucket :
    shufflePivotPreimage [] 1 ≠
      shufflePivotPreimageWithBucket [] 1 0 :=
  pivot_preimage_omits_bucket [] 1 0

/-- phase0:1213-1215. The bucket preimage extends the pivot preimage. -/
theorem shuffle_bucket_preimage_extends_pivot :
    shuffleBucketPreimage [] 1 0 =
      shufflePivotPreimage [] 1 ++ uintToBytes 4 0 :=
  shuffleBucketPreimage_eq_pivot_append [] 1 0

/-- phase0:1206 vs 1213-1215. Hashing the longer preimage is a mutant. -/
theorem shuffle_pivot_raw_ne_bucket_hash :
    shufflePivotRaw echoLenHash [] 1 ≠
      uintFromBytes ((echoLenHash (shuffleBucketPreimage [] 1 0)).take 8) :=
  pivot_raw_ne_bucket_echoLen

/-- phase0:1024-1028 / 1206. A suffix byte does not change `[0:8]`. -/
theorem shuffle_pivot_ignores_suffix_byte :
    samplePivotDigest.take 8 = sampleTailDigest.take 8 ∧
      samplePivotDigest ≠ sampleTailDigest :=
  take8_ignores_suffix_byte

/-- phase0:1206. `[8:16]` is not the archived pivot slice. -/
theorem shuffle_pivot_uses_take8_not_drop8 :
    shufflePivotRaw sampleTailHash [] 0 ≠
      shufflePivotRawDrop8 sampleTailHash [] 0 :=
  pivot_raw_ne_drop8

/-- phase0:1206. `[24:32]` is not the archived pivot slice. -/
theorem shuffle_pivot_uses_take8_not_tail :
    shufflePivotRaw sampleTailHash [] 0 ≠
      shufflePivotRawTail sampleTailHash [] 0 :=
  pivot_raw_ne_tail

/-- phase0:1206. The archived pivot is `raw % index_count`, not the raw
uint64. At `samplePivotHash` / count 1 the raw is 1 and `% 1` is 0. -/
theorem shuffle_pivot_uses_mod :
    shufflePivot samplePivotHash [] 0 1 ≠
      shufflePivotNoMod samplePivotHash [] 0 1 :=
  ProtocolSlotExtraction.shufflePivot_uses_mod

/-- phase0:1206. Omitting `% index_count` is not `< index_count`. -/
theorem shuffle_pivot_no_mod_not_lt :
    ¬ shufflePivotNoMod samplePivotHash [] 0 1 < 1 :=
  shufflePivotNoMod_not_lt

/-- phase0:1209. `shuffleFlip` already `% index_count`, so the no-mod
mutant agrees on the partner. The load-bearing fact is
`pivot < index_count`. -/
theorem shuffle_flip_ignores_pivot_mod :
    shuffleFlip (shufflePivotNoMod samplePivotHash [] 0 8) 8 3 =
      shuffleFlip (shufflePivot samplePivotHash [] 0 8) 8 3 :=
  shuffleFlip_no_mod_eq (by decide : 0 < 8)

/-- phase0:1206 / 1230. Lean `n % 0 = n` is not Python
`ZeroDivisionError`; the archived assert already rejects count 0. -/
theorem shuffle_empty_count_named_div0 :
    shufflePivot samplePivotHash [] 0 0 =
      shufflePivotRaw samplePivotHash [] 0 ∧
      ¬ ShuffledIndexOk 0 0 :=
  ProtocolSlotExtraction.shuffle_empty_count_named_div0 0

/-- phase0:1275. The maximal slot overflows `Uint64(genesis + slot*12)`
at genesis 0. A wrap-free mutant of `compute_time_at_slot` is false. -/
theorem timeFits_rejects_overflow : ¬ TimeFitsU64 z ⟨2 ^ 64 - 1, by decide⟩ :=
  timeFits_rejects_max_slot

/-- phase0:678. Mainnet `MIN_GENESIS_TIME` at slot 0 fits. -/
theorem timeFits_mainnet_genesis : TimeFitsU64 ⟨MIN_GENESIS_TIME, by decide⟩ z :=
  timeFits_min_genesis_zero

/-- phase0:1275. Under Fits the wrap is the Nat sum. -/
theorem time_wrap_eq_nat_when_fits :
    timeAtSlotWrap ⟨MIN_GENESIS_TIME, by decide⟩ z =
      timeAtSlotNat ⟨MIN_GENESIS_TIME, by decide⟩ z :=
  timeAtSlotWrap_eq_of_fits timeFits_min_genesis_zero

/-- phase0:678. Slot `2^60` at mainnet genesis still Fits. -/
theorem timeFits_slot_two_pow_60 :
    TimeFitsU64 ⟨MIN_GENESIS_TIME, by decide⟩ ⟨2 ^ 60, by decide⟩ :=
  timeFits_min_genesis_two_pow_60

/-- The sufficient `slot < 2^60` bound is not necessary. -/
theorem bounded_time_is_not_necessary :
    ¬ ∀ g s : U64, TimeFitsU64 g s → g.val ≤ MIN_GENESIS_TIME ∧ s.val < 2 ^ 60 :=
  timeFits_of_bounded_not_necessary

/-- phase0:1275. Slot `2^61` at mainnet genesis overflows. -/
theorem timeFits_rejects_two_pow_61 :
    ¬ TimeFitsU64 ⟨MIN_GENESIS_TIME, by decide⟩ ⟨2 ^ 61, by decide⟩ :=
  timeFits_rejects_min_genesis_two_pow_61

/-- That overflow wraps to `MIN + 2^63`, not the Nat sum. -/
theorem time_wrap_two_pow_61_is_min_plus_two_pow_63 :
    timeAtSlotWrap ⟨MIN_GENESIS_TIME, by decide⟩ ⟨2 ^ 61, by decide⟩ =
      MIN_GENESIS_TIME + 2 ^ 63 :=
  timeAtSlotWrap_min_genesis_two_pow_61

/-- Lean Nat sum is not the wrap. `TimeFitsU64` is this gap. -/
theorem time_nat_ne_wrap_two_pow_61 :
    timeAtSlotNat ⟨MIN_GENESIS_TIME, by decide⟩ ⟨2 ^ 61, by decide⟩ ≠
      timeAtSlotWrap ⟨MIN_GENESIS_TIME, by decide⟩ ⟨2 ^ 61, by decide⟩ :=
  timeAtSlotNat_ne_wrap_two_pow_61

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

/-- Gloas:1999. Empty parent with a nonempty `expected` list: items
drop the list; a mutant that always concatenated `expected` would not. -/
def emptyPending : Block := blockOfElectra one false [unit] [] [] []

def fullAtTwo : Block :=
  blockOfElectra ⟨2, by decide⟩ true [unit] [] [] []

def clockZero : Clock := { slot := z, header := z }
def clockOne : Clock := { slot := one, header := one }
def clockTwo : Clock := { slot := ⟨2, by decide⟩, header := ⟨2, by decide⟩ }

/-- Mutant that ignores Gloas:1999 and always concatenates `expected`. -/
def itemsAlwaysExpected (b : Block) : List Item := expected b

theorem emptyPending_expected : expected emptyPending = [unit] := by
  simp [expected, builderPending, builderSweep, emptyPending, blockOfElectra,
    queueStage, sweepStage, electraPartials, electraPartialLoop]

theorem emptyPending_items : items emptyPending = [] :=
  items_empty emptyPending rfl

theorem fullAtTwo_expected : expected fullAtTwo = [unit] := by
  simp [expected, builderPending, builderSweep, fullAtTwo, blockOfElectra,
    queueStage, sweepStage, electraPartials, electraPartialLoop]

theorem fullAtTwo_items : items fullAtTwo = [unit] := by
  have hp : fullAtTwo.parentFull = true := rfl
  simp [items, hp, fullAtTwo_expected]

/-- phase0:1762-1776. Singleton accepted slot 1 from clock 0. -/
theorem accepted_emptyPending :
    AcceptedBlocks clockZero [emptyPending] clockOne := by
  change Accepted clockZero [one] clockOne
  refine Accepted.cons ?_ (Accepted.nil clockOne)
  refine ⟨{ slot := one, header := z }, ⟨by decide, rfl, rfl⟩, ⟨rfl, by decide, rfl, rfl⟩⟩

theorem accepted_empty_then_full :
    AcceptedBlocks clockZero [emptyPending, fullAtTwo] clockTwo := by
  change Accepted clockZero [one, ⟨2, by decide⟩] clockTwo
  refine Accepted.cons
    (⟨{ slot := one, header := z }, ⟨by decide, rfl, rfl⟩,
      ⟨rfl, by decide, rfl, rfl⟩⟩ : StateTransition clockZero one clockOne)
    (Accepted.cons
      (⟨{ slot := ⟨2, by decide⟩, header := one }, ⟨by decide, rfl, rfl⟩,
        ⟨rfl, by decide, rfl, rfl⟩⟩ :
          StateTransition clockOne ⟨2, by decide⟩ clockTwo)
      (Accepted.nil clockTwo))

/-- Gloas:1999 kill-line: nonempty `expected` is dropped on an empty parent. -/
theorem empty_parent_drops_nonempty_expected :
    items emptyPending = [] ∧ expected emptyPending = [unit] :=
  ⟨emptyPending_items, emptyPending_expected⟩

/-- The always-`expected` mutant credits an empty parent. -/
theorem always_expected_mutant_credits_empty_parent :
    itemsAlwaysExpected emptyPending ≠ items emptyPending := by
  simp [itemsAlwaysExpected, emptyPending_expected, emptyPending_items]

/-- Accepted empty parent: exact count 0, uniqueness from the guards.
The consumer `16 * 2^64` bound is not load-bearing here. -/
theorem accepted_empty_parent_count_is_zero :
    AcceptedBlocks clockZero [emptyPending] clockOne ∧
      ([emptyPending].map (fun b => (items b).length)).sum = 0 ∧
      (expected emptyPending).length = 1 ∧
      (([emptyPending].map payload).map (·.slot)).Nodup := by
  refine ⟨accepted_emptyPending, ?_, ?_, ?_⟩
  · exact (accepted_empty_parents_zero accepted_emptyPending
      (by
        intro b hb
        have : b = emptyPending := List.mem_singleton.mp hb
        subst this
        rfl)).1
  · rw [emptyPending_expected]; rfl
  · exact (accepted_empty_parents_zero accepted_emptyPending
      (by
        intro b hb
        have : b = emptyPending := List.mem_singleton.mp hb
        subst this
        rfl)).2

/-- Mixed accepted sequence: empty parent contributes 0; summing
`expected.length` overcounts by one. -/
theorem accepted_mixed_count_ignores_empty :
    ([emptyPending, fullAtTwo].map (fun b => (items b).length)).sum =
      (items fullAtTwo).length ∧
    ([emptyPending, fullAtTwo].map (fun b => (expected b).length)).sum =
      (expected emptyPending).length + (expected fullAtTwo).length ∧
    (expected emptyPending).length = 1 ∧
    (items fullAtTwo).length = 1 := by
  have hi : items emptyPending = [] := emptyPending_items
  have he : expected emptyPending = [unit] := emptyPending_expected
  have hf : items fullAtTwo = [unit] := fullAtTwo_items
  have hex : expected fullAtTwo = [unit] := fullAtTwo_expected
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hi, hf]
  · simp [he, hex]
  · simp [he]
  · simp [hf]

/-- Always-`expected` overcounts an accepted empty-then-full pair. -/
theorem always_expected_overcounts_accepted :
    ([emptyPending, fullAtTwo].map
        (fun b => (itemsAlwaysExpected b).length)).sum =
      ([emptyPending, fullAtTwo].map
        (fun b => (items b).length)).sum + 1 := by
  simp [itemsAlwaysExpected, emptyPending_expected, emptyPending_items,
    fullAtTwo_expected, fullAtTwo_items]

/-- Empty accepted list is exactly 0. -/
theorem accepted_nil_count_is_zero :
    (([] : List Block).map (fun b => (items b).length)).sum = 0 ∧
      ((([] : List Block).map payload).map (·.slot)).Nodup :=
  let h := accepted_nil_zero (Accepted.nil clockZero)
  ⟨h.1, h.2.2⟩

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

/-- Lean `increaseBalance` (AccountMap.lean:42-44) never deletes.
Python `modify_state` 583-587 would delete an empty account; that
destroy is not `CreateEther`. -/
theorem create_ether_never_deletes
    {before after : AccountMap .EVM} {item : Item}
    (h : CreateEther before item after) :
    after.get? item.recipient ≠ none :=
  createEther_keeps_present h

/-- state_tracker.py:188-211 then 642. Missing + 0 Gwei satisfies
383/385. Line 384 `EMPTY_CODE_HASH` remains named. -/
theorem missing_zero_gwei_is_nonce_balance_empty
    {before after : AccountMap .EVM} {acc' : Account .EVM}
    (hacc : before.get? unit.recipient = none)
    (h : CreateEther before unit after)
    (hlook : after.get? unit.recipient = some acc') :
    AccountNonceBalanceEmpty acc' :=
  createEther_missing_zero_nonce_balance_empty hacc rfl h hlook

/-- state_tracker.py:642 identity. An already-empty existing account
stays nonce/balance empty after a zero increment. -/
theorem existing_empty_zero_stays_empty
    {before after : AccountMap .EVM} {acc acc' : Account .EVM}
    (hacc : before.get? unit.recipient = some acc)
    (hempty : AccountNonceBalanceEmpty acc)
    (h : CreateEther before unit after)
    (hlook : after.get? unit.recipient = some acc') :
    AccountNonceBalanceEmpty acc' :=
  createEther_existing_zero_keeps_empty hacc rfl hempty h hlook

/-- state_tracker.py:188-190. Lean `Account` default nonce/balance
are 0. Field identity with Python `EMPTY_ACCOUNT` (including
`EMPTY_CODE_HASH`) remains named. -/
theorem lean_default_is_nonce_balance_empty :
    AccountNonceBalanceEmpty (default : Account .EVM) :=
  default_nonce_balance_empty

def creditedUnit : CreditedWithdrawal where
  validatorIndex := 0
  item := unit

/-- Gloas:1924 and fork.py:1111-1118 walk the same list. A mutant that
dropped builder withdrawals from only one projection would disagree
on length. -/
theorem credited_projections_agree_on_count
    (ws : List CreditedWithdrawal) :
    (creditedPairs ws).length = (creditedItems ws).length :=
  credited_projection_count ws

/-- Empty joint walk is the identity on both CL balances and the EL
world. -/
theorem credited_empty_is_identity (s : DualBalances)
    (world : AccountMap .EVM)
    (h : CreditedRun s world [] s world) :
    applyTagged s (creditedPairs []) = s ∧
      ElCredit world [] world := by
  refine ⟨?_, ?_⟩
  · simpa using (creditedRun_cl h).symm
  · exact creditedRun_el h

/-- A singleton credited withdrawal is one `applyOneWithdrawal` and
one `create_ether`, not a free pair of unrelated lists. -/
theorem credited_singleton_is_one_write
    {s t : DualBalances} {before after : AccountMap .EVM}
    (h : CreditedRun s before [creditedUnit] t after) :
    t = applyOneWithdrawal s 0 0 ∧ CreateEther before unit after :=
  creditedRun_singleton h

/-- CL writes Gwei, EL credits Wei. A 1e18 mutant of the EL scale is
not `create_ether`. -/
theorem credited_el_scale_is_gwei_times_1e9 (w : CreditedWithdrawal) :
    w.item.amount.toNat = w.item.gwei.val * 10 ^ 9 :=
  credited_el_amount_is_wei w

/-- Capella:458 `+= 1`. Two identical credited entries still receive
distinct `Withdrawal.index` values. A mutant that reused
`validator_index` as `index` is not `stampIndex`. -/
theorem stamp_repeats_still_unique :
    ((archivedIndexed (stampIndex 0 [creditedUnit, creditedUnit])).map
        (·.index)).Nodup :=
  stampIndex_nodup 0 [creditedUnit, creditedUnit]

/-- Capella:452 keeps `validator_index` while assigning `index`. -/
theorem stamp_keeps_validator_index (start : Nat) (w : CreditedWithdrawal)
    (ws : List CreditedWithdrawal) :
    (stampIndex start (w :: ws)).head?.map (·.validatorIndex) =
      some w.validatorIndex := by
  simp [stampIndex]

/-- The Item projection of the stamped list is the credited list, not
a second payload. -/
theorem stamp_items_are_credited (start : Nat)
    (ws : List CreditedWithdrawal) :
    archivedItems (stampIndex start ws) = creditedItems ws :=
  stampIndex_items start ws

/-- Electra:1429-1449. An ineligible visit adds no withdrawal. -/
theorem ineligible_visit_is_skipped :
    creditEligible 16 0 [7, 8] [(unit, false)] = [] := by
  simp [creditEligible]

/-- Electra:1432. An eligible visit keeps the ring index, not a free
index. Start 1 on a 4-validator registry is index 1, not 0. -/
theorem eligible_visit_keeps_ring_index :
    (creditEligible 16 0 (visitRing 4 1 4) [(oneGwei, true)]).map
        (fun w => w.validatorIndex) = [1] := by
  simp [creditEligible, visitRing, nextValidatorIndex]

/-- The Item projection is `sweepStage`, so dropping an eligible
visit from only one side disagrees. -/
theorem credit_items_are_sweep :
    creditedItems (creditEligible 16 0 [0, 1]
        [(oneGwei, true), (unit, false)]) =
      sweepStage 16 0 [(oneGwei, true), (unit, false)] :=
  creditEligible_items 16 0 [0, 1] _ (by decide)

/-- Electra:1421-1451. Credited validator indices on the visit ring
are Nodup. -/
theorem electra_credits_are_nodup :
    ((electraCreditEligible 4 1 0
        [(oneGwei, true), (unit, true)]).map
        (fun w => w.validatorIndex)).Nodup :=
  electraCreditEligible_nodup ⟨by decide, by decide⟩

/-- A visit key below the builder flag is a validator write, not a
builder write. -/
theorem visit_below_flag_is_not_builder :
    isBuilderIndex 3 = false :=
  isBuilderIndex_of_lt (by decide : (3 : Nat) < BUILDER_INDEX_FLAG)

/-- A full-parent Electra block with empty first three Gloas lists
mints the credited sweep items, not an unconstrained payload. -/
theorem electra_block_items_are_credited :
    items (blockOfElectra one true [] [] [] [(oneGwei, true)]) =
      creditedItems (electraCreditEligible 4 1 0 [(oneGwei, true)]) :=
  items_of_electra_validator_block one 4 1 [(oneGwei, true)] (by decide)

def two : U64 := ⟨2, by decide⟩
def three : U64 := ⟨3, by decide⟩
def twoGwei : Item := { recipient := default, gwei := two }
def threeGwei : Item := { recipient := default, gwei := three }

/-- Gloas:1805-1833 / 1879-1888. A nonempty builder-pending entry is
the first credited item. Putting the validator sweep first is not
`get_expected_withdrawals`. -/
theorem gloas_queue_heads_items :
    (items (blockOfElectra one true [oneGwei] [] [] [])).head? =
      some oneGwei := by
  simp [items, expected, builderPending, builderSweep, blockOfElectra,
    queueStage, electraPartials, electraPartialLoop, sweepStage]

/-- Gloas:1879-1916 order: pending, then partial, then builder sweep,
then validators. A permutation is not the archived concatenation. -/
theorem gloas_four_stage_order :
    items (blockOfElectra one true [oneGwei]
        [{ item := unit, mature := true, eligible := true }]
        [(twoGwei, true)] [(threeGwei, true)]) =
      [oneGwei, unit, twoGwei, threeGwei] := by
  simp [items, expected, builderPending, builderSweep, blockOfElectra,
    queueStage, electraPartials, electraPartialLoop, electraPartialsLimit,
    MAX_PENDING_PARTIALS, MAX_WITHDRAWALS_PER_PAYLOAD, sweepStage]

/-- The four-stage Item list is the `gloasCredited` projection, not a
second payload. Visit keys stay off `Block`. -/
theorem gloas_four_stage_items_are_credited :
    let pending : List CreditedWithdrawal :=
      [{ validatorIndex := 1, item := oneGwei }]
    let partials : List CreditedPartial :=
      [{ w := { validatorIndex := 2, item := unit }, mature := true,
          eligible := true }]
    let builders : List (CreditedWithdrawal × Bool) :=
      [({ validatorIndex := 3, item := twoGwei }, true)]
    items (blockOfElectra one true (creditedItems pending)
        (partials.map asElectraPartial)
        (builders.map (fun p => (p.1.item, p.2)))
        [(threeGwei, true)]) =
      creditedItems (gloasCredited pending partials builders 4 0
        [(threeGwei, true)]) :=
  items_of_gloas_credited one
    [{ validatorIndex := 1, item := oneGwei }]
    [{ w := { validatorIndex := 2, item := unit }, mature := true,
        eligible := true }]
    [({ validatorIndex := 3, item := twoGwei }, true)]
    4 0 [(threeGwei, true)] (by decide)

/-- Capella:458. Stamping a four-stage Gloas payload assigns successor
indices; a restart-at-zero mutant of the second item is not `indexSeq`. -/
theorem gloas_stamp_indices_are_successors :
    ((archivedIndexed (stampIndex 0
        (gloasCredited
          [{ validatorIndex := 1, item := oneGwei }]
          [{ w := { validatorIndex := 2, item := unit }, mature := true,
              eligible := true }]
          [({ validatorIndex := 3, item := twoGwei }, true)]
          4 0 [(threeGwei, true)]))).map (·.index)) =
      [0, 1, 2, 3] := by
  rw [stampIndex_indices]
  decide

/-- Capella:452 keeps `validator_index` of the builder-pending entry. -/
theorem gloas_stamp_keeps_queue_validator :
    ((stampIndex 5 (gloasCredited
        [{ validatorIndex := 7, item := oneGwei }] [] [] 1 0 [])).map
        (·.validatorIndex)).head? = some 7 := by
  simp [gloasCredited, creditQueueStage, creditPartials, creditPartialLoop,
    creditSweepStage, electraCreditEligible, creditEligible, stampIndex]

/-- The indexed walk of a full-parent Gloas block is that stamp, not a
second payload. -/
theorem gloas_chain_is_stamped :
    indexedChain 0 [gloasBlock one
        [{ validatorIndex := 1, item := oneGwei }] [] [] []] =
      archivedIndexed (stampIndex 0
        (gloasCredited
          [{ validatorIndex := 1, item := oneGwei }] [] [] 1 0 [])) :=
  indexedChain_of_gloas_block 0 one
    [{ validatorIndex := 1, item := oneGwei }] [] [] 1 0 [] (by decide)

/-- Capella:510. The second payload continues the cursor; it does not
restart at 0. -/
theorem gloas_second_payload_continues_index :
    ((archivedIndexed (stampedChain 0
        [gloasCredited [{ validatorIndex := 1, item := oneGwei }] [] [] 1 0 [],
          gloasCredited [{ validatorIndex := 2, item := twoGwei }] [] [] 1
            0 []])).map (·.index)) =
      [0, 1] := by
  rw [stampedChain_indices]
  decide

/-- Gloas:1127-1128. Builder 3 is stored as `3 | 2^40`, not as 3. -/
theorem builder_pending_uses_flagged_index :
    (asQueueCredited { builderIndex := 3, item := oneGwei }).validatorIndex =
      toValidatorIndex 3 ∧
      isBuilderIndex (toValidatorIndex 3) = true ∧
      isBuilderIndex 3 = false := by
  refine ⟨rfl, toValidatorIndex_is_builder 3, ?_⟩
  exact isBuilderIndex_of_lt (by decide : (3 : Nat) < BUILDER_INDEX_FLAG)

/-- Gloas:1134-1135. A flag-clear builder index survives convert and
convert-back. Leaving bit 40 set is not `BuilderIndexFits`. -/
theorem flagged_builder_index_recovers :
    toBuilderIndex (toValidatorIndex 3) = 3 :=
  toBuilderIndex_toValidatorIndex_of_lt (by decide : (3 : Nat) < BUILDER_INDEX_FLAG)

/-- Gloas:1926-1927. A builder-pending credit writes builders, not
validator balances. -/
theorem builder_queue_keeps_validator_balances (s : DualBalances) :
    (applyTagged s (creditedPairs (creditBuilderQueue
        [{ builderIndex := 3, item := oneGwei }]))).validators =
      s.validators :=
  creditBuilderQueue_keeps_validators s _

/-- Electra:1388. A pending-partial below the flag is a validator
write, not a builder write. -/
theorem partial_below_flag_is_not_builder :
    isBuilderIndex
      ({ w := { validatorIndex := 3, item := unit }, mature := true,
          eligible := true } : CreditedPartial).w.validatorIndex = false :=
  isBuilderIndex_of_lt (by decide : (3 : Nat) < BUILDER_INDEX_FLAG)

/-- The Item list of a full-parent block built from archived
builder_index fields is `gloasFromBuilders`, not a second payload. -/
theorem gloas_from_builders_items_are_credited :
    items (blockOfElectra one true [oneGwei] [] [] []) =
      creditedItems (gloasFromBuilders
        [{ builderIndex := 3, item := oneGwei }] [] [] 1 0 []) :=
  items_of_gloasFromBuilders one
    [{ builderIndex := 3, item := oneGwei }] [] [] 1 0 [] (by decide)

/-- Gloas:1924. Concatenating two write lists is sequential application,
not a restarted fold. -/
theorem apply_tagged_concat_is_sequential (s : DualBalances) :
    applyTagged s [(3, 1), (toValidatorIndex 0, 2)] =
      applyTagged (applyTagged s [(3, 1)]) [(toValidatorIndex 0, 2)] :=
  applyTagged_append s [(3, 1)] [(toValidatorIndex 0, 2)]

def mixedQueue : List BuilderPending :=
  [{ builderIndex := 3, item := oneGwei }]

def mixedPartials : List CreditedPartial :=
  [{ w := { validatorIndex := 1, item := oneGwei },
      mature := true, eligible := true }]

def mixedSweeps : List BuilderSweepVisit :=
  [{ builderIndex := 5, item := twoGwei, eligible := true }]

theorem mixed_partials_below_flag :
    ∀ c ∈ mixedPartials, c.w.validatorIndex < BUILDER_INDEX_FLAG := by
  intro c hc
  simp [mixedPartials] at hc
  subst hc
  decide

theorem mixed_sweep_start : SweepStart 1 0 :=
  ⟨Nat.succ_pos 0, Nat.zero_lt_one⟩

/-- Gloas:1879-1916 / 1926-1927. A mixed payload writes `balances` only
from the validator stages. Builder queue and sweep are not a second
validator list. -/
theorem mixed_gloas_validators_are_partials_only (s : DualBalances) :
    (applyTagged s (creditedPairs
        (gloasFromBuilders mixedQueue mixedPartials mixedSweeps 1 0 []))).validators =
      (applyTagged s (creditedPairs (creditPartials 1 mixedPartials))).validators := by
  have hv := gloasFromBuilders_applyTagged_validators s
    mixedQueue mixedPartials mixedSweeps 1 0 []
    mixed_partials_below_flag mixed_sweep_start (by decide)
  have hq : (creditBuilderQueue mixedQueue).length = 1 := by
    simp [mixedQueue, creditBuilderQueue, creditQueueStage, asQueueCredited]
  have hp : (creditPartials 1 mixedPartials).length = 1 := by
    simp [mixedPartials, creditPartials, creditPartialLoop, electraPartialsLimit,
      MAX_PENDING_PARTIALS, MAX_WITHDRAWALS_PER_PAYLOAD]
  have hs : (creditBuilderSweep 2 mixedSweeps).length = 1 := by
    simp [mixedSweeps, creditBuilderSweep, creditSweepStage, asSweepCredited]
  have hel : electraCreditEligible 1 0 3 ([] : List (Item × Bool)) = [] :=
    creditEligible_nil_flagged _ _ _
  simp [hq, hp, hs, hel] at hv
  exact hv

/-- Gloas:1879-1916 / 1926-1927. A mixed payload writes `builders` only
from the builder stages. Partials are not a second builder list. -/
theorem mixed_gloas_builders_are_queue_and_sweep (s : DualBalances) :
    (applyTagged s (creditedPairs
        (gloasFromBuilders mixedQueue mixedPartials mixedSweeps 1 0 []))).builders =
      (applyTagged
        (applyTagged s (creditedPairs (creditBuilderQueue mixedQueue)))
        (creditedPairs (creditBuilderSweep 2 mixedSweeps))).builders := by
  have hb := gloasFromBuilders_applyTagged_builders s
    mixedQueue mixedPartials mixedSweeps 1 0 []
    mixed_partials_below_flag mixed_sweep_start (by decide)
  have hq : (creditBuilderQueue mixedQueue).length = 1 := by
    simp [mixedQueue, creditBuilderQueue, creditQueueStage, asQueueCredited]
  have hp : (creditPartials 1 mixedPartials).length = 1 := by
    simp [mixedPartials, creditPartials, creditPartialLoop, electraPartialsLimit,
      MAX_PENDING_PARTIALS, MAX_WITHDRAWALS_PER_PAYLOAD]
  simp [hq, hp] at hb
  exact hb

/-- Gloas:1940 then 1999. A full `gloasFromBuilders` parent assigns the
credited list; the empty parent remints that list, it does not assign
a successor payload. -/
theorem remint_gloas_from_builders_repeats_items :
    mintedItemLists []
        [gloasFromBuildersBlock one mixedQueue mixedPartials mixedSweeps [],
          emptyParent] =
      [creditedItems (gloasFromBuilders mixedQueue mixedPartials mixedSweeps
          1 0 []),
        creditedItems (gloasFromBuilders mixedQueue mixedPartials mixedSweeps
          1 0 [])] :=
  mintedItemLists_gloas_then_empty one mixedQueue mixedPartials mixedSweeps
    1 0 [] (by decide) (e := emptyParent) rfl

/-- Gloas:1999. Both reminted copies keep `Withdrawal.index` 0, they
do not continue at 1. -/
theorem remint_gloas_from_builders_repeats_index_zero :
    (indexedCachedFrom 0 []
        [gloasFromBuildersBlock one mixedQueue mixedPartials mixedSweeps [],
          emptyParent]).map (fun ws => ws.map (fun w => w.index)) =
      [[0, 1, 2], [0, 1, 2]] := by
  have h := remint_repeats_gloasFromBuilders_indices 0 one
    mixedQueue mixedPartials mixedSweeps 1 0 [] (by decide)
    (e := emptyParent) rfl
  have hlen :
      (creditedItems (gloasFromBuilders mixedQueue mixedPartials mixedSweeps
          1 0 [])).length = 3 := by
    simp [mixedQueue, mixedPartials, mixedSweeps, gloasFromBuilders,
      gloasCredited, creditQueueStage, creditPartials, creditPartialLoop,
      electraPartialsLimit, MAX_PENDING_PARTIALS, MAX_WITHDRAWALS_PER_PAYLOAD,
      creditSweepStage, electraCreditEligible, creditedItems,
      asQueueCredited, asSweepCredited, creditEligible_nil_flagged]
  simpa [hlen, indexSeq] using h

/-- Computed `indexedChain` drops the empty parent. Remint uniqueness
is not this chain. -/
theorem remint_gloas_chain_is_not_doubled :
    indexedChain 0
        [gloasFromBuildersBlock one mixedQueue mixedPartials mixedSweeps [],
          emptyParent] =
      indexedWithdrawals 0
        (creditedItems (gloasFromBuilders mixedQueue mixedPartials mixedSweeps
          1 0 [])) :=
  indexedChain_gloas_then_empty 0 one mixedQueue mixedPartials mixedSweeps
    1 0 [] (by decide) (e := emptyParent) rfl

/-- Envelope remint count is 3+3. The computed chain length is 3. -/
theorem remint_gloas_count_is_two_copies :
    ((indexedCachedFrom 0 []
        [gloasFromBuildersBlock one mixedQueue mixedPartials mixedSweeps [],
          emptyParent]).map List.length).sum = 6 ∧
      (indexedChain 0
        [gloasFromBuildersBlock one mixedQueue mixedPartials mixedSweeps [],
          emptyParent]).length = 3 := by
  have hlen :
      (creditedItems (gloasFromBuilders mixedQueue mixedPartials mixedSweeps
          1 0 [])).length = 3 := by
    simp [mixedQueue, mixedPartials, mixedSweeps, gloasFromBuilders,
      gloasCredited, creditQueueStage, creditPartials, creditPartialLoop,
      electraPartialsLimit, MAX_PENDING_PARTIALS, MAX_WITHDRAWALS_PER_PAYLOAD,
      creditSweepStage, electraCreditEligible, creditedItems,
      asQueueCredited, asSweepCredited, creditEligible_nil_flagged]
  refine ⟨?_, ?_⟩
  · have h := remint_count_gloasFromBuilders 0 one
      mixedQueue mixedPartials mixedSweeps 1 0 [] (by decide)
      (e := emptyParent) rfl
    rw [h, hlen]
  · have hc := remint_gloas_chain_is_not_doubled
    rw [hc, ← List.length_map (fun w : IndexedWithdrawal => w.item),
      indexedWithdrawals_items, hlen]

/-- Gloas:1999. The retained-cache flatten consumed by
`ProtocolWithdrawalCount` is two credited copies, not the computed
`items` projection (empty parent contributes []). -/
theorem remint_gloas_cached_flat_is_two_copies :
    (cachedPayloads
        [gloasFromBuildersBlock one mixedQueue mixedPartials mixedSweeps [],
          emptyParent]).flatMap (fun p => p.items) =
      creditedItems (gloasFromBuilders mixedQueue mixedPartials mixedSweeps
          1 0 [] ++
        gloasFromBuilders mixedQueue mixedPartials mixedSweeps 1 0 []) :=
  cached_flat_gloas_then_empty one mixedQueue mixedPartials mixedSweeps
    1 0 [] (by decide) (e := emptyParent) rfl

/-- Envelope `totalItems` is 6. Computed `items` of the pair sum to 3. -/
theorem remint_gloas_total_items_is_six :
    totalItems (cachedPayloads
        [gloasFromBuildersBlock one mixedQueue mixedPartials mixedSweeps [],
          emptyParent]) = 6 ∧
      (([gloasFromBuildersBlock one mixedQueue mixedPartials mixedSweeps [],
          emptyParent].map (fun b => (items b).length)).sum) = 3 := by
  refine ⟨?_, ?_⟩
  · have h := totalItems_gloas_then_empty one mixedQueue mixedPartials
      mixedSweeps 1 0 [] (by decide) (e := emptyParent) rfl
    have hlen :
        (creditedItems (gloasFromBuilders mixedQueue mixedPartials mixedSweeps
            1 0 [])).length = 3 := by
      simp [mixedQueue, mixedPartials, mixedSweeps, gloasFromBuilders,
        gloasCredited, creditQueueStage, creditPartials, creditPartialLoop,
        electraPartialsLimit, MAX_PENDING_PARTIALS, MAX_WITHDRAWALS_PER_PAYLOAD,
        creditSweepStage, electraCreditEligible, creditedItems,
        asQueueCredited, asSweepCredited, creditEligible_nil_flagged]
    rw [h, hlen]
  · have hi := items_of_gloasFromBuildersBlock one mixedQueue mixedPartials
      mixedSweeps 1 0 [] (by decide)
    have he := items_empty emptyParent rfl
    have hlen :
        (creditedItems (gloasFromBuilders mixedQueue mixedPartials mixedSweeps
            1 0 [])).length = 3 := by
      simp [mixedQueue, mixedPartials, mixedSweeps, gloasFromBuilders,
        gloasCredited, creditQueueStage, creditPartials, creditPartialLoop,
        electraPartialsLimit, MAX_PENDING_PARTIALS, MAX_WITHDRAWALS_PER_PAYLOAD,
        creditSweepStage, electraCreditEligible, creditedItems,
        asQueueCredited, asSweepCredited, creditEligible_nil_flagged]
    simp [hi, he, hlen]

/-- fork-choice.md:688 / Gloas:1940. The listed envelope of a full
`gloasFromBuilders` parent is the credited list, not a second payload. -/
theorem remint_full_envelope_lists_credited :
    VerifiedEnvelope
      (gloasFromBuildersBlock one mixedQueue mixedPartials mixedSweeps []) []
      (creditedItems (gloasFromBuilders mixedQueue mixedPartials mixedSweeps
        1 0 [])) :=
  verifiedEnvelope_gloasFromBuildersBlock one mixedQueue mixedPartials
    mixedSweeps 1 0 [] (by decide)

/-- fork-choice.md:688 / Gloas:1999. An empty parent lists the retained
cache. -/
theorem remint_empty_envelope_lists_cache :
    VerifiedEnvelope emptyParent
      (creditedItems (gloasFromBuilders mixedQueue mixedPartials mixedSweeps
        1 0 []))
      (creditedItems (gloasFromBuilders mixedQueue mixedPartials mixedSweeps
        1 0 [])) :=
  verifiedEnvelope_empty_remint _ rfl

/-- Computed `items` flatten is one copy; remint flatten is two. -/
theorem computed_gloas_flat_is_one_copy :
    List.flatMap items
        [gloasFromBuildersBlock one mixedQueue mixedPartials mixedSweeps [],
          emptyParent] =
      creditedItems (gloasFromBuilders mixedQueue mixedPartials mixedSweeps
        1 0 []) :=
  computed_flat_gloas_then_empty one mixedQueue mixedPartials mixedSweeps
    1 0 [] (by decide) (e := emptyParent) rfl

/-- Gloas:1999 does not take the double CL fold. `applyTagged` of
`g ++ g` is sequential application of `g` twice. -/
theorem apply_tagged_double_is_sequential (s : DualBalances) :
    applyTagged s (creditedPairs
        (gloasFromBuilders mixedQueue mixedPartials mixedSweeps 1 0 [] ++
          gloasFromBuilders mixedQueue mixedPartials mixedSweeps 1 0 [])) =
      applyTagged
        (applyTagged s (creditedPairs
          (gloasFromBuilders mixedQueue mixedPartials mixedSweeps 1 0 [])))
        (creditedPairs
          (gloasFromBuilders mixedQueue mixedPartials mixedSweeps 1 0 [])) :=
  applyTagged_credited_append s _ _

/-- fork.py:840 / 1111-1118. Two empty `create_ether` loops still
construct the remint `EnvelopeCredits`; Gloas:1999 does not skip the
second envelope pass. -/
theorem empty_gloas_remint_from_nils (world : AccountMap .EVM) :
    EnvelopeCredits world []
      [gloasFromBuildersBlock one [] [] [] [], emptyParent] world :=
  envelopeCredits_gloas_then_empty_of_elCredit one [] [] [] 1 0 []
    (by decide) (e := emptyParent) rfl
    (ElCredit.nil world) (ElCredit.nil world)

/-- Those two passes are `ElCredit` of the (empty) credited list. -/
theorem empty_gloas_remint_el_twice (world : AccountMap .EVM) :
    ∃ mid,
      ElCredit world
        (creditedItems (gloasFromBuilders [] [] [] 1 0 [])) mid ∧
      ElCredit mid
        (creditedItems (gloasFromBuilders [] [] [] 1 0 [])) world :=
  remint_elCredit_twice (by decide) (e := emptyParent) rfl
    (empty_gloas_remint_from_nils world)

/-- Gloas:1927. Builder 3 writes `builders[3]`, not an OOB slot. -/
theorem flagged_builder_is_in_range :
    IndexInRange 8 8 (toValidatorIndex 3) :=
  indexInRange_toValidatorIndex
    (by decide : (3 : Nat) < BUILDER_INDEX_FLAG)
    (by decide : (3 : Nat) < 8)

/-- Electra:1388. Validator 3 writes `balances[3]` when the registry
has length 8. -/
theorem validator_below_flag_is_in_range :
    IndexInRange 8 8 3 :=
  (indexInRange_validator (nv := 8) (nb := 8) (v := 3)
    (isBuilderIndex_of_lt (by decide : (3 : Nat) < BUILDER_INDEX_FLAG))).mpr
    (by decide)

/-- Gloas:1931. An in-range validator write does not touch
`balances[10]` when `len(validators) = 8`. -/
theorem apply_tagged_keeps_validator_past_len (s : DualBalances) :
    (applyTagged s [(3, 1)]).validators 10 = s.validators 10 :=
  applyTagged_keeps_validator_oob s [(3, 1)] 8 8 10
    (by
      intro p hp
      have : p = (3, 1) := List.mem_singleton.mp hp
      subst this
      exact validator_below_flag_is_in_range)
    (by decide)

/-- Gloas:1927. A mixed `gloasFromBuilders` payload does not write
`builders[10]` when every archived `builder_index` is `< 8`. -/
theorem mixed_gloas_keeps_builder_past_len (s : DualBalances) :
    (applyTagged s (creditedPairs
        (gloasFromBuilders mixedQueue mixedPartials mixedSweeps 1 0 []))).builders
      10 =
      s.builders 10 :=
  applyTagged_gloasFromBuilders_keeps_builder_oob
    (nv := 8) (nb := 8) (j := 10) s
    (by
      intro p hp
      simp [mixedQueue] at hp
      subst hp
      exact ⟨by decide, by decide⟩)
    (by
      intro c hc
      simp [mixedPartials] at hc
      subst hc
      exact ⟨by decide, by decide⟩)
    (by
      intro p hp
      simp [mixedSweeps] at hp
      subst hp
      exact ⟨by decide, by decide⟩)
    mixed_sweep_start (by decide) (by decide) (by decide)

/-- Electra:1451 / Gloas:1033. `n = 2^40+1` starting at the flag
visits a builder index. `visitRing_not_builder` needs `n ≤ 2^40`. -/
theorem large_registry_visit_is_builder :
    ∃ i ∈ visitRing (BUILDER_INDEX_FLAG + 1) BUILDER_INDEX_FLAG 1,
      isBuilderIndex i = true :=
  visitRing_exists_builder (Nat.lt_succ_self _) Nat.zero_lt_one

/-- Electra:1426-1449. That visit credits `validator_index = 2^40`. -/
theorem large_registry_electra_credits_flag :
    electraCreditEligible (BUILDER_INDEX_FLAG + 1) BUILDER_INDEX_FLAG 0
      [(oneGwei, true)] =
      [{ validatorIndex := BUILDER_INDEX_FLAG, item := oneGwei }] :=
  electraCreditEligible_gt_flag_credits_flag oneGwei

/-- Gloas:1926-1927. The same payload writes `builders[0]`, not a
validator slot. Dropping `hnflag` is this write. -/
theorem large_registry_electra_writes_builder_zero :
    (applyTagged sampleBalances (creditedPairs
        (electraCreditEligible (BUILDER_INDEX_FLAG + 1) BUILDER_INDEX_FLAG 0
          [(oneGwei, true)]))).builders 0 =
      99 := by
  have h := applyTagged_electra_gt_flag_writes_builder_zero sampleBalances oneGwei
  simp [sampleBalances, oneGwei, one] at h
  exact h

/-- The `n ≤ 2^40` conjunct of `electraCreditEligible_pairs_not_builder`
is refuted on this payload. -/
theorem hnflag_drop_refuted :
    ¬ (∀ p ∈ creditedPairs
          (electraCreditEligible (BUILDER_INDEX_FLAG + 1) BUILDER_INDEX_FLAG 0
            [(oneGwei, true)]),
        isBuilderIndex p.1 = false) :=
  electraCreditEligible_gt_flag_not_all_validators oneGwei

/-- Electra:1451. Lean `(i+1) % 0 = i+1`; Python raises. -/
theorem empty_registry_next_is_plus_one :
    nextValidatorIndex 0 7 = 8 :=
  nextValidatorIndex_of_zero 7

/-- Electra:1427/1451. `SweepStart 0 start` is uninhabited. -/
theorem empty_registry_not_sweep_start :
    ¬ SweepStart 0 0 :=
  sweepStart_of_zero

/-- The empty-registry walk with fuel 1 is `[0]`, not a ring of
length 0. `visitRing_lt` needs `SweepStart`. -/
theorem empty_registry_visit_unbounded :
    0 ∈ visitRing 0 0 1 ∧ ¬ 0 < 0 :=
  ⟨visitRing_start_mem 0 0 1 Nat.zero_lt_one, Nat.not_lt_zero 0⟩

/-- Dropping `SweepStart.registry` from `visitRing_lt` is this
counterexample. -/
theorem visit_ring_lt_needs_nonempty :
    ¬ (∀ n start fuel i, i ∈ visitRing n start fuel → i < n) :=
  visitRing_lt_needs_registry

/-- Electra:1413. Archived fuel `min(0, 16384) = 0` credits nothing. -/
theorem empty_registry_electra_is_nil :
    electraCreditEligible 0 0 0 [(oneGwei, true)] = [] :=
  electraCreditEligible_empty_registry 0 0 _

/-- Capella:411-421. Python Gwei 5 − 7 wraps to `2^64-2`. -/
theorem wrap_five_seven_is_u64_borrow :
    gweiWrapSub 5 7 = 2 ^ 64 - 2 :=
  gweiWrapSub_five_seven

/-- phase0:1610-1613. Lean saturate of that pair is 0, not the wrap. -/
theorem saturate_ne_wrap_on_excess :
    decreaseBalance 5 7 ≠ gweiWrapSub 5 7 :=
  decreaseBalance_ne_gweiWrap (by decide) (by decide) (by decide)

/-- Capella:411-421 vs 498-500. Lean fold equals sum-then-sub even
on excess; `BalanceAfterFits` is not this identity. -/
theorem apply_excess_equals_sat_sum :
    applyWithdrawals (fun _ => 5) [(0, 7)] 0 =
      balanceAfterWithdrawals 5 0 [(0, 7)] :=
  apply_eq_balanceAfter_sat (fun _ => 5) [(0, 7)] 0

/-- Dropping `BalanceAfterFits` from wrap agreement is this pair. -/
theorem fits_needed_for_wrap_agreement :
    applyWithdrawals (fun _ => 5) [(0, 7)] 0 ≠ gweiWrapSub 5 7 :=
  apply_ne_wrap_of_gt (b := fun _ => 5) (idx := 0) (amt := 7)
    (by decide) (by decide) (by decide)

/-- Under `BalanceAfterFits` the same read is the wrap. -/
theorem fits_agrees_with_wrap :
    balanceAfterWithdrawals 32 0 [(0, 32)] = gweiWrapSub 32 32 :=
  balanceAfter_eq_wrap_of_fits (by decide) ⟨by decide⟩

/-- Capella:506-510. After index `2^64-1` Lean next is `2^64`. -/
theorem next_index_after_max_is_two_pow :
    updateNextWithdrawalIndex (2 ^ 64 - 1) (indexSeq (2 ^ 64 - 1) 1) =
      2 ^ 64 :=
  updateNext_last_u64_is_two_pow

/-- phase0:473. That successor wraps to 0 as `WithdrawalIndex`. -/
theorem wrap_of_two_pow_is_zero :
    withdrawalIndexWrap (2 ^ 64) = 0 :=
  withdrawalIndexWrap_two_pow

/-- Lean cursor is not the wrap. `WithdrawalIndexFits` is this gap. -/
theorem last_u64_cursor_ne_wrap :
    updateNextWithdrawalIndex (2 ^ 64 - 1) (indexSeq (2 ^ 64 - 1) 1) ≠
      withdrawalIndexWrap (2 ^ 64) :=
  updateNext_last_u64_ne_wrap

/-- Lean assigns `2^64` as a second index; the wrap list is
`[2^64-1, 0]`. Nat Nodup is not that list. -/
theorem last_u64_pair_ne_wrap :
    indexSeq (2 ^ 64 - 1) 2 ≠
      (indexSeq (2 ^ 64 - 1) 2).map withdrawalIndexWrap :=
  indexSeq_last_u64_ne_wrap_list

/-- `start + 2 ≥ 2^64` is not `WithdrawalIndexFits`. -/
theorem fits_rejects_overflow_pair :
    ¬ WithdrawalIndexFits (2 ^ 64 - 1) 2 :=
  withdrawalIndexFits_rejects_last_u64_two

/-- Under Fits the cursor is the wrap. -/
theorem fits_cursor_is_wrap :
    updateNextWithdrawalIndex 4 (indexSeq 4 2) = withdrawalIndexWrap 6 :=
  updateNext_eq_wrap_of_fits (by decide) ⟨by decide⟩

/-- Gloas:1127-1128. `FLAG | FLAG` is `FLAG`, not `2^41`. -/
theorem flag_or_flag_is_not_add :
    toValidatorIndex BUILDER_INDEX_FLAG ≠
      BUILDER_INDEX_FLAG + BUILDER_INDEX_FLAG :=
  toValidatorIndex_flag_ne_add

/-- Convert-and-back of the flag is 0, not the flag. -/
theorem flag_convert_back_is_zero :
    toBuilderIndex (toValidatorIndex BUILDER_INDEX_FLAG) = 0 :=
  toBuilderIndex_toValidatorIndex_flag

/-- Lean `2^64 | 2^40` is not Python `Uint64 |`. -/
theorem two_pow_or_flag_ne_u64 :
    toValidatorIndex (2 ^ 64) ≠ toValidatorIndexU64 (2 ^ 64) :=
  toValidatorIndex_two_pow_ne_u64

/-- Python wrap of that pair is `2^40`. -/
theorem two_pow_u64_or_is_flag :
    toValidatorIndexU64 (2 ^ 64) = BUILDER_INDEX_FLAG :=
  toValidatorIndexU64_two_pow

/-- `BuilderIndexFits` rejects a bit-40 index and a `≥ 2^64` index. -/
theorem builder_fits_rejects_flag_and_overflow :
    ¬ BuilderIndexFits BUILDER_INDEX_FLAG ∧ ¬ BuilderIndexFits (2 ^ 64) :=
  ⟨builderIndexFits_flag, builderIndexFits_two_pow⟩

/-- Under a `Uint64` clear index the two conversions agree. -/
theorem small_builder_or_agrees_u64 :
    toValidatorIndex 3 = toValidatorIndexU64 3 :=
  toValidatorIndex_eq_u64_of_lt (by decide)

/-- Gloas:1134-1135. Python `~FLAG` clears bit 40 on the 64-bit mask. -/
theorem flag_u64_not_clears_bit_40 :
    builderFlagNotU64.testBit 40 = false :=
  builderFlagNotU64_testBit_40

/-- Lean `2^64 - (2^64 &&& FLAG)` is not Python `Uint64 & ~FLAG`. -/
theorem two_pow_and_not_ne_u64 :
    toBuilderIndex (2 ^ 64) ≠ toBuilderIndexU64 (2 ^ 64) :=
  toBuilderIndex_two_pow_ne_u64

/-- Python wrap of that pair is 0. -/
theorem two_pow_u64_and_not_is_zero :
    toBuilderIndexU64 (2 ^ 64) = 0 :=
  toBuilderIndexU64_two_pow

/-- Under a `Uint64` index the two conversions agree, including FLAG. -/
theorem small_validator_and_agrees_u64 :
    toBuilderIndex 3 = toBuilderIndexU64 3 ∧
      toBuilderIndex BUILDER_INDEX_FLAG = toBuilderIndexU64 BUILDER_INDEX_FLAG :=
  ⟨toBuilderIndex_three_eq_u64, toBuilderIndex_flag_eq_u64⟩

/-- Set bit 40 is XOR-clear, not `FLAG + FLAG`. -/
theorem flag_xor_flag_is_sub :
    BUILDER_INDEX_FLAG ^^^ BUILDER_INDEX_FLAG =
      BUILDER_INDEX_FLAG - BUILDER_INDEX_FLAG :=
  xor_flag_eq_sub_of_flag_bit (by decide)

/-- A tagged-plus-offset index agrees with Python `& ~FLAG`. -/
theorem flag_plus_three_and_agrees_u64 :
    toBuilderIndex (BUILDER_INDEX_FLAG + 3) =
      toBuilderIndexU64 (BUILDER_INDEX_FLAG + 3) :=
  toBuilderIndex_eq_u64_of_lt (by
    unfold BUILDER_INDEX_FLAG
    decide)

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
#print axioms create_ether_never_deletes
#print axioms missing_zero_gwei_is_nonce_balance_empty
#print axioms existing_empty_zero_stays_empty
#print axioms lean_default_is_nonce_balance_empty
#print axioms credited_projections_agree_on_count
#print axioms credited_empty_is_identity
#print axioms credited_singleton_is_one_write
#print axioms credited_el_scale_is_gwei_times_1e9
#print axioms stamp_repeats_still_unique
#print axioms stamp_keeps_validator_index
#print axioms stamp_items_are_credited
#print axioms ineligible_visit_is_skipped
#print axioms eligible_visit_keeps_ring_index
#print axioms credit_items_are_sweep
#print axioms electra_credits_are_nodup
#print axioms visit_below_flag_is_not_builder
#print axioms electra_block_items_are_credited
#print axioms gloas_queue_heads_items
#print axioms gloas_four_stage_order
#print axioms gloas_four_stage_items_are_credited
#print axioms gloas_stamp_indices_are_successors
#print axioms gloas_stamp_keeps_queue_validator
#print axioms gloas_chain_is_stamped
#print axioms gloas_second_payload_continues_index
#print axioms builder_pending_uses_flagged_index
#print axioms flagged_builder_index_recovers
#print axioms builder_queue_keeps_validator_balances
#print axioms partial_below_flag_is_not_builder
#print axioms gloas_from_builders_items_are_credited
#print axioms apply_tagged_concat_is_sequential
#print axioms mixed_gloas_validators_are_partials_only
#print axioms mixed_gloas_builders_are_queue_and_sweep
#print axioms remint_gloas_from_builders_repeats_items
#print axioms remint_gloas_from_builders_repeats_index_zero
#print axioms remint_gloas_chain_is_not_doubled
#print axioms remint_gloas_count_is_two_copies
#print axioms remint_gloas_cached_flat_is_two_copies
#print axioms remint_gloas_total_items_is_six
#print axioms remint_full_envelope_lists_credited
#print axioms remint_empty_envelope_lists_cache
#print axioms computed_gloas_flat_is_one_copy
#print axioms apply_tagged_double_is_sequential
#print axioms empty_gloas_remint_from_nils
#print axioms empty_gloas_remint_el_twice
#print axioms flagged_builder_is_in_range
#print axioms validator_below_flag_is_in_range
#print axioms apply_tagged_keeps_validator_past_len
#print axioms mixed_gloas_keeps_builder_past_len
#print axioms large_registry_visit_is_builder
#print axioms large_registry_electra_credits_flag
#print axioms large_registry_electra_writes_builder_zero
#print axioms hnflag_drop_refuted
#print axioms empty_registry_next_is_plus_one
#print axioms empty_registry_not_sweep_start
#print axioms empty_registry_visit_unbounded
#print axioms visit_ring_lt_needs_nonempty
#print axioms empty_registry_electra_is_nil
#print axioms wrap_five_seven_is_u64_borrow
#print axioms saturate_ne_wrap_on_excess
#print axioms apply_excess_equals_sat_sum
#print axioms fits_needed_for_wrap_agreement
#print axioms fits_agrees_with_wrap
#print axioms next_index_after_max_is_two_pow
#print axioms wrap_of_two_pow_is_zero
#print axioms last_u64_cursor_ne_wrap
#print axioms last_u64_pair_ne_wrap
#print axioms fits_rejects_overflow_pair
#print axioms fits_cursor_is_wrap
#print axioms flag_or_flag_is_not_add
#print axioms flag_convert_back_is_zero
#print axioms two_pow_or_flag_ne_u64
#print axioms two_pow_u64_or_is_flag
#print axioms builder_fits_rejects_flag_and_overflow
#print axioms small_builder_or_agrees_u64
#print axioms flag_u64_not_clears_bit_40
#print axioms two_pow_and_not_ne_u64
#print axioms two_pow_u64_and_not_is_zero
#print axioms small_validator_and_agrees_u64
#print axioms flag_xor_flag_is_sub
#print axioms flag_plus_three_and_agrees_u64

#print axioms processSlots_rejects_equal
#print axioms transition_requires_advance
#print axioms duplicate_slots_rejected
#print axioms le_pair_is_not_nodup
#print axioms el_rejects_parent
#print axioms validate_header_admits_duplicate_slots
#print axioms validate_header_ignores_slot_relabel
#print axioms validate_header_is_not_slot_nodup
#print axioms queueStage_caps
#print axioms electra_partials_cap
#print axioms electra_validators_need_room
#print axioms exited_not_partial_eligible
#print axioms zero_balance_not_fully_withdrawable
#print axioms compounding_max_is_2048e9
#print axioms eth1_prefix_is_one_compounding_is_two
#print axioms empty_cred_is_not_eth1
#print axioms bls_prefix_is_not_execution
#print axioms prefix_swap_flips_max
#print axioms first_byte_selects_tag
#print axioms cred_address_is_not_first_twenty
#print axioms eth1_layout_keeps_prefix
#print axioms el_fields_ignore_validator_index
#print axioms el_address_is_not_validator_index
#print axioms execution_address_is_not_uint256
#print axioms execution_address_is_big_endian
#print axioms execution_width_is_not_credential
#print axioms account_address_wraps_two_pow_160
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
#print axioms start_slot_two_pow_59_wraps_to_zero
#print axioms uint_to_bytes_is_little_endian
#print axioms proposer_seeds_need_slot_offset
#print axioms proposer_seed_slots_wrap_still_unique
#print axioms proposer_seeds_length_is_not_lookahead
#print axioms proposer_preimage_is_seed_then_slot
#print axioms get_seed_uses_proposer_domain
#print axioms proposer_fill_from_seeds_is_32
#print axioms get_seed_mix_is_not_current_epoch
#print axioms get_seed_mix_needs_historical_vector
#print axioms get_seed_mix_uses_lookahead
#print axioms get_seed_mix_wraps_at_epoch_two
#print axioms get_randao_mix_genesis_is_eth1
#print axioms get_randao_mix_is_not_epoch_bytes
#print axioms get_randao_mix_wraps_vector
#print axioms get_seed_mix_is_not_slot_zero
#print axioms get_seed_preimage_tracks_mix
#print axioms get_randao_reset_copies_current
#print axioms get_randao_reset_genesis_noop
#print axioms xor_truncates_unequal_lengths
#print axioms process_randao_writes_xor
#print axioms process_randao_is_not_copy
#print axioms process_randao_leaves_next
#print axioms process_randao_is_not_reset
#print axioms process_randao_is_not_copy_mutant
#print axioms process_randao_then_reset_next_is_xor
#print axioms process_randao_then_reset_not_swapped
#print axioms process_randao_then_reset_keeps_current
#print axioms epoch_at_slot_is_floor_div
#print axioms get_current_epoch_reads_slot
#print axioms eth1_reset_keeps_off_boundary
#print axioms eth1_reset_clears_on_boundary
#print axioms eth1_reset_not_always_clear
#print axioms slashings_vector_is_not_randao
#print axioms slashings_reset_writes_zero_not_copy
#print axioms process_epoch_cannot_accept_payload
#print axioms same_clock_cannot_accept
#print axioms historical_period_is_256
#print axioms historical_uses_period_not_slots
#print axioms historical_summaries_keep_off_boundary
#print axioms participation_rotates_off_historical_boundary
#print axioms participation_flags_clear_current
#print axioms historical_append_is_not_payload
#print axioms hysteresis_thresholds_are_asymmetric
#print axioms effective_balance_keeps_in_band
#print axioms effective_balance_not_always_update
#print axioms electra_compounding_keeps_40e9
#print axioms electra_compounding_ne_phase0_cap
#print axioms sync_committee_keeps_off_boundary
#print axioms sync_committee_rotates_on_boundary
#print axioms sync_committee_not_always_rotate
#print axioms effective_balance_update_is_not_payload
#print axioms sync_committee_update_is_not_payload
#print axioms pending_deposits_cap_at_sixteen
#print axioms gloas_pending_deposits_drop_eth1_bridge
#print axioms deposit_churn_clears_when_not_hit
#print axioms builder_payments_ignore_next_window
#print axioms builder_quorum_uses_per_slot
#print axioms electra_activation_queue_accepts_40e9
#print axioms pending_deposits_are_not_payload
#print axioms builder_pending_payments_are_not_payload
#print axioms activation_exit_epoch_uses_lookahead
#print axioms active_validator_is_half_open
#print axioms consolidation_skips_slashed
#print axioms consolidation_stops_before_later
#print axioms initiate_exit_is_noop_if_exiting
#print axioms initiate_exit_uses_256_delay
#print axioms registry_prefers_queue_to_eject
#print axioms ejection_balance_is_not_max_eb
#print axioms pending_consolidations_are_not_payload
#print axioms registry_updates_are_not_payload
#print axioms exit_overflow_epochs_ceil
#print axioms exit_churn_resets_on_new_epoch
#print axioms gloas_exit_churn_uses_half_quotient
#print axioms slashing_penalty_is_mid_vector
#print axioms electra_slashing_penalty_ne_phase0
#print axioms exit_churn_is_not_payload
#print axioms process_slashings_is_not_payload
#print axioms justification_skips_epoch_one_not_inactivity
#print axioms justification_threshold_is_ge
#print axioms justification_bits_shift_left_insert_false
#print axioms inactivity_leak_is_strictly_above_four
#print axioms inactivity_score_does_not_recover_in_leak
#print axioms head_miss_has_no_flag_penalty
#print axioms justification_is_not_payload
#print axioms inactivity_updates_are_not_payload
#print axioms rewards_and_penalties_are_not_payload
#print axioms compute_proposer_index_rejects_empty
#print axioms proposer_accept_is_ge_not_gt
#print axioms proposer_zero_balance_rejects_nonzero
#print axioms proposer_random_byte_uses_div
#print axioms proposer_random_byte_chunk_steps
#print axioms shuffled_index_rejects_equal_count
#print axioms shuffle_rounds_are_not_hash32
#print axioms shuffle_round_bytes_are_uint8
#print axioms shuffle_bucket_bytes_are_uint32
#print axioms shuffled_index_identity_before_rounds
#print axioms shuffle_flip_is_involution
#print axioms shuffle_pivot_is_little_endian
#print axioms shuffle_bit_uses_position
#print axioms shuffle_swap_on_bit_one
#print axioms shuffle_is_not_zero_rounds
#print axioms shuffle_flip_shares_position
#print axioms shuffle_bit_at_index_collides
#print axioms shuffle_step_partners_distinct
#print axioms shuffle_perm_rejects_out_of_range
#print axioms shuffle_perm_rejects_short
#print axioms shuffled_index_is_the_walk
#print axioms shuffle_bucket_is_256_window
#print axioms shuffle_source_uses_bucket_not_position
#print axioms shuffle_source_cache_hits_again
#print axioms shuffle_same_bucket_distinct_byte
#print axioms shuffle_bit_byte_uses_mod_256
#print axioms shuffle_bit_uses_offset_not_bucket
#print axioms shuffle_step_uses_cached_bit
#print axioms shuffle_bit_uses_bucket_not_position
#print axioms shuffle_preimage_uses_round
#print axioms shuffle_preimage_rounds_distinct
#print axioms shuffle_rounds_uint8_distinct
#print axioms shuffle_uint8_256_collides_zero
#print axioms shuffle_cache_starts_empty_each_round
#print axioms shuffle_cache_not_reused_across_rounds
#print axioms shuffle_stale_cache_hit_is_wrong_round
#print axioms shuffle_step_eq_empty_cache
#print axioms shuffle_walk_not_fixed_round
#print axioms shuffle_pivot_preimage_omits_bucket
#print axioms shuffle_bucket_preimage_extends_pivot
#print axioms shuffle_pivot_raw_ne_bucket_hash
#print axioms shuffle_pivot_ignores_suffix_byte
#print axioms shuffle_pivot_uses_take8_not_drop8
#print axioms shuffle_pivot_uses_take8_not_tail
#print axioms shuffle_pivot_uses_mod
#print axioms shuffle_pivot_no_mod_not_lt
#print axioms shuffle_flip_ignores_pivot_mod
#print axioms shuffle_empty_count_named_div0
#print axioms timeFits_rejects_overflow
#print axioms timeFits_mainnet_genesis
#print axioms time_wrap_eq_nat_when_fits
#print axioms timeFits_slot_two_pow_60
#print axioms bounded_time_is_not_necessary
#print axioms timeFits_rejects_two_pow_61
#print axioms time_wrap_two_pow_61_is_min_plus_two_pow_63
#print axioms time_nat_ne_wrap_two_pow_61
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
#print axioms empty_parent_drops_nonempty_expected
#print axioms always_expected_mutant_credits_empty_parent
#print axioms accepted_empty_parent_count_is_zero
#print axioms accepted_mixed_count_ignores_empty
#print axioms always_expected_overcounts_accepted
#print axioms accepted_nil_count_is_zero
#print axioms beacon_proposer_seed_uses_slot_not_epoch
#print axioms beacon_proposer_seed_is_not_bare
#print axioms fulu_proposer_index_mods_slot
#print axioms electra_random_is_not_byte
#print axioms electra_random_preimage_uses_div16
#print axioms electra_random_offset_is_pairs
#print axioms electra_accept_uses_2048e9
#print axioms gloas_proposer_indices_drop_slashed
#print axioms ptc_seed_uses_ptc_domain
#print axioms beacon_proposer_seed_is_not_payload
#print axioms electra_proposer_sample_is_not_payload
#print axioms fulu_proposer_index_is_not_payload
#print axioms gloas_proposer_unslashed_is_not_payload
#print axioms ptc_seed_is_not_payload
#print axioms balance_weighted_rejects_empty_indices
#print axioms balance_weighted_refresh_is_chunked
#print axioms ptc_does_not_shuffle
#print axioms ptc_size_is_not_one
#print axioms ptc_committees_keep_order
#print axioms ptc_committees_are_not_first_only
#print axioms next_sync_committee_uses_next_epoch
#print axioms balance_weighted_is_not_payload
#print axioms compute_ptc_is_not_payload
#print axioms next_sync_committee_indices_are_not_payload
#print axioms apply_pending_deposit_existing_skips_sig
#print axioms electra_pending_adds_amount_not_zero
#print axioms validator_from_deposit_uses_max_eb
#print axioms process_deposit_index_always_advances
#print axioms deposit_proof_depth_includes_mixin
#print axioms deposit_message_omits_signature
#print axioms deposit_domain_is_not_attester
#print axioms apply_pending_deposit_is_not_payload
#print axioms apply_deposit_is_not_payload
#print axioms is_valid_deposit_signature_is_not_payload
#print axioms get_validator_from_deposit_is_not_payload
#print axioms process_deposit_is_not_payload
#print axioms merkle_sibling_uses_level
#print axioms merkle_pair_left_is_not_always_right
#print axioms fulu_drops_electra_start_latch
#print axioms deposit_request_slot_is_not_genesis
#print axioms deposit_request_slot_is_not_index
#print axioms fulu_rejects_legacy_deposits
#print axioms deposit_request_type_is_not_withdrawal
#print axioms merkle_branch_is_not_payload
#print axioms process_deposit_request_is_not_payload
end Eip8282.Tests.ProtocolSlotWithdrawalMutants
