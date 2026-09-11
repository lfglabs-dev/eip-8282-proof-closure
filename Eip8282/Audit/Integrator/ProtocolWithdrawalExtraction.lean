import Eip8282.Audit.Integrator.ProtocolWithdrawalCount
import Eip8282.Audit.Integrator.ProtocolSlotExtraction
import Mathlib.Data.Nat.Bitwise

/-! Withdrawal counts of an accepted Gloas block sequence, extracted from the
archived `process_withdrawals` guard and the two archived builder loops, and
discharged into `ProtocolWithdrawalCount.total_count`/`dispatched_counts`
with the slot Nodup DERIVED by `ProtocolSlotExtraction`, never assumed.
Archived body: consensus-specs `specs/gloas/beacon-chain.md`
10b7decc3dd86a1e4921f8cf49081c87dc528d61631bc83646cb5d6a062c65ce (see the
slot module header for provenance). EL credit loop: Amsterdam fork.py:1101-1120
credits every listed item once; apply_body fork.py:788-857 calls it exactly
once per executed block (line 840) with `block.withdrawals`.

Exact Gloas facts modelled. Line 1999: `process_withdrawals` returns before any
list is computed when `state.latest_block_hash !=
state.latest_execution_payload_bid.block_hash` (empty parent). Lines
1879-1916: `get_expected_withdrawals` concatenates builder-pending, pending
partial, builders-sweep, validators-sweep lists in that order and no other.
Lines 1805-1833 `get_builder_withdrawals`: `withdrawals_limit = 16-1`,
`assert len(prior) <= 15`, break once `len(prior)+len(current) >= 15`, else
append one Withdrawal per queue entry retaining `fee_recipient`/`amount`.
Lines 1839-1873 `get_builders_sweep_withdrawals`: line 1847
`assert len(prior_withdrawals) <= withdrawals_limit` with the prior list being
builder-pending ++ pending-partial (1888, 1894); same break; append only when
`withdrawable_epoch <= epoch and balance > 0`. The visited-builder count
(`builders_limit`, 1845/1852) is not modelled: the list is an unconstrained
input, which only weakens nothing in the bound. Lines 402-408: Gloas `Withdrawals` is a
`ProgressiveList[Withdrawal]`, so unlike Capella no SSZ type cap of 16 exists
here; the per-block bound below comes only from the loop guards. The value
`MAX_WITHDRAWALS_PER_PAYLOAD = 16` is used symbolically at lines 1810/1846; its
definition is Capella beacon-chain.md:138 (SHA256 e68a7653e3bab44d4eae2a5b2e7b96
2605c166f8e9527c21e7a46a3ef8d63042, cited by
audit/receipts/direct-protocol-withdrawal-count-binding-20260910.md), whose
body is not in the transported bundle: the literals 15/16 below rest on it.

`queueStage`/`sweepStage` lengths are now derived from the archived break
guards (Gloas:1817-1819, 1854-1856). The EL `process_withdrawals` for-loop
(fork.py:1111-1118) is reconstructed as `ElCredit`; `Dispatch` of the flattened
computed lists is derived from one `apply_body` invocation per accepted block
(fork.py:840) plus the named `CreateEther` agreement, not assumed as the
consumer's flatMap premise.

The Gloas cache recurrence is now extracted here: fork.md:221 initializes
`payload_expected_withdrawals` empty; Gloas:1999 returns without assignment
on an empty parent; Gloas:1940 assigns `expected` otherwise. The CL-to-EL
binding is fork-choice.md:688
`assert hash_tree_root(payload.withdrawals) == hash_tree_root(state.payload_expected_withdrawals)`
inside `verify_execution_payload_envelope` (659-699), called from
`on_execution_payload_envelope` (1113). List identity after that root check
is the named SSZ adapter `WithdrawalsRootMatch`. `EnvelopeCredits` then
derives the consumer `Dispatch` of the retained-cache lists, not of the
computed-only `items`.

The engine gate of `verify_execution_payload_envelope` is now extracted
as control flow, not as an EL credit. Electra:1307-1336
`verify_and_notify_new_payload` returns false on an empty transaction byte
(1318) or when any of `is_valid_block_hash` / `is_valid_versioned_hashes` /
`notify_new_payload` is false. Those three predicates are
implementation-dependent (Bellatrix:361-370, Electra:1271-1297). Gloas
fork-choice.md:690-698 constructs the Electra-shaped `NewPayloadRequest`
(Electra:1255-1261). `on_execution_payload_envelope` (1096-1116) asserts a
known beacon root (1104) and data availability (1108), then verifies (1113)
and assigns `store.payloads` (1116). That store write is not
`apply_body`:840 / `create_ether`. `EnvelopeCredits.cons` still requires
`ApplyBodyWithdrawals` of the listed withdrawals. fork-choice.md:681/686
are equalities on an uninterpreted hash type; Gloas:1999 `parentFull` is
`latest == bid`, so `cacheAfter` follows from those hashes.
`EnvelopeTimestamp` (phase0:1278-1280) discharges fork-choice.md:687.
`HashEnvelopeCredits` requires `ParentFullFromHashes` at each step so the
minted list is `expected` iff `latest = bid`.
`VerifiedHashCredits` requires a full `VerifyExecutionPayloadEnvelope`
(consistency, 681/685-688, engine) plus that hash flag, so the minted
list is forced by those conjuncts rather than a free `listed`.
`create_ether` (state_tracker.py:624-644) increments via `modify_state`
(575-587) after `get_account` (188-211). Lean `increaseBalance` matches
the existing-account increment and the missing-key insert. A nonzero
Gwei credit has positive Wei; under the named no-wrap `BalanceFits`,
the 385 `balance == 0` conjunct of `account_exists_and_is_empty` is
false, so `modify_state` 583-587 cannot destroy. After a zero
increment Lean `increaseBalance` still inserts or updates and never
deletes (`createEther_keeps_present`); nonce/balance emptiness
(383/385) is derived for missing+0 and already-empty+0. Line 384
`code_hash == EMPTY_CODE_HASH` and the Python `modify_state` 583-587
delete remain named. Gloas:1924 and fork.py:1111-1118 walk the same
archived `Withdrawal` list: `CreditedWithdrawal` pairs
`validator_index` with the EL `Item`; `CreditedRun` derives
`applyTagged` and `ElCredit` from that joint walk. SSZ decode onto
the pair remains named.

Electra `get_pending_partial_withdrawals` (1360-1398) and
`get_validators_sweep_withdrawals` (1407-1454) are now extracted:
limit `min(prior+8, 15)` (Electra:336-338 / 1366-1368), pending assert
1370, validator `withdrawals_limit = 16` and `prior < 16` (1414-1416).
`partialBound` / `validatorsGuard` are derived for a block built from
those loops (`blockOfElectra`). Eligibility is now the archived Electra
predicates (708-718, 668-677, 688-702), not a free Boolean; remaining
named inputs are the remaining 31 credential bytes (first-byte 0x00/0x01/0x02
are extracted) and an empty validator registry
(`% 0`). `get_balance_after_withdrawals` underflow is discharged on an
empty prior and whenever `withdrawn ≤ balance` (the Gwei `Uint64` wrap
remains named only when that inequality fails). The sweep cursor
rotation (Electra:1420-1451 / Capella:516-528) is extracted below.

OPEN (explicit hypotheses or adapters, not proved): SSZ byte-string
decode of the whole `Withdrawal` container (field order,
`credentials[12:]`, and 20-byte BE `executionAddress` are extracted);
credential bytes 1–11 are the Capella:639 pad of `eth1Credential`;
the first-byte prefixes 0x00/0x01/0x02 are
`BLS_WITHDRAWAL_PREFIX` / `ETH1_ADDRESS_WITHDRAWAL_PREFIX` /
`COMPOUNDING_WITHDRAWAL_PREFIX` via `credOfByte` / `hasExecutionBytes`;
the Gwei `Uint64` wrap of
`get_balance_after_withdrawals` when `withdrawn > balance` is
extracted as `gweiWrapSub` and shown unequal to Lean saturate;
`BalanceAfterFits` is that Python agreement, not a Lean fold
identity (the saturating `decrease_balance` / builder-`min` path
is extracted);
empty-registry Python `ZeroDivisionError` (Lean `Nat.mod _ 0 = id`
is extracted and is not that exception; `SweepStart.registry` is
load-bearing); `IndexInRange` is the
extracted `ValidatorIndex < len(validators)` / `builder_index <
len(builders)` guard (Gloas:1926-1931), not Python `IndexError`;
visit keys with `n > 2^40` are builder-tagged (the `n ≤ 2^40`
hypothesis is load-bearing); `WithdrawalIndex` Uint64 wrap when
`start + n ≥ 2^64` is extracted as `withdrawalIndexWrap`; Lean
`indexSeq` uniqueness is Nat `+= 1` (always Nodup); Fits is the
Python cursor/list wrap agreement; Gloas:1127-1128 `|` wrap of
`toValidatorIndex` is extracted as `toValidatorIndexU64` (Lean
unbounded `|||` ≠ Python `Uint64 |` when `b ≥ 2^64`; `|||` ≠ `+`
when bit 40 is already set);
`indexedChain` / `indexedCachedFrom` produce `Withdrawal.index` on
credited and retained-cache lists here and are not yet imported by
StageExtraction / Makefile; `stampIndex` joins that index with
`CreditedWithdrawal.validatorIndex` on one `ArchivedWithdrawal`
(Capella:196-204) without claiming SSZ injectivity; `creditEligible`
stamps `visitRing` keys onto those credited withdrawals (Electra:1420-1449)
and its Item projection is `sweepStage`; `gloasCredited` concatenates
the four Gloas stages as credited lists (1879-1916) so `items` of a
full parent is that Item projection; `stampedChain` assigns Capella
`Withdrawal.index` across those credited payloads (452/458 then 510)
so `indexedChain` of the constructed blocks is that stamp; `gloasFromBuilders`
assigns queue/sweep `validator_index` via `toValidatorIndex` of the archived
`builder_index` (Gloas:1826/1863) and recovers that index when it is
`< 2^40`; the Uint64 `|` wrap of
`convert_builder_index_to_validator_index` is `toValidatorIndexU64`
(input wrap when `b ≥ 2^64`; `|||` ≠ `+` when bit 40 is set);
`builder_index < len(builders)` and
`validator_index < len(validators)` on the Gloas:1923-1931 fold
(`is_builder_index` and the two-array split are extracted);
the 64-bit one's-complement of `BUILDER_INDEX_FLAG` is
`builderFlagNotU64` (Gloas:1134-1135 `validator_index & ~FLAG`; Lean
`toBuilderIndex` agrees on every `Uint64` input via
`xor_flag_eq_sub_of_flag_bit` and disagrees when `v ≥ 2^64`);
`get_beacon_proposer_indices` SHA256 *values* (Fulu:372-378) of the
lookahead fill (`process_proposer_lookahead` Fulu:481-489, the 32 LE
seed preimages, `uint_to_bytes` / `ENDIANNESS`,
`compute_start_slot_at_epoch` wrap, `get_seed` mix index
phase0:1449-1451 / 1414, `compute_proposer_index` nonempty / accept-byte
/ `i // 32` preimage, and `compute_shuffled_index` assert / identity
init / 90-round Uint8+Uint32 preimages / flip involution / LE take-8
pivot / position-max bit / swap-or-not / shared partner bit /
one-round injectivity / `List.Perm` against `range(n)` / `perm[index]`
as the 90-round walk / `source_by_bucket` cache are extracted
in the slot module; SHA256 pivot and swap-bit *values* stay uninterpreted);
SSZ `Withdrawal` root injectivity (`SszWithdrawal` field order,
`credentials[12:]`, and the 20-byte BE `ExecutionAddress` →
`AccountAddress` decode are extracted; `WithdrawalsRootMatch` is root equality to
decoded list equality); implementation-dependent engine predicates
`is_valid_block_hash` / `is_valid_versioned_hashes` / `notify_new_payload`;
`notify_new_payload` is not `create_ether`; signature / header / bid-field
bodies behind the named consistency Booleans (fork-choice.md:668-682);
hash *values* are uninterpreted (no Keccak); `TimeFitsU64` wrap is
`timeAtSlotWrap` (identity under Fits; still Fits at MIN + slot `2^60`;
not the Nat sum at MIN + slot `2^61`); canonical
store contents behind `store.block_states` / `is_data_available`;
`validate_header` does not bind `header.slot_number` (fork.py:323 vs 472;
`ElHeader.slotNumber` may repeat while `number` is Nodup);
Python `modify_state` 583-587 delete after a zero increment on an
already-empty or missing recipient (Lean `increaseBalance` never
deletes; nonce/balance 383/385 are derived; a zero increment on a
nonzero existing balance is the identity);
`BalanceFits` (no UInt256 wrap of existing balance + Wei);
line 384 `code_hash == EMPTY_CODE_HASH` (not a Keccak proof);
default Lean `Account` versus Python `EMPTY_ACCOUNT` field identity;
PoW count and migration conservation. -/
namespace Eip8282.Audit.Integrator.ProtocolWithdrawalExtraction
open EvmYul EvmYul.EVM
open ProtocolCreditEnvelope ProtocolWithdrawalCount ProtocolSlotExtraction
open ResourceBounds (U64)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 400000

/-- Gloas:1805-1833 loop over `state.builder_pending_withdrawals`, given the
combined prior length: break at the limit, otherwise append the entry. -/
def queueStage (limit prior : Nat) : List Item → List Item
  | [] => []
  | item::rest => if limit ≤ prior then [] else item::queueStage limit (prior+1) rest

theorem queueStage_guarded (limit : Nat) (queue : List Item) :
    ∀ prior : Nat, prior ≤ limit → GuardedAdds limit prior (queueStage limit prior queue) := by
  induction queue with
  | nil => intro prior h; exact .nil h
  | cons item rest ih =>
    intro prior h
    by_cases hl : limit ≤ prior
    · simp only [queueStage,hl,if_true]; exact .nil h
    · simp only [queueStage,hl,if_false]
      exact .cons (by omega) (ih (prior+1) (by omega))

/-- Gloas:1817-1819: the builder-pending loop appends while combined length
is strictly below the limit, otherwise breaks. The produced length is the
remaining capacity, never an extra count hypothesis. -/
theorem queueStage_length (limit prior : Nat) (queue : List Item)
    (h : prior ≤ limit) :
    (queueStage limit prior queue).length = min (limit - prior) queue.length := by
  induction queue generalizing prior with
  | nil =>
    simp only [queueStage, List.length_nil]
    exact (Nat.min_eq_right (Nat.zero_le _)).symm
  | cons item rest ih =>
    by_cases hl : limit ≤ prior
    · simp only [queueStage, hl, ↓reduceIte, List.length_nil]
      have hz : limit - prior = 0 := Nat.sub_eq_zero_of_le hl
      rw [hz, Nat.zero_min]
    · have hlt : prior < limit := Nat.not_le.mp hl
      simp only [queueStage, hl, ↓reduceIte, List.length_cons]
      have hih := ih (prior + 1) (Nat.succ_le_of_lt hlt)
      rw [hih, Nat.sub_add_eq]
      have hpos : 0 < limit - prior := Nat.sub_pos_of_lt hlt
      omega

/-- Gloas:1839-1873 loop over the visited builders, each tagged with the
archived eligibility test `withdrawable_epoch <= epoch and balance > 0`. -/
def sweepStage (limit prior : Nat) : List (Item × Bool) → List Item
  | [] => []
  | (item,eligible)::rest =>
    if limit ≤ prior then []
    else if eligible then item::sweepStage limit (prior+1) rest
    else sweepStage limit prior rest

theorem sweepStage_guarded (limit : Nat) (builders : List (Item × Bool)) :
    ∀ prior : Nat, prior ≤ limit → GuardedAdds limit prior (sweepStage limit prior builders) := by
  induction builders with
  | nil => intro prior h; exact .nil h
  | cons entry rest ih =>
    intro prior h
    obtain ⟨item,eligible⟩ := entry
    by_cases hl : limit ≤ prior
    · simp only [sweepStage,hl,if_true]; exact .nil h
    · cases eligible with
      | false => simp only [sweepStage,hl,if_false,Bool.false_eq_true]; exact ih prior h
      | true =>
        simp only [sweepStage,hl,if_false,if_true]
        exact .cons (by omega) (ih (prior+1) (by omega))

/-- Gloas:1854-1856 / 1859: ineligible builders add no entry, so the sweep
length is at most the remaining capacity and at most the visit count. -/
theorem sweepStage_length (limit prior : Nat) (builders : List (Item × Bool))
    (h : prior ≤ limit) :
    (sweepStage limit prior builders).length ≤ min (limit - prior) builders.length := by
  induction builders generalizing prior with
  | nil =>
    simp only [sweepStage, List.length_nil]
    exact Nat.zero_le _
  | cons entry rest ih =>
    obtain ⟨item, eligible⟩ := entry
    by_cases hl : limit ≤ prior
    · simp only [sweepStage, hl, ↓reduceIte, List.length_nil]
      exact Nat.zero_le _
    · have hlt : prior < limit := Nat.not_le.mp hl
      cases eligible with
      | false =>
        simp only [sweepStage, hl, ↓reduceIte, Bool.false_eq_true]
        have hih := ih prior h
        exact hih.trans (min_le_min (le_refl _) (Nat.le_succ _))
      | true =>
        simp only [sweepStage, hl, ↓reduceIte, List.length_cons]
        have hih := ih (prior + 1) (Nat.succ_le_of_lt hlt)
        have hpos : 0 < limit - prior := Nat.sub_pos_of_lt hlt
        have hstep : min (limit - (prior + 1)) rest.length + 1 ≤
            min (limit - prior) (rest.length + 1) := by
          rw [Nat.sub_add_eq]
          omega
        exact (Nat.add_le_add_right hih 1).trans hstep

/-- A combined-length bound is exactly a guarded trace of the same limit. -/
theorem guarded_of_length {α : Type} (limit : Nat) (items : List α) :
    ∀ prior : Nat, prior + items.length ≤ limit → GuardedAdds limit prior items := by
  induction items with
  | nil => intro prior h; exact .nil (by simpa using h)
  | cons _ rest ih =>
    intro prior h
    simp only [List.length_cons] at h
    exact .cons (by omega) (ih (prior+1) (by omega))

theorem sweepStage_combined (limit prior : Nat) (builders : List (Item × Bool))
    (h : prior ≤ limit) :
    prior + (sweepStage limit prior builders).length ≤ limit := by
  have hlen := sweepStage_length limit prior builders h
  have hmin : (sweepStage limit prior builders).length ≤ limit - prior :=
    hlen.trans (Nat.min_le_left _ _)
  omega

/-- Electra:338 `MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP = Uint64(2**3)` (= 8).
SHA256 c722ff14969bc58c3b348ff059a40f413d9598509692b470c3832f64662a11a8. -/
def MAX_PENDING_PARTIALS : Nat := 8

/-- Capella / Electra `MAX_WITHDRAWALS_PER_PAYLOAD = 16`. -/
def MAX_WITHDRAWALS_PER_PAYLOAD : Nat := 16

/-- Electra:1366-1368: `min(len(prior)+8, MAX_WITHDRAWALS_PER_PAYLOAD-1)`. -/
def electraPartialsLimit (prior : Nat) : Nat :=
  min (prior + MAX_PENDING_PARTIALS) (MAX_WITHDRAWALS_PER_PAYLOAD - 1)

theorem electraPartialsLimit_le_15 (prior : Nat) : electraPartialsLimit prior ≤ 15 :=
  Nat.min_le_right _ _

/-- Electra:1370 `assert len(prior_withdrawals) <= withdrawals_limit`.
Holds whenever the Gloas builder-pending prior is already ≤ 15. -/
theorem electraPartials_assert (prior : Nat) (h : prior ≤ 15) :
    prior ≤ electraPartialsLimit prior := by
  unfold electraPartialsLimit MAX_PENDING_PARTIALS MAX_WITHDRAWALS_PER_PAYLOAD
  omega

/-- Electra:1360-1398 queue entry: `withdrawable_epoch <= epoch` and
`is_eligible_for_partial_withdrawals`. Balance/credentials remain named. -/
structure ElectraPartial where
  item : Item
  mature : Bool
  eligible : Bool

/-- Electra:1374-1396. Break on immature or at limit; skip an ineligible
mature entry; otherwise append. The limit is fixed at entry (1366-1368),
not recomputed from the growing list. -/
def electraPartialLoop (limit prior : Nat) : List ElectraPartial → List Item
  | [] => []
  | c::rest =>
    if !c.mature || decide (limit ≤ prior) then []
    else if c.eligible then c.item :: electraPartialLoop limit (prior + 1) rest
    else electraPartialLoop limit prior rest

theorem electraPartialLoop_guarded (limit : Nat) (cs : List ElectraPartial) :
    ∀ prior, prior ≤ limit →
      GuardedAdds limit prior (electraPartialLoop limit prior cs) := by
  induction cs with
  | nil => intro prior h; exact .nil h
  | cons c rest ih =>
    intro prior h
    unfold electraPartialLoop
    split
    · exact .nil h
    · rename_i keep
      have hlt : prior < limit := by
        by_contra hge
        have : limit ≤ prior := Nat.le_of_not_gt hge
        simp [this] at keep
      split
      · exact .cons hlt (ih (prior + 1) (by omega))
      · exact ih prior h

def electraPartials (prior : Nat) (cs : List ElectraPartial) : List Item :=
  electraPartialLoop (electraPartialsLimit prior) prior cs

theorem electraPartials_guarded (prior : Nat) (cs : List ElectraPartial)
    (h : prior ≤ 15) :
    GuardedAdds (electraPartialsLimit prior) prior (electraPartials prior cs) :=
  electraPartialLoop_guarded _ cs prior (electraPartials_assert prior h)

/-- Electra:1366-1378: appended partials fit in `min(prior+8, 15)`, so
the Gloas:1847 prior (builder ++ partial) is ≤ 15 and partials ≤ 8. -/
theorem electraPartials_bound (prior : Nat) (cs : List ElectraPartial)
    (h : prior ≤ 15) :
    prior + (electraPartials prior cs).length ≤ 15 ∧
      (electraPartials prior cs).length ≤ 8 := by
  have hg := guarded_length (electraPartials_guarded prior cs h)
  unfold electraPartialsLimit MAX_PENDING_PARTIALS MAX_WITHDRAWALS_PER_PAYLOAD at hg
  omega

/-- All-mature all-eligible entries reduce to the builder-pending loop. -/
def electraRipe (item : Item) : ElectraPartial where
  item := item
  mature := true
  eligible := true

theorem electraPartialLoop_ripe (limit prior : Nat) (items : List Item) :
    electraPartialLoop limit prior (items.map electraRipe) =
      queueStage limit prior items := by
  induction items generalizing prior with
  | nil => rfl
  | cons item rest ih =>
    by_cases hl : limit ≤ prior
    · simp [electraPartialLoop, electraRipe, queueStage, hl]
    · simp [electraPartialLoop, electraRipe, queueStage, hl, ih]

/-- Electra:1414-1416: validator sweep limit is 16 and requires a strict
free slot (`len(prior) < 16`). -/
theorem electraValidators_assert {prior : Nat} (h : prior < 16) : prior ≤ 16 :=
  Nat.le_of_lt h

theorem electraValidators_guarded (prior : Nat) (visits : List (Item × Bool))
    (h : prior < 16) :
    GuardedAdds 16 prior (sweepStage 16 prior visits) :=
  sweepStage_guarded 16 visits prior (electraValidators_assert h)

/-- Electra:301 `MIN_ACTIVATION_BALANCE = Gwei(2**5 * 10**9)` (= 32e9). -/
def MIN_ACTIVATION_BALANCE : Nat := 32 * 10^9

/-- Electra:302 `MAX_EFFECTIVE_BALANCE_ELECTRA = Gwei(2**11 * 10**9)` (= 2048e9). -/
def MAX_EFFECTIVE_BALANCE_ELECTRA : Nat := 2048 * 10^9

/-- phase0:544 `FAR_FUTURE_EPOCH = Epoch(2**64 - 1)`. -/
def FAR_FUTURE_EPOCH : Nat := 2^64 - 1

/-- Capella:317 `ETH1_ADDRESS_WITHDRAWAL_PREFIX = 0x01`;
Electra:285 / 635 `COMPOUNDING_WITHDRAWAL_PREFIX = 0x02`.
First-byte values are `ETH1_ADDRESS_WITHDRAWAL_PREFIX` /
`COMPOUNDING_WITHDRAWAL_PREFIX` / `BLS_WITHDRAWAL_PREFIX`; the
remaining 31 credential bytes stay named. -/
inductive WithdrawalPrefix where
  | eth1
  | compounding
  | other
  deriving DecidableEq

/-- Fields read by Electra:651-718 / 668-702 / 733-740. -/
structure ValidatorView where
  effectiveBalance : Nat
  exitEpoch : Nat
  withdrawableEpoch : Nat
  cred : WithdrawalPrefix

/-- Electra:651-658 / Capella:313-317. -/
def hasExecutionCredential (v : ValidatorView) : Bool :=
  decide (v.cred = .eth1) || decide (v.cred = .compounding)

/-- Electra:733-740. Compounding uses 2048e9; otherwise 32e9. -/
def maxEffectiveBalance (v : ValidatorView) : Nat :=
  if v.cred = .compounding then MAX_EFFECTIVE_BALANCE_ELECTRA
  else MIN_ACTIVATION_BALANCE

/-- Electra:708-718. -/
def isEligibleForPartial (v : ValidatorView) (balance : Nat) : Bool :=
  decide (v.exitEpoch = FAR_FUTURE_EPOCH) &&
    decide (MIN_ACTIVATION_BALANCE ≤ v.effectiveBalance) &&
    decide (MIN_ACTIVATION_BALANCE < balance)

/-- Electra:668-677. -/
def isFullyWithdrawable (v : ValidatorView) (balance epoch : Nat) : Bool :=
  hasExecutionCredential v &&
    decide (v.withdrawableEpoch ≤ epoch) &&
    decide (0 < balance)

/-- Electra:688-702. -/
def isPartiallyWithdrawable (v : ValidatorView) (balance : Nat) : Bool :=
  hasExecutionCredential v &&
    decide (v.effectiveBalance = maxEffectiveBalance v) &&
    decide (maxEffectiveBalance v < balance)

/-- Electra:1429-1449: the validator sweep appends on either test. -/
def validatorSweepEligible (v : ValidatorView) (balance epoch : Nat) : Bool :=
  isFullyWithdrawable v balance epoch || isPartiallyWithdrawable v balance

theorem isEligibleForPartial_flags {v : ValidatorView} {balance : Nat}
    (h : isEligibleForPartial v balance = true) :
    v.exitEpoch = FAR_FUTURE_EPOCH ∧
      MIN_ACTIVATION_BALANCE ≤ v.effectiveBalance ∧
      MIN_ACTIVATION_BALANCE < balance := by
  simp [isEligibleForPartial] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem isEligibleForPartial_rejects_exited {v : ValidatorView} {balance : Nat}
    (h : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    isEligibleForPartial v balance = false := by
  simp [isEligibleForPartial, h]

theorem isEligibleForPartial_rejects_no_excess {v : ValidatorView} {balance : Nat}
    (h : balance ≤ MIN_ACTIVATION_BALANCE) :
    isEligibleForPartial v balance = false := by
  simp [isEligibleForPartial]
  exact fun _ _ => h

theorem isFullyWithdrawable_rejects_zero {v : ValidatorView} {epoch : Nat} :
    isFullyWithdrawable v 0 epoch = false := by
  simp [isFullyWithdrawable]

theorem isFullyWithdrawable_rejects_other_prefix {v : ValidatorView}
    {balance epoch : Nat} (h : v.cred = .other) :
    isFullyWithdrawable v balance epoch = false := by
  simp [isFullyWithdrawable, hasExecutionCredential, h]

theorem maxEffectiveBalance_compounding {v : ValidatorView}
    (h : v.cred = .compounding) :
    maxEffectiveBalance v = MAX_EFFECTIVE_BALANCE_ELECTRA := by
  simp [maxEffectiveBalance, h]

theorem maxEffectiveBalance_eth1 {v : ValidatorView} (h : v.cred = .eth1) :
    maxEffectiveBalance v = MIN_ACTIVATION_BALANCE := by
  simp [maxEffectiveBalance, h]

/-- phase0:553 `BLS_WITHDRAWAL_PREFIX = Bytes1('0x00')`. -/
def BLS_WITHDRAWAL_PREFIX : Nat := 0x00

/-- phase0:554 `ETH1_ADDRESS_WITHDRAWAL_PREFIX = Bytes1('0x01')`. -/
def ETH1_ADDRESS_WITHDRAWAL_PREFIX : Nat := 0x01

/-- Electra:285 `COMPOUNDING_WITHDRAWAL_PREFIX = Bytes1('0x02')`. -/
def COMPOUNDING_WITHDRAWAL_PREFIX : Nat := 0x02

theorem bls_prefix_byte : BLS_WITHDRAWAL_PREFIX = 0 :=
  rfl

theorem eth1_prefix_byte : ETH1_ADDRESS_WITHDRAWAL_PREFIX = 1 :=
  rfl

theorem compounding_prefix_byte : COMPOUNDING_WITHDRAWAL_PREFIX = 2 :=
  rfl

theorem prefix_bytes_distinct :
    ETH1_ADDRESS_WITHDRAWAL_PREFIX ≠ COMPOUNDING_WITHDRAWAL_PREFIX ∧
      ETH1_ADDRESS_WITHDRAWAL_PREFIX ≠ BLS_WITHDRAWAL_PREFIX ∧
      COMPOUNDING_WITHDRAWAL_PREFIX ≠ BLS_WITHDRAWAL_PREFIX := by
  decide

/-- Capella:317 / Electra:635: first byte of `withdrawal_credentials`. -/
def credOfByte (b : Nat) : WithdrawalPrefix :=
  if b = ETH1_ADDRESS_WITHDRAWAL_PREFIX then .eth1
  else if b = COMPOUNDING_WITHDRAWAL_PREFIX then .compounding
  else .other

theorem credOfByte_eth1 :
    credOfByte ETH1_ADDRESS_WITHDRAWAL_PREFIX = .eth1 :=
  rfl

theorem credOfByte_compounding :
    credOfByte COMPOUNDING_WITHDRAWAL_PREFIX = .compounding :=
  rfl

theorem credOfByte_bls :
    credOfByte BLS_WITHDRAWAL_PREFIX = .other :=
  rfl

theorem credOfByte_eq_eth1_iff {b : Nat} :
    credOfByte b = .eth1 ↔ b = ETH1_ADDRESS_WITHDRAWAL_PREFIX := by
  unfold credOfByte ETH1_ADDRESS_WITHDRAWAL_PREFIX COMPOUNDING_WITHDRAWAL_PREFIX
  constructor
  · intro h
    split at h
    · assumption
    · split at h
      · cases h
      · cases h
  · intro h
    simp [h]

theorem credOfByte_eq_compounding_iff {b : Nat} :
    credOfByte b = .compounding ↔ b = COMPOUNDING_WITHDRAWAL_PREFIX := by
  unfold credOfByte ETH1_ADDRESS_WITHDRAWAL_PREFIX COMPOUNDING_WITHDRAWAL_PREFIX
  constructor
  · intro h
    split at h
    · cases h
    · split at h
      · assumption
      · cases h
  · intro h
    simp [h]

/-- A one-byte swap of 0x01 and 0x02 is not the identity on the tag. -/
theorem credOfByte_swap_ne :
    credOfByte ETH1_ADDRESS_WITHDRAWAL_PREFIX ≠
      credOfByte COMPOUNDING_WITHDRAWAL_PREFIX := by
  simp [credOfByte_eth1, credOfByte_compounding]

/-- Capella:317 `withdrawal_credentials[:1] == ETH1_ADDRESS_WITHDRAWAL_PREFIX`.
An empty slice is not `Bytes1('0x01')`. -/
def hasEth1Bytes (bytes : List Nat) : Bool :=
  match bytes with
  | [] => false
  | b :: _ => decide (b = ETH1_ADDRESS_WITHDRAWAL_PREFIX)

/-- Electra:634-635 `withdrawal_credentials[:1] == COMPOUNDING_WITHDRAWAL_PREFIX`. -/
def isCompoundingBytes (bytes : List Nat) : Bool :=
  match bytes with
  | [] => false
  | b :: _ => decide (b = COMPOUNDING_WITHDRAWAL_PREFIX)

/-- Electra:641-645. -/
def hasCompoundingBytes (bytes : List Nat) : Bool :=
  isCompoundingBytes bytes

/-- Electra:651-658 `has_eth1` (0x01) or `has_compounding` (0x02). -/
def hasExecutionBytes (bytes : List Nat) : Bool :=
  hasEth1Bytes bytes || hasCompoundingBytes bytes

theorem hasEth1Bytes_nil : hasEth1Bytes [] = false :=
  rfl

theorem hasEth1Bytes_cons (rest : List Nat) :
    hasEth1Bytes (ETH1_ADDRESS_WITHDRAWAL_PREFIX :: rest) = true :=
  rfl

theorem hasEth1Bytes_bls (rest : List Nat) :
    hasEth1Bytes (BLS_WITHDRAWAL_PREFIX :: rest) = false :=
  rfl

theorem hasCompoundingBytes_cons (rest : List Nat) :
    hasCompoundingBytes (COMPOUNDING_WITHDRAWAL_PREFIX :: rest) = true :=
  rfl

theorem hasCompoundingBytes_eth1 (rest : List Nat) :
    hasCompoundingBytes (ETH1_ADDRESS_WITHDRAWAL_PREFIX :: rest) = false :=
  rfl

theorem hasExecutionBytes_nil : hasExecutionBytes [] = false :=
  rfl

theorem hasExecutionBytes_eth1 (rest : List Nat) :
    hasExecutionBytes (ETH1_ADDRESS_WITHDRAWAL_PREFIX :: rest) = true :=
  rfl

theorem hasExecutionBytes_compounding (rest : List Nat) :
    hasExecutionBytes (COMPOUNDING_WITHDRAWAL_PREFIX :: rest) = true :=
  rfl

theorem hasExecutionBytes_bls (rest : List Nat) :
    hasExecutionBytes (BLS_WITHDRAWAL_PREFIX :: rest) = false :=
  rfl

/-- Tag a view from the archived first byte. Tail bytes are unused. -/
def viewWithByte (b effectiveBalance exitEpoch withdrawableEpoch : Nat) :
    ValidatorView where
  effectiveBalance := effectiveBalance
  exitEpoch := exitEpoch
  withdrawableEpoch := withdrawableEpoch
  cred := credOfByte b

theorem hasExecutionCredential_of_byte (b eb ex w : Nat) :
    hasExecutionCredential (viewWithByte b eb ex w) = hasExecutionBytes [b] := by
  simp [hasExecutionCredential, viewWithByte, hasExecutionBytes, hasEth1Bytes,
    hasCompoundingBytes, isCompoundingBytes]
  by_cases h1 : b = ETH1_ADDRESS_WITHDRAWAL_PREFIX
  · simp [h1, credOfByte]
  · by_cases h2 : b = COMPOUNDING_WITHDRAWAL_PREFIX
    · simp [h2, credOfByte]
    · simp [h1, h2, credOfByte]

theorem maxEffective_of_eth1_byte (eb ex w : Nat) :
    maxEffectiveBalance (viewWithByte ETH1_ADDRESS_WITHDRAWAL_PREFIX eb ex w) =
      MIN_ACTIVATION_BALANCE := by
  simp [maxEffectiveBalance, viewWithByte, credOfByte_eth1]

theorem maxEffective_of_compounding_byte (eb ex w : Nat) :
    maxEffectiveBalance (viewWithByte COMPOUNDING_WITHDRAWAL_PREFIX eb ex w) =
      MAX_EFFECTIVE_BALANCE_ELECTRA := by
  simp [maxEffectiveBalance, viewWithByte, credOfByte_compounding]

/-- Electra:737-740. Swapping 0x01 and 0x02 flips 32e9 vs 2048e9. -/
theorem prefix_swap_changes_max (eb ex w : Nat) :
    maxEffectiveBalance (viewWithByte ETH1_ADDRESS_WITHDRAWAL_PREFIX eb ex w) ≠
      maxEffectiveBalance (viewWithByte COMPOUNDING_WITHDRAWAL_PREFIX eb ex w) := by
  rw [maxEffective_of_eth1_byte, maxEffective_of_compounding_byte]
  exact (by decide :
    MIN_ACTIVATION_BALANCE ≠ MAX_EFFECTIVE_BALANCE_ELECTRA)

theorem isFullyWithdrawable_rejects_bls {v : ValidatorView} {balance epoch : Nat}
    (h : v.cred = credOfByte BLS_WITHDRAWAL_PREFIX) :
    isFullyWithdrawable v balance epoch = false := by
  have ho : v.cred = .other := by
    simpa [credOfByte_bls] using h
  exact isFullyWithdrawable_rejects_other_prefix ho

/-- phase0:742 `withdrawal_credentials: Bytes32`. -/
def CREDENTIAL_BYTES : Nat := 32

/-- Capella:454 / Electra:1390 `withdrawal_credentials[12:]`. -/
def CREDENTIAL_ADDRESS_OFFSET : Nat := 12

/-- Capella:639 `to_execution_address` width: `1 + 11 + 20 = 32`. -/
def EXECUTION_ADDRESS_BYTES : Nat := 20

theorem credential_layout :
    1 + 11 + EXECUTION_ADDRESS_BYTES = CREDENTIAL_BYTES :=
  rfl

theorem address_slice_width :
    CREDENTIAL_ADDRESS_OFFSET + EXECUTION_ADDRESS_BYTES = CREDENTIAL_BYTES :=
  rfl

/-- Capella:454 `ExecutionAddress(validator.withdrawal_credentials[12:])`. -/
def credAddressBytes (bytes : List Nat) : List Nat :=
  bytes.drop CREDENTIAL_ADDRESS_OFFSET

theorem credAddressBytes_length {bytes : List Nat}
    (h : bytes.length = CREDENTIAL_BYTES) :
    (credAddressBytes bytes).length = EXECUTION_ADDRESS_BYTES := by
  simp [credAddressBytes, List.length_drop, h, CREDENTIAL_ADDRESS_OFFSET,
    CREDENTIAL_BYTES, EXECUTION_ADDRESS_BYTES]

/-- Capella:639 `ETH1_ADDRESS_WITHDRAWAL_PREFIX + b"\x00" * 11 + address`. -/
def eth1Credential (addr : List Nat) : List Nat :=
  ETH1_ADDRESS_WITHDRAWAL_PREFIX :: List.replicate 11 0 ++ addr

theorem eth1Credential_length (addr : List Nat) :
    (eth1Credential addr).length = 12 + addr.length := by
  simp [eth1Credential, List.length_cons]
  omega

theorem eth1Credential_hasEth1 (addr : List Nat) :
    hasEth1Bytes (eth1Credential addr) = true :=
  rfl

theorem eth1Credential_hasExecution (addr : List Nat) :
    hasExecutionBytes (eth1Credential addr) = true :=
  rfl

theorem eth1Credential_pad (addr : List Nat) :
    ((eth1Credential addr).drop 1).take 11 = List.replicate 11 0 := by
  unfold eth1Credential
  rw [List.cons_append, List.drop_succ_cons]
  have hlen : (List.replicate 11 0).length = 11 := List.length_replicate
  nth_rw 1 [← hlen]
  exact List.take_append_length

theorem credAddress_of_eth1 (addr : List Nat) :
    credAddressBytes (eth1Credential addr) = addr := by
  unfold credAddressBytes eth1Credential CREDENTIAL_ADDRESS_OFFSET
  rw [List.cons_append]
  change List.drop (11 + 1)
      (ETH1_ADDRESS_WITHDRAWAL_PREFIX :: (List.replicate 11 0 ++ addr)) = addr
  rw [List.drop_succ_cons]
  have hlen : (List.replicate 11 0).length = 11 := List.length_replicate
  nth_rw 1 [← hlen]
  exact List.drop_append_length

/-- Capella:454 vs a `[:20]` mutant of the address slice. -/
def sampleExecutionAddr : List Nat :=
  List.replicate EXECUTION_ADDRESS_BYTES 9

theorem cred_address_is_not_take20 :
    credAddressBytes (eth1Credential sampleExecutionAddr) ≠
      (eth1Credential sampleExecutionAddr).take 20 := by
  rw [credAddress_of_eth1]
  simp [eth1Credential, sampleExecutionAddr, EXECUTION_ADDRESS_BYTES,
    ETH1_ADDRESS_WITHDRAWAL_PREFIX]

/-- Capella:156 `ExecutionAddress` is 20 bytes = 160 bits. EvmYul
`AccountAddress.size` is that same width (Wheels.lean). -/
theorem executionAddress_bits :
    EXECUTION_ADDRESS_BYTES * 8 = 160 :=
  rfl

theorem accountAddress_size_eq : AccountAddress.size = 2 ^ 160 := by
  decide

theorem execution_address_width_matches :
    2 ^ (EXECUTION_ADDRESS_BYTES * 8) = AccountAddress.size := by
  rw [executionAddress_bits, accountAddress_size_eq]

theorem accountAddress_size_ne_u256 :
    AccountAddress.size ≠ UInt256.size := by
  decide

/-- Capella:454 big-endian integer of the 20-byte slice. -/
def bytesBeToNat : List Nat → Nat
  | [] => 0
  | b :: bs => (b % 256) * 256 ^ bs.length + bytesBeToNat bs

/-- Little-endian mutant of the same bytes. -/
def bytesLeToNat : List Nat → Nat
  | [] => 0
  | b :: bs => (b % 256) + 256 * bytesLeToNat bs

theorem bytesBeToNat_nil : bytesBeToNat [] = 0 :=
  rfl

theorem bytesLeToNat_nil : bytesLeToNat [] = 0 :=
  rfl

theorem bytesBeToNat_lt (bytes : List Nat) :
    bytesBeToNat bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil =>
    simp [bytesBeToNat]
  | cons b bs ih =>
    have hp : 0 < 256 := by decide
    have hb : b % 256 < 256 := Nat.mod_lt b hp
    have hpown : 256 ^ bs.length > 0 := Nat.pow_pos hp
    have hstep :
        (b % 256) * 256 ^ bs.length + bytesBeToNat bs <
          256 * 256 ^ bs.length := by
      have hadd :
          (b % 256) * 256 ^ bs.length + bytesBeToNat bs <
            (b % 256) * 256 ^ bs.length + 256 ^ bs.length :=
        Nat.add_lt_add_left ih _
      have hmul :
          (b % 256) * 256 ^ bs.length + 256 ^ bs.length =
            (b % 256 + 1) * 256 ^ bs.length := by
        rw [Nat.add_mul, Nat.one_mul]
      have hle :
          (b % 256 + 1) * 256 ^ bs.length ≤ 256 * 256 ^ bs.length :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hb)
      exact Nat.lt_of_lt_of_le (hmul ▸ hadd) hle
    simpa [bytesBeToNat, List.length_cons, Nat.pow_succ, Nat.mul_comm] using hstep

theorem two_pow_8_eq_256 : 2 ^ 8 = 256 :=
  rfl

theorem pow256_20_eq_two_pow_160 : 256 ^ 20 = 2 ^ 160 := by
  rw [← two_pow_8_eq_256, ← Nat.pow_mul]

def executionAddressNat (bytes : List Nat) : Nat :=
  bytesBeToNat (bytes.take EXECUTION_ADDRESS_BYTES)

theorem executionAddressNat_lt (bytes : List Nat) :
    executionAddressNat bytes < 2 ^ 160 := by
  have hlen : (bytes.take EXECUTION_ADDRESS_BYTES).length ≤ EXECUTION_ADDRESS_BYTES :=
    List.length_take_le _ _
  have hlt := bytesBeToNat_lt (bytes.take EXECUTION_ADDRESS_BYTES)
  have hpow : 256 ^ (bytes.take EXECUTION_ADDRESS_BYTES).length ≤ 256 ^ 20 :=
    Nat.pow_le_pow_right (by decide : 0 < 256) hlen
  have hbound : 256 ^ 20 = 2 ^ 160 := pow256_20_eq_two_pow_160
  exact Nat.lt_of_lt_of_le hlt (hpow.trans (Nat.le_of_eq hbound))

/-- Capella:454 `ExecutionAddress(...)` as EvmYul `AccountAddress`. -/
def executionAddress (bytes : List Nat) : AccountAddress :=
  AccountAddress.ofNat (executionAddressNat bytes)

theorem executionAddress_val_eq (bytes : List Nat) :
    (executionAddress bytes).val = executionAddressNat bytes := by
  unfold executionAddress AccountAddress.ofNat
  have hlt : executionAddressNat bytes < AccountAddress.size := by
    rw [accountAddress_size_eq]
    exact executionAddressNat_lt bytes
  exact Nat.mod_eq_of_lt hlt

/-- 20-byte `[1, 0, …, 0]`: BE is `256^19`, LE is `1`. -/
def sampleBeAddr : List Nat :=
  1 :: List.replicate 19 0

theorem bytesBeToNat_zeros (n : Nat) :
    bytesBeToNat (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [bytesBeToNat, List.replicate_succ, ih]

theorem bytesLeToNat_zeros (n : Nat) :
    bytesLeToNat (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [bytesLeToNat, List.replicate_succ, ih]

theorem sample_be_eq : bytesBeToNat sampleBeAddr = 256 ^ 19 := by
  simp [sampleBeAddr, bytesBeToNat]

theorem sample_le_eq : bytesLeToNat sampleBeAddr = 1 := by
  simp [sampleBeAddr, bytesLeToNat]

/-- A little-endian mutant of Capella:454 is not the archived address. -/
theorem execution_be_ne_le :
    bytesBeToNat sampleBeAddr ≠ bytesLeToNat sampleBeAddr := by
  rw [sample_be_eq, sample_le_eq]
  exact Nat.ne_of_gt (Nat.one_lt_pow (by decide : 19 ≠ 0) (by decide : 1 < 256))

theorem execution_width_ne_credential :
    EXECUTION_ADDRESS_BYTES ≠ CREDENTIAL_BYTES := by
  decide

/-- wrap of `2^160` as `AccountAddress` is 0, not the unbounded Nat. -/
theorem accountAddress_two_pow_wraps :
    (AccountAddress.ofNat (2 ^ 160)).val = 0 := by
  change 2 ^ 160 % AccountAddress.size = 0
  rw [accountAddress_size_eq]
  exact Nat.mod_self _

/-- Electra:1376 / 1384: maturity and eligibility are those two tests. -/
def electraPartialOf (v : ValidatorView) (item : Item) (balance epoch : Nat) :
    ElectraPartial where
  item := item
  mature := decide (v.withdrawableEpoch ≤ epoch)
  eligible := isEligibleForPartial v balance

theorem electraPartialOf_skips_exited {v : ValidatorView} {item : Item}
    {balance epoch : Nat} (h : v.exitEpoch ≠ FAR_FUTURE_EPOCH) :
    (electraPartialOf v item balance epoch).eligible = false :=
  isEligibleForPartial_rejects_exited h

/-- Electra:1378-1385: an ineligible mature entry is skipped, not appended. -/
theorem electraPartialLoop_skips_ineligible (limit prior : Nat)
    (c : ElectraPartial) (rest : List ElectraPartial)
    (hm : c.mature = true) (he : c.eligible = false)
    (hroom : ¬ limit ≤ prior) :
    electraPartialLoop limit prior (c::rest) =
      electraPartialLoop limit prior rest := by
  simp [electraPartialLoop, hm, he, hroom]

/-- Capella:411-421. `withdrawn` is the sum of prior amounts for this
validator. Lean Nat subtraction saturates; Python Gwei non-underflow
is the named `BalanceAfterFits`. -/
def withdrawnAmount (validatorIndex : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (idx, amt)::rest =>
    (if idx = validatorIndex then amt else 0) + withdrawnAmount validatorIndex rest

def balanceAfterWithdrawals (balance validatorIndex : Nat)
    (prior : List (Nat × Nat)) : Nat :=
  balance - withdrawnAmount validatorIndex prior

structure BalanceAfterFits (balance validatorIndex : Nat)
    (prior : List (Nat × Nat)) : Prop where
  le : withdrawnAmount validatorIndex prior ≤ balance

theorem balanceAfterWithdrawals_exact {balance validatorIndex : Nat}
    {prior : List (Nat × Nat)} (h : BalanceAfterFits balance validatorIndex prior) :
    balanceAfterWithdrawals balance validatorIndex prior +
      withdrawnAmount validatorIndex prior = balance :=
  Nat.sub_add_cancel h.le

/-- Capella:481 starts the prior list empty; withdrawn is 0 (411-420). -/
theorem withdrawnAmount_nil (idx : Nat) : withdrawnAmount idx [] = 0 :=
  rfl

theorem balanceAfterFits_nil (balance idx : Nat) :
    BalanceAfterFits balance idx [] where
  le := by simp [withdrawnAmount]

theorem balanceAfter_nil (balance idx : Nat) :
    balanceAfterWithdrawals balance idx [] = balance := by
  simp [balanceAfterWithdrawals, withdrawnAmount]

theorem withdrawnAmount_cons_eq {idx amt : Nat} (rest : List (Nat × Nat)) :
    withdrawnAmount idx ((idx, amt)::rest) = amt + withdrawnAmount idx rest := by
  simp [withdrawnAmount]

theorem withdrawnAmount_cons_ne {idx j amt : Nat} (rest : List (Nat × Nat))
    (h : j ≠ idx) :
    withdrawnAmount idx ((j, amt)::rest) = withdrawnAmount idx rest := by
  simp [withdrawnAmount, h]

/-- phase0:1606-1613 `decrease_balance`: saturate at 0 when `delta > balance`.
Gloas:1982-1983 names that saturation. Lean `Nat.sub` is the same function. -/
def decreaseBalance (balance delta : Nat) : Nat :=
  if delta > balance then 0 else balance - delta

theorem decreaseBalance_eq_sub (balance delta : Nat) :
    decreaseBalance balance delta = balance - delta := by
  unfold decreaseBalance
  split
  · next h =>
    exact (Nat.sub_eq_zero_of_le (Nat.le_of_lt h)).symm
  · rfl

/-- Gloas:1929 builder branch `balance -= min(amount, builder_balance)`. -/
theorem builder_min_eq_decrease (balance amt : Nat) :
    balance - min amt balance = decreaseBalance balance amt := by
  rw [decreaseBalance_eq_sub]
  by_cases h : amt ≤ balance
  · simp [min_eq_left h]
  · have hlt : balance < amt := Nat.lt_of_not_ge h
    have hmin : min amt balance = balance := min_eq_right (Nat.le_of_lt hlt)
    rw [hmin, Nat.sub_self, Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]

/-- Gloas:1926-1931: both the builder `min` path and `decrease_balance`
saturate; they agree with `Nat.sub`. -/
def applyOne (isBuilder : Bool) (balance amt : Nat) : Nat :=
  if isBuilder then balance - min amt balance else decreaseBalance balance amt

theorem applyOne_eq_sub (isBuilder : Bool) (balance amt : Nat) :
    applyOne isBuilder balance amt = balance - amt := by
  unfold applyOne
  split
  · exact (builder_min_eq_decrease balance amt).trans (decreaseBalance_eq_sub balance amt)
  · exact decreaseBalance_eq_sub balance amt

/-- phase0:473 `Gwei` is `uint64`. Capella:411-421 subtraction on that
type wraps. Lean `Nat.sub` saturates; this is the Python remainder,
not a second balance map. -/
def GWEI_MOD : Nat := 2 ^ 64

theorem GWEI_MOD_pos : 0 < GWEI_MOD := by
  decide

theorem GWEI_MOD_eq : GWEI_MOD = 2 ^ 64 :=
  rfl

def gweiWrapSub (balance withdrawn : Nat) : Nat :=
  (balance % GWEI_MOD + GWEI_MOD - withdrawn % GWEI_MOD) % GWEI_MOD

theorem gweiWrapSub_lt (balance withdrawn : Nat) :
    gweiWrapSub balance withdrawn < GWEI_MOD :=
  Nat.mod_lt _ GWEI_MOD_pos

/-- Under a `Uint64` balance and `withdrawn ≤ balance`, wrap agrees
with Lean `Nat.sub` / `decrease_balance`. -/
theorem gweiWrapSub_eq_sub {balance withdrawn : Nat}
    (hb : balance < GWEI_MOD) (hle : withdrawn ≤ balance) :
    gweiWrapSub balance withdrawn = balance - withdrawn := by
  have hw : withdrawn < GWEI_MOD := Nat.lt_of_le_of_lt hle hb
  simp only [gweiWrapSub, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hw]
  rw [Nat.add_comm balance GWEI_MOD, Nat.add_sub_assoc hle GWEI_MOD,
    Nat.add_comm GWEI_MOD (balance - withdrawn), Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hb)

/-- Capella:411-421 wrap when `withdrawn > balance`: the two's
complement borrow, not 0. Both operands are `Gwei` (`< 2^64`). -/
theorem gweiWrapSub_of_gt {balance withdrawn : Nat}
    (hb : balance < GWEI_MOD) (hw : withdrawn < GWEI_MOD)
    (hlt : balance < withdrawn) :
    gweiWrapSub balance withdrawn = GWEI_MOD - (withdrawn - balance) := by
  simp only [gweiWrapSub, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hw]
  have hdiff : balance + GWEI_MOD - withdrawn =
      GWEI_MOD - (withdrawn - balance) := by
    have hle : balance ≤ withdrawn := Nat.le_of_lt hlt
    have : withdrawn ≤ balance + GWEI_MOD :=
      Nat.le_trans (Nat.le_of_lt hw) (Nat.le_add_left GWEI_MOD balance)
    omega
  have hlt' : GWEI_MOD - (withdrawn - balance) < GWEI_MOD :=
    Nat.sub_lt GWEI_MOD_pos (Nat.sub_pos_of_lt hlt)
  rw [hdiff, Nat.mod_eq_of_lt hlt']

theorem gweiWrapSub_pos_of_gt {balance withdrawn : Nat}
    (hb : balance < GWEI_MOD) (hw : withdrawn < GWEI_MOD)
    (hlt : balance < withdrawn) :
    0 < gweiWrapSub balance withdrawn := by
  rw [gweiWrapSub_of_gt hb hw hlt]
  exact Nat.sub_pos_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hw)

/-- The finite kill-line `decrease_not_u64_wrap`: wrap of 5 − 7 is
`2^64-2`, not the saturating 0. -/
theorem gweiWrapSub_five_seven :
    gweiWrapSub 5 7 = GWEI_MOD - 2 :=
  gweiWrapSub_of_gt (by decide) (by decide) (by decide)

/-- Gloas:1982-1983 / phase0:1610-1613 saturate; Capella:411-421 wrap
does not. `BalanceAfterFits` is this disagreement. -/
theorem decreaseBalance_ne_gweiWrap {balance withdrawn : Nat}
    (hb : balance < GWEI_MOD) (hw : withdrawn < GWEI_MOD)
    (hlt : balance < withdrawn) :
    decreaseBalance balance withdrawn ≠ gweiWrapSub balance withdrawn := by
  have hsat : decreaseBalance balance withdrawn = 0 := by
    simp [decreaseBalance_eq_sub, Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]
  have hpos := gweiWrapSub_pos_of_gt hb hw hlt
  simp [hsat]
  exact Nat.ne_of_lt hpos

/-- Lean `get_balance_after_withdrawals` is `Nat.sub`. On excess it
is 0, not the Gwei wrap. -/
theorem balanceAfter_ne_wrap_of_gt {balance idx : Nat} {prior : List (Nat × Nat)}
    (hb : balance < GWEI_MOD)
    (hw : withdrawnAmount idx prior < GWEI_MOD)
    (hlt : balance < withdrawnAmount idx prior) :
    balanceAfterWithdrawals balance idx prior ≠
      gweiWrapSub balance (withdrawnAmount idx prior) := by
  have hsat : balanceAfterWithdrawals balance idx prior = 0 := by
    simp [balanceAfterWithdrawals, Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]
  have hpos := gweiWrapSub_pos_of_gt hb hw hlt
  simp [hsat]
  exact Nat.ne_of_lt hpos

/-- Under `BalanceAfterFits` and a `Uint64` balance, Capella:411-421
agrees with the Gwei wrap. -/
theorem balanceAfter_eq_wrap_of_fits {balance idx : Nat} {prior : List (Nat × Nat)}
    (hb : balance < GWEI_MOD)
    (h : BalanceAfterFits balance idx prior) :
    balanceAfterWithdrawals balance idx prior =
      gweiWrapSub balance (withdrawnAmount idx prior) := by
  simp [balanceAfterWithdrawals]
  exact (gweiWrapSub_eq_sub hb h.le).symm

/-- Dropping `BalanceAfterFits` from wrap agreement is refuted. -/
theorem gweiWrapSub_ne_sub_of_gt {balance withdrawn : Nat}
    (hb : balance < GWEI_MOD) (hw : withdrawn < GWEI_MOD)
    (hlt : balance < withdrawn) :
    gweiWrapSub balance withdrawn ≠ balance - withdrawn := by
  have hsat : balance - withdrawn = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)
  have hpos := gweiWrapSub_pos_of_gt hb hw hlt
  simp [hsat]
  exact Nat.ne_of_gt hpos

/-- Gloas:555 `BUILDER_INDEX_FLAG = Uint64(2**40)`. -/
def BUILDER_INDEX_FLAG : Nat := 2 ^ 40

theorem BUILDER_INDEX_FLAG_eq : BUILDER_INDEX_FLAG = 1099511627776 := by
  decide

/-- Gloas:1033-1034 `is_builder_index`: `(validator_index & FLAG) != 0`. -/
def isBuilderIndex (validatorIndex : Nat) : Bool :=
  decide ((validatorIndex &&& BUILDER_INDEX_FLAG) ≠ 0)

theorem isBuilderIndex_iff (v : Nat) :
    isBuilderIndex v = true ↔ (v &&& BUILDER_INDEX_FLAG) ≠ 0 := by
  simp [isBuilderIndex]

theorem isBuilderIndex_zero : isBuilderIndex 0 = false := by
  decide

theorem isBuilderIndex_flag : isBuilderIndex BUILDER_INDEX_FLAG = true := by
  decide

/-- Gloas:1134-1135 `validator_index & ~BUILDER_INDEX_FLAG`.
On `Nat` the bit-clear is `v - (v &&& FLAG)`. The 64-bit one's
complement is `builderFlagNotU64` (Python `Uint64(~FLAG)`); Lean
subtract disagrees after wrap when `v ≥ 2^64`. -/
def toBuilderIndex (validatorIndex : Nat) : Nat :=
  validatorIndex - (validatorIndex &&& BUILDER_INDEX_FLAG)

/-- Gloas:1127-1128 `builder_index | BUILDER_INDEX_FLAG`. -/
def toValidatorIndex (builderIndex : Nat) : Nat :=
  builderIndex ||| BUILDER_INDEX_FLAG

theorem toBuilderIndex_le (v : Nat) : toBuilderIndex v ≤ v :=
  Nat.sub_le _ _

theorem toBuilderIndex_zero : toBuilderIndex 0 = 0 := by
  decide

theorem toBuilderIndex_flag : toBuilderIndex BUILDER_INDEX_FLAG = 0 := by
  decide

theorem toValidatorIndex_zero :
    toValidatorIndex 0 = BUILDER_INDEX_FLAG := by
  decide

theorem BUILDER_INDEX_FLAG_testBit :
    BUILDER_INDEX_FLAG.testBit 40 = true := by
  decide

theorem land_lor_flag (b : Nat) :
    (b ||| BUILDER_INDEX_FLAG) &&& BUILDER_INDEX_FLAG = BUILDER_INDEX_FLAG := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_land, Nat.testBit_lor]
  cases hf : BUILDER_INDEX_FLAG.testBit j <;> simp [hf]

theorem toValidatorIndex_is_builder (b : Nat) :
    isBuilderIndex (toValidatorIndex b) = true := by
  rw [isBuilderIndex, toValidatorIndex, land_lor_flag]
  decide

/-- Gloas:1127-1128: a builder index below the flag is `b + 2^40`.
The `|` wrap when `b ≥ 2^40` remains named. -/
theorem or_flag_eq_add_of_lt {b : Nat} (h : b < BUILDER_INDEX_FLAG) :
    b ||| BUILDER_INDEX_FLAG = b + BUILDER_INDEX_FLAG := by
  have hadd : BUILDER_INDEX_FLAG + b = BUILDER_INDEX_FLAG ||| b := by
    simpa [BUILDER_INDEX_FLAG] using
      Nat.two_pow_add_eq_or_of_lt (i := 40) (by simpa [BUILDER_INDEX_FLAG] using h) 1
  rw [Nat.or_comm, Nat.add_comm]
  exact hadd.symm

/-- Gloas:1127-1128 then 1134-1135 on a flag-clear builder index. -/
theorem toBuilderIndex_toValidatorIndex_of_lt {b : Nat}
    (h : b < BUILDER_INDEX_FLAG) :
    toBuilderIndex (toValidatorIndex b) = b := by
  simp [toBuilderIndex, toValidatorIndex, land_lor_flag]
  rw [or_flag_eq_add_of_lt h, Nat.add_sub_cancel]

/-- Gloas:1127-1128. `FLAG | FLAG = FLAG`, not `FLAG + FLAG`.
`or_flag_eq_add_of_lt` needs `b < 2^40`. -/
theorem toValidatorIndex_flag :
    toValidatorIndex BUILDER_INDEX_FLAG = BUILDER_INDEX_FLAG := by
  simp [toValidatorIndex]

theorem toValidatorIndex_flag_ne_add :
    toValidatorIndex BUILDER_INDEX_FLAG ≠
      BUILDER_INDEX_FLAG + BUILDER_INDEX_FLAG := by
  rw [toValidatorIndex_flag]
  decide

/-- Convert-and-back is not the identity when bit 40 is already set. -/
theorem toBuilderIndex_toValidatorIndex_flag :
    toBuilderIndex (toValidatorIndex BUILDER_INDEX_FLAG) = 0 := by
  rw [toValidatorIndex_flag, toBuilderIndex_flag]

/-- A `Uint64` input stays a `Uint64` after Lean `||| FLAG`.
Python `Uint64 |` never sets bits ≥ 64: OR does not carry into bit 64.
Gloas:1127-1128. -/
theorem builder_flag_lt_u64 : BUILDER_INDEX_FLAG < 2 ^ 64 := by
  unfold BUILDER_INDEX_FLAG
  decide

theorem toValidatorIndex_lt_of_u64 {b : Nat} (h : b < 2 ^ 64) :
    toValidatorIndex b < 2 ^ 64 :=
  Nat.or_lt_two_pow h builder_flag_lt_u64

/-- Python `Uint64(builder_index) | FLAG` (Gloas:1127-1128). Lean
`toValidatorIndex` is unbounded `|||`. -/
def toValidatorIndexU64 (b : Nat) : Nat :=
  ((b % GWEI_MOD) ||| BUILDER_INDEX_FLAG) % GWEI_MOD

theorem toValidatorIndexU64_lt (b : Nat) :
    toValidatorIndexU64 b < 2 ^ 64 := by
  simpa [toValidatorIndexU64, GWEI_MOD] using
    Nat.mod_lt ((b % GWEI_MOD) ||| BUILDER_INDEX_FLAG) GWEI_MOD_pos

/-- Under a `Uint64` builder index the two conversions agree. -/
theorem toValidatorIndex_eq_u64_of_lt {b : Nat} (h : b < 2 ^ 64) :
    toValidatorIndex b = toValidatorIndexU64 b := by
  have hb : b % GWEI_MOD = b := Nat.mod_eq_of_lt (by simpa [GWEI_MOD] using h)
  have htagged : toValidatorIndex b < GWEI_MOD := by
    simpa [GWEI_MOD] using toValidatorIndex_lt_of_u64 h
  unfold toValidatorIndexU64 toValidatorIndex
  rw [hb]
  exact Eq.symm (Nat.mod_eq_of_lt htagged)

/-- Dropping `b < 2^64` is refuted: Lean `2^64 | 2^40` is `2^64+2^40`,
Python wrap is `2^40`. -/
theorem toValidatorIndex_two_pow :
    toValidatorIndex (2 ^ 64) = 2 ^ 64 + BUILDER_INDEX_FLAG := by
  have hor : 2 ^ 64 * 1 + BUILDER_INDEX_FLAG =
      2 ^ 64 * 1 ||| BUILDER_INDEX_FLAG :=
    Nat.two_pow_add_eq_or_of_lt (i := 64) builder_flag_lt_u64 1
  have hmul : 2 ^ 64 + BUILDER_INDEX_FLAG =
      2 ^ 64 ||| BUILDER_INDEX_FLAG := by
    simpa [Nat.mul_one] using hor
  simpa [toValidatorIndex] using hmul.symm

theorem toValidatorIndexU64_two_pow :
    toValidatorIndexU64 (2 ^ 64) = BUILDER_INDEX_FLAG := by
  unfold toValidatorIndexU64 GWEI_MOD BUILDER_INDEX_FLAG
  decide

theorem toValidatorIndex_two_pow_ne_u64 :
    toValidatorIndex (2 ^ 64) ≠ toValidatorIndexU64 (2 ^ 64) := by
  rw [toValidatorIndex_two_pow, toValidatorIndexU64_two_pow]
  decide

/-- Gloas:1926 uses `is_builder_index(withdrawal.validator_index)`, not a
free Boolean, to choose the builder `min` vs `decrease_balance` branch. -/
def applyOneFromIndex (validatorIndex balance amt : Nat) : Nat :=
  applyOne (isBuilderIndex validatorIndex) balance amt

theorem applyOneFromIndex_eq_sub (validatorIndex balance amt : Nat) :
    applyOneFromIndex validatorIndex balance amt = balance - amt :=
  applyOne_eq_sub _ _ _

/-- Named: `ValidatorIndex` / `BuilderIndex` are `Uint64`. Conversion
stays below `2^64` when the input does. `BuilderIndexFits.clear` /
`fits` are load-bearing: bit 40 already set is not `b + FLAG`, and
`b ≥ 2^64` is `toValidatorIndexU64`, not unbounded `|||`. -/
structure BuilderIndexFits (b : Nat) : Prop where
  clear : (b &&& BUILDER_INDEX_FLAG) = 0
  fits : b < 2 ^ 64

theorem builderIndexFits_flag :
    ¬ BuilderIndexFits BUILDER_INDEX_FLAG := by
  intro h
  have : BUILDER_INDEX_FLAG &&& BUILDER_INDEX_FLAG = 0 := h.clear
  have hzero : BUILDER_INDEX_FLAG = 0 := by simpa using this
  exact (by decide : BUILDER_INDEX_FLAG ≠ 0) hzero

theorem builderIndexFits_two_pow :
    ¬ BuilderIndexFits (2 ^ 64) := by
  intro h
  exact Nat.not_lt.mpr (Nat.le_refl _) h.fits

theorem toBuilderIndex_u64 {v : Nat} (h : v < 2 ^ 64) :
    toBuilderIndex v < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (toBuilderIndex_le v) h

/-- Python `Uint64(~BUILDER_INDEX_FLAG)` (Gloas:1134-1135). Lean `Nat`
has no width, so the complement is the 64-bit mask with bit 40 cleared. -/
def builderFlagNotU64 : Nat :=
  (GWEI_MOD - 1) ^^^ BUILDER_INDEX_FLAG

theorem builderFlagNotU64_lt : builderFlagNotU64 < 2 ^ 64 :=
  Nat.xor_lt_two_pow
    (Nat.sub_lt (by simpa [GWEI_MOD] using Nat.two_pow_pos 64)
      (by decide : (0 : Nat) < 1))
    builder_flag_lt_u64

theorem builderFlagNotU64_testBit_40 :
    builderFlagNotU64.testBit 40 = false := by
  unfold builderFlagNotU64 BUILDER_INDEX_FLAG GWEI_MOD
  decide

/-- Python `validator_index & ~FLAG` after both sides wrap to `Uint64`. -/
def toBuilderIndexU64 (v : Nat) : Nat :=
  (v % GWEI_MOD) &&& builderFlagNotU64

theorem toBuilderIndexU64_lt (v : Nat) :
    toBuilderIndexU64 v < 2 ^ 64 :=
  Nat.lt_of_le_of_lt Nat.and_le_right builderFlagNotU64_lt

theorem land_flag_eq_ite (v : Nat) :
    v &&& BUILDER_INDEX_FLAG =
      if v.testBit 40 then BUILDER_INDEX_FLAG else 0 := by
  by_cases hv : v.testBit 40
  · refine Nat.eq_of_testBit_eq fun j => ?_
    simp only [Nat.testBit_and, BUILDER_INDEX_FLAG, Nat.testBit_two_pow]
    by_cases hj : j = 40
    · subst hj; simp [hv]; decide
    · rw [if_pos hv, decide_eq_false (Ne.symm hj)]
      simp
      exact Nat.testBit_two_pow_of_ne (n := 40) (Ne.symm hj)
  · refine Nat.eq_of_testBit_eq fun j => ?_
    have hv' : v.testBit 40 = false := by
      cases ht : v.testBit 40
      · rfl
      · exact (hv ht).elim
    simp only [Nat.testBit_and, BUILDER_INDEX_FLAG, Nat.testBit_two_pow]
    by_cases hj : j = 40
    · subst hj; simp [hv']
    · simp [hv', show ¬ (40 = j) from Ne.symm hj]

theorem toBuilderIndex_of_clear_bit {v : Nat}
    (hv : v.testBit 40 = false) :
    toBuilderIndex v = v := by
  have hand : v &&& BUILDER_INDEX_FLAG = 0 := by
    rw [land_flag_eq_ite, if_neg (by simpa using hv)]
  simp [toBuilderIndex, hand]

theorem toBuilderIndex_of_flag_bit {v : Nat}
    (hv : v.testBit 40 = true) :
    toBuilderIndex v = v - BUILDER_INDEX_FLAG := by
  have hand : v &&& BUILDER_INDEX_FLAG = BUILDER_INDEX_FLAG := by
    rw [land_flag_eq_ite, if_pos hv]
  simp [toBuilderIndex, hand]

/-- Gloas:1134-1135. A set bit 40 splits as `q * 2^41 + 2^40 + r`. -/
theorem split_of_flag_bit {v : Nat} (hv : v.testBit 40 = true) :
    v = v / 2 ^ 41 * 2 ^ 41 + 2 ^ 40 + v % 2 ^ 40 := by
  have hbit : v / 2 ^ 40 % 2 = 1 := by
    simpa [Nat.testBit_eq_decide_div_mod_eq] using hv
  have hdd : v / 2 ^ 40 / 2 = v / 2 ^ 41 := by
    rw [Nat.div_div_eq_div_mul]
    rw [show 2 ^ 40 * 2 = 2 ^ 41 from (Nat.pow_succ 2 40).symm]
  have hdiv : v / 2 ^ 40 = 2 * (v / 2 ^ 41) + 1 := by
    have hmod := Nat.div_add_mod (v / 2 ^ 40) 2
    rw [hbit, hdd] at hmod
    exact hmod.symm
  have hmul : 2 ^ 40 * (2 * (v / 2 ^ 41)) = v / 2 ^ 41 * 2 ^ 41 := by
    rw [← Nat.mul_assoc, ← Nat.pow_succ, Nat.mul_comm]
  calc
    v = 2 ^ 40 * (v / 2 ^ 40) + v % 2 ^ 40 := (Nat.div_add_mod v (2 ^ 40)).symm
    _ = 2 ^ 40 * (2 * (v / 2 ^ 41) + 1) + v % 2 ^ 40 := by rw [hdiv]
    _ = 2 ^ 40 * (2 * (v / 2 ^ 41)) + 2 ^ 40 + v % 2 ^ 40 := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    _ = v / 2 ^ 41 * 2 ^ 41 + 2 ^ 40 + v % 2 ^ 40 := by rw [hmul]

theorem sub_two_pow_of_flag_bit {v : Nat} (hv : v.testBit 40 = true) :
    v - 2 ^ 40 = v / 2 ^ 41 * 2 ^ 41 + v % 2 ^ 40 := by
  have hsplit := split_of_flag_bit hv
  have hr : 2 ^ 40 ≤ 2 ^ 40 + v % 2 ^ 40 := Nat.le_add_right _ _
  nth_rw 1 [hsplit]
  rw [Nat.add_assoc, Nat.add_sub_assoc hr, Nat.add_comm (2 ^ 40),
    Nat.add_sub_cancel]

theorem testBit_high_of_flag {v j : Nat} (hj : 41 ≤ j) :
    v.testBit j = (v / 2 ^ 41).testBit (j - 41) := by
  have hpow : 2 ^ 41 * 2 ^ (j - 41) = 2 ^ j := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hj]
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    Nat.div_div_eq_div_mul, hpow]

theorem xor_two_pow_of_flag_bit {v : Nat} (hv : v.testBit 40 = true) :
    v ^^^ 2 ^ 40 = v / 2 ^ 41 * 2 ^ 41 + v % 2 ^ 40 := by
  have hlo : v % 2 ^ 40 < 2 ^ 40 := Nat.mod_lt _ (Nat.two_pow_pos 40)
  have hor :
      v / 2 ^ 41 * 2 ^ 41 + v % 2 ^ 40 =
        v / 2 ^ 41 * 2 ^ 41 ||| v % 2 ^ 40 := by
    have hx :=
      Nat.two_pow_add_eq_or_of_lt (i := 41)
        (Nat.lt_trans hlo (by decide : 2 ^ 40 < 2 ^ 41)) (v / 2 ^ 41)
    simpa [Nat.mul_comm] using hx
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_xor, hor, Nat.testBit_or, Nat.testBit_mul_two_pow]
  simp only [Nat.testBit_two_pow]
  by_cases hj : j = 40
  · subst hj
    have hlow : (v % 2 ^ 40).testBit 40 = false :=
      Nat.testBit_lt_two_pow hlo
    simp [hv]
    exact hlow
  · have hdec : decide (40 = j) = false := decide_eq_false (Ne.symm hj)
    simp [hdec]
    by_cases hj41 : 41 ≤ j
    · have hlow : (v % 2 ^ 40).testBit j = false :=
        Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le hlo
            (Nat.le_trans (Nat.le_of_lt (by decide : 2 ^ 40 < 2 ^ 41))
              (Nat.pow_le_pow_right (by decide) hj41)))
      have hvj := testBit_high_of_flag (v := v) hj41
      have hlow' :
          (v % 1099511627776).testBit j = false := hlow
      rw [hvj]
      simp [hj41, hlow']
    · have hj40 : j < 40 :=
        Nat.lt_of_le_of_ne
          (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hj41)) hj
      have hlow : (v % 2 ^ 40).testBit j = v.testBit j := by
        simpa [hj40] using Nat.testBit_mod_two_pow v 40 j
      simp [hj41]
      exact hlow.symm

/-- Load-bearing: a set bit 40 is cleared by XOR and by subtract. -/
theorem xor_flag_eq_sub_of_flag_bit {v : Nat}
    (hv : v.testBit 40 = true) :
    v ^^^ BUILDER_INDEX_FLAG = v - BUILDER_INDEX_FLAG := by
  simpa [BUILDER_INDEX_FLAG] using
    (xor_two_pow_of_flag_bit hv).trans (sub_two_pow_of_flag_bit hv).symm

theorem toBuilderIndexU64_of_lt {v : Nat} (h : v < 2 ^ 64) :
    toBuilderIndexU64 v =
      (v &&& (GWEI_MOD - 1)) ^^^ (v &&& BUILDER_INDEX_FLAG) := by
  have hmod : v % GWEI_MOD = v := Nat.mod_eq_of_lt (by simpa [GWEI_MOD] using h)
  simp [toBuilderIndexU64, builderFlagNotU64, hmod, Nat.and_xor_distrib_left]

/-- Flag-clear `Uint64` indices: Lean subtract is the identity and
matches Python `v & ~FLAG`. -/
theorem toBuilderIndex_eq_u64_of_clear {v : Nat}
    (h : v < 2 ^ 64) (hv : v.testBit 40 = false) :
    toBuilderIndex v = toBuilderIndexU64 v := by
  have hand64 : v &&& (GWEI_MOD - 1) = v := by
    simpa [GWEI_MOD] using
      Nat.and_two_pow_sub_one_of_lt_two_pow (n := 64) h
  have hflag : v &&& BUILDER_INDEX_FLAG = 0 := by
    rw [land_flag_eq_ite, if_neg (by simpa using hv)]
  rw [toBuilderIndex_of_clear_bit hv, toBuilderIndexU64_of_lt h, hand64, hflag]
  simp

/-- Under any `Uint64` validator index, Lean bit-clear agrees with
Python `v & ~FLAG`. The set-bit case uses `xor_flag_eq_sub_of_flag_bit`. -/
theorem toBuilderIndex_eq_u64_of_lt {v : Nat} (h : v < 2 ^ 64) :
    toBuilderIndex v = toBuilderIndexU64 v := by
  by_cases hv : v.testBit 40
  · have hand64 : v &&& (GWEI_MOD - 1) = v := by
      simpa [GWEI_MOD] using
        Nat.and_two_pow_sub_one_of_lt_two_pow (n := 64) h
    have hflag : v &&& BUILDER_INDEX_FLAG = BUILDER_INDEX_FLAG := by
      rw [land_flag_eq_ite, if_pos hv]
    rw [toBuilderIndex_of_flag_bit hv, toBuilderIndexU64_of_lt h, hand64, hflag]
    exact (xor_flag_eq_sub_of_flag_bit hv).symm
  · exact toBuilderIndex_eq_u64_of_clear h (by simpa using hv)

/-- Dropping `v < 2^64` is refuted: Lean `2^64 - (2^64 &&& FLAG)` is
`2^64`; Python wrap is `0 & ~FLAG = 0`. -/
theorem toBuilderIndex_two_pow :
    toBuilderIndex (2 ^ 64) = 2 ^ 64 := by
  unfold toBuilderIndex BUILDER_INDEX_FLAG
  decide

theorem toBuilderIndexU64_two_pow :
    toBuilderIndexU64 (2 ^ 64) = 0 := by
  unfold toBuilderIndexU64 GWEI_MOD builderFlagNotU64 BUILDER_INDEX_FLAG
  decide

theorem toBuilderIndex_two_pow_ne_u64 :
    toBuilderIndex (2 ^ 64) ≠ toBuilderIndexU64 (2 ^ 64) := by
  rw [toBuilderIndex_two_pow, toBuilderIndexU64_two_pow]
  decide

theorem toBuilderIndex_flag_eq_u64 :
    toBuilderIndex BUILDER_INDEX_FLAG = toBuilderIndexU64 BUILDER_INDEX_FLAG := by
  unfold toBuilderIndex toBuilderIndexU64 builderFlagNotU64 BUILDER_INDEX_FLAG GWEI_MOD
  decide

theorem toBuilderIndex_three_eq_u64 :
    toBuilderIndex 3 = toBuilderIndexU64 3 := by
  unfold toBuilderIndex toBuilderIndexU64 builderFlagNotU64 BUILDER_INDEX_FLAG GWEI_MOD
  decide


/-- Gloas:1923-1931. `state.builders` and `state.balances` are distinct
arrays. Bounds `builder_index < len(builders)` and
`validator_index < len(validators)` remain named. -/
structure DualBalances where
  validators : Nat → Nat
  builders : Nat → Nat

/-- Gloas:1927 converted builder key, else the raw validator index. -/
def writtenIndex (validatorIndex : Nat) : Nat :=
  if isBuilderIndex validatorIndex then toBuilderIndex validatorIndex
  else validatorIndex

theorem writtenIndex_builder {v : Nat} (h : isBuilderIndex v = true) :
    writtenIndex v = toBuilderIndex v := by
  simp [writtenIndex, h]

theorem writtenIndex_validator {v : Nat} (h : isBuilderIndex v = false) :
    writtenIndex v = v := by
  simp [writtenIndex, h]

theorem writtenIndex_of_builder {b : Nat} :
    writtenIndex (toValidatorIndex b) = toBuilderIndex (toValidatorIndex b) :=
  writtenIndex_builder (toValidatorIndex_is_builder b)

/-- Gloas:1927: the written builder key of a converted index below the
flag is the archived `builder_index`. -/
theorem writtenIndex_of_lt {b : Nat} (h : b < BUILDER_INDEX_FLAG) :
    writtenIndex (toValidatorIndex b) = b := by
  rw [writtenIndex_of_builder, toBuilderIndex_toValidatorIndex_of_lt h]

/-- Gloas:1926-1931. Python `state.builders[builder_index]` /
`state.balances[validator_index]` throw `IndexError` when the written
key is out of range. Lean `DualBalances` maps are total; this
predicate is that archived guard, not a second length premise. -/
def IndexInRange (nValidators nBuilders validatorIndex : Nat) : Prop :=
  if isBuilderIndex validatorIndex then
    toBuilderIndex validatorIndex < nBuilders
  else
    validatorIndex < nValidators

theorem indexInRange_builder {nv nb v : Nat} (h : isBuilderIndex v = true) :
    IndexInRange nv nb v ↔ toBuilderIndex v < nb := by
  simp [IndexInRange, h]

theorem indexInRange_validator {nv nb v : Nat} (h : isBuilderIndex v = false) :
    IndexInRange nv nb v ↔ v < nv := by
  simp [IndexInRange, h]

/-- Gloas:1826/1863 then 1927: a flag-clear `builder_index` writes
`state.builders[b]` only when `b < len(builders)`. -/
theorem indexInRange_toValidatorIndex {nv nb b : Nat}
    (hflag : b < BUILDER_INDEX_FLAG) (h : b < nb) :
    IndexInRange nv nb (toValidatorIndex b) := by
  simp [IndexInRange, toValidatorIndex_is_builder]
  rw [toBuilderIndex_toValidatorIndex_of_lt hflag]
  exact h

/-- One Gloas:1924-1931 iteration. The branch is `is_builder_index`,
not a free Boolean. Amount update is `applyOneFromIndex`. -/
def applyOneWithdrawal (s : DualBalances) (validatorIndex amt : Nat) :
    DualBalances :=
  if isBuilderIndex validatorIndex then
    { s with
      builders := fun j =>
        if j = toBuilderIndex validatorIndex then
          applyOneFromIndex validatorIndex
            (s.builders (toBuilderIndex validatorIndex)) amt
        else s.builders j }
  else
    { s with
      validators := fun j =>
        if j = validatorIndex then
          applyOneFromIndex validatorIndex (s.validators validatorIndex) amt
        else s.validators j }

theorem applyOneWithdrawal_builder_keeps_validators
    (s : DualBalances) (v amt : Nat) (h : isBuilderIndex v = true) :
    (applyOneWithdrawal s v amt).validators = s.validators := by
  simp [applyOneWithdrawal, h]

theorem applyOneWithdrawal_validator_keeps_builders
    (s : DualBalances) (v amt : Nat) (h : isBuilderIndex v = false) :
    (applyOneWithdrawal s v amt).builders = s.builders := by
  simp [applyOneWithdrawal, h]

theorem applyOneWithdrawal_builder_written
    (s : DualBalances) (v amt : Nat) (h : isBuilderIndex v = true) :
    (applyOneWithdrawal s v amt).builders (toBuilderIndex v) =
      s.builders (toBuilderIndex v) - amt := by
  simp [applyOneWithdrawal, h, applyOneFromIndex_eq_sub]

theorem applyOneWithdrawal_validator_written
    (s : DualBalances) (v amt : Nat) (h : isBuilderIndex v = false) :
    (applyOneWithdrawal s v amt).validators v =
      s.validators v - amt := by
  simp [applyOneWithdrawal, h, applyOneFromIndex_eq_sub]

theorem applyOneWithdrawal_builder_other
    (s : DualBalances) (v amt j : Nat)
    (h : isBuilderIndex v = true) (hne : j ≠ toBuilderIndex v) :
    (applyOneWithdrawal s v amt).builders j = s.builders j := by
  simp [applyOneWithdrawal, h, hne]

theorem applyOneWithdrawal_validator_other
    (s : DualBalances) (v amt j : Nat)
    (h : isBuilderIndex v = false) (hne : j ≠ v) :
    (applyOneWithdrawal s v amt).validators j = s.validators j := by
  simp [applyOneWithdrawal, h, hne]

/-- Gloas:1924 `for withdrawal in withdrawals`: every listed pair is
applied once, in list order. The write count is the list length. -/
def applyTagged (s : DualBalances) : List (Nat × Nat) → DualBalances
  | [] => s
  | (v, amt) :: rest => applyTagged (applyOneWithdrawal s v amt) rest

theorem applyTagged_nil (s : DualBalances) : applyTagged s [] = s :=
  rfl

theorem applyTagged_cons (s : DualBalances) (v amt : Nat)
    (rest : List (Nat × Nat)) :
    applyTagged s ((v, amt) :: rest) =
      applyTagged (applyOneWithdrawal s v amt) rest :=
  rfl

theorem applyTagged_singleton (s : DualBalances) (v amt : Nat) :
    applyTagged s [(v, amt)] = applyOneWithdrawal s v amt :=
  rfl

/-- Gloas:1924 is a left fold: every listed pair is applied once, in
order. The write count is `ws.length`, derived from that fold. -/
theorem applyTagged_foldl (s : DualBalances) (ws : List (Nat × Nat)) :
    applyTagged s ws =
      ws.foldl (fun acc p => applyOneWithdrawal acc p.1 p.2) s := by
  induction ws generalizing s with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨v, amt⟩ := p
    simp only [applyTagged, List.foldl]
    exact ih _

/-- Gloas:1924 is a list fold: concatenating two withdrawal lists is
sequential application, not a restart. -/
theorem applyTagged_append (s : DualBalances) (xs ys : List (Nat × Nat)) :
    applyTagged s (xs ++ ys) = applyTagged (applyTagged s xs) ys := by
  induction xs generalizing s with
  | nil =>
    rfl
  | cons p rest ih =>
    obtain ⟨v, amt⟩ := p
    simp only [List.cons_append, applyTagged]
    exact ih _

def decreaseAt (b : Nat → Nat) (idx amt : Nat) (j : Nat) : Nat :=
  if j = idx then decreaseBalance (b idx) amt else b j

/-- Capella:498-500 / Gloas:1931 validator branch: fold `decrease_balance`. -/
def applyWithdrawals (b : Nat → Nat) : List (Nat × Nat) → Nat → Nat
  | [], i => b i
  | (idx, amt)::rest, i => applyWithdrawals (decreaseAt b idx amt) rest i

theorem applyWithdrawals_nil (b : Nat → Nat) (i : Nat) :
    applyWithdrawals b [] i = b i :=
  rfl

/-- Validator branch of Gloas:1931 is the existing `decreaseAt` map. -/
theorem applyOneWithdrawal_validators_fn
    (s : DualBalances) (v amt : Nat) (h : isBuilderIndex v = false) :
    (applyOneWithdrawal s v amt).validators = decreaseAt s.validators v amt := by
  funext j
  by_cases hj : j = v
  · subst hj
    simp [applyOneWithdrawal, h, decreaseAt, applyOneFromIndex_eq_sub,
      decreaseBalance_eq_sub]
  · simp [applyOneWithdrawal, h, decreaseAt, hj]

/-- A validator-only payload is the Capella/phase0 fold. Builder
withdrawals are excluded by the archived predicate, not by an extra
filter premise. -/
theorem applyTagged_validators_only
    (s : DualBalances) (ws : List (Nat × Nat))
    (h : ∀ p ∈ ws, isBuilderIndex p.1 = false) (i : Nat) :
    (applyTagged s ws).validators i = applyWithdrawals s.validators ws i := by
  induction ws generalizing s with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨v, amt⟩ := p
    have hv : isBuilderIndex v = false :=
      h (v, amt) (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ q ∈ rest, isBuilderIndex q.1 = false :=
      fun q hq => h q (List.mem_cons.mpr (Or.inr hq))
    simp only [applyTagged, applyWithdrawals]
    have ih' := ih (applyOneWithdrawal s v amt) hrest
    rw [ih', applyOneWithdrawal_validators_fn s v amt hv]

/-- Gloas:1926-1927 builder branch: a payload of only flagged indices
leaves `state.balances` unchanged. -/
theorem applyTagged_builders_only
    (s : DualBalances) (ws : List (Nat × Nat))
    (h : ∀ p ∈ ws, isBuilderIndex p.1 = true) :
    (applyTagged s ws).validators = s.validators := by
  induction ws generalizing s with
  | nil =>
    rfl
  | cons p rest ih =>
    obtain ⟨v, amt⟩ := p
    have hv : isBuilderIndex v = true :=
      h (v, amt) (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ q ∈ rest, isBuilderIndex q.1 = true :=
      fun q hq => h q (List.mem_cons.mpr (Or.inr hq))
    simp only [applyTagged]
    rw [ih (applyOneWithdrawal s v amt) hrest,
      applyOneWithdrawal_builder_keeps_validators s v amt hv]

/-- Gloas:1931 validator branch: a payload of only unflagged indices
leaves `state.builders` unchanged. -/
theorem applyTagged_validators_keep_builders
    (s : DualBalances) (ws : List (Nat × Nat))
    (h : ∀ p ∈ ws, isBuilderIndex p.1 = false) :
    (applyTagged s ws).builders = s.builders := by
  induction ws generalizing s with
  | nil =>
    rfl
  | cons p rest ih =>
    obtain ⟨v, amt⟩ := p
    have hv : isBuilderIndex v = false :=
      h (v, amt) (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ q ∈ rest, isBuilderIndex q.1 = false :=
      fun q hq => h q (List.mem_cons.mpr (Or.inr hq))
    simp only [applyTagged]
    rw [ih (applyOneWithdrawal s v amt) hrest,
      applyOneWithdrawal_validator_keeps_builders s v amt hv]

/-- Gloas:1931. In-range validator writes never touch
`state.balances[j]` for `j ≥ len(validators)`. An out-of-range key
is Python `IndexError`; Lean keeps the incoming value. -/
theorem applyTagged_keeps_validator_oob
    (s : DualBalances) (ws : List (Nat × Nat)) (nv nb j : Nat)
    (hr : ∀ p ∈ ws, IndexInRange nv nb p.1) (hj : nv ≤ j) :
    (applyTagged s ws).validators j = s.validators j := by
  induction ws generalizing s with
  | nil =>
    rfl
  | cons p rest ih =>
    obtain ⟨v, amt⟩ := p
    have hv := hr (v, amt) (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ q ∈ rest, IndexInRange nv nb q.1 :=
      fun q hq => hr q (List.mem_cons.mpr (Or.inr hq))
    simp only [applyTagged]
    rw [ih (applyOneWithdrawal s v amt) hrest]
    cases hvb : isBuilderIndex v
    · have hlt : v < nv := by
        simp [IndexInRange, hvb] at hv
        exact hv
      have hne : j ≠ v := Nat.ne_of_gt (Nat.lt_of_lt_of_le hlt hj)
      exact applyOneWithdrawal_validator_other s v amt j hvb hne
    · exact congrFun
        (applyOneWithdrawal_builder_keeps_validators s v amt hvb) j

/-- Gloas:1927. In-range builder writes never touch
`state.builders[j]` for `j ≥ len(builders)`. -/
theorem applyTagged_keeps_builder_oob
    (s : DualBalances) (ws : List (Nat × Nat)) (nv nb j : Nat)
    (hr : ∀ p ∈ ws, IndexInRange nv nb p.1) (hj : nb ≤ j) :
    (applyTagged s ws).builders j = s.builders j := by
  induction ws generalizing s with
  | nil =>
    rfl
  | cons p rest ih =>
    obtain ⟨v, amt⟩ := p
    have hv := hr (v, amt) (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ q ∈ rest, IndexInRange nv nb q.1 :=
      fun q hq => hr q (List.mem_cons.mpr (Or.inr hq))
    simp only [applyTagged]
    rw [ih (applyOneWithdrawal s v amt) hrest]
    cases hvb : isBuilderIndex v
    · exact congrFun
        (applyOneWithdrawal_validator_keeps_builders s v amt hvb) j
    · have hlt : toBuilderIndex v < nb := by
        simp [IndexInRange, hvb] at hv
        exact hv
      have hne : j ≠ toBuilderIndex v :=
        Nat.ne_of_gt (Nat.lt_of_lt_of_le hlt hj)
      exact applyOneWithdrawal_builder_other s v amt j hvb hne

theorem applyOneWithdrawal_validators_eq_of_validators_eq
    (s t : DualBalances) (v amt : Nat)
    (h : isBuilderIndex v = false)
    (hv : s.validators = t.validators) :
    (applyOneWithdrawal s v amt).validators =
      (applyOneWithdrawal t v amt).validators := by
  simp [applyOneWithdrawal, h, hv]

theorem applyOneWithdrawal_builders_eq_of_builders_eq
    (s t : DualBalances) (v amt : Nat)
    (h : isBuilderIndex v = true)
    (hb : s.builders = t.builders) :
    (applyOneWithdrawal s v amt).builders =
      (applyOneWithdrawal t v amt).builders := by
  simp [applyOneWithdrawal, h, hb]

/-- Validator-only folds depend only on `state.balances`. -/
theorem applyTagged_validators_eq_of_validators_eq
    (s t : DualBalances) (ws : List (Nat × Nat))
    (h : ∀ p ∈ ws, isBuilderIndex p.1 = false)
    (hv : s.validators = t.validators) :
    (applyTagged s ws).validators = (applyTagged t ws).validators := by
  induction ws generalizing s t with
  | nil =>
    simpa [applyTagged] using hv
  | cons p rest ih =>
    obtain ⟨v, amt⟩ := p
    have hv0 : isBuilderIndex v = false :=
      h (v, amt) (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ q ∈ rest, isBuilderIndex q.1 = false :=
      fun q hq => h q (List.mem_cons.mpr (Or.inr hq))
    simp only [applyTagged]
    exact ih (applyOneWithdrawal s v amt) (applyOneWithdrawal t v amt) hrest
      (applyOneWithdrawal_validators_eq_of_validators_eq s t v amt hv0 hv)

/-- Builder-only folds depend only on `state.builders`. -/
theorem applyTagged_builders_eq_of_builders_eq
    (s t : DualBalances) (ws : List (Nat × Nat))
    (h : ∀ p ∈ ws, isBuilderIndex p.1 = true)
    (hb : s.builders = t.builders) :
    (applyTagged s ws).builders = (applyTagged t ws).builders := by
  induction ws generalizing s t with
  | nil =>
    simpa [applyTagged] using hb
  | cons p rest ih =>
    obtain ⟨v, amt⟩ := p
    have hv0 : isBuilderIndex v = true :=
      h (v, amt) (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ q ∈ rest, isBuilderIndex q.1 = true :=
      fun q hq => h q (List.mem_cons.mpr (Or.inr hq))
    simp only [applyTagged]
    exact ih (applyOneWithdrawal s v amt) (applyOneWithdrawal t v amt) hrest
      (applyOneWithdrawal_builders_eq_of_builders_eq s t v amt hv0 hb)

/-- Under `BalanceAfterFits`, the saturating fold equals Capella:411-421
(sum then subtract). The named wrap is only the case `withdrawn > balance`. -/
theorem apply_eq_balanceAfter {b : Nat → Nat} {ws : List (Nat × Nat)} {idx : Nat}
    (h : BalanceAfterFits (b idx) idx ws) :
    applyWithdrawals b ws idx = balanceAfterWithdrawals (b idx) idx ws := by
  induction ws generalizing b with
  | nil =>
    simp [applyWithdrawals, balanceAfterWithdrawals, withdrawnAmount]
  | cons p rest ih =>
    obtain ⟨j, amt⟩ := p
    by_cases hj : j = idx
    · have hsum : amt + withdrawnAmount idx rest ≤ b idx := by
        have hw : withdrawnAmount idx ((j, amt)::rest) =
            amt + withdrawnAmount idx rest := by
          rw [hj]; exact withdrawnAmount_cons_eq rest
        exact hw ▸ h.le
      have hrest : withdrawnAmount idx rest ≤ decreaseBalance (b idx) amt := by
        rw [decreaseBalance_eq_sub]
        exact Nat.le_sub_of_add_le (Nat.add_comm amt _ ▸ hsum)
      have hdec : decreaseAt b j amt idx = decreaseBalance (b idx) amt := by
        unfold decreaseAt
        rw [if_pos (Eq.symm hj), hj]
      have hf : BalanceAfterFits (decreaseAt b j amt idx) idx rest :=
        ⟨by rw [hdec]; exact hrest⟩
      have ih' := ih (b := decreaseAt b j amt) hf
      simp [applyWithdrawals]
      rw [ih', hdec, decreaseBalance_eq_sub]
      simp [balanceAfterWithdrawals, hj, withdrawnAmount]
      exact (Nat.sub_add_eq (b idx) amt (withdrawnAmount idx rest)).symm
    · have hrest : withdrawnAmount idx rest ≤ b idx := by
        have hw : withdrawnAmount idx ((j, amt)::rest) =
            withdrawnAmount idx rest := withdrawnAmount_cons_ne rest hj
        exact hw ▸ h.le
      have hdec : decreaseAt b j amt idx = b idx := by
        unfold decreaseAt
        exact if_neg (Ne.symm hj)
      have hf : BalanceAfterFits (decreaseAt b j amt idx) idx rest :=
        ⟨by rw [hdec]; exact hrest⟩
      have ih' := ih (b := decreaseAt b j amt) hf
      simp [applyWithdrawals]
      rw [ih', hdec]
      simp [balanceAfterWithdrawals, withdrawnAmount, hj]

/-- Lean `Nat.sub` is associative: the saturating fold equals the
sum-then-subtract read without `BalanceAfterFits`. That hypothesis
is only the Python wrap agreement. -/
theorem apply_eq_balanceAfter_sat (b : Nat → Nat) (ws : List (Nat × Nat))
    (idx : Nat) :
    applyWithdrawals b ws idx = balanceAfterWithdrawals (b idx) idx ws := by
  induction ws generalizing b with
  | nil =>
    simp [applyWithdrawals, balanceAfterWithdrawals, withdrawnAmount]
  | cons p rest ih =>
    obtain ⟨j, amt⟩ := p
    simp only [applyWithdrawals]
    rw [ih]
    by_cases hj : j = idx
    · have hdec : decreaseAt b j amt idx = b idx - amt := by
        simp [decreaseAt, hj, decreaseBalance_eq_sub]
      rw [hdec, hj]
      simp [balanceAfterWithdrawals, withdrawnAmount, Nat.sub_add_eq]
    · have hdec : decreaseAt b j amt idx = b idx := by
        simp [decreaseAt, Ne.symm hj]
      rw [hdec]
      simp [balanceAfterWithdrawals, withdrawnAmount, hj]

/-- Capella:498-500 fold equals the Gwei wrap only under
`BalanceAfterFits`. -/
theorem apply_eq_wrap_of_fits {b : Nat → Nat} {ws : List (Nat × Nat)}
    {idx : Nat} (hb : b idx < GWEI_MOD)
    (h : BalanceAfterFits (b idx) idx ws) :
    applyWithdrawals b ws idx = gweiWrapSub (b idx) (withdrawnAmount idx ws) := by
  rw [apply_eq_balanceAfter_sat, balanceAfter_eq_wrap_of_fits hb h]

/-- An excess singleton is saturating 0, not the wrap. -/
theorem apply_ne_wrap_of_gt {b : Nat → Nat} {idx amt : Nat}
    (hb : b idx < GWEI_MOD) (hw : amt < GWEI_MOD) (hlt : b idx < amt) :
    applyWithdrawals b [(idx, amt)] idx ≠ gweiWrapSub (b idx) amt := by
  have hlist : withdrawnAmount idx [(idx, amt)] = amt := by
    simp [withdrawnAmount]
  have hne := balanceAfter_ne_wrap_of_gt (prior := [(idx, amt)]) hb
    (hlist.symm ▸ hw) (hlist.symm ▸ hlt)
  rw [apply_eq_balanceAfter_sat]
  simpa [hlist] using hne

/-- Concrete Gwei domain: a `Uint64` balance stays a `Uint64` after a
fitting subtract (Capella:411-421 / phase0:473 `Gwei`). -/
theorem balanceAfter_u64 {balance idx : Nat} {prior : List (Nat × Nat)}
    (hb : balance < 2 ^ 64) :
    balanceAfterWithdrawals balance idx prior < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.sub_le _ _) hb

/-- Crediting the original balance as a full withdrawal zeros the remainder. -/
theorem balanceAfter_full {balance idx : Nat} :
    balanceAfterWithdrawals balance idx [(idx, balance)] = 0 := by
  simp [balanceAfterWithdrawals, withdrawnAmount]

/-- Electra:1429-1449 visit: the sweep Bool is the archived disjunction. -/
def electraValidatorVisit (v : ValidatorView) (item : Item) (balance epoch : Nat) :
    Item × Bool :=
  (item, validatorSweepEligible v balance epoch)

/-- Capella:144 `MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP = Uint64(2**14)` (= 16384). -/
def MAX_VALIDATORS_PER_SWEEP : Nat := 2 ^ 14

/-- Electra:1413 `min(len(state.validators), MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP)`. -/
def validatorsSweepLimit (n : Nat) : Nat :=
  min n MAX_VALIDATORS_PER_SWEEP

theorem validatorsSweepLimit_le_sweep (n : Nat) :
    validatorsSweepLimit n ≤ MAX_VALIDATORS_PER_SWEEP :=
  Nat.min_le_right _ _

theorem validatorsSweepLimit_le_registry (n : Nat) :
    validatorsSweepLimit n ≤ n :=
  Nat.min_le_left _ _

/-- Python `validator_index % len(state.validators)` (Electra:1451) and
`state.validators[validator_index]` (1427) require a nonempty registry
and a cursor in range. An empty list is `ZeroDivisionError` / `IndexError`. -/
structure SweepStart (n start : Nat) : Prop where
  registry : 0 < n
  inRange : start < n

/-- Electra:1451 `validator_index = (validator_index + 1) % len(state.validators)`. -/
def nextValidatorIndex (n i : Nat) : Nat := (i + 1) % n

theorem nextValidatorIndex_lt {n i : Nat} (h : 0 < n) :
    nextValidatorIndex n i < n :=
  Nat.mod_lt _ h

theorem nextValidatorIndex_wrap {n : Nat} (h : 0 < n) :
    nextValidatorIndex n (n - 1) = 0 := by
  have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel h
  simp [nextValidatorIndex, hsucc, Nat.mod_self]

/-- Lean `Nat.mod x 0 = x`. Python `x % 0` is `ZeroDivisionError`
(Electra:1451). This successor is not the archived remainder. -/
theorem nextValidatorIndex_of_zero (i : Nat) :
    nextValidatorIndex 0 i = i + 1 := by
  simp [nextValidatorIndex]

/-- `nextValidatorIndex_lt` needs `0 < n`. The empty-registry Lean
successor is never `< 0`. -/
theorem nextValidatorIndex_zero_not_bound (i : Nat) :
    ¬ nextValidatorIndex 0 i < 0 :=
  Nat.not_lt_zero _

theorem sweepStart_of_zero {start : Nat} : ¬ SweepStart 0 start := by
  intro h
  exact Nat.lt_irrefl 0 h.registry

/-- Electra:1420-1451: `fuel` successive indices from `start`. The
archived fuel is `validatorsSweepLimit n`, and the 16-withdrawal break
(1423-1425) only shortens the walk. -/
def visitRing (n start fuel : Nat) : List Nat :=
  match fuel with
  | 0 => []
  | fuel' + 1 => start :: visitRing n (nextValidatorIndex n start) fuel'

theorem visitRing_length (n start fuel : Nat) :
    (visitRing n start fuel).length = fuel := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih => simp [visitRing, nextValidatorIndex, ih]

theorem visitRing_pos (n start fuel : Nat) (h : 0 < fuel) :
    visitRing n start fuel =
      start :: visitRing n (nextValidatorIndex n start) (fuel - 1) := by
  cases fuel with
  | zero => exact (Nat.lt_irrefl 0 h).elim
  | succ fuel => rfl

theorem visitRing_start_mem (n start fuel : Nat) (h : 0 < fuel) :
    start ∈ visitRing n start fuel := by
  rw [visitRing_pos n start fuel h]
  exact List.mem_cons.mpr (Or.inl rfl)

/-- Electra:1451 on `len(validators) = 0`: Lean walks `start, start+1, …`
instead of raising. The walk is not a ring. -/
theorem visitRing_zero_succ (start fuel : Nat) :
    visitRing 0 start (fuel + 1) =
      start :: visitRing 0 (start + 1) fuel := by
  simp [visitRing, nextValidatorIndex]

theorem visitRing_zero_get (start fuel k : Nat) (hk : k < fuel) :
    (visitRing 0 start fuel)[k]? = some (start + k) := by
  induction fuel generalizing start k with
  | zero => exact (Nat.not_lt_zero k hk).elim
  | succ fuel ih =>
    cases k with
    | zero =>
      simp [visitRing, nextValidatorIndex]
    | succ k =>
      simp [visitRing, nextValidatorIndex]
      have hih := ih (start + 1) k (Nat.lt_of_succ_lt_succ hk)
      have : start + 1 + k = start + (k + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 k]
      simpa [this] using hih

theorem visitRing_zero_last (start fuel : Nat) (h : 0 < fuel) :
    start + (fuel - 1) ∈ visitRing 0 start fuel := by
  have hk : fuel - 1 < fuel := Nat.sub_lt h (by decide)
  have hg := visitRing_zero_get start fuel (fuel - 1) hk
  have hlen : fuel - 1 < (visitRing 0 start fuel).length := by
    rw [visitRing_length]
    exact hk
  rw [List.getElem?_eq_getElem hlen] at hg
  exact (Option.some.inj hg) ▸ List.getElem_mem hlen

theorem add_left_mod (n a b : Nat) : (a % n + b) % n = (a + b) % n := by
  have hdiv : n * (a / n) + a % n = a := Nat.div_add_mod a n
  have hsum : n * (a / n) + (a % n + b) = a + b := by
    rw [← Nat.add_assoc, hdiv]
  rw [← hsum]
  exact (Nat.mul_add_mod n (a / n) (a % n + b)).symm

theorem visitRing_get {n start fuel k : Nat}
    (h : SweepStart n start) (hk : k < fuel) :
    (visitRing n start fuel)[k]? = some ((start + k) % n) := by
  induction fuel generalizing start k with
  | zero => exact (Nat.not_lt_zero k hk).elim
  | succ fuel ih =>
    cases k with
    | zero =>
      simp [visitRing]
      exact (Nat.mod_eq_of_lt h.inRange).symm
    | succ k =>
      have hnext : SweepStart n (nextValidatorIndex n start) :=
        ⟨h.registry, nextValidatorIndex_lt h.registry⟩
      have hk' : k < fuel := Nat.lt_of_succ_lt_succ hk
      simp [visitRing]
      rw [ih hnext hk']
      simp [nextValidatorIndex]
      rw [Nat.add_assoc, Nat.add_comm 1 k]

theorem visitRing_mem {n start fuel i : Nat} (h : SweepStart n start)
    (hin : i ∈ visitRing n start fuel) :
    ∃ k < fuel, i = (start + k) % n := by
  induction fuel generalizing start i with
  | zero => cases hin
  | succ fuel ih =>
    simp [visitRing] at hin
    rcases hin with rfl | hin
    · exact ⟨0, Nat.succ_pos _, (Nat.mod_eq_of_lt h.inRange).symm⟩
    · have hnext : SweepStart n (nextValidatorIndex n start) :=
        ⟨h.registry, nextValidatorIndex_lt h.registry⟩
      obtain ⟨k, hk, hs⟩ := ih hnext hin
      refine ⟨k + 1, Nat.succ_lt_succ hk, ?_⟩
      rw [hs, nextValidatorIndex, add_left_mod, Nat.add_assoc, Nat.add_comm 1 k]

/-- A prefix of length `fuel ≤ n` of the modular walk is duplicate-free
(Electra:1421-1451 never revisits an index in one payload). -/
theorem visitRing_nodup {n start fuel : Nat}
    (h : SweepStart n start) (hfuel : fuel ≤ n) :
    (visitRing n start fuel).Nodup := by
  induction fuel generalizing start with
  | zero => simp [visitRing]
  | succ fuel ih =>
    refine List.nodup_cons.2 ⟨?_, ?_⟩
    · intro hin
      have hnext : SweepStart n (nextValidatorIndex n start) :=
        ⟨h.registry, nextValidatorIndex_lt h.registry⟩
      obtain ⟨k, hk, hs⟩ := visitRing_mem hnext hin
      have heq : start = (start + (k + 1)) % n := by
        calc start
            = (nextValidatorIndex n start + k) % n := hs
          _ = ((start + 1) % n + k) % n := by rw [nextValidatorIndex]
          _ = (start + 1 + k) % n := add_left_mod n (start + 1) k
          _ = (start + (k + 1)) % n := by rw [Nat.add_assoc, Nat.add_comm 1 k]
      have hmod : (start + (k + 1)) % n = start % n := by
        rw [← heq, Nat.mod_eq_of_lt h.inRange]
      have hzero : k + 1 ≡ 0 [MOD n] := Nat.ModEq.add_left_cancel' start hmod
      have hdvd : n ∣ k + 1 := (Nat.modEq_zero_iff_dvd).1 hzero
      have hlt : k + 1 < n :=
        Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hk) (Nat.lt_of_succ_le hfuel)
      exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos k) hlt hdvd
    · exact ih ⟨h.registry, nextValidatorIndex_lt h.registry⟩
        (Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self fuel)) hfuel)

theorem electraVisit_nodup {n start : Nat} (h : SweepStart n start) :
    (visitRing n start (validatorsSweepLimit n)).Nodup :=
  visitRing_nodup h (validatorsSweepLimit_le_registry n)

/-- Capella:516-528 `update_next_withdrawal_validator_index`. A full
16-withdrawal payload restarts after the last credited validator;
otherwise the cursor advances by the sweep cap from the original start. -/
def updateNextWithdrawalValidatorIndex (n start : Nat) (credited : List Nat) : Nat :=
  if credited.length = MAX_WITHDRAWALS_PER_PAYLOAD then
    match credited.getLast? with
    | some last => nextValidatorIndex n last
    | none => nextValidatorIndex n (start + MAX_VALIDATORS_PER_SWEEP - 1)
  else
    (start + MAX_VALIDATORS_PER_SWEEP) % n

theorem updateNext_partial {n start : Nat} {credited : List Nat}
    (h : credited.length ≠ MAX_WITHDRAWALS_PER_PAYLOAD) :
    updateNextWithdrawalValidatorIndex n start credited =
      (start + MAX_VALIDATORS_PER_SWEEP) % n := by
  simp [updateNextWithdrawalValidatorIndex, h]

theorem updateNext_full {n start last : Nat} {credited : List Nat}
    (hlen : credited.length = MAX_WITHDRAWALS_PER_PAYLOAD)
    (hlast : credited.getLast? = some last) :
    updateNextWithdrawalValidatorIndex n start credited =
      nextValidatorIndex n last := by
  simp [updateNextWithdrawalValidatorIndex, hlen, hlast]

/-- Capella:452/458, Electra:1388/1394/1432/1438, Gloas:1824/1830:
each credited withdrawal takes the running `withdrawal_index`, then
`withdrawal_index += 1`. -/
def indexSeq (start n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n' + 1 => start :: indexSeq (start + 1) n'

theorem indexSeq_length (start n : Nat) : (indexSeq start n).length = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [indexSeq, ih]

theorem indexSeq_lower (start n : Nat) : ∀ i ∈ indexSeq start n, start ≤ i := by
  induction n generalizing start with
  | zero => intro i hi; cases hi
  | succ n ih =>
    intro i hi
    simp [indexSeq] at hi
    cases hi with
    | inl heq => exact heq ▸ Nat.le_refl start
    | inr hi => exact Nat.le_trans (Nat.le_succ start) (ih (start + 1) i hi)

theorem indexSeq_succ_lt (start n : Nat) :
    ∀ i ∈ indexSeq (start + 1) n, start < i :=
  fun i hi => Nat.lt_of_succ_le (indexSeq_lower (start + 1) n i hi)

/-- Assigned indices are strictly increasing, hence Nodup. Uniqueness is
derived from the += 1, not assumed. -/
theorem indexSeq_pairwise (start n : Nat) :
    (indexSeq start n).Pairwise (· < ·) := by
  induction n generalizing start with
  | zero => simp [indexSeq]
  | succ n ih =>
    refine List.Pairwise.cons (indexSeq_succ_lt start n) (ih (start + 1))

theorem indexSeq_nodup (start n : Nat) : (indexSeq start n).Nodup :=
  (indexSeq_pairwise start n).imp (fun h => Nat.ne_of_lt h)

theorem indexSeq_append (s n m : Nat) :
    indexSeq s n ++ indexSeq (s + n) m = indexSeq s (n + m) := by
  induction n generalizing s with
  | zero => simp [indexSeq]
  | succ n ih =>
    have hshift : s + (n + 1) = s + 1 + n := by
      omega
    have hlen : n + 1 + m = n + m + 1 := by
      omega
    simp only [indexSeq, List.cons_append, hshift]
    rw [ih]
    simp [indexSeq, hlen]

/-- Capella:506-510 `update_next_withdrawal_index`. Empty keeps the
cursor; otherwise `last.index + 1`. -/
def updateNextWithdrawalIndex (start : Nat) (indices : List Nat) : Nat :=
  match indices.getLast? with
  | none => start
  | some last => last + 1

theorem updateNextWithdrawalIndex_empty (start : Nat) :
    updateNextWithdrawalIndex start [] = start :=
  rfl

theorem updateNextWithdrawalIndex_singleton (start last : Nat) :
    updateNextWithdrawalIndex start [last] = last + 1 :=
  rfl

theorem indexSeq_last {start n : Nat} (hn : 0 < n) :
    (indexSeq start n).getLast? = some (start + n - 1) := by
  induction n generalizing start with
  | zero => cases hn
  | succ n ih =>
    cases n with
    | zero => simp [indexSeq]
    | succ n =>
      have ih' : (indexSeq (start + 1) (n + 1)).getLast? =
          some (start + 1 + (n + 1) - 1) := ih (Nat.succ_pos n)
      have hcons : (indexSeq start (n + 2)).getLast? =
          (indexSeq (start + 1) (n + 1)).getLast? := by
        change (start :: indexSeq (start + 1) (n + 1)).getLast? = _
        cases h : indexSeq (start + 1) (n + 1) with
        | nil =>
          have hl := indexSeq_length (start + 1) (n + 1)
          rw [h] at hl
          cases hl
        | cons a t => simp [List.getLast?]
      rw [hcons, ih']
      congr 1
      omega

theorem updateNextWithdrawalIndex_seq {start n : Nat} (hn : 0 < n) :
    updateNextWithdrawalIndex start (indexSeq start n) = start + n := by
  unfold updateNextWithdrawalIndex
  rw [indexSeq_last hn]
  have hle : 1 ≤ start + n :=
    Nat.le_trans (Nat.succ_le_of_lt hn) (Nat.le_add_left n start)
  exact Nat.sub_add_cancel hle

/-- Two consecutive payloads (Capella:510 then 480) concatenate to one
`indexSeq`, so indices stay unique across the pair. -/
theorem indexSeq_pair_nodup (s n m : Nat) :
    (indexSeq s n ++ indexSeq (updateNextWithdrawalIndex s (indexSeq s n)) m).Nodup := by
  by_cases hn : n = 0
  · subst hn
    simp [indexSeq, updateNextWithdrawalIndex_empty]
    exact indexSeq_nodup s m
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [updateNextWithdrawalIndex_seq hpos, indexSeq_append]
    exact indexSeq_nodup s (n + m)

/-- Named Uint64 wrap of `WithdrawalIndex` (phase0:473 style). The
successor `last+1` is exact when `start + n < 2^64`. -/
structure WithdrawalIndexFits (start n : Nat) : Prop where
  fits : start + n < 2 ^ 64

theorem updateNextWithdrawalIndex_u64 {start n : Nat}
    (hn : 0 < n) (h : WithdrawalIndexFits start n) :
    updateNextWithdrawalIndex start (indexSeq start n) < 2 ^ 64 := by
  rw [updateNextWithdrawalIndex_seq hn]
  exact h.fits

/-- phase0:473 `WithdrawalIndex` is `uint64`. Capella:506-510
`last.index + 1` wraps on that type. Lean `Nat` successor does not. -/
def withdrawalIndexWrap (i : Nat) : Nat :=
  i % (2 ^ 64)

theorem withdrawalIndexWrap_lt (i : Nat) :
    withdrawalIndexWrap i < 2 ^ 64 :=
  Nat.mod_lt _ (by decide)

theorem withdrawalIndexWrap_eq_of_lt {i : Nat} (h : i < 2 ^ 64) :
    withdrawalIndexWrap i = i :=
  Nat.mod_eq_of_lt h

theorem withdrawalIndexWrap_two_pow :
    withdrawalIndexWrap (2 ^ 64) = 0 := by
  simp [withdrawalIndexWrap]

/-- Assigned indices sit in `[start, start+n)`. -/
theorem indexSeq_upper (start n : Nat) :
    ∀ i ∈ indexSeq start n, i < start + n := by
  induction n generalizing start with
  | zero =>
    intro i hi
    cases hi
  | succ n ih =>
    intro i hi
    simp [indexSeq] at hi
    cases hi with
    | inl heq =>
      subst heq
      exact Nat.lt_add_of_pos_right (Nat.succ_pos _)
    | inr hi =>
      have hlt := ih (start + 1) i hi
      have : start + 1 + n = start + (n + 1) := by
        omega
      exact this ▸ hlt

theorem indexSeq_lt_of_fits {start n i : Nat}
    (h : WithdrawalIndexFits start n) (hi : i ∈ indexSeq start n) :
    i < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (indexSeq_upper start n i hi) (Nat.le_of_lt h.fits)

/-- Under `WithdrawalIndexFits` the Lean list is already `Uint64`;
wrap is the identity. -/
theorem indexSeq_eq_wrap_of_fits {start n : Nat}
    (h : WithdrawalIndexFits start n) :
    (indexSeq start n).map withdrawalIndexWrap = indexSeq start n := by
  induction n generalizing start with
  | zero =>
    simp [indexSeq]
  | succ n ih =>
    have hhead : start < 2 ^ 64 :=
      indexSeq_lt_of_fits h (List.mem_cons.mpr (Or.inl rfl))
    have hrest : WithdrawalIndexFits (start + 1) n :=
      ⟨by
        have := h.fits
        omega⟩
    simp [indexSeq, withdrawalIndexWrap_eq_of_lt hhead, ih hrest]

/-- Capella:506-510. The Lean cursor is `start+n`. Python wrap equals
that cursor only under `WithdrawalIndexFits`. -/
theorem updateNext_eq_wrap_of_fits {start n : Nat} (hn : 0 < n)
    (h : WithdrawalIndexFits start n) :
    updateNextWithdrawalIndex start (indexSeq start n) =
      withdrawalIndexWrap (start + n) := by
  rw [updateNextWithdrawalIndex_seq hn, withdrawalIndexWrap_eq_of_lt h.fits]

/-- Dropping `WithdrawalIndexFits` from cursor wrap agreement is
refuted: Lean `start+n` is not `(start+n) % 2^64`. -/
theorem updateNext_ne_wrap_of_ge {start n : Nat} (hn : 0 < n)
    (hge : 2 ^ 64 ≤ start + n) :
    updateNextWithdrawalIndex start (indexSeq start n) ≠
      withdrawalIndexWrap (start + n) := by
  rw [updateNextWithdrawalIndex_seq hn]
  intro heq
  have hw := withdrawalIndexWrap_lt (start + n)
  rw [← heq] at hw
  exact Nat.not_le.mpr hw hge

/-- Capella:506-510 on the last `Uint64` index: Lean next is `2^64`,
Python wrap is 0. -/
theorem updateNext_last_u64_is_two_pow :
    updateNextWithdrawalIndex (2 ^ 64 - 1) (indexSeq (2 ^ 64 - 1) 1) =
      2 ^ 64 := by
  rw [updateNextWithdrawalIndex_seq (by decide)]
  omega

theorem updateNext_last_u64_ne_wrap :
    updateNextWithdrawalIndex (2 ^ 64 - 1) (indexSeq (2 ^ 64 - 1) 1) ≠
      withdrawalIndexWrap (2 ^ 64) := by
  rw [updateNext_last_u64_is_two_pow, withdrawalIndexWrap_two_pow]
  decide

/-- Lean assigns `2^64` as the second index; the wrap is 0. Nat
uniqueness of `indexSeq` is not this list. -/
theorem indexSeq_last_u64_pair :
    indexSeq (2 ^ 64 - 1) 2 = [2 ^ 64 - 1, 2 ^ 64] := by
  simp [indexSeq]

theorem indexSeqWrap_last_u64_pair :
    (indexSeq (2 ^ 64 - 1) 2).map withdrawalIndexWrap =
      [2 ^ 64 - 1, 0] := by
  simp [indexSeq, withdrawalIndexWrap]

theorem indexSeq_last_u64_ne_wrap_list :
    indexSeq (2 ^ 64 - 1) 2 ≠
      (indexSeq (2 ^ 64 - 1) 2).map withdrawalIndexWrap := by
  conv => lhs; rw [indexSeq_last_u64_pair]
  rw [indexSeqWrap_last_u64_pair]
  decide

theorem withdrawalIndexFits_rejects_last_u64_two :
    ¬ WithdrawalIndexFits (2 ^ 64 - 1) 2 := by
  intro h
  have : (2 ^ 64 - 1) + 2 < 2 ^ 64 := h.fits
  omega

/-- The withdrawal inputs of one accepted Gloas block. `parentFull` is the
line-1999 test. `pending` and `builders` are the archived Gloas loop inputs.
`pendingPartial` / `validators` may still be supplied directly; `blockOfElectra`
derives them from the Electra loops so `partialBound` / `validatorsGuard`
are not extra premises. -/
structure Block where
  slot : U64
  parentFull : Bool
  pending : List Item
  pendingPartial : List Item
  partialBound : (queueStage 15 0 pending).length + pendingPartial.length ≤ 15
  builders : List (Item × Bool)
  validators : List Item
  validatorsGuard : GuardedAdds 16
    ((queueStage 15 0 pending).length + pendingPartial.length +
      (sweepStage 15 ((queueStage 15 0 pending).length + pendingPartial.length) builders).length)
    validators

def builderPending (b : Block) : List Item := queueStage 15 0 b.pending

def builderSweep (b : Block) : List Item :=
  sweepStage 15 ((builderPending b).length + b.pendingPartial.length) b.builders

/-- Gloas:1879-1916 concatenation order. -/
def expected (b : Block) : List Item :=
  builderPending b ++ b.pendingPartial ++ builderSweep b ++ b.validators

theorem partial_prior (b : Block) : (builderPending b).length + b.pendingPartial.length ≤ 15 :=
  b.partialBound

def expectedPayload (b : Block) : Payload :=
  gloasPayload b.slot (builderPending b) b.pendingPartial (builderSweep b) b.validators
    (queueStage_guarded 15 b.pending 0 (Nat.zero_le 15))
    (guarded_of_length 15 b.pendingPartial _ b.partialBound)
    (sweepStage_guarded 15 b.builders _ (partial_prior b)) b.validatorsGuard

/-- Gloas builder stages cap the first three lists at 15, so Electra:1416
`len(prior) < 16` holds for the validator sweep. -/
theorem validators_prior_lt_16 (b : Block) :
    (builderPending b).length + b.pendingPartial.length + (builderSweep b).length < 16 := by
  have hcomb := sweepStage_combined 15
    ((builderPending b).length + b.pendingPartial.length) b.builders (partial_prior b)
  simpa only [builderSweep] using Nat.lt_of_le_of_lt hcomb (by decide : (15 : Nat) < 16)

/-- Electra:1360-1398 / 1407-1454 plus Gloas:1805-1873. The two Block
guard fields are produced, not assumed. -/
def blockOfElectra (slot : U64) (parentFull : Bool)
    (pending : List Item) (partials : List ElectraPartial)
    (builders validators : List (Item × Bool)) : Block :=
  let first := queueStage 15 0 pending
  let partialItems := electraPartials first.length partials
  let prior := first.length + partialItems.length
  let sweep := sweepStage 15 prior builders
  { slot := slot
    parentFull := parentFull
    pending := pending
    pendingPartial := partialItems
    partialBound := by
      have hfirst := guarded_length (queueStage_guarded 15 pending 0 (Nat.zero_le 15))
      exact (electraPartials_bound first.length partials
        (by simpa [first] using hfirst)).1
    builders := builders
    validators := sweepStage 16 (prior + sweep.length) validators
    validatorsGuard := by
      have hfirst := guarded_length (queueStage_guarded 15 pending 0 (Nat.zero_le 15))
      have hpartial := (electraPartials_bound first.length partials
        (by simpa [first] using hfirst)).1
      have hsweep := sweepStage_combined 15 prior builders
        (by simpa [prior, first] using hpartial)
      have hroom : prior + sweep.length < 16 :=
        Nat.lt_of_le_of_lt hsweep (by decide : (15 : Nat) < 16)
      exact electraValidators_guarded (prior + sweep.length) validators hroom }

theorem blockOfElectra_slot (slot : U64) (parentFull : Bool)
    (pending : List Item) (partials : List ElectraPartial)
    (builders validators : List (Item × Bool)) :
    (blockOfElectra slot parentFull pending partials builders validators).slot = slot :=
  rfl

/-- Gloas:1999 early return: an empty parent contributes no item at this block. -/
def items (b : Block) : List Item := if b.parentFull then expected b else []

def payload (b : Block) : Payload :=
  if b.parentFull then expectedPayload b else ⟨b.slot,[],by simp⟩

theorem payload_slot (b : Block) : (payload b).slot = b.slot := by
  unfold payload; split <;> rfl

theorem payload_items (b : Block) : (payload b).items = items b := by
  unfold payload items; split <;> rfl

theorem items_bounded (b : Block) : (items b).length ≤ 16 := by
  rw [←payload_items]; exact (payload b).bounded

theorem items_empty (b : Block) (h : b.parentFull = false) : items b = [] := by
  simp [items,h]

theorem payload_slots (blocks : List Block) :
    (blocks.map payload).map (·.slot) = blocks.map (·.slot) := by
  induction blocks with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons,payload_slot,ih]

theorem payload_flat (blocks : List Block) :
    (blocks.map payload).flatMap (·.items) = blocks.flatMap items := by
  induction blocks with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons,List.flatMap_cons,payload_items,ih]

theorem total_items (blocks : List Block) :
    totalItems (blocks.map payload) = (blocks.map (fun b => (items b).length)).sum := by
  induction blocks with
  | nil => rfl
  | cons b bs ih =>
    simp only [totalItems,List.map_cons,List.sum_cons,payload_items] at ih ⊢
    exact congrArg ((items b).length + ·) ih

/-- Blocks accepted consecutively under the archived slot guards. -/
abbrev AcceptedBlocks (pre : Clock) (blocks : List Block) (post : Clock) : Prop :=
  Accepted pre (blocks.map (·.slot)) post

theorem accepted_nodup {pre post : Clock} {blocks : List Block}
    (h : AcceptedBlocks pre blocks post) : ((blocks.map payload).map (·.slot)).Nodup := by
  rw [payload_slots]; exact ProtocolSlotExtraction.accepted_nodup h

/-- The consumer's slot Nodup premise is discharged from the guards; the count
bound is the consumer's own `total_count`. -/
theorem total_count {pre post : Clock} (blocks : List Block)
    (h : AcceptedBlocks pre blocks post) :
    (blocks.map (fun b => (items b).length)).sum ≤ 16*2^64 := by
  rw [←total_items]
  exact ProtocolWithdrawalCount.total_count (blocks.map payload) (accepted_nodup h)

/-- Raw Electra/Gloas loop inputs. No `partialBound` / `validatorsGuard`. -/
structure ElectraInputs where
  slot : U64
  parentFull : Bool
  pending : List Item
  partials : List ElectraPartial
  builders : List (Item × Bool)
  validators : List (Item × Bool)

def ElectraInputs.block (i : ElectraInputs) : Block :=
  blockOfElectra i.slot i.parentFull i.pending i.partials i.builders i.validators

theorem electraInputs_slot (i : ElectraInputs) : i.block.slot = i.slot := rfl

theorem electraInputs_items_bounded (i : ElectraInputs) :
    (items i.block).length ≤ 16 :=
  items_bounded i.block

/-- Accepted slots discharge Nodup; Electra/Gloas loops produce the lists. -/
theorem total_count_from_electra {pre post : Clock} (inputs : List ElectraInputs)
    (h : Accepted pre (inputs.map (·.slot)) post) :
    (inputs.map (fun i => (items i.block).length)).sum ≤ 16 * 2^64 := by
  have hab : AcceptedBlocks pre (inputs.map ElectraInputs.block) post := by
    simpa [AcceptedBlocks, List.map_map, Function.comp_def, electraInputs_slot] using h
  simpa [List.map_map, Function.comp_def] using total_count _ hab

/-- Sharper finite form: sixteen per accepted block and at most 2^64 blocks. -/
theorem total_blocks {pre post : Clock} (blocks : List Block)
    (h : AcceptedBlocks pre blocks post) :
    (blocks.map (fun b => (items b).length)).sum ≤ 16*blocks.length ∧ blocks.length ≤ 2^64 := by
  refine ⟨?_,projected_count (fun b : Block => b.slot) blocks h⟩
  rw [←total_items]
  have hp := per_payload_sum (blocks.map payload)
  simpa only [List.length_map] using hp

/-- Literal dispatch of every accepted block's items, in acceptance order,
composed with the derived slot facts and the independent PoW/migration inputs. -/
theorem dispatched_counts {initial before after : AccountMap .EVM} {p s c : Nat}
    {pre post : Clock} (prior : Ledger initial p 0 s c before) (blocks : List Block)
    (h : AcceptedBlocks pre blocks post)
    (run : Dispatch before (blocks.flatMap items) after)
    (powBound : p ≤ 2^64) (migrationConserving : s=0) :
    Ledger initial p ((blocks.map (fun b => (items b).length)).sum) s
        (c+credits (blocks.flatMap items)) after ∧
      Counts p ((blocks.map (fun b => (items b).length)).sum) s := by
  rw [←total_items,←payload_flat]
  rw [←payload_flat] at run
  exact ProtocolWithdrawalCount.dispatched_counts prior (blocks.map payload) run
    (accepted_nodup h) powBound migrationConserving

/-- Capella `Withdrawal.index` (Capella:196-204) assigned by the running
cursor. Address/amount stay on `Item`; `validator_index` is the sweep
cursor already extracted above. -/
structure IndexedWithdrawal where
  index : Nat
  item : Item

/-- Capella:452/458, Electra:1388/1394/1432/1438, Gloas:1824/1830:
`Withdrawal(index=withdrawal_index, ...)` then `withdrawal_index += 1`. -/
def indexedWithdrawals (start : Nat) : List Item → List IndexedWithdrawal
  | [] => []
  | w :: ws => { index := start, item := w } :: indexedWithdrawals (start + 1) ws

theorem indexedWithdrawals_indices (start : Nat) (ws : List Item) :
    (indexedWithdrawals start ws).map (fun w => w.index) =
      indexSeq start ws.length := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [indexedWithdrawals, List.map_cons, List.length_cons]
    change start :: (indexedWithdrawals (start + 1) ws).map (fun w => w.index) =
      start :: indexSeq (start + 1) ws.length
    exact congrArg (List.cons start) (ih (start + 1))

theorem indexedWithdrawals_items (start : Nat) (ws : List Item) :
    (indexedWithdrawals start ws).map (fun w => w.item) = ws := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [indexedWithdrawals, List.map_cons]
    exact congrArg (List.cons w) (ih (start + 1))

/-- Uniqueness of assigned indices is the successor `indexSeq`, not an
extra Nodup premise. -/
theorem indexedWithdrawals_nodup (start : Nat) (ws : List Item) :
    ((indexedWithdrawals start ws).map (fun w => w.index)).Nodup := by
  rw [indexedWithdrawals_indices]
  exact indexSeq_nodup start ws.length

/-- Capella:506-510 `update_next_withdrawal_index` applied to the indices
just produced. Empty keeps the cursor; otherwise `last.index + 1`. -/
def nextIndexAfter (start : Nat) (ws : List Item) : Nat :=
  updateNextWithdrawalIndex start
    ((indexedWithdrawals start ws).map (fun w => w.index))

theorem nextIndexAfter_nil (start : Nat) : nextIndexAfter start [] = start := by
  simp [nextIndexAfter, indexedWithdrawals, updateNextWithdrawalIndex]

theorem nextIndexAfter_eq (start : Nat) (ws : List Item) :
    nextIndexAfter start ws = start + ws.length := by
  unfold nextIndexAfter
  rw [indexedWithdrawals_indices]
  cases ws with
  | nil => simp [indexSeq, updateNextWithdrawalIndex]
  | cons w ws => exact updateNextWithdrawalIndex_seq (Nat.succ_pos _)

/-- Capella:480 then 510 across accepted payloads. An empty `items`
(Gloas:1999 early return, or Capella:508 empty list) consumes no index. -/
def indexedChain (start : Nat) : List Block → List IndexedWithdrawal
  | [] => []
  | b :: bs =>
      indexedWithdrawals start (items b) ++
        indexedChain (nextIndexAfter start (items b)) bs

theorem indexedChain_items (start : Nat) (bs : List Block) :
    (indexedChain start bs).map (fun w => w.item) = bs.flatMap items := by
  induction bs generalizing start with
  | nil => rfl
  | cons b bs ih =>
    simp only [indexedChain, List.map_append, List.flatMap_cons]
    rw [indexedWithdrawals_items, ih]

theorem indexedChain_indices (start : Nat) (bs : List Block) :
    (indexedChain start bs).map (fun w => w.index) =
      indexSeq start ((bs.map (fun b => (items b).length)).sum) := by
  induction bs generalizing start with
  | nil => simp [indexedChain, indexSeq]
  | cons b bs ih =>
    simp only [indexedChain, List.map_append, List.map_cons, List.sum_cons]
    rw [indexedWithdrawals_indices, nextIndexAfter_eq, ih]
    exact indexSeq_append start (items b).length _

/-- Withdrawal-index uniqueness across a block sequence is derived from
`+= 1` (Capella:458 then 510), independently of beacon-slot Nodup. -/
theorem indexedChain_nodup (start : Nat) (bs : List Block) :
    ((indexedChain start bs).map (fun w => w.index)).Nodup := by
  rw [indexedChain_indices]
  exact indexSeq_nodup start _

theorem indexedChain_length (start : Nat) (bs : List Block) :
    (indexedChain start bs).length =
      (bs.map (fun b => (items b).length)).sum := by
  have h := congrArg List.length (indexedChain_indices start bs)
  simpa [List.length_map, indexSeq_length] using h

/-- The consumer count bound is the length of the unique index sequence. -/
theorem indexed_total_count {pre post : Clock} (start : Nat)
    (blocks : List Block) (h : AcceptedBlocks pre blocks post) :
    (indexedChain start blocks).length ≤ 16 * 2 ^ 64 := by
  rw [indexedChain_length]
  exact total_count blocks h

/-- `Dispatch` of the indexed items is `Dispatch` of `flatMap items`.
The consumer premise is that zip, not a renamed copy of it. -/
theorem dispatch_of_indexed {before after : AccountMap .EVM} {start : Nat}
    {bs : List Block}
    (run : Dispatch before ((indexedChain start bs).map (fun w => w.item)) after) :
    Dispatch before (bs.flatMap items) after := by
  rwa [indexedChain_items] at run

/-- Slot Nodup from `AcceptedBlocks`; item list and count from the
derived `indexedChain`. -/
theorem dispatched_counts_from_indexed {initial before after : AccountMap .EVM}
    {p s c start : Nat} {pre post : Clock}
    (prior : Ledger initial p 0 s c before) (blocks : List Block)
    (h : AcceptedBlocks pre blocks post)
    (run : Dispatch before ((indexedChain start blocks).map (fun w => w.item)) after)
    (powBound : p ≤ 2 ^ 64) (migrationConserving : s = 0) :
    Ledger initial p (indexedChain start blocks).length s
        (c + credits ((indexedChain start blocks).map (fun w => w.item))) after ∧
      Counts p (indexedChain start blocks).length s := by
  have hitems := indexedChain_items start blocks
  have hlen := indexedChain_length start blocks
  rw [hitems] at run
  have hdc := dispatched_counts prior blocks h run powBound migrationConserving
  rwa [← hlen, ← hitems] at hdc

/-- fork.py:120 `GWEI_TO_WEI = U256(10**9)`, used at fork.py:1118. -/
def GWEI_TO_WEI : Nat := 10^9

/-- fork.py:1118 `U256(wd.amount) * GWEI_TO_WEI`. The uint64-Gwei product
fits in UInt256 (`ProtocolWithdrawalCount.amount_exact`). -/
theorem create_ether_wei (item : Item) :
    item.amount.toNat = item.gwei.val * GWEI_TO_WEI := by
  simpa [GWEI_TO_WEI] using ProtocolWithdrawalCount.amount_exact item

/-- fork.py:1118 calls `create_ether` in state_tracker.py:624-644
(SHA256 ce420ad5682df9051178d298220d1552448e26c37f67be3b604b9f493541cf4a,
archived in direct-reference-amsterdam-gas-sources-20260910.json):
`account.balance += amount` (642) via `modify_state` (575-587) after
`get_account` (188-211). Lean `increaseBalance` on an existing account is
that increment; on a missing key it inserts `default` with the credited
amount. Lean never deletes the recipient after that write
(`createEther_keeps_present`). Python empty-account destroy after a
zero increment (`account_exists_and_is_empty` 359-385,
`modify_state` 583-587) remains named, as does field identity of Lean
`default` vs Python `EMPTY_ACCOUNT` and line 384 `EMPTY_CODE_HASH`. -/
structure CreateEther (before : AccountMap .EVM) (item : Item)
    (after : AccountMap .EVM) : Prop where
  agreed : after = before.increaseBalance .EVM item.recipient item.amount

/-- state_tracker.py:641-642 for an account already in the map. -/
theorem increaseBalance_existing {σ : AccountMap .EVM} {addr : AccountAddress}
    {acc : Account .EVM} {amount : UInt256} (h : σ.get? addr = some acc) :
    (σ.increaseBalance .EVM addr amount).get? addr =
      some {acc with balance := acc.balance + amount} := by
  unfold AccountMap.increaseBalance
  rw [h]
  exact Std.TreeMap.getElem?_insert_self

/-- state_tracker.py:188-211: missing key is read as `EMPTY_ACCOUNT`, then
642 adds `amount`. Lean inserts `default` with that balance. -/
theorem increaseBalance_missing {σ : AccountMap .EVM} {addr : AccountAddress}
    {amount : UInt256} (h : σ.get? addr = none) :
    (σ.increaseBalance .EVM addr amount).get? addr =
      some {(default : Account .EVM) with balance := amount} := by
  unfold AccountMap.increaseBalance
  rw [h]
  exact Std.TreeMap.getElem?_insert_self

theorem createEther_existing {before after : AccountMap .EVM} {item : Item}
    {acc : Account .EVM} (hacc : before.get? item.recipient = some acc)
    (h : CreateEther before item after) :
    after.get? item.recipient =
      some {acc with balance := acc.balance + item.amount} := by
  rw [h.agreed]
  exact increaseBalance_existing hacc

theorem createEther_missing {before after : AccountMap .EVM} {item : Item}
    (hacc : before.get? item.recipient = none)
    (h : CreateEther before item after) :
    after.get? item.recipient =
      some {(default : Account .EVM) with balance := item.amount} := by
  rw [h.agreed]
  exact increaseBalance_missing hacc

/-- fork.py:1118 Wei scale plus state_tracker.py:642 increment, for a
recipient already present. -/
theorem createEther_existing_wei {before after : AccountMap .EVM} {item : Item}
    {acc : Account .EVM} (hacc : before.get? item.recipient = some acc)
    (h : CreateEther before item after) :
    after.get? item.recipient =
        some {acc with balance := acc.balance + item.amount} ∧
      item.amount.toNat = item.gwei.val * GWEI_TO_WEI :=
  ⟨createEther_existing hacc h, create_ether_wei item⟩

/-- fork.py:120/1118: a nonzero Gwei credit is a nonzero Wei product. -/
theorem create_ether_gwei_nonzero (item : Item) (h : item.gwei.val ≠ 0) :
    item.amount.toNat ≠ 0 := by
  rw [create_ether_wei]
  exact Nat.mul_ne_zero h (by decide : GWEI_TO_WEI ≠ 0)

/-- Named: Lean Fin-add of an existing balance plus credited Wei does not
wrap. Python `account.balance += amount` (642) is a U256 add in the
archived body; wrap correspondence is not proved. -/
structure BalanceFits (acc : Account .EVM) (amount : UInt256) : Prop where
  lt : acc.balance.toNat + amount.toNat < UInt256.size

theorem uint256_add_toNat (a b : UInt256)
    (h : a.toNat + b.toNat < UInt256.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  change (a.val + b.val).val = a.val.val + b.val.val
  exact Nat.mod_eq_of_lt h

theorem uint256_add_pos (a b : UInt256)
    (hb : 0 < b.toNat) (hfit : a.toNat + b.toNat < UInt256.size) :
    0 < (a + b).toNat := by
  rw [uint256_add_toNat a b hfit]
  omega

/-- state_tracker.py:383 and 385. Line 384 (`code_hash == EMPTY_CODE_HASH`)
is a named adapter, not extracted. Destroy at modify_state:583-587 needs
all three conjuncts plus presence (381-382). -/
structure AccountNonceBalanceEmpty (acc : Account .EVM) : Prop where
  nonceZero : acc.nonce = UInt256.ofNat 0
  balanceZero : acc.balance.toNat = 0

theorem accountNonceBalanceEmpty_balance {acc : Account .EVM}
    (h : AccountNonceBalanceEmpty acc) : acc.balance.toNat = 0 :=
  h.balanceZero

/-- state_tracker.py:385 fails after a nonzero, non-wrapping increment. -/
theorem createEther_existing_balance_pos
    {before after : AccountMap .EVM} {item : Item} {acc : Account .EVM}
    (hacc : before.get? item.recipient = some acc)
    (h : CreateEther before item after)
    (hg : item.gwei.val ≠ 0) (hfit : BalanceFits acc item.amount) :
    ∃ acc', after.get? item.recipient = some acc' ∧ 0 < acc'.balance.toNat := by
  refine ⟨{acc with balance := acc.balance + item.amount},
    createEther_existing hacc h, ?_⟩
  exact uint256_add_pos acc.balance item.amount
    (Nat.pos_of_ne_zero (create_ether_gwei_nonzero item hg)) hfit.lt

theorem createEther_existing_not_empty
    {before after : AccountMap .EVM} {item : Item} {acc acc' : Account .EVM}
    (hacc : before.get? item.recipient = some acc)
    (h : CreateEther before item after)
    (hg : item.gwei.val ≠ 0) (hfit : BalanceFits acc item.amount)
    (hlook : after.get? item.recipient = some acc') :
    ¬ AccountNonceBalanceEmpty acc' := by
  intro hempty
  obtain ⟨acc₁, h₁, hpos⟩ := createEther_existing_balance_pos hacc h hg hfit
  have heq : acc' = acc₁ := Option.some.inj (hlook.symm.trans h₁)
  exact (Nat.ne_of_gt hpos) (heq ▸ hempty.balanceZero)

/-- state_tracker.py:188-211 then 642: a missing recipient credited a
nonzero Gwei is inserted at a positive balance, so 385 fails. -/
theorem createEther_missing_balance_pos
    {before after : AccountMap .EVM} {item : Item}
    (hacc : before.get? item.recipient = none)
    (h : CreateEther before item after)
    (hg : item.gwei.val ≠ 0) :
    ∃ acc', after.get? item.recipient = some acc' ∧ 0 < acc'.balance.toNat := by
  refine ⟨{(default : Account .EVM) with balance := item.amount},
    createEther_missing hacc h, ?_⟩
  exact Nat.pos_of_ne_zero (create_ether_gwei_nonzero item hg)

theorem createEther_missing_not_empty
    {before after : AccountMap .EVM} {item : Item} {acc' : Account .EVM}
    (hacc : before.get? item.recipient = none)
    (h : CreateEther before item after)
    (hg : item.gwei.val ≠ 0)
    (hlook : after.get? item.recipient = some acc') :
    ¬ AccountNonceBalanceEmpty acc' := by
  intro hempty
  obtain ⟨acc₁, h₁, hpos⟩ := createEther_missing_balance_pos hacc h hg
  have heq : acc' = acc₁ := Option.some.inj (hlook.symm.trans h₁)
  exact (Nat.ne_of_gt hpos) (heq ▸ hempty.balanceZero)

/-- fork.py:120/1118: a 0 Gwei credit is 0 Wei. -/
theorem create_ether_zero_wei (item : Item) (h : item.gwei.val = 0) :
    item.amount.toNat = 0 := by
  rw [create_ether_wei, h, Nat.zero_mul]

theorem uint256_eq_of_toNat {a b : UInt256} (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | mk va =>
    cases b with
    | mk vb =>
      simp [UInt256.toNat] at h
      exact congrArg UInt256.mk (Fin.eq_of_val_eq h)

theorem uint256_add_zero (a : UInt256) : a + UInt256.ofNat 0 = a := by
  apply uint256_eq_of_toNat
  have hz : (UInt256.ofNat 0).toNat = 0 := rfl
  have hfit : a.toNat + (UInt256.ofNat 0).toNat < UInt256.size := by
    rw [hz, Nat.add_zero]
    exact a.val.isLt
  rw [uint256_add_toNat a (UInt256.ofNat 0) hfit, hz, Nat.add_zero]

/-- state_tracker.py:642: a zero increment on an existing account is the
identity on the stored record. Destroy after zero remains named only
when the pre-state is already empty (359-385). -/
theorem createEther_existing_zero
    {before after : AccountMap .EVM} {item : Item} {acc : Account .EVM}
    (hacc : before.get? item.recipient = some acc)
    (hg : item.gwei.val = 0)
    (h : CreateEther before item after) :
    after.get? item.recipient = some acc := by
  have ha := createEther_existing hacc h
  have hz : item.amount = UInt256.ofNat 0 := by
    apply uint256_eq_of_toNat
    rw [create_ether_zero_wei item hg]
    rfl
  rw [hz, uint256_add_zero] at ha
  simpa using ha

theorem createEther_existing_zero_keeps_nonzero
    {before after : AccountMap .EVM} {item : Item} {acc acc' : Account .EVM}
    (hacc : before.get? item.recipient = some acc)
    (hg : item.gwei.val = 0)
    (hbal : acc.balance.toNat ≠ 0)
    (h : CreateEther before item after)
    (hlook : after.get? item.recipient = some acc') :
    ¬ AccountNonceBalanceEmpty acc' := by
  intro hempty
  have ha := createEther_existing_zero hacc hg h
  have heq : acc' = acc := Option.some.inj (hlook.symm.trans ha)
  exact hbal (heq ▸ hempty.balanceZero)

/-- Lean `Account` default nonce/balance are 0 (`Inhabited`). Field
identity with Python `EMPTY_ACCOUNT` remains named. -/
theorem default_account_nonce :
    (default : Account .EVM).nonce = UInt256.ofNat 0 :=
  rfl

theorem default_account_balance :
    (default : Account .EVM).balance.toNat = 0 :=
  rfl

theorem default_nonce_balance_empty :
    AccountNonceBalanceEmpty (default : Account .EVM) :=
  ⟨default_account_nonce, default_account_balance⟩

/-- state_tracker.py:188-211 then 642: missing + 0 Gwei inserts
`default` at 0 Wei. Lines 383/385 then hold. Line 384
`EMPTY_CODE_HASH` is still named. -/
theorem createEther_missing_zero
    {before after : AccountMap .EVM} {item : Item}
    (hacc : before.get? item.recipient = none)
    (hg : item.gwei.val = 0)
    (h : CreateEther before item after) :
    after.get? item.recipient =
      some {(default : Account .EVM) with balance := UInt256.ofNat 0} := by
  have hm := createEther_missing hacc h
  have hz : item.amount = UInt256.ofNat 0 := by
    apply uint256_eq_of_toNat
    rw [create_ether_zero_wei item hg]
    rfl
  rw [hz] at hm
  exact hm

theorem createEther_missing_zero_nonce_balance_empty
    {before after : AccountMap .EVM} {item : Item} {acc' : Account .EVM}
    (hacc : before.get? item.recipient = none)
    (hg : item.gwei.val = 0)
    (h : CreateEther before item after)
    (hlook : after.get? item.recipient = some acc') :
    AccountNonceBalanceEmpty acc' := by
  have ha := createEther_missing_zero hacc hg h
  have heq : acc' = {(default : Account .EVM) with balance := UInt256.ofNat 0} :=
    Option.some.inj (hlook.symm.trans ha)
  rw [heq]
  refine ⟨?_, ?_⟩
  · simp [default_account_nonce]
  · rfl

/-- state_tracker.py:642 identity: an already-empty existing account
stays nonce/balance empty after a zero increment. Destroy still needs
line 384. -/
theorem createEther_existing_zero_keeps_empty
    {before after : AccountMap .EVM} {item : Item} {acc acc' : Account .EVM}
    (hacc : before.get? item.recipient = some acc)
    (hg : item.gwei.val = 0)
    (hempty : AccountNonceBalanceEmpty acc)
    (h : CreateEther before item after)
    (hlook : after.get? item.recipient = some acc') :
    AccountNonceBalanceEmpty acc' := by
  have ha := createEther_existing_zero hacc hg h
  have heq : acc' = acc := Option.some.inj (hlook.symm.trans ha)
  exact heq ▸ hempty

/-- `AccountMap.increaseBalance` (evmyul AccountMap.lean:42-44) is
insert/update only. Python `modify_state` 583-587 may delete; that
destroy is not this Lean function. -/
theorem increaseBalance_present (σ : AccountMap .EVM) (addr : AccountAddress)
    (amount : UInt256) :
    (σ.increaseBalance .EVM addr amount).get? addr ≠ none := by
  unfold AccountMap.increaseBalance
  split <;> simp

theorem createEther_keeps_present
    {before after : AccountMap .EVM} {item : Item}
    (h : CreateEther before item after) :
    after.get? item.recipient ≠ none := by
  rw [h.agreed]
  exact increaseBalance_present before item.recipient item.amount

/-- fork.py:1111-1118: one `create_ether` per listed withdrawal, in list order.
`apply_body` fork.py:840 calls this loop exactly once with `block.withdrawals`. -/
inductive ElCredit : AccountMap .EVM → List Item → AccountMap .EVM → Prop where
  | nil (world : AccountMap .EVM) : ElCredit world [] world
  | cons {before mid after : AccountMap .EVM} {item : Item} {rest : List Item}
      (one : CreateEther before item mid) (tail : ElCredit mid rest after) :
      ElCredit before (item::rest) after

/-- fork.py:1111-1118: a singleton listed withdrawal is one `create_ether`. -/
theorem elCredit_singleton {before after : AccountMap .EVM} {item : Item}
    (h : ElCredit before [item] after) : CreateEther before item after := by
  cases h with
  | cons one tail =>
    cases tail
    exact one

theorem elCredit_singleton_existing {before after : AccountMap .EVM}
    {item : Item} {acc : Account .EVM}
    (hacc : before.get? item.recipient = some acc)
    (h : ElCredit before [item] after) :
    after.get? item.recipient =
      some {acc with balance := acc.balance + item.amount} :=
  createEther_existing hacc (elCredit_singleton h)

theorem elCredit_dispatch {before after : AccountMap .EVM} {items : List Item}
    (h : ElCredit before items after) : Dispatch before items after := by
  induction h with
  | nil world => exact .nil world
  | cons one tail ih =>
    exact .cons (by rw [←one.agreed]; exact ih)

/-- One accepted-block `apply_body` withdrawal pass (fork.py:840, 1101-1120). -/
structure ApplyBodyWithdrawals (before after : AccountMap .EVM) (listed : List Item) :
    Prop where
  once : ElCredit before listed after

/-- Gloas `Withdrawal.validator_index` (1926) plus the EL `Item`
(address / Gwei) that fork.py:1118 credits. The same archived object
is consumed by `apply_withdrawals` and `create_ether`. SSZ decode of
that object onto this pair remains named. -/
structure CreditedWithdrawal where
  validatorIndex : Nat
  item : Item

/-- fork.py:1111-1118 projection: every listed withdrawal is credited
once, retaining `address` / `amount`. -/
def creditedItems (ws : List CreditedWithdrawal) : List Item :=
  ws.map (·.item)

/-- Gloas:1924-1931 projection: every listed withdrawal is written
once, retaining `validator_index` / Gwei `amount`. -/
def creditedPairs (ws : List CreditedWithdrawal) : List (Nat × Nat) :=
  ws.map fun w => (w.validatorIndex, w.item.gwei.val)

theorem creditedItems_length (ws : List CreditedWithdrawal) :
    (creditedItems ws).length = ws.length := by
  simp [creditedItems]

theorem creditedPairs_length (ws : List CreditedWithdrawal) :
    (creditedPairs ws).length = ws.length := by
  simp [creditedPairs]

/-- The CL write list and the EL credit list are projections of the
same archived withdrawals, so they have the same length. Neither
count is an extra premise. -/
theorem credited_projection_count (ws : List CreditedWithdrawal) :
    (creditedPairs ws).length = (creditedItems ws).length := by
  simp [creditedPairs, creditedItems]

theorem creditedItems_nil : creditedItems [] = ([] : List Item) :=
  rfl

theorem creditedPairs_nil : creditedPairs [] = ([] : List (Nat × Nat)) :=
  rfl

theorem creditedItems_cons (w : CreditedWithdrawal) (ws : List CreditedWithdrawal) :
    creditedItems (w :: ws) = w.item :: creditedItems ws :=
  rfl

theorem creditedPairs_cons (w : CreditedWithdrawal) (ws : List CreditedWithdrawal) :
    creditedPairs (w :: ws) =
      (w.validatorIndex, w.item.gwei.val) :: creditedPairs ws :=
  rfl

theorem creditedPairs_append (xs ys : List CreditedWithdrawal) :
    creditedPairs (xs ++ ys) = creditedPairs xs ++ creditedPairs ys := by
  simp [creditedPairs, List.map_append]

/-- Concatenating a credited list with itself is sequential
`applyTagged`, not Gloas:1999 (empty parent returns before CL writes). -/
theorem applyTagged_credited_append (s : DualBalances)
    (xs ys : List CreditedWithdrawal) :
    applyTagged s (creditedPairs (xs ++ ys)) =
      applyTagged (applyTagged s (creditedPairs xs)) (creditedPairs ys) := by
  rw [creditedPairs_append, applyTagged_append]

/-- Gloas:1931 writes Gwei `withdrawal.amount`; fork.py:1118 credits
Wei `wd.amount * GWEI_TO_WEI`. Same field, different scale. -/
theorem credited_cl_amount_is_gwei (w : CreditedWithdrawal) :
    creditedPairs [w] = [(w.validatorIndex, w.item.gwei.val)] :=
  rfl

theorem credited_el_amount_is_wei (w : CreditedWithdrawal) :
    w.item.amount.toNat = w.item.gwei.val * GWEI_TO_WEI :=
  create_ether_wei w.item

/-- One Gloas:1924 iteration together with one fork.py:1118
`create_ether`. -/
structure CreditedStep (s : DualBalances) (before : AccountMap .EVM)
    (w : CreditedWithdrawal) (t : DualBalances) (after : AccountMap .EVM) :
    Prop where
  cl : t = applyOneWithdrawal s w.validatorIndex w.item.gwei.val
  el : CreateEther before w.item after

/-- Gloas:1924 `for withdrawal in withdrawals` and fork.py:1111-1118
`for wd in block.withdrawals` walk the same list, in list order. -/
inductive CreditedRun : DualBalances → AccountMap .EVM →
    List CreditedWithdrawal → DualBalances → AccountMap .EVM → Prop where
  | nil (s : DualBalances) (world : AccountMap .EVM) :
      CreditedRun s world [] s world
  | cons {s t u : DualBalances} {before mid after : AccountMap .EVM}
      {w : CreditedWithdrawal} {rest : List CreditedWithdrawal}
      (step : CreditedStep s before w t mid)
      (tail : CreditedRun t mid rest u after) :
      CreditedRun s before (w :: rest) u after

/-- The CL fold is derived from the joint walk, not assumed. -/
theorem creditedRun_cl {s t : DualBalances} {before after : AccountMap .EVM}
    {ws : List CreditedWithdrawal}
    (h : CreditedRun s before ws t after) :
    t = applyTagged s (creditedPairs ws) := by
  induction h with
  | nil s world =>
    simp [applyTagged, creditedPairs]
  | @cons s midS u before mid after w rest step tail ih =>
    have hstep :
        applyTagged s (creditedPairs (w :: rest)) =
          applyTagged (applyOneWithdrawal s w.validatorIndex w.item.gwei.val)
            (creditedPairs rest) := by
      simp only [creditedPairs, List.map_cons, applyTagged]
    rw [hstep, ← step.cl]
    exact ih

/-- The EL credit loop is derived from the joint walk, not assumed. -/
theorem creditedRun_el {s t : DualBalances} {before after : AccountMap .EVM}
    {ws : List CreditedWithdrawal}
    (h : CreditedRun s before ws t after) :
    ElCredit before (creditedItems ws) after := by
  induction h with
  | nil s world =>
    exact ElCredit.nil world
  | @cons s midS u before mid after w rest step tail ih =>
    simp only [creditedItems_cons]
    exact ElCredit.cons step.el ih

theorem creditedRun_dispatch {s t : DualBalances} {before after : AccountMap .EVM}
    {ws : List CreditedWithdrawal}
    (h : CreditedRun s before ws t after) :
    Dispatch before (creditedItems ws) after :=
  elCredit_dispatch (creditedRun_el h)

theorem creditedRun_empty {s t : DualBalances} {before after : AccountMap .EVM}
    (h : CreditedRun s before [] t after) :
    t = s ∧ after = before := by
  cases h
  exact ⟨rfl, rfl⟩

theorem creditedRun_singleton {s t : DualBalances}
    {before after : AccountMap .EVM} {w : CreditedWithdrawal}
    (h : CreditedRun s before [w] t after) :
    t = applyOneWithdrawal s w.validatorIndex w.item.gwei.val ∧
      CreateEther before w.item after := by
  cases h with
  | cons step tail =>
    cases tail
    exact ⟨step.cl, step.el⟩

/-- `apply_body` of the Item projection is the EL half of the joint
walk. The CL half is `applyTagged` of the index projection. -/
theorem applyBody_of_credited {s t : DualBalances}
    {before after : AccountMap .EVM} {ws : List CreditedWithdrawal}
    (h : CreditedRun s before ws t after) :
    ApplyBodyWithdrawals before after (creditedItems ws) :=
  ⟨creditedRun_el h⟩

/-- Named: SSZ `Withdrawal` list equals the Item projection. The
consumer `Dispatch` / count is then that list, not a second premise. -/
theorem dispatched_counts_from_credited
    {initial before after : AccountMap .EVM} {p mig c : Nat}
    {pre post : Clock} {s0 t0 : DualBalances}
    {ws : List CreditedWithdrawal}
    (prior : Ledger initial p 0 mig c before)
    (blocks : List Block) (hacc : AcceptedBlocks pre blocks post)
    (run : CreditedRun s0 before ws t0 after)
    (hflat : blocks.flatMap items = creditedItems ws)
    (powBound : p ≤ 2 ^ 64) (migrationConserving : mig = 0) :
    Ledger initial p ((blocks.map (fun b => (items b).length)).sum) mig
        (c + credits (blocks.flatMap items)) after ∧
      Counts p ((blocks.map (fun b => (items b).length)).sum) mig := by
  have hd : Dispatch before (blocks.flatMap items) after := by
    rw [hflat]
    exact creditedRun_dispatch run
  exact dispatched_counts prior blocks hacc hd powBound migrationConserving

/-- Capella:153-157 `Withdrawal` field order. Byte-string decode onto
these fields remains named; `ExecutionAddress` → `AccountAddress` is
not claimed. -/
structure SszWithdrawal where
  index : Nat
  validatorIndex : Nat
  addressBytes : List Nat
  amount : Nat

/-- fork.py:1118 EL credit fields: `address` / `amount`, not
`validator_index` or `index`. -/
def sszElFields (w : SszWithdrawal) : List Nat × Nat :=
  (w.addressBytes, w.amount)

/-- Gloas:1924-1931 CL write fields: `validator_index` / Gwei, not
the execution address. -/
def sszClFields (w : SszWithdrawal) : Nat × Nat :=
  (w.validatorIndex, w.amount)

theorem sszEl_ignores_index (w : SszWithdrawal) (i : Nat) :
    sszElFields { w with index := i } = sszElFields w :=
  rfl

theorem sszEl_ignores_validator (w : SszWithdrawal) (v : Nat) :
    sszElFields { w with validatorIndex := v } = sszElFields w :=
  rfl

theorem sszCl_ignores_address (w : SszWithdrawal) (a : List Nat) :
    sszClFields { w with addressBytes := a } = sszClFields w :=
  rfl

/-- A mutant that treats `validator_index` as the EL address. -/
theorem sszEl_ne_validator_as_address {w : SszWithdrawal}
    (h : w.addressBytes ≠ [w.validatorIndex]) :
    sszElFields w ≠ ([w.validatorIndex], w.amount) := by
  intro he
  exact h (congrArg Prod.fst he)

/-- Capella:196-204 `Withdrawal`: `index`, `validator_index`, address,
amount. `IndexedWithdrawal` is the index projection;
`CreditedWithdrawal` is the validator_index projection. Byte-string
decode onto this record remains named. -/
structure ArchivedWithdrawal where
  index : Nat
  validatorIndex : Nat
  item : Item

def asIndexed (w : ArchivedWithdrawal) : IndexedWithdrawal :=
  { index := w.index, item := w.item }

def asCredited (w : ArchivedWithdrawal) : CreditedWithdrawal :=
  { validatorIndex := w.validatorIndex, item := w.item }

/-- Capella:451-455 constructor: the four fields join an `Item` whose
Gwei is the archived amount. Address-byte decode stays named. -/
def sszAsArchived (w : SszWithdrawal) (item : Item)
    (hamt : w.amount = item.gwei.val) : ArchivedWithdrawal :=
  { index := w.index, validatorIndex := w.validatorIndex, item := item }

theorem sszAsArchived_asCredited (w : SszWithdrawal) (item : Item)
    (hamt : w.amount = item.gwei.val) :
    asCredited (sszAsArchived w item hamt) =
      { validatorIndex := w.validatorIndex, item := item } :=
  rfl

theorem sszAsArchived_asIndexed (w : SszWithdrawal) (item : Item)
    (hamt : w.amount = item.gwei.val) :
    asIndexed (sszAsArchived w item hamt) =
      { index := w.index, item := item } :=
  rfl

theorem sszAsArchived_pair (w : SszWithdrawal) (item : Item)
    (hamt : w.amount = item.gwei.val) :
    sszClFields w = (w.validatorIndex, item.gwei.val) := by
  simp [sszClFields, hamt]

def archivedItems (ws : List ArchivedWithdrawal) : List Item :=
  ws.map (·.item)

def archivedIndexed (ws : List ArchivedWithdrawal) : List IndexedWithdrawal :=
  ws.map asIndexed

def archivedCredited (ws : List ArchivedWithdrawal) : List CreditedWithdrawal :=
  ws.map asCredited

theorem archived_items_of_indexed (ws : List ArchivedWithdrawal) :
    (archivedIndexed ws).map (·.item) = archivedItems ws := by
  simp [archivedIndexed, asIndexed, archivedItems]

theorem archived_items_of_credited (ws : List ArchivedWithdrawal) :
    creditedItems (archivedCredited ws) = archivedItems ws := by
  simp [creditedItems, archivedCredited, asCredited, archivedItems]

theorem archived_projection_count (ws : List ArchivedWithdrawal) :
    (archivedIndexed ws).length = (archivedCredited ws).length := by
  simp [archivedIndexed, archivedCredited]

/-- Capella:452/458 `Withdrawal(index=withdrawal_index, validator_index=...,
address=..., amount=...)` then `withdrawal_index += 1`. The running
index is stamped onto the credited list; validator_index is kept. -/
def stampIndex (start : Nat) : List CreditedWithdrawal → List ArchivedWithdrawal
  | [] => []
  | w :: ws =>
      { index := start
        validatorIndex := w.validatorIndex
        item := w.item } :: stampIndex (start + 1) ws

theorem stampIndex_nil (start : Nat) : stampIndex start [] = [] :=
  rfl

theorem stampIndex_cons (start : Nat) (w : CreditedWithdrawal)
    (ws : List CreditedWithdrawal) :
    stampIndex start (w :: ws) =
      { index := start, validatorIndex := w.validatorIndex, item := w.item } ::
        stampIndex (start + 1) ws :=
  rfl

theorem stampIndex_length (start : Nat) (ws : List CreditedWithdrawal) :
    (stampIndex start ws).length = ws.length := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [stampIndex, List.length_cons]
    exact congrArg Nat.succ (ih (start + 1))

theorem stampIndex_credited (start : Nat) (ws : List CreditedWithdrawal) :
    archivedCredited (stampIndex start ws) = ws := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [archivedCredited, stampIndex, asCredited, List.map_cons]
    exact congrArg (List.cons w) (ih (start + 1))

theorem stampIndex_items (start : Nat) (ws : List CreditedWithdrawal) :
    archivedItems (stampIndex start ws) = creditedItems ws := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [archivedItems, stampIndex, creditedItems, List.map_cons]
    exact congrArg (List.cons w.item) (ih (start + 1))

theorem stampIndex_indexed (start : Nat) (ws : List CreditedWithdrawal) :
    archivedIndexed (stampIndex start ws) =
      indexedWithdrawals start (creditedItems ws) := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [archivedIndexed, stampIndex, asIndexed, indexedWithdrawals,
      creditedItems, List.map_cons]
    exact congrArg (List.cons { index := start, item := w.item }) (ih (start + 1))

/-- Assigned indices are the successor cursor, not an extra Nodup
premise. Two identical credited entries still get distinct indices. -/
theorem stampIndex_indices (start : Nat) (ws : List CreditedWithdrawal) :
    (archivedIndexed (stampIndex start ws)).map (·.index) =
      indexSeq start ws.length := by
  rw [stampIndex_indexed, indexedWithdrawals_indices, creditedItems_length]

theorem stampIndex_nodup (start : Nat) (ws : List CreditedWithdrawal) :
    ((archivedIndexed (stampIndex start ws)).map (·.index)).Nodup := by
  rw [stampIndex_indices]
  exact indexSeq_nodup start ws.length

/-- The joint CL/EL walk on the credited projection of a stamped list
is the walk on that credited list. Index uniqueness is `stampIndex_nodup`. -/
theorem creditedRun_of_stamped {s t : DualBalances}
    {before after : AccountMap .EVM} {start : Nat}
    {ws : List CreditedWithdrawal}
    (h : CreditedRun s before (archivedCredited (stampIndex start ws)) t after) :
    CreditedRun s before ws t after := by
  rwa [stampIndex_credited] at h

theorem dispatched_counts_from_stamped
    {initial before after : AccountMap .EVM} {p mig c start : Nat}
    {pre post : Clock} {s0 t0 : DualBalances}
    {ws : List CreditedWithdrawal}
    (prior : Ledger initial p 0 mig c before)
    (blocks : List Block) (hacc : AcceptedBlocks pre blocks post)
    (run : CreditedRun s0 before (archivedCredited (stampIndex start ws)) t0 after)
    (hflat : blocks.flatMap items = archivedItems (stampIndex start ws))
    (powBound : p ≤ 2 ^ 64) (migrationConserving : mig = 0) :
    Ledger initial p ((blocks.map (fun b => (items b).length)).sum) mig
        (c + credits (blocks.flatMap items)) after ∧
      Counts p ((blocks.map (fun b => (items b).length)).sum) mig := by
  have hrun := creditedRun_of_stamped run
  have hitems : blocks.flatMap items = creditedItems ws := by
    rwa [stampIndex_items] at hflat
  exact dispatched_counts_from_credited prior blocks hacc hrun hitems
    powBound migrationConserving

theorem stampIndex_validators (start : Nat) (ws : List CreditedWithdrawal) :
    (stampIndex start ws).map (·.validatorIndex) =
      ws.map (·.validatorIndex) := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [stampIndex, List.map_cons]
    exact congrArg (List.cons w.validatorIndex) (ih (start + 1))

theorem archivedItems_append (xs ys : List ArchivedWithdrawal) :
    archivedItems (xs ++ ys) = archivedItems xs ++ archivedItems ys := by
  simp [archivedItems]

theorem archivedIndexed_append (xs ys : List ArchivedWithdrawal) :
    archivedIndexed (xs ++ ys) = archivedIndexed xs ++ archivedIndexed ys := by
  simp [archivedIndexed]

theorem archivedCredited_append (xs ys : List ArchivedWithdrawal) :
    archivedCredited (xs ++ ys) = archivedCredited xs ++ archivedCredited ys := by
  simp [archivedCredited]

/-- Capella:452/458 on a concatenated payload: the second stage
continues the running `withdrawal_index`, it does not restart. -/
theorem stampIndex_append (start : Nat)
    (xs ys : List CreditedWithdrawal) :
    stampIndex start (xs ++ ys) =
      stampIndex start xs ++ stampIndex (start + xs.length) ys := by
  induction xs generalizing start with
  | nil =>
    simp [stampIndex]
  | cons x xs ih =>
    simp only [List.cons_append, stampIndex, List.length_cons]
    have hshift : start + (xs.length + 1) = start + 1 + xs.length := by
      omega
    rw [ih (start + 1), hshift]

/-- Capella:480 then 510 across credited payloads. An empty list
consumes no index. -/
def stampedChain (start : Nat) :
    List (List CreditedWithdrawal) → List ArchivedWithdrawal
  | [] => []
  | ws :: rest =>
      stampIndex start ws ++ stampedChain (start + ws.length) rest

theorem stampedChain_nil (start : Nat) : stampedChain start [] = [] :=
  rfl

theorem stampedChain_cons (start : Nat) (ws : List CreditedWithdrawal)
    (rest : List (List CreditedWithdrawal)) :
    stampedChain start (ws :: rest) =
      stampIndex start ws ++ stampedChain (start + ws.length) rest :=
  rfl

theorem stampedChain_items (start : Nat)
    (wss : List (List CreditedWithdrawal)) :
    archivedItems (stampedChain start wss) =
      (wss.map creditedItems).flatten := by
  induction wss generalizing start with
  | nil =>
    simp [stampedChain, archivedItems]
  | cons ws rest ih =>
    simp only [stampedChain, List.map_cons, List.flatten_cons]
    rw [archivedItems_append, stampIndex_items, ih]

theorem stampedChain_credited (start : Nat)
    (wss : List (List CreditedWithdrawal)) :
    archivedCredited (stampedChain start wss) = wss.flatten := by
  induction wss generalizing start with
  | nil =>
    simp [stampedChain, archivedCredited]
  | cons ws rest ih =>
    simp only [stampedChain, List.flatten_cons]
    rw [archivedCredited_append, stampIndex_credited, ih]

theorem stampedChain_indices (start : Nat)
    (wss : List (List CreditedWithdrawal)) :
    (archivedIndexed (stampedChain start wss)).map (·.index) =
      indexSeq start ((wss.map List.length).sum) := by
  induction wss generalizing start with
  | nil =>
    simp [stampedChain, archivedIndexed, indexSeq]
  | cons ws rest ih =>
    simp only [stampedChain, archivedIndexed_append, List.map_append,
      List.map_cons, List.sum_cons]
    rw [stampIndex_indices, ih]
    exact indexSeq_append start ws.length _

theorem stampedChain_nodup (start : Nat)
    (wss : List (List CreditedWithdrawal)) :
    ((archivedIndexed (stampedChain start wss)).map (·.index)).Nodup := by
  rw [stampedChain_indices]
  exact indexSeq_nodup start _

/-- `indexedChain` of blocks whose `items` are credited projections is
the stamped index walk of those credited lists. Neither side names the
consumer flatMap premise. -/
theorem indexedChain_of_credited (start : Nat)
    (pairs : List (Block × List CreditedWithdrawal))
    (h : ∀ p ∈ pairs, items p.1 = creditedItems p.2) :
    indexedChain start (pairs.map (·.1)) =
      archivedIndexed (stampedChain start (pairs.map (·.2))) := by
  induction pairs generalizing start with
  | nil =>
    simp [indexedChain, stampedChain, archivedIndexed]
  | cons p rest ih =>
    have hb : items p.1 = creditedItems p.2 :=
      h p (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ q ∈ rest, items q.1 = creditedItems q.2 := by
      intro q hq
      exact h q (List.mem_cons.mpr (Or.inr hq))
    simp only [List.map_cons, indexedChain, stampedChain]
    rw [hb, nextIndexAfter_eq, creditedItems_length]
    rw [ih (start + p.2.length) hrest]
    rw [archivedIndexed_append, stampIndex_indexed]

/-- Electra:1420-1449: walk the visit ring; append a `Withdrawal` with
that `validator_index` only when eligible; break at the payload limit.
Same break as `sweepStage` (Gloas:1854-1856 / Electra:1423-1425). -/
def creditEligible (limit prior : Nat) :
    List Nat → List (Item × Bool) → List CreditedWithdrawal
  | [], _ => []
  | _, [] => []
  | i :: is, (item, eligible) :: rest =>
      if limit ≤ prior then []
      else if eligible then
        { validatorIndex := i, item := item } ::
          creditEligible limit (prior + 1) is rest
      else
        creditEligible limit prior is rest

theorem creditEligible_nil_visits (limit prior : Nat)
    (flagged : List (Item × Bool)) :
    creditEligible limit prior [] flagged = [] := by
  cases flagged <;> rfl

theorem creditEligible_nil_flagged (limit prior : Nat) (visits : List Nat) :
    creditEligible limit prior visits [] = [] := by
  cases visits <;> rfl

/-- The Item projection is the archived sweep, not a second list.
Requires one visit key per flagged validator (Electra:1420-1451). -/
theorem creditEligible_items (limit prior : Nat)
    (visits : List Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ visits.length) :
    creditedItems (creditEligible limit prior visits flagged) =
      sweepStage limit prior flagged := by
  induction flagged generalizing prior visits with
  | nil =>
    cases visits <;> simp [creditEligible, creditedItems, sweepStage]
  | cons entry rest ih =>
    obtain ⟨item, eligible⟩ := entry
    cases visits with
    | nil =>
      simp at hle
    | cons i is =>
      have hrest : rest.length ≤ is.length := by
        simp only [List.length_cons] at hle
        exact Nat.le_of_succ_le_succ hle
      by_cases hl : limit ≤ prior
      · simp [creditEligible, sweepStage, creditedItems, hl]
      · cases eligible with
        | false =>
          simp only [creditEligible, sweepStage, hl, ↓reduceIte, Bool.false_eq_true]
          exact ih prior is hrest
        | true =>
          simp only [creditEligible, sweepStage, creditedItems, hl, ↓reduceIte,
            List.map_cons]
          exact congrArg (List.cons item) (ih (prior + 1) is hrest)

/-- Credited `validator_index` values are a sublist of the visit walk,
not a free index list. -/
theorem creditEligible_indices_sublist (limit prior : Nat) :
    ∀ visits flagged,
      List.Sublist
        ((creditEligible limit prior visits flagged).map
          (fun w => w.validatorIndex))
        visits := by
  intro visits
  induction visits generalizing prior with
  | nil =>
    intro flagged
    simp [creditEligible_nil_visits]
  | cons i is ih =>
    intro flagged
    cases flagged with
    | nil =>
      simp [creditEligible]
    | cons entry rest =>
      obtain ⟨item, eligible⟩ := entry
      by_cases hl : limit ≤ prior
      · simp [creditEligible, hl]
      · cases eligible with
        | false =>
          simp only [creditEligible, hl, ↓reduceIte, Bool.false_eq_true]
          exact List.Sublist.cons i (ih prior rest)
        | true =>
          simp only [creditEligible, hl, ↓reduceIte, List.map_cons]
          exact List.Sublist.cons_cons i (ih (prior + 1) rest)

theorem creditEligible_indices_nodup
    {n start fuel limit prior : Nat} {flagged : List (Item × Bool)}
    (h : SweepStart n start) (hfuel : fuel ≤ n) :
    ((creditEligible limit prior (visitRing n start fuel) flagged).map
        (fun w => w.validatorIndex)).Nodup :=
  (visitRing_nodup h hfuel).sublist
    (creditEligible_indices_sublist limit prior (visitRing n start fuel) flagged)

theorem creditEligible_mem_ring
    {n start fuel limit prior : Nat} {flagged : List (Item × Bool)} {i : Nat}
    (h : SweepStart n start)
    (hin : i ∈ (creditEligible limit prior (visitRing n start fuel) flagged).map
        (fun w => w.validatorIndex)) :
    ∃ k < fuel, i = (start + k) % n :=
  visitRing_mem h
    (List.Sublist.mem hin
      (creditEligible_indices_sublist limit prior
        (visitRing n start fuel) flagged))

theorem visitRing_lt {n start fuel i : Nat} (h : SweepStart n start)
    (hin : i ∈ visitRing n start fuel) : i < n := by
  obtain ⟨k, _, hs⟩ := visitRing_mem h hin
  rw [hs]
  exact Nat.mod_lt _ h.registry

/-- Dropping `SweepStart.registry` from `visitRing_lt` is refuted:
`0 ∈ visitRing 0 0 1` and `¬ 0 < 0`. Python would raise
`ZeroDivisionError` before this walk. -/
theorem visitRing_lt_needs_registry :
    ¬ (∀ n start fuel i, i ∈ visitRing n start fuel → i < n) := by
  intro h
  have hin : 0 ∈ visitRing 0 0 1 :=
    visitRing_start_mem 0 0 1 Nat.zero_lt_one
  exact Nat.not_lt_zero _ (h 0 0 1 0 hin)

theorem land_flag_of_lt {v : Nat} (h : v < BUILDER_INDEX_FLAG) :
    v &&& BUILDER_INDEX_FLAG = 0 := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_land]
  have hz : (0 : Nat).testBit j = false := by
    simp
  rw [hz]
  simp only [BUILDER_INDEX_FLAG, Nat.testBit_two_pow]
  by_cases hj : j = 40
  · subst hj
    have : v.testBit 40 = false :=
      Nat.testBit_lt_two_pow (by simpa [BUILDER_INDEX_FLAG] using h)
    simp [this]
  · simp [decide_eq_false (Ne.symm hj)]

theorem isBuilderIndex_of_lt {v : Nat} (h : v < BUILDER_INDEX_FLAG) :
    isBuilderIndex v = false := by
  simp [isBuilderIndex, land_flag_of_lt h]

/-- A registry no larger than the flag produces ordinary validator
indices on the visit ring. Builder-tagged keys remain named when
`n > 2^40`. -/
theorem visitRing_not_builder {n start fuel i : Nat}
    (h : SweepStart n start) (hn : n ≤ BUILDER_INDEX_FLAG)
    (hin : i ∈ visitRing n start fuel) :
    isBuilderIndex i = false :=
  isBuilderIndex_of_lt (Nat.lt_of_lt_of_le (visitRing_lt h hin) hn)

/-- Electra:1451 membership from `visitRing_get`: the k-th walk key
is `(start + k) % n`. -/
theorem visitRing_mem_offset {n start fuel k : Nat}
    (h : SweepStart n start) (hk : k < fuel) :
    (start + k) % n ∈ visitRing n start fuel := by
  have hlen : k < (visitRing n start fuel).length := by
    rw [visitRing_length]
    exact hk
  have hg := visitRing_get h hk
  rw [List.getElem?_eq_getElem hlen] at hg
  exact (Option.some.inj hg) ▸ List.getElem_mem hlen

/-- Electra:1420-1451 / Gloas:1033-1034. A registry larger than the
flag can land on `BUILDER_INDEX_FLAG` itself. That key is
`is_builder_index`; `visitRing_not_builder` needs `n ≤ 2^40`. -/
theorem visitRing_flag_mem {n fuel : Nat}
    (hn : BUILDER_INDEX_FLAG < n) (hfuel : 0 < fuel) :
    BUILDER_INDEX_FLAG ∈ visitRing n BUILDER_INDEX_FLAG fuel :=
  visitRing_start_mem n BUILDER_INDEX_FLAG fuel hfuel

theorem sweepStart_flag_succ :
    SweepStart (BUILDER_INDEX_FLAG + 1) BUILDER_INDEX_FLAG :=
  ⟨Nat.succ_pos _, Nat.lt_succ_self _⟩

/-- The `n ≤ 2^40` hypothesis is load-bearing: `n = 2^40+1` and
cursor `2^40` produce a builder-tagged visit key. -/
theorem visitRing_exists_builder {n fuel : Nat}
    (hn : BUILDER_INDEX_FLAG < n) (hfuel : 0 < fuel) :
    ∃ i ∈ visitRing n BUILDER_INDEX_FLAG fuel, isBuilderIndex i = true :=
  ⟨BUILDER_INDEX_FLAG, visitRing_flag_mem hn hfuel, isBuilderIndex_flag⟩

/-- Reaching the flag from an earlier cursor: `start ≤ 2^40` and
enough fuel walk onto the flagged index when it sits in-range. -/
theorem visitRing_mem_flag {n start fuel : Nat}
    (h : SweepStart n start) (hn : BUILDER_INDEX_FLAG < n)
    (hreach : start ≤ BUILDER_INDEX_FLAG)
    (hfuel : BUILDER_INDEX_FLAG - start < fuel) :
    BUILDER_INDEX_FLAG ∈ visitRing n start fuel := by
  have hmem := visitRing_mem_offset h hfuel
  have heq : (start + (BUILDER_INDEX_FLAG - start)) % n =
      BUILDER_INDEX_FLAG := by
    rw [Nat.add_sub_of_le hreach, Nat.mod_eq_of_lt hn]
  rwa [heq] at hmem

theorem creditEligible_not_builder
    {n start fuel limit prior : Nat} {flagged : List (Item × Bool)}
    {w : CreditedWithdrawal}
    (h : SweepStart n start) (hn : n ≤ BUILDER_INDEX_FLAG)
    (hw : w ∈ creditEligible limit prior (visitRing n start fuel) flagged) :
    isBuilderIndex w.validatorIndex = false := by
  have him : w.validatorIndex ∈
      (creditEligible limit prior (visitRing n start fuel) flagged).map
        (fun w => w.validatorIndex) :=
    List.mem_map.mpr ⟨w, hw, rfl⟩
  have hring : w.validatorIndex ∈ visitRing n start fuel :=
    List.Sublist.mem him
      (creditEligible_indices_sublist limit prior
        (visitRing n start fuel) flagged)
  exact visitRing_not_builder h hn hring

theorem creditEligible_pairs_not_builder
    {n start fuel limit prior : Nat} {flagged : List (Item × Bool)}
    (h : SweepStart n start) (hn : n ≤ BUILDER_INDEX_FLAG) :
    ∀ p ∈ creditedPairs
        (creditEligible limit prior (visitRing n start fuel) flagged),
      isBuilderIndex p.1 = false := by
  intro p hp
  simp only [creditedPairs, List.mem_map] at hp
  obtain ⟨w, hw, rfl⟩ := hp
  exact creditEligible_not_builder h hn hw

/-- `applyTagged` of an Electra-credited list is the validator
`decrease_balance` fold: visit keys do not carry the builder flag. -/
theorem creditEligible_apply_validators
    (s : DualBalances) {n start fuel limit prior : Nat}
    {flagged : List (Item × Bool)} (h : SweepStart n start)
    (hn : n ≤ BUILDER_INDEX_FLAG) (i : Nat) :
    (applyTagged s (creditedPairs
        (creditEligible limit prior (visitRing n start fuel) flagged))).validators i =
      applyWithdrawals s.validators
        (creditedPairs
          (creditEligible limit prior (visitRing n start fuel) flagged)) i :=
  applyTagged_validators_only s _ (creditEligible_pairs_not_builder h hn) i

/-- Electra:1413/1420-1449: visit `min(n, 16384)` keys from `start`,
credit under the payload cap 16. -/
def electraCreditEligible (n start prior : Nat)
    (flagged : List (Item × Bool)) : List CreditedWithdrawal :=
  creditEligible MAX_WITHDRAWALS_PER_PAYLOAD prior
    (visitRing n start (validatorsSweepLimit n)) flagged

/-- Electra:1413. An empty registry has fuel `min(0, 16384) = 0`, so
the archived sweep credits nothing. The `% 0` exception is the
cursor increment on a positive-fuel walk (`visitRing_zero_succ`),
not this constructor. -/
theorem electraCreditEligible_empty_registry (start prior : Nat)
    (flagged : List (Item × Bool)) :
    electraCreditEligible 0 start prior flagged = [] := by
  simp [electraCreditEligible, validatorsSweepLimit, visitRing,
    creditEligible_nil_visits]

theorem electraCreditEligible_items {n start prior : Nat}
    {flagged : List (Item × Bool)}
    (hle : flagged.length ≤ validatorsSweepLimit n) :
    creditedItems (electraCreditEligible n start prior flagged) =
      sweepStage MAX_WITHDRAWALS_PER_PAYLOAD prior flagged := by
  have hvisits : flagged.length ≤
      (visitRing n start (validatorsSweepLimit n)).length := by
    rwa [visitRing_length]
  exact creditEligible_items _ _ _ _ hvisits

theorem electraCreditEligible_nodup {n start prior : Nat}
    {flagged : List (Item × Bool)} (h : SweepStart n start) :
    ((electraCreditEligible n start prior flagged).map
        (fun w => w.validatorIndex)).Nodup :=
  creditEligible_indices_nodup h (validatorsSweepLimit_le_registry n)

theorem electraCreditEligible_pairs_not_builder
    {n start prior : Nat} {flagged : List (Item × Bool)}
    (h : SweepStart n start) (hn : n ≤ BUILDER_INDEX_FLAG) :
    ∀ p ∈ creditedPairs (electraCreditEligible n start prior flagged),
      isBuilderIndex p.1 = false := by
  intro p hp
  exact creditEligible_pairs_not_builder h hn p
    (by simpa [electraCreditEligible] using hp)

/-- Electra:1426-1449 writes `state.balances`, not `state.builders`. -/
theorem electraCreditEligible_keeps_builders
    (s : DualBalances) {n start prior : Nat} {flagged : List (Item × Bool)}
    (h : SweepStart n start) (hn : n ≤ BUILDER_INDEX_FLAG) :
    (applyTagged s (creditedPairs
        (electraCreditEligible n start prior flagged))).builders =
      s.builders :=
  applyTagged_validators_keep_builders s _
    (electraCreditEligible_pairs_not_builder h hn)

/-- Electra:1451 visit keys are `< n`. They write `state.balances[i]`
only when `n ≤ len(validators)` and `n ≤ 2^40`. -/
theorem electraCreditEligible_inRange
    {n start prior nv nb : Nat} {flagged : List (Item × Bool)}
    (h : SweepStart n start) (hn : n ≤ nv)
    (hnflag : n ≤ BUILDER_INDEX_FLAG) :
    ∀ p ∈ creditedPairs (electraCreditEligible n start prior flagged),
      IndexInRange nv nb p.1 := by
  intro p hp
  have hnb := electraCreditEligible_pairs_not_builder h hnflag p hp
  have hring : p.1 ∈ visitRing n start (validatorsSweepLimit n) := by
    simp only [creditedPairs, List.mem_map] at hp
    obtain ⟨w, hw, rfl⟩ := hp
    have him : w.validatorIndex ∈
        (electraCreditEligible n start prior flagged).map
          (fun w => w.validatorIndex) :=
      List.mem_map.mpr ⟨w, hw, rfl⟩
    have hsub := creditEligible_indices_sublist
      MAX_WITHDRAWALS_PER_PAYLOAD prior
      (visitRing n start (validatorsSweepLimit n)) flagged
    exact List.Sublist.mem (by simpa [electraCreditEligible] using him) hsub
  have hlt := visitRing_lt h hring
  simp [IndexInRange, hnb]
  exact Nat.lt_of_lt_of_le hlt hn

theorem validatorsSweepLimit_flag_succ :
    validatorsSweepLimit (BUILDER_INDEX_FLAG + 1) = MAX_VALIDATORS_PER_SWEEP :=
  Nat.min_eq_right (by decide : MAX_VALIDATORS_PER_SWEEP ≤ BUILDER_INDEX_FLAG + 1)

theorem validatorsSweepLimit_flag_succ_pos :
    0 < validatorsSweepLimit (BUILDER_INDEX_FLAG + 1) := by
  rw [validatorsSweepLimit_flag_succ]
  decide

/-- Electra:1426-1449 on `n = 2^40+1`, cursor `2^40`: the first visit
key is the flag. An eligible first validator credits a builder index.
`electraCreditEligible_pairs_not_builder` requires `n ≤ 2^40`. -/
theorem electraCreditEligible_gt_flag_credits_flag (item : Item) :
    electraCreditEligible (BUILDER_INDEX_FLAG + 1) BUILDER_INDEX_FLAG 0
      [(item, true)] =
      [{ validatorIndex := BUILDER_INDEX_FLAG, item }] := by
  simp only [electraCreditEligible]
  rw [visitRing_pos _ _ _ validatorsSweepLimit_flag_succ_pos]
  simp [creditEligible, creditEligible_nil_flagged,
    show ¬(MAX_WITHDRAWALS_PER_PAYLOAD ≤ 0) by decide]

theorem electraCreditEligible_gt_flag_pairs_are_builder (item : Item) :
    ∀ p ∈ creditedPairs
        (electraCreditEligible (BUILDER_INDEX_FLAG + 1) BUILDER_INDEX_FLAG 0
          [(item, true)]),
      isBuilderIndex p.1 = true := by
  intro p hp
  simp [electraCreditEligible_gt_flag_credits_flag, creditedPairs] at hp
  subst hp
  exact isBuilderIndex_flag

/-- Dropping `n ≤ 2^40` from `electraCreditEligible_pairs_not_builder`
is refuted by this payload. -/
theorem electraCreditEligible_gt_flag_not_all_validators (item : Item) :
    ¬ (∀ p ∈ creditedPairs
          (electraCreditEligible (BUILDER_INDEX_FLAG + 1) BUILDER_INDEX_FLAG 0
            [(item, true)]),
        isBuilderIndex p.1 = false) := by
  intro h
  have hp := h (BUILDER_INDEX_FLAG, item.gwei.val) (by
    simp [electraCreditEligible_gt_flag_credits_flag, creditedPairs])
  simp [isBuilderIndex_flag] at hp

/-- Gloas:1926-1927. That Electra credit writes `state.builders[0]`,
not `state.balances`. `toBuilderIndex` of the flag is 0. -/
theorem applyTagged_electra_gt_flag_writes_builder_zero
    (s : DualBalances) (item : Item) :
    (applyTagged s (creditedPairs
        (electraCreditEligible (BUILDER_INDEX_FLAG + 1) BUILDER_INDEX_FLAG 0
          [(item, true)]))).builders 0 =
      s.builders 0 - item.gwei.val := by
  have hlist :
      creditedPairs
        (electraCreditEligible (BUILDER_INDEX_FLAG + 1) BUILDER_INDEX_FLAG 0
          [(item, true)]) =
        [(BUILDER_INDEX_FLAG, item.gwei.val)] := by
    simp [electraCreditEligible_gt_flag_credits_flag, creditedPairs]
  rw [hlist, applyTagged_singleton]
  have h := applyOneWithdrawal_builder_written s BUILDER_INDEX_FLAG
    item.gwei.val isBuilderIndex_flag
  rw [toBuilderIndex_flag] at h
  exact h

theorem electraCreditEligible_stamped_nodup {n start prior wstart : Nat}
    {flagged : List (Item × Bool)} (h : SweepStart n start) :
    ((archivedIndexed
        (stampIndex wstart (electraCreditEligible n start prior flagged))).map
        (·.index)).Nodup ∧
      ((stampIndex wstart (electraCreditEligible n start prior flagged)).map
          (·.validatorIndex)).Nodup :=
  ⟨stampIndex_nodup wstart _,
    by
      rw [stampIndex_validators]
      exact electraCreditEligible_nodup h⟩

theorem dispatched_counts_from_electra_credits
    {initial before after : AccountMap .EVM} {p mig c n start prior : Nat}
    {pre post : Clock} {s0 t0 : DualBalances}
    {flagged : List (Item × Bool)}
    (priorL : Ledger initial p 0 mig c before)
    (blocks : List Block) (hacc : AcceptedBlocks pre blocks post)
    (run : CreditedRun s0 before
      (electraCreditEligible n start prior flagged) t0 after)
    (hflat : blocks.flatMap items =
      creditedItems (electraCreditEligible n start prior flagged))
    (powBound : p ≤ 2 ^ 64) (migrationConserving : mig = 0) :
    Ledger initial p ((blocks.map (fun b => (items b).length)).sum) mig
        (c + credits (blocks.flatMap items)) after ∧
      Counts p ((blocks.map (fun b => (items b).length)).sum) mig :=
  dispatched_counts_from_credited priorL blocks hacc run hflat
    powBound migrationConserving

/-- Empty builder-pending / partial / builder-sweep priors: the
validator field is `sweepStage 16 0`. Public `Block` fields are
unchanged. -/
theorem blockOfElectra_empty_stages (slot : U64)
    (flagged : List (Item × Bool)) :
    let b := blockOfElectra slot true [] [] [] flagged
    builderPending b = [] ∧
      b.pendingPartial = [] ∧
      builderSweep b = [] ∧
      b.validators = sweepStage 16 0 flagged ∧
      b.parentFull = true := by
  simp [blockOfElectra, builderPending, builderSweep, queueStage,
    electraPartials, electraPartialLoop, sweepStage]

/-- Gloas:1879-1916 with empty first three lists: `items` of a full
parent is the Electra-credited Item projection. The visit keys stay
on `electraCreditEligible`, not on `Block`. -/
theorem items_of_electra_validator_block (slot : U64) (n start : Nat)
    (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n) :
    items (blockOfElectra slot true [] [] [] flagged) =
      creditedItems (electraCreditEligible n start 0 flagged) := by
  have ⟨hp, hpart, hsweep, hval, hfull⟩ :=
    blockOfElectra_empty_stages slot flagged
  have hex : expected (blockOfElectra slot true [] [] [] flagged) =
      sweepStage 16 0 flagged := by
    simp [expected, hp, hpart, hsweep, hval]
  have hitems : items (blockOfElectra slot true [] [] [] flagged) =
      expected (blockOfElectra slot true [] [] [] flagged) := by
    simp [items, hfull]
  rw [hitems, hex, electraCreditEligible_items hle]
  rfl

/-- `hflat` is derived from `blockOfElectra`, not named. Slot Nodup
is still `AcceptedBlocks`. -/
theorem dispatched_counts_from_electra_block
    {initial before after : AccountMap .EVM} {p mig c n start : Nat}
    {pre post : Clock} {s0 t0 : DualBalances} {slot : U64}
    {flagged : List (Item × Bool)}
    (priorL : Ledger initial p 0 mig c before)
    (hle : flagged.length ≤ validatorsSweepLimit n)
    (hacc : AcceptedBlocks pre [blockOfElectra slot true [] [] [] flagged] post)
    (run : CreditedRun s0 before
      (electraCreditEligible n start 0 flagged) t0 after)
    (powBound : p ≤ 2 ^ 64) (migrationConserving : mig = 0) :
    Ledger initial p
        (([blockOfElectra slot true [] [] [] flagged].map
            (fun b => (items b).length)).sum) mig
        (c + credits
          (List.flatMap items [blockOfElectra slot true [] [] [] flagged])) after ∧
      Counts p
        (([blockOfElectra slot true [] [] [] flagged].map
            (fun b => (items b).length)).sum) mig := by
  have hflat :
      List.flatMap items [blockOfElectra slot true [] [] [] flagged] =
        creditedItems (electraCreditEligible n start 0 flagged) := by
    simp [List.flatMap_cons, List.flatMap_nil,
      items_of_electra_validator_block slot n start flagged hle]
  exact dispatched_counts_from_electra_credits priorL
    [blockOfElectra slot true [] [] [] flagged] hacc run hflat
    powBound migrationConserving

theorem creditedItems_append (xs ys : List CreditedWithdrawal) :
    creditedItems (xs ++ ys) = creditedItems xs ++ creditedItems ys := by
  simp [creditedItems]

/-- Gloas:1805-1833 on credited queue entries: same break, keep
`validator_index`. -/
def creditQueueStage (limit prior : Nat) :
    List CreditedWithdrawal → List CreditedWithdrawal
  | [] => []
  | w :: rest =>
      if limit ≤ prior then []
      else w :: creditQueueStage limit (prior + 1) rest

theorem creditQueueStage_items (limit prior : Nat)
    (ws : List CreditedWithdrawal) :
    creditedItems (creditQueueStage limit prior ws) =
      queueStage limit prior (creditedItems ws) := by
  induction ws generalizing prior with
  | nil =>
    simp [creditQueueStage, queueStage, creditedItems]
  | cons w rest ih =>
    by_cases hl : limit ≤ prior
    · simp [creditQueueStage, queueStage, creditedItems, hl]
    · simp [creditQueueStage, queueStage, creditedItems, hl]
      simpa [creditedItems] using ih (prior + 1)

/-- Electra:1360-1398 queue entry carrying `validator_index`. -/
structure CreditedPartial where
  w : CreditedWithdrawal
  mature : Bool
  eligible : Bool

def asElectraPartial (c : CreditedPartial) : ElectraPartial where
  item := c.w.item
  mature := c.mature
  eligible := c.eligible

/-- Electra:1374-1396 on credited partials: same break, keep
`validator_index`. -/
def creditPartialLoop (limit prior : Nat) :
    List CreditedPartial → List CreditedWithdrawal
  | [] => []
  | c :: rest =>
      if !c.mature || decide (limit ≤ prior) then []
      else if c.eligible then
        c.w :: creditPartialLoop limit (prior + 1) rest
      else
        creditPartialLoop limit prior rest

theorem creditPartialLoop_items (limit prior : Nat)
    (cs : List CreditedPartial) :
    creditedItems (creditPartialLoop limit prior cs) =
      electraPartialLoop limit prior (cs.map asElectraPartial) := by
  induction cs generalizing prior with
  | nil =>
    simp [creditPartialLoop, electraPartialLoop, creditedItems]
  | cons c rest ih =>
    simp only [creditPartialLoop, electraPartialLoop, asElectraPartial,
      List.map_cons]
    by_cases hstop : !c.mature || decide (limit ≤ prior)
    · simp [hstop, creditedItems]
    · simp [hstop]
      cases c.eligible with
      | false =>
        simpa [creditedItems] using ih prior
      | true =>
        simpa [creditedItems] using ih (prior + 1)

def creditPartials (prior : Nat) (cs : List CreditedPartial) :
    List CreditedWithdrawal :=
  creditPartialLoop (electraPartialsLimit prior) prior cs

theorem creditPartials_items (prior : Nat) (cs : List CreditedPartial) :
    creditedItems (creditPartials prior cs) =
      electraPartials prior (cs.map asElectraPartial) := by
  simpa [creditPartials, electraPartials] using
    creditPartialLoop_items (electraPartialsLimit prior) prior cs

/-- Gloas:1839-1873 on credited builder entries: same eligibility
break, keep `validator_index`. -/
def creditSweepStage (limit prior : Nat) :
    List (CreditedWithdrawal × Bool) → List CreditedWithdrawal
  | [] => []
  | (w, eligible) :: rest =>
      if limit ≤ prior then []
      else if eligible then
        w :: creditSweepStage limit (prior + 1) rest
      else
        creditSweepStage limit prior rest

theorem creditSweepStage_items (limit prior : Nat)
    (cs : List (CreditedWithdrawal × Bool)) :
    creditedItems (creditSweepStage limit prior cs) =
      sweepStage limit prior (cs.map (fun p => (p.1.item, p.2))) := by
  induction cs generalizing prior with
  | nil =>
    simp [creditSweepStage, sweepStage, creditedItems]
  | cons entry rest ih =>
    obtain ⟨w, eligible⟩ := entry
    by_cases hl : limit ≤ prior
    · simp [creditSweepStage, sweepStage, creditedItems, hl]
    · cases eligible with
      | false =>
        simp only [creditSweepStage, sweepStage, hl, ↓reduceIte,
          Bool.false_eq_true, List.map_cons]
        simpa [creditedItems] using ih prior
      | true =>
        simp only [creditSweepStage, sweepStage, creditedItems, hl, ↓reduceIte,
          List.map_cons]
        simpa [creditedItems] using ih (prior + 1)

/-- Gloas:1879-1916: the four credited stages in source order.
Validator keys are `visitRing` via `electraCreditEligible`. Queue /
partial / builder-sweep keys stay on those credited inputs. -/
def gloasCredited (pending : List CreditedWithdrawal)
    (partials : List CreditedPartial)
    (builders : List (CreditedWithdrawal × Bool))
    (n start : Nat) (flagged : List (Item × Bool)) :
    List CreditedWithdrawal :=
  let first := creditQueueStage 15 0 pending
  let part := creditPartials first.length partials
  let sweep := creditSweepStage 15 (first.length + part.length) builders
  first ++ part ++ sweep ++
    electraCreditEligible n start (first.length + part.length + sweep.length)
      flagged

theorem creditQueueStage_length (limit prior : Nat)
    (ws : List CreditedWithdrawal) :
    (creditQueueStage limit prior ws).length =
      (queueStage limit prior (creditedItems ws)).length :=
  (creditedItems_length (creditQueueStage limit prior ws)).symm.trans
    (congrArg List.length (creditQueueStage_items limit prior ws))

theorem creditPartials_length (prior : Nat) (cs : List CreditedPartial) :
    (creditPartials prior cs).length =
      (electraPartials prior (cs.map asElectraPartial)).length :=
  (creditedItems_length (creditPartials prior cs)).symm.trans
    (congrArg List.length (creditPartials_items prior cs))

theorem creditSweepStage_length (limit prior : Nat)
    (cs : List (CreditedWithdrawal × Bool)) :
    (creditSweepStage limit prior cs).length =
      (sweepStage limit prior (cs.map (fun p => (p.1.item, p.2)))).length :=
  (creditedItems_length (creditSweepStage limit prior cs)).symm.trans
    (congrArg List.length (creditSweepStage_items limit prior cs))

/-- Gloas:1879-1916: each credited stage projects to the Item stage
`blockOfElectra` already concatenates. Priors are the credited
lengths, rewritten by the projection lemmas, not assumed. -/
theorem gloasCredited_items (slot : U64)
    (pending : List CreditedWithdrawal)
    (partials : List CreditedPartial)
    (builders : List (CreditedWithdrawal × Bool))
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n) :
    creditedItems (gloasCredited pending partials builders n start flagged) =
      expected (blockOfElectra slot true (creditedItems pending)
        (partials.map asElectraPartial)
        (builders.map (fun p => (p.1.item, p.2))) flagged) := by
  have hfirst :
      creditedItems (creditQueueStage 15 0 pending) =
        queueStage 15 0 (creditedItems pending) :=
    creditQueueStage_items 15 0 pending
  have hpart :
      creditedItems (creditPartials (creditQueueStage 15 0 pending).length partials) =
        electraPartials (queueStage 15 0 (creditedItems pending)).length
          (partials.map asElectraPartial) := by
    rw [creditPartials_items, creditQueueStage_length]
  have hsweep :
      creditedItems (creditSweepStage 15
          ((creditQueueStage 15 0 pending).length +
            (creditPartials (creditQueueStage 15 0 pending).length partials).length)
          builders) =
        sweepStage 15
          ((queueStage 15 0 (creditedItems pending)).length +
            (electraPartials (queueStage 15 0 (creditedItems pending)).length
              (partials.map asElectraPartial)).length)
          (builders.map (fun p => (p.1.item, p.2))) := by
    rw [creditSweepStage_items, creditQueueStage_length, creditPartials_length]
  have hval :
      creditedItems (electraCreditEligible n start
          ((creditQueueStage 15 0 pending).length +
            (creditPartials (creditQueueStage 15 0 pending).length partials).length +
            (creditSweepStage 15
              ((creditQueueStage 15 0 pending).length +
                (creditPartials (creditQueueStage 15 0 pending).length partials).length)
              builders).length)
          flagged) =
        sweepStage 16
          ((queueStage 15 0 (creditedItems pending)).length +
            (electraPartials (queueStage 15 0 (creditedItems pending)).length
              (partials.map asElectraPartial)).length +
            (sweepStage 15
              ((queueStage 15 0 (creditedItems pending)).length +
                (electraPartials (queueStage 15 0 (creditedItems pending)).length
                  (partials.map asElectraPartial)).length)
              (builders.map (fun p => (p.1.item, p.2)))).length)
          flagged := by
    rw [electraCreditEligible_items hle, creditQueueStage_length,
      creditPartials_length, creditSweepStage_length]
    simp [MAX_WITHDRAWALS_PER_PAYLOAD]
  have hex :
      expected (blockOfElectra slot true (creditedItems pending)
          (partials.map asElectraPartial)
          (builders.map (fun p => (p.1.item, p.2))) flagged) =
        queueStage 15 0 (creditedItems pending) ++
          electraPartials (queueStage 15 0 (creditedItems pending)).length
            (partials.map asElectraPartial) ++
          sweepStage 15
            ((queueStage 15 0 (creditedItems pending)).length +
              (electraPartials (queueStage 15 0 (creditedItems pending)).length
                (partials.map asElectraPartial)).length)
            (builders.map (fun p => (p.1.item, p.2))) ++
          sweepStage 16
            ((queueStage 15 0 (creditedItems pending)).length +
              (electraPartials (queueStage 15 0 (creditedItems pending)).length
                (partials.map asElectraPartial)).length +
              (sweepStage 15
                ((queueStage 15 0 (creditedItems pending)).length +
                  (electraPartials (queueStage 15 0 (creditedItems pending)).length
                    (partials.map asElectraPartial)).length)
                (builders.map (fun p => (p.1.item, p.2)))).length)
            flagged := by
    simp only [expected, builderPending, builderSweep, blockOfElectra]
  dsimp only [gloasCredited]
  rw [creditedItems_append, creditedItems_append, creditedItems_append]
  rw [hfirst, hpart, hsweep, hval, hex]

/-- Gloas:1999 full parent: `items` is the four-stage credited
projection, including nonempty builder-pending / partial /
builder-sweep priors. Visit keys stay off `Block`. -/
theorem items_of_gloas_credited (slot : U64)
    (pending : List CreditedWithdrawal)
    (partials : List CreditedPartial)
    (builders : List (CreditedWithdrawal × Bool))
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n) :
    items (blockOfElectra slot true (creditedItems pending)
        (partials.map asElectraPartial)
        (builders.map (fun p => (p.1.item, p.2))) flagged) =
      creditedItems (gloasCredited pending partials builders n start flagged) := by
  have hfull :
      (blockOfElectra slot true (creditedItems pending)
          (partials.map asElectraPartial)
          (builders.map (fun p => (p.1.item, p.2))) flagged).parentFull = true :=
    rfl
  simp only [items, hfull]
  exact (gloasCredited_items slot pending partials builders n start flagged hle).symm

/-- `hflat` is derived from `gloasCredited_items`, not named. Slot
Nodup is still `AcceptedBlocks`. -/
theorem dispatched_counts_from_gloas_credited
    {initial before after : AccountMap .EVM} {p mig c n start : Nat}
    {pre post : Clock} {s0 t0 : DualBalances} {slot : U64}
    {pending : List CreditedWithdrawal}
    {partials : List CreditedPartial}
    {builders : List (CreditedWithdrawal × Bool)}
    {flagged : List (Item × Bool)}
    (priorL : Ledger initial p 0 mig c before)
    (hle : flagged.length ≤ validatorsSweepLimit n)
    (hacc : AcceptedBlocks pre
      [blockOfElectra slot true (creditedItems pending)
        (partials.map asElectraPartial)
        (builders.map (fun p => (p.1.item, p.2))) flagged] post)
    (run : CreditedRun s0 before
      (gloasCredited pending partials builders n start flagged) t0 after)
    (powBound : p ≤ 2 ^ 64) (migrationConserving : mig = 0) :
    Ledger initial p
        (([blockOfElectra slot true (creditedItems pending)
            (partials.map asElectraPartial)
            (builders.map (fun p => (p.1.item, p.2))) flagged].map
            (fun b => (items b).length)).sum) mig
        (c + credits
          (List.flatMap items
            [blockOfElectra slot true (creditedItems pending)
              (partials.map asElectraPartial)
              (builders.map (fun p => (p.1.item, p.2))) flagged])) after ∧
      Counts p
        (([blockOfElectra slot true (creditedItems pending)
            (partials.map asElectraPartial)
            (builders.map (fun p => (p.1.item, p.2))) flagged].map
            (fun b => (items b).length)).sum) mig := by
  have hflat :
      List.flatMap items
        [blockOfElectra slot true (creditedItems pending)
          (partials.map asElectraPartial)
          (builders.map (fun p => (p.1.item, p.2))) flagged] =
        creditedItems (gloasCredited pending partials builders n start flagged) := by
    simp [List.flatMap_cons, List.flatMap_nil,
      items_of_gloas_credited slot pending partials builders n start flagged hle]
  exact dispatched_counts_from_credited priorL
    [blockOfElectra slot true (creditedItems pending)
      (partials.map asElectraPartial)
      (builders.map (fun p => (p.1.item, p.2))) flagged] hacc run hflat
    powBound migrationConserving

/-- Full-parent Gloas block whose four Item stages are the projections
of the credited inputs. Public `Block` fields stay the constructor's. -/
def gloasBlock (slot : U64)
    (pending : List CreditedWithdrawal)
    (partials : List CreditedPartial)
    (builders : List (CreditedWithdrawal × Bool))
    (flagged : List (Item × Bool)) : Block :=
  blockOfElectra slot true (creditedItems pending)
    (partials.map asElectraPartial)
    (builders.map (fun p => (p.1.item, p.2))) flagged

theorem items_of_gloasBlock (slot : U64)
    (pending : List CreditedWithdrawal)
    (partials : List CreditedPartial)
    (builders : List (CreditedWithdrawal × Bool))
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n) :
    items (gloasBlock slot pending partials builders flagged) =
      creditedItems (gloasCredited pending partials builders n start flagged) :=
  items_of_gloas_credited slot pending partials builders n start flagged hle

/-- Capella:452/458 + Gloas:1879-1916: the indexed walk of a
full-parent Gloas block is the stamp of `gloasCredited`. -/
theorem indexedChain_of_gloas_block (wstart : Nat) (slot : U64)
    (pending : List CreditedWithdrawal)
    (partials : List CreditedPartial)
    (builders : List (CreditedWithdrawal × Bool))
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n) :
    indexedChain wstart [gloasBlock slot pending partials builders flagged] =
      archivedIndexed (stampIndex wstart
        (gloasCredited pending partials builders n start flagged)) := by
  have hpair := indexedChain_of_credited wstart
    [(gloasBlock slot pending partials builders flagged,
      gloasCredited pending partials builders n start flagged)]
    (by
      intro p hp
      have hp' : p =
          (gloasBlock slot pending partials builders flagged,
            gloasCredited pending partials builders n start flagged) :=
        List.mem_singleton.mp hp
      rw [hp']
      exact items_of_gloasBlock slot pending partials builders n start flagged hle)
  simpa [stampedChain, archivedIndexed_append, archivedIndexed] using hpair

/-- Capella:510: the second full-parent Gloas payload continues the
running index. The consumer flat list is not a premise. -/
theorem indexedChain_of_two_gloas (wstart : Nat)
    (slot₁ slot₂ : U64)
    (pending₁ pending₂ : List CreditedWithdrawal)
    (partials₁ partials₂ : List CreditedPartial)
    (builders₁ builders₂ : List (CreditedWithdrawal × Bool))
    (n₁ start₁ n₂ start₂ : Nat)
    (flagged₁ flagged₂ : List (Item × Bool))
    (hle₁ : flagged₁.length ≤ validatorsSweepLimit n₁)
    (hle₂ : flagged₂.length ≤ validatorsSweepLimit n₂) :
    indexedChain wstart
      [gloasBlock slot₁ pending₁ partials₁ builders₁ flagged₁,
        gloasBlock slot₂ pending₂ partials₂ builders₂ flagged₂] =
      archivedIndexed (stampedChain wstart
        [gloasCredited pending₁ partials₁ builders₁ n₁ start₁ flagged₁,
          gloasCredited pending₂ partials₂ builders₂ n₂ start₂ flagged₂]) := by
  have h1 := items_of_gloasBlock slot₁ pending₁ partials₁ builders₁ n₁ start₁
    flagged₁ hle₁
  have h2 := items_of_gloasBlock slot₂ pending₂ partials₂ builders₂ n₂ start₂
    flagged₂ hle₂
  simp only [indexedChain, stampedChain, archivedIndexed_append]
  rw [h1, nextIndexAfter_eq, creditedItems_length, h2]
  simp only [List.append_nil]
  rw [stampIndex_indexed, stampIndex_indexed]
  simp [archivedIndexed]

/-- `hflat` is derived from the stamp of `gloasCredited`, not named. -/
theorem dispatched_counts_from_stamped_gloas
    {initial before after : AccountMap .EVM} {p mig c n start wstart : Nat}
    {pre post : Clock} {s0 t0 : DualBalances} {slot : U64}
    {pending : List CreditedWithdrawal}
    {partials : List CreditedPartial}
    {builders : List (CreditedWithdrawal × Bool)}
    {flagged : List (Item × Bool)}
    (priorL : Ledger initial p 0 mig c before)
    (hle : flagged.length ≤ validatorsSweepLimit n)
    (hacc : AcceptedBlocks pre
      [gloasBlock slot pending partials builders flagged] post)
    (run : CreditedRun s0 before
      (archivedCredited (stampIndex wstart
        (gloasCredited pending partials builders n start flagged))) t0 after)
    (powBound : p ≤ 2 ^ 64) (migrationConserving : mig = 0) :
    Ledger initial p
        (([gloasBlock slot pending partials builders flagged].map
            (fun b => (items b).length)).sum) mig
        (c + credits
          (List.flatMap items
            [gloasBlock slot pending partials builders flagged])) after ∧
      Counts p
        (([gloasBlock slot pending partials builders flagged].map
            (fun b => (items b).length)).sum) mig := by
  have hflat :
      List.flatMap items [gloasBlock slot pending partials builders flagged] =
        archivedItems (stampIndex wstart
          (gloasCredited pending partials builders n start flagged)) := by
    simp [List.flatMap_cons, List.flatMap_nil,
      items_of_gloasBlock slot pending partials builders n start flagged hle,
      stampIndex_items]
  exact dispatched_counts_from_stamped priorL
    [gloasBlock slot pending partials builders flagged] hacc run hflat
    powBound migrationConserving

/-- Gloas:1824-1830 `builder_pending_withdrawals` entry: `builder_index`
plus `fee_recipient`/`amount`. SSZ decode of those fields remains named. -/
structure BuilderPending where
  builderIndex : Nat
  item : Item

/-- Gloas:1826 `convert_builder_index_to_validator_index(builder_index)`. -/
def asQueueCredited (p : BuilderPending) : CreditedWithdrawal where
  validatorIndex := toValidatorIndex p.builderIndex
  item := p.item

/-- Gloas:1859-1866 sweep visit: the cursor `builder_index` plus the
archived eligibility `withdrawable_epoch <= epoch and balance > 0`. -/
structure BuilderSweepVisit where
  builderIndex : Nat
  item : Item
  eligible : Bool

def asSweepCredited (p : BuilderSweepVisit) : CreditedWithdrawal × Bool :=
  ({ validatorIndex := toValidatorIndex p.builderIndex, item := p.item },
    p.eligible)

theorem asQueueCredited_is_builder (p : BuilderPending) :
    isBuilderIndex (asQueueCredited p).validatorIndex = true :=
  toValidatorIndex_is_builder p.builderIndex

theorem asSweepCredited_is_builder (p : BuilderSweepVisit) :
    isBuilderIndex (asSweepCredited p).1.validatorIndex = true :=
  toValidatorIndex_is_builder p.builderIndex

theorem creditedItems_asQueue (pending : List BuilderPending) :
    creditedItems (pending.map asQueueCredited) = pending.map (·.item) := by
  simp [creditedItems, asQueueCredited]

/-- Gloas:1805-1833 on archived builder-pending entries. -/
def creditBuilderQueue (pending : List BuilderPending) : List CreditedWithdrawal :=
  creditQueueStage 15 0 (pending.map asQueueCredited)

theorem creditBuilderQueue_items (pending : List BuilderPending) :
    creditedItems (creditBuilderQueue pending) =
      queueStage 15 0 (pending.map (·.item)) := by
  simpa [creditBuilderQueue, creditedItems_asQueue] using
    creditQueueStage_items 15 0 (pending.map asQueueCredited)

theorem creditQueueStage_indices_sublist (limit prior : Nat)
    (ws : List CreditedWithdrawal) :
    List.Sublist
      ((creditQueueStage limit prior ws).map (·.validatorIndex))
      (ws.map (·.validatorIndex)) := by
  induction ws generalizing prior with
  | nil =>
    simp [creditQueueStage]
  | cons w rest ih =>
    by_cases hl : limit ≤ prior
    · simp [creditQueueStage, hl]
    · simp only [creditQueueStage, hl, ↓reduceIte, List.map_cons]
      exact List.Sublist.cons_cons w.validatorIndex (ih (prior + 1))

theorem creditBuilderQueue_is_builder (pending : List BuilderPending) :
    ∀ w ∈ creditBuilderQueue pending, isBuilderIndex w.validatorIndex = true := by
  intro w hw
  have hsub := creditQueueStage_indices_sublist 15 0 (pending.map asQueueCredited)
  have hmem : w.validatorIndex ∈
      (pending.map asQueueCredited).map (·.validatorIndex) :=
    List.Sublist.mem (List.mem_map.mpr ⟨w, hw, rfl⟩) hsub
  simp only [List.mem_map] at hmem
  obtain ⟨p, hp, heq⟩ := hmem
  obtain ⟨q, hq, rfl⟩ := hp
  rw [← heq]
  exact asQueueCredited_is_builder q

theorem creditBuilderQueue_pairs_are_builder (pending : List BuilderPending) :
    ∀ p ∈ creditedPairs (creditBuilderQueue pending),
      isBuilderIndex p.1 = true := by
  intro p hp
  simp only [creditedPairs, List.mem_map] at hp
  obtain ⟨w, hw, rfl⟩ := hp
  exact creditBuilderQueue_is_builder pending w hw

/-- Gloas:1826 then 1927: queued `builder_index` writes
`state.builders[b]` when every archived index is flag-clear and
`< len(builders)`. -/
theorem creditBuilderQueue_inRange
    {pending : List BuilderPending} {nv nb : Nat}
    (hp : ∀ p ∈ pending,
      p.builderIndex < BUILDER_INDEX_FLAG ∧ p.builderIndex < nb) :
    ∀ q ∈ creditedPairs (creditBuilderQueue pending),
      IndexInRange nv nb q.1 := by
  intro q hq
  simp only [creditedPairs, List.mem_map] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  have hsub := creditQueueStage_indices_sublist 15 0 (pending.map asQueueCredited)
  have hmem : w.validatorIndex ∈
      (pending.map asQueueCredited).map (·.validatorIndex) :=
    List.Sublist.mem (List.mem_map.mpr ⟨w, hw, rfl⟩) hsub
  simp only [List.mem_map] at hmem
  obtain ⟨p, hp', heq⟩ := hmem
  obtain ⟨bp, hbp, rfl⟩ := hp'
  have hb := hp bp hbp
  rw [← heq]
  exact indexInRange_toValidatorIndex hb.1 hb.2

/-- Gloas:1926-1927: a builder-pending payload writes `state.builders`,
not `state.balances`. -/
theorem creditBuilderQueue_keeps_validators (s : DualBalances)
    (pending : List BuilderPending) :
    (applyTagged s (creditedPairs (creditBuilderQueue pending))).validators =
      s.validators :=
  applyTagged_builders_only s _ (creditBuilderQueue_pairs_are_builder pending)

/-- Gloas:1839-1873 on archived builder-sweep visits. -/
def creditBuilderSweep (prior : Nat) (vs : List BuilderSweepVisit) :
    List CreditedWithdrawal :=
  creditSweepStage 15 prior (vs.map asSweepCredited)

theorem creditSweepStage_indices_sublist (limit prior : Nat)
    (cs : List (CreditedWithdrawal × Bool)) :
    List.Sublist
      ((creditSweepStage limit prior cs).map (·.validatorIndex))
      (cs.map (fun p => p.1.validatorIndex)) := by
  induction cs generalizing prior with
  | nil =>
    simp [creditSweepStage]
  | cons entry rest ih =>
    obtain ⟨w, eligible⟩ := entry
    by_cases hl : limit ≤ prior
    · simp [creditSweepStage, hl]
    · cases eligible with
      | false =>
        simp only [creditSweepStage, hl, ↓reduceIte, Bool.false_eq_true,
          List.map_cons]
        exact List.Sublist.cons w.validatorIndex (ih prior)
      | true =>
        simp only [creditSweepStage, hl, ↓reduceIte, List.map_cons]
        exact List.Sublist.cons_cons w.validatorIndex (ih (prior + 1))

theorem creditBuilderSweep_is_builder (prior : Nat)
    (vs : List BuilderSweepVisit) :
    ∀ w ∈ creditBuilderSweep prior vs,
      isBuilderIndex w.validatorIndex = true := by
  intro w hw
  have hsub := creditSweepStage_indices_sublist 15 prior (vs.map asSweepCredited)
  have hmem : w.validatorIndex ∈
      (vs.map asSweepCredited).map (fun p => p.1.validatorIndex) :=
    List.Sublist.mem (List.mem_map.mpr ⟨w, hw, rfl⟩) hsub
  simp only [List.mem_map] at hmem
  obtain ⟨p, hp, heq⟩ := hmem
  obtain ⟨q, hq, rfl⟩ := hp
  rw [← heq]
  exact asSweepCredited_is_builder q

theorem creditBuilderSweep_pairs_are_builder (prior : Nat)
    (vs : List BuilderSweepVisit) :
    ∀ p ∈ creditedPairs (creditBuilderSweep prior vs),
      isBuilderIndex p.1 = true := by
  intro p hp
  simp only [creditedPairs, List.mem_map] at hp
  obtain ⟨w, hw, rfl⟩ := hp
  exact creditBuilderSweep_is_builder prior vs w hw

/-- Gloas:1863 then 1927: sweep `builder_index` writes
`state.builders[b]` under the same flag-clear / length guard. -/
theorem creditBuilderSweep_inRange
    {prior nv nb : Nat} {vs : List BuilderSweepVisit}
    (hp : ∀ p ∈ vs,
      p.builderIndex < BUILDER_INDEX_FLAG ∧ p.builderIndex < nb) :
    ∀ q ∈ creditedPairs (creditBuilderSweep prior vs),
      IndexInRange nv nb q.1 := by
  intro q hq
  simp only [creditedPairs, List.mem_map] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  have hsub := creditSweepStage_indices_sublist 15 prior (vs.map asSweepCredited)
  have hmem : w.validatorIndex ∈
      (vs.map asSweepCredited).map (fun p => p.1.validatorIndex) :=
    List.Sublist.mem (List.mem_map.mpr ⟨w, hw, rfl⟩) hsub
  simp only [List.mem_map] at hmem
  obtain ⟨p, hp', heq⟩ := hmem
  obtain ⟨bp, hbp, rfl⟩ := hp'
  have hb := hp bp hbp
  rw [← heq]
  exact indexInRange_toValidatorIndex hb.1 hb.2

theorem creditBuilderSweep_keeps_validators (s : DualBalances) (prior : Nat)
    (vs : List BuilderSweepVisit) :
    (applyTagged s (creditedPairs (creditBuilderSweep prior vs))).validators =
      s.validators :=
  applyTagged_builders_only s _ (creditBuilderSweep_pairs_are_builder prior vs)

theorem creditPartialLoop_indices_sublist (limit prior : Nat)
    (cs : List CreditedPartial) :
    List.Sublist
      ((creditPartialLoop limit prior cs).map (·.validatorIndex))
      (cs.map (fun c => c.w.validatorIndex)) := by
  induction cs generalizing prior with
  | nil =>
    simp [creditPartialLoop]
  | cons c rest ih =>
    simp only [creditPartialLoop, List.map_cons]
    by_cases hstop : !c.mature || decide (limit ≤ prior)
    · simp [hstop]
    · simp only [hstop, ↓reduceIte]
      cases c.eligible with
      | false =>
        exact List.Sublist.cons c.w.validatorIndex (ih prior)
      | true =>
        exact List.Sublist.cons_cons c.w.validatorIndex (ih (prior + 1))

theorem creditPartials_not_builder
    {cs : List CreditedPartial} (prior : Nat)
    (h : ∀ c ∈ cs, c.w.validatorIndex < BUILDER_INDEX_FLAG) :
    ∀ w ∈ creditPartials prior cs,
      isBuilderIndex w.validatorIndex = false := by
  intro w hw
  have hsub := creditPartialLoop_indices_sublist (electraPartialsLimit prior) prior cs
  have hmem : w.validatorIndex ∈ cs.map (fun c => c.w.validatorIndex) :=
    List.Sublist.mem
      (by
        have : w ∈ creditPartialLoop (electraPartialsLimit prior) prior cs := by
          simpa [creditPartials] using hw
        exact List.mem_map.mpr ⟨w, this, rfl⟩)
      hsub
  simp only [List.mem_map] at hmem
  obtain ⟨c, hc, heq⟩ := hmem
  rw [← heq]
  exact isBuilderIndex_of_lt (h c hc)

theorem creditPartials_pairs_not_builder
    {cs : List CreditedPartial} (prior : Nat)
    (h : ∀ c ∈ cs, c.w.validatorIndex < BUILDER_INDEX_FLAG) :
    ∀ p ∈ creditedPairs (creditPartials prior cs),
      isBuilderIndex p.1 = false := by
  intro p hp
  simp only [creditedPairs, List.mem_map] at hp
  obtain ⟨w, hw, rfl⟩ := hp
  exact creditPartials_not_builder prior h w hw

/-- Electra:1388 copies `PendingPartialWithdrawal.validator_index`.
Those keys write `state.balances[i]` when `i < len(validators)`. -/
theorem creditPartials_inRange
    {cs : List CreditedPartial} {nv nb prior : Nat}
    (h : ∀ c ∈ cs,
      c.w.validatorIndex < nv ∧ c.w.validatorIndex < BUILDER_INDEX_FLAG) :
    ∀ q ∈ creditedPairs (creditPartials prior cs),
      IndexInRange nv nb q.1 := by
  intro q hq
  have hnb := creditPartials_pairs_not_builder prior (fun c hc => (h c hc).2) q hq
  simp only [creditedPairs, List.mem_map] at hq
  obtain ⟨w, hw, rfl⟩ := hq
  have hsub := creditPartialLoop_indices_sublist (electraPartialsLimit prior) prior cs
  have hmem : w.validatorIndex ∈ cs.map (fun c => c.w.validatorIndex) :=
    List.Sublist.mem
      (by
        have : w ∈ creditPartialLoop (electraPartialsLimit prior) prior cs := by
          simpa [creditPartials] using hw
        exact List.mem_map.mpr ⟨w, this, rfl⟩)
      hsub
  simp only [List.mem_map] at hmem
  obtain ⟨c, hc, heq⟩ := hmem
  have hlt : w.validatorIndex < nv := by
    rw [← heq]
    exact (h c hc).1
  simp [IndexInRange, hnb]
  exact hlt

/-- Electra:1388 copies `PendingPartialWithdrawal.validator_index`;
those keys write `state.balances`, not `state.builders`. -/
theorem creditPartials_keeps_builders
    (s : DualBalances) {cs : List CreditedPartial} (prior : Nat)
    (h : ∀ c ∈ cs, c.w.validatorIndex < BUILDER_INDEX_FLAG) :
    (applyTagged s (creditedPairs (creditPartials prior cs))).builders =
      s.builders :=
  applyTagged_validators_keep_builders s _
    (creditPartials_pairs_not_builder prior h)

/-- Gloas:1879-1916 from archived builder_index / validator_index
fields. Queue and builder-sweep keys are `toValidatorIndex`; partial
and validator keys stay as supplied. -/
def gloasFromBuilders (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool)) :
    List CreditedWithdrawal :=
  gloasCredited (pending.map asQueueCredited) partials
    (sweeps.map asSweepCredited) n start flagged

theorem items_of_gloasFromBuilders (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n) :
    items (blockOfElectra slot true (pending.map (·.item))
        (partials.map asElectraPartial)
        (sweeps.map (fun p => (p.item, p.eligible))) flagged) =
      creditedItems (gloasFromBuilders pending partials sweeps n start flagged) := by
  have hpend : pending.map (·.item) =
      creditedItems (pending.map asQueueCredited) :=
    (creditedItems_asQueue pending).symm
  have hsweep :
      sweeps.map (fun p => (p.item, p.eligible)) =
        (sweeps.map asSweepCredited).map (fun p => (p.1.item, p.2)) := by
    simp [asSweepCredited]
  rw [hpend, hsweep]
  simpa [gloasFromBuilders] using
    items_of_gloas_credited slot (pending.map asQueueCredited) partials
      (sweeps.map asSweepCredited) n start flagged hle

theorem dispatched_counts_from_gloasFromBuilders
    {initial before after : AccountMap .EVM} {p mig c n start : Nat}
    {pre post : Clock} {s0 t0 : DualBalances} {slot : U64}
    {pending : List BuilderPending}
    {partials : List CreditedPartial}
    {sweeps : List BuilderSweepVisit}
    {flagged : List (Item × Bool)}
    (priorL : Ledger initial p 0 mig c before)
    (hle : flagged.length ≤ validatorsSweepLimit n)
    (hacc : AcceptedBlocks pre
      [blockOfElectra slot true (pending.map (·.item))
        (partials.map asElectraPartial)
        (sweeps.map (fun p => (p.item, p.eligible))) flagged] post)
    (run : CreditedRun s0 before
      (gloasFromBuilders pending partials sweeps n start flagged) t0 after)
    (powBound : p ≤ 2 ^ 64) (migrationConserving : mig = 0) :
    Ledger initial p
        (([blockOfElectra slot true (pending.map (·.item))
            (partials.map asElectraPartial)
            (sweeps.map (fun p => (p.item, p.eligible))) flagged].map
            (fun b => (items b).length)).sum) mig
        (c + credits
          (List.flatMap items
            [blockOfElectra slot true (pending.map (·.item))
              (partials.map asElectraPartial)
              (sweeps.map (fun p => (p.item, p.eligible))) flagged])) after ∧
      Counts p
        (([blockOfElectra slot true (pending.map (·.item))
            (partials.map asElectraPartial)
            (sweeps.map (fun p => (p.item, p.eligible))) flagged].map
            (fun b => (items b).length)).sum) mig := by
  have hflat :
      List.flatMap items
        [blockOfElectra slot true (pending.map (·.item))
          (partials.map asElectraPartial)
          (sweeps.map (fun p => (p.item, p.eligible))) flagged] =
        creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged) := by
    simp [List.flatMap_cons, List.flatMap_nil,
      items_of_gloasFromBuilders slot pending partials sweeps n start flagged hle]
  exact dispatched_counts_from_credited priorL
    [blockOfElectra slot true (pending.map (·.item))
      (partials.map asElectraPartial)
      (sweeps.map (fun p => (p.item, p.eligible))) flagged] hacc run hflat
    powBound migrationConserving

/-- Gloas:1879-1916: the four stages are the archived concatenation,
not a second payload. Queue / sweep keys are converted builder
indices; partial / Electra keys stay as supplied. -/
theorem gloasFromBuilders_eq_stages
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool)) :
    gloasFromBuilders pending partials sweeps n start flagged =
      creditBuilderQueue pending ++
      creditPartials (creditBuilderQueue pending).length partials ++
      creditBuilderSweep
        ((creditBuilderQueue pending).length +
          (creditPartials (creditBuilderQueue pending).length partials).length)
        sweeps ++
      electraCreditEligible n start
        ((creditBuilderQueue pending).length +
          (creditPartials (creditBuilderQueue pending).length partials).length +
          (creditBuilderSweep
            ((creditBuilderQueue pending).length +
              (creditPartials (creditBuilderQueue pending).length partials).length)
            sweeps).length)
        flagged := by
  unfold gloasFromBuilders gloasCredited creditBuilderQueue creditBuilderSweep
  rfl

/-- Gloas:1926-1931 on the four archived stages: every credited key is
in range when queue/sweep `builder_index` and partial `validator_index`
are, and the Electra visit ring is a registry no larger than both
`len(validators)` and the flag. -/
theorem gloasFromBuilders_pairs_inRange
    {pending : List BuilderPending}
    {partials : List CreditedPartial}
    {sweeps : List BuilderSweepVisit}
    {n start nv nb : Nat} {flagged : List (Item × Bool)}
    (hq : ∀ p ∈ pending,
      p.builderIndex < BUILDER_INDEX_FLAG ∧ p.builderIndex < nb)
    (hp : ∀ c ∈ partials,
      c.w.validatorIndex < nv ∧ c.w.validatorIndex < BUILDER_INDEX_FLAG)
    (hs : ∀ p ∈ sweeps,
      p.builderIndex < BUILDER_INDEX_FLAG ∧ p.builderIndex < nb)
    (hstart : SweepStart n start) (hn : n ≤ nv)
    (hnflag : n ≤ BUILDER_INDEX_FLAG) :
    ∀ q ∈ creditedPairs (gloasFromBuilders pending partials sweeps n start
        flagged),
      IndexInRange nv nb q.1 := by
  intro q hqmem
  rw [gloasFromBuilders_eq_stages, creditedPairs_append, creditedPairs_append,
    creditedPairs_append, List.mem_append] at hqmem
  rcases hqmem with (hpre | hel)
  · rw [List.mem_append] at hpre
    rcases hpre with (hpre | hsw)
    · rw [List.mem_append] at hpre
      rcases hpre with (hq' | hp')
      · exact creditBuilderQueue_inRange hq q hq'
      · exact creditPartials_inRange hp q hp'
    · exact creditBuilderSweep_inRange hs q hsw
  · exact electraCreditEligible_inRange hstart hn hnflag q hel

theorem applyTagged_gloasFromBuilders_keeps_validator_oob
    (s : DualBalances) {pending : List BuilderPending}
    {partials : List CreditedPartial}
    {sweeps : List BuilderSweepVisit}
    {n start nv nb j : Nat} {flagged : List (Item × Bool)}
    (hq : ∀ p ∈ pending,
      p.builderIndex < BUILDER_INDEX_FLAG ∧ p.builderIndex < nb)
    (hp : ∀ c ∈ partials,
      c.w.validatorIndex < nv ∧ c.w.validatorIndex < BUILDER_INDEX_FLAG)
    (hs : ∀ p ∈ sweeps,
      p.builderIndex < BUILDER_INDEX_FLAG ∧ p.builderIndex < nb)
    (hstart : SweepStart n start) (hn : n ≤ nv)
    (hnflag : n ≤ BUILDER_INDEX_FLAG) (hj : nv ≤ j) :
    (applyTagged s (creditedPairs
        (gloasFromBuilders pending partials sweeps n start flagged))).validators j =
      s.validators j :=
  applyTagged_keeps_validator_oob s _ nv nb j
    (gloasFromBuilders_pairs_inRange hq hp hs hstart hn hnflag) hj

theorem applyTagged_gloasFromBuilders_keeps_builder_oob
    (s : DualBalances) {pending : List BuilderPending}
    {partials : List CreditedPartial}
    {sweeps : List BuilderSweepVisit}
    {n start nv nb j : Nat} {flagged : List (Item × Bool)}
    (hq : ∀ p ∈ pending,
      p.builderIndex < BUILDER_INDEX_FLAG ∧ p.builderIndex < nb)
    (hp : ∀ c ∈ partials,
      c.w.validatorIndex < nv ∧ c.w.validatorIndex < BUILDER_INDEX_FLAG)
    (hs : ∀ p ∈ sweeps,
      p.builderIndex < BUILDER_INDEX_FLAG ∧ p.builderIndex < nb)
    (hstart : SweepStart n start) (hn : n ≤ nv)
    (hnflag : n ≤ BUILDER_INDEX_FLAG) (hj : nb ≤ j) :
    (applyTagged s (creditedPairs
        (gloasFromBuilders pending partials sweeps n start flagged))).builders j =
      s.builders j :=
  applyTagged_keeps_builder_oob s _ nv nb j
    (gloasFromBuilders_pairs_inRange hq hp hs hstart hn hnflag) hj

/-- Gloas:1924-1931 on the archived four-stage order: builder stages
leave `state.balances` untouched, so the net validator write is the
partials fold then the Electra fold. The consumer flat list is not
named. -/
theorem applyTagged_mixed_validators
    (s : DualBalances)
    (q part sw el : List (Nat × Nat))
    (hq : ∀ p ∈ q, isBuilderIndex p.1 = true)
    (hpart : ∀ p ∈ part, isBuilderIndex p.1 = false)
    (hsw : ∀ p ∈ sw, isBuilderIndex p.1 = true)
    (hel : ∀ p ∈ el, isBuilderIndex p.1 = false) :
    (applyTagged s (q ++ part ++ sw ++ el)).validators =
      (applyTagged (applyTagged s part) el).validators := by
  rw [applyTagged_append s ((q ++ part) ++ sw) el,
    applyTagged_append s (q ++ part) sw,
    applyTagged_append s q part]
  have hqv : (applyTagged s q).validators = s.validators :=
    applyTagged_builders_only s q hq
  have hswv :
      (applyTagged (applyTagged (applyTagged s q) part) sw).validators =
        (applyTagged (applyTagged s q) part).validators :=
    applyTagged_builders_only (applyTagged (applyTagged s q) part) sw hsw
  have hpartv :
      (applyTagged (applyTagged s q) part).validators =
        (applyTagged s part).validators :=
    applyTagged_validators_eq_of_validators_eq
      (applyTagged s q) s part hpart hqv
  have h1 :
      (applyTagged (applyTagged (applyTagged (applyTagged s q) part) sw) el).validators =
        (applyTagged (applyTagged (applyTagged s q) part) el).validators :=
    applyTagged_validators_eq_of_validators_eq
      (applyTagged (applyTagged (applyTagged s q) part) sw)
      (applyTagged (applyTagged s q) part) el hel hswv
  have h2 :
      (applyTagged (applyTagged (applyTagged s q) part) el).validators =
        (applyTagged (applyTagged s part) el).validators :=
    applyTagged_validators_eq_of_validators_eq
      (applyTagged (applyTagged s q) part) (applyTagged s part) el hel hpartv
  exact h1.trans h2

/-- Gloas:1924-1931 on the archived four-stage order: validator stages
leave `state.builders` untouched, so the net builder write is the
queue fold then the builder-sweep fold. The consumer flat list is not
named. -/
theorem applyTagged_mixed_builders
    (s : DualBalances)
    (q part sw el : List (Nat × Nat))
    (hq : ∀ p ∈ q, isBuilderIndex p.1 = true)
    (hpart : ∀ p ∈ part, isBuilderIndex p.1 = false)
    (hsw : ∀ p ∈ sw, isBuilderIndex p.1 = true)
    (hel : ∀ p ∈ el, isBuilderIndex p.1 = false) :
    (applyTagged s (q ++ part ++ sw ++ el)).builders =
      (applyTagged (applyTagged s q) sw).builders := by
  rw [applyTagged_append s ((q ++ part) ++ sw) el,
    applyTagged_append s (q ++ part) sw,
    applyTagged_append s q part]
  have hpartb :
      (applyTagged (applyTagged s q) part).builders =
        (applyTagged s q).builders :=
    applyTagged_validators_keep_builders (applyTagged s q) part hpart
  have helb :
      (applyTagged (applyTagged (applyTagged (applyTagged s q) part) sw) el).builders =
        (applyTagged (applyTagged (applyTagged s q) part) sw).builders :=
    applyTagged_validators_keep_builders
      (applyTagged (applyTagged (applyTagged s q) part) sw) el hel
  have hswb :
      (applyTagged (applyTagged (applyTagged s q) part) sw).builders =
        (applyTagged (applyTagged s q) sw).builders :=
    applyTagged_builders_eq_of_builders_eq
      (applyTagged (applyTagged s q) part) (applyTagged s q) sw hsw hpartb
  exact helb.trans hswb

/-- Gloas:1879-1916 / 1926-1927: net `state.balances` of a mixed
`gloasFromBuilders` payload is the validator stages only. Builder
queue and sweep do not write `balances`. `hflat` is not named. -/
theorem gloasFromBuilders_applyTagged_validators
    (s : DualBalances)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hp : ∀ c ∈ partials, c.w.validatorIndex < BUILDER_INDEX_FLAG)
    (hstart : SweepStart n start)
    (hn : n ≤ BUILDER_INDEX_FLAG) :
    (applyTagged s (creditedPairs
        (gloasFromBuilders pending partials sweeps n start flagged))).validators =
      (applyTagged
        (applyTagged s (creditedPairs
          (creditPartials (creditBuilderQueue pending).length partials)))
        (creditedPairs
          (electraCreditEligible n start
            ((creditBuilderQueue pending).length +
              (creditPartials (creditBuilderQueue pending).length partials).length +
              (creditBuilderSweep
                ((creditBuilderQueue pending).length +
                  (creditPartials (creditBuilderQueue pending).length partials).length)
                sweeps).length)
            flagged))).validators := by
  rw [gloasFromBuilders_eq_stages, creditedPairs_append, creditedPairs_append,
    creditedPairs_append]
  refine applyTagged_mixed_validators s _ _ _ _ ?_ ?_ ?_ ?_
  · exact creditBuilderQueue_pairs_are_builder pending
  · exact creditPartials_pairs_not_builder _ hp
  · exact creditBuilderSweep_pairs_are_builder _ sweeps
  · exact electraCreditEligible_pairs_not_builder hstart hn

/-- Gloas:1879-1916 / 1926-1927: net `state.builders` of a mixed
`gloasFromBuilders` payload is the builder stages only. Partials and
Electra visits do not write `builders`. `hflat` is not named. -/
theorem gloasFromBuilders_applyTagged_builders
    (s : DualBalances)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hp : ∀ c ∈ partials, c.w.validatorIndex < BUILDER_INDEX_FLAG)
    (hstart : SweepStart n start)
    (hn : n ≤ BUILDER_INDEX_FLAG) :
    (applyTagged s (creditedPairs
        (gloasFromBuilders pending partials sweeps n start flagged))).builders =
      (applyTagged
        (applyTagged s (creditedPairs (creditBuilderQueue pending)))
        (creditedPairs
          (creditBuilderSweep
            ((creditBuilderQueue pending).length +
              (creditPartials (creditBuilderQueue pending).length partials).length)
            sweeps))).builders := by
  rw [gloasFromBuilders_eq_stages, creditedPairs_append, creditedPairs_append,
    creditedPairs_append]
  refine applyTagged_mixed_builders s _ _ _ _ ?_ ?_ ?_ ?_
  · exact creditBuilderQueue_pairs_are_builder pending
  · exact creditPartials_pairs_not_builder _ hp
  · exact creditBuilderSweep_pairs_are_builder _ sweeps
  · exact electraCreditEligible_pairs_not_builder hstart hn

/-- Full-parent Gloas block built from archived `builder_index` /
`validator_index` fields. Public `Block` fields stay the constructor's. -/
def gloasFromBuildersBlock (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (flagged : List (Item × Bool)) : Block :=
  blockOfElectra slot true (pending.map (·.item))
    (partials.map asElectraPartial)
    (sweeps.map (fun p => (p.item, p.eligible))) flagged

theorem gloasFromBuildersBlock_parentFull (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (flagged : List (Item × Bool)) :
    (gloasFromBuildersBlock slot pending partials sweeps flagged).parentFull =
      true :=
  rfl

theorem items_of_gloasFromBuildersBlock (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n) :
    items (gloasFromBuildersBlock slot pending partials sweeps flagged) =
      creditedItems (gloasFromBuilders pending partials sweeps n start flagged) :=
  items_of_gloasFromBuilders slot pending partials sweeps n start flagged hle

/-- Gloas:1879-1916 / 1940: a full parent assigns `expected`, which is
the credited four-stage list, not a second payload. -/
theorem expected_of_gloasFromBuildersBlock (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n) :
    expected (gloasFromBuildersBlock slot pending partials sweeps flagged) =
      creditedItems (gloasFromBuilders pending partials sweeps n start flagged) := by
  have hi := items_of_gloasFromBuildersBlock slot pending partials sweeps
    n start flagged hle
  simpa [items, gloasFromBuildersBlock_parentFull] using hi

/-- Consecutive accepted blocks, each contributing exactly its computed
`items` once. This is CL computation order, not the retained-cache mint
order of an empty parent. -/
inductive BlockCredits : AccountMap .EVM → List Block → AccountMap .EVM → Prop where
  | nil (world : AccountMap .EVM) : BlockCredits world [] world
  | cons {before mid after : AccountMap .EVM} {b : Block} {rest : List Block}
      (here : ApplyBodyWithdrawals before mid (items b))
      (tail : BlockCredits mid rest after) :
      BlockCredits before (b::rest) after

/-- Concatenate two literal `Dispatch` runs. -/
theorem dispatch_append {before mid after : AccountMap .EVM} {xs ys : List Item}
    (hx : Dispatch before xs mid) (hy : Dispatch mid ys after) :
    Dispatch before (xs ++ ys) after := by
  induction hx generalizing after with
  | nil world => simpa using hy
  | @cons before' after' item items tail ih =>
    exact .cons (ih hy)

theorem blockCredits_flat {before after : AccountMap .EVM} {blocks : List Block}
    (h : BlockCredits before blocks after) :
    Dispatch before (blocks.flatMap items) after := by
  induction h with
  | nil world => exact .nil world
  | cons here tail ih =>
    simp only [List.flatMap_cons]
    exact dispatch_append (elCredit_dispatch here.once) ih

/-- The consumer `Dispatch` premise is derived from per-block EL credits.
Slot Nodup is still derived from `AcceptedBlocks`, never assumed. -/
theorem dispatched_counts_from_blocks {initial before after : AccountMap .EVM}
    {p s c : Nat} {pre post : Clock} (prior : Ledger initial p 0 s c before)
    (blocks : List Block) (h : AcceptedBlocks pre blocks post)
    (run : BlockCredits before blocks after)
    (powBound : p ≤ 2^64) (migrationConserving : s = 0) :
    Ledger initial p ((blocks.map (fun b => (items b).length)).sum) s
        (c+credits (blocks.flatMap items)) after ∧
      Counts p ((blocks.map (fun b => (items b).length)).sum) s :=
  dispatched_counts prior blocks h (blockCredits_flat run) powBound migrationConserving

/-- Gloas:1999/2011 and fork.md:221. An empty parent retains the cache;
a full parent assigns `expected`. -/
def cacheAfter (cached : List Item) (b : Block) : List Item :=
  if b.parentFull then expected b else cached

theorem cacheAfter_empty (cached : List Item) (b : Block) (h : b.parentFull = false) :
    cacheAfter cached b = cached := by simp [cacheAfter, h]

theorem cacheAfter_full (cached : List Item) (b : Block) (h : b.parentFull = true) :
    cacheAfter cached b = expected b := by simp [cacheAfter, h]

theorem expected_length (b : Block) : (expected b).length ≤ 16 :=
  (expectedPayload b).bounded

theorem cacheAfter_bounded {cached : List Item} (h : cached.length ≤ 16) (b : Block) :
    (cacheAfter cached b).length ≤ 16 := by
  unfold cacheAfter
  split
  · exact expected_length b
  · exact h

/-- Payload lists at each accepted slot, including repetitions after empty
parents (the retained-cache mint order). Bound fields are produced. -/
def cachedPayloadsFrom (cached : List Item) (bound : cached.length ≤ 16) :
    List Block → List Payload
  | [] => []
  | b::rest =>
    let next := cacheAfter cached b
    let nextBound := cacheAfter_bounded bound b
    { slot := b.slot, items := next, bounded := nextBound } ::
      cachedPayloadsFrom next nextBound rest

/-- fork.md:221 `payload_expected_withdrawals=Withdrawals()`. -/
def cachedPayloads (blocks : List Block) : List Payload :=
  cachedPayloadsFrom [] (by simp) blocks

theorem cached_slots (blocks : List Block) (cached : List Item)
    (bound : cached.length ≤ 16) :
    (cachedPayloadsFrom cached bound blocks).map (·.slot) = blocks.map (·.slot) := by
  induction blocks generalizing cached with
  | nil => rfl
  | cons b rest ih =>
    simp only [cachedPayloadsFrom, List.map_cons]
    exact congrArg (b.slot :: ·) (ih _ _)

/-- fork-choice.md:688 compares SSZ roots. Decoded-list identity is the
named adapter, not a proved injective `hash_tree_root`. -/
structure WithdrawalsRootMatch (listed cached : List Item) : Prop where
  decoded : listed = cached

/-- fork-choice.md:659-699, invoked at on_execution_payload_envelope:1113. -/
structure VerifiedEnvelope (b : Block) (cachedBefore listed : List Item) : Prop where
  honors : WithdrawalsRootMatch listed (cacheAfter cachedBefore b)

/-- One `apply_body` credit of each verified envelope's listed withdrawals,
threading the retained cache. Empty parents still mint the retained list. -/
inductive EnvelopeCredits : AccountMap .EVM → List Item → List Block →
    AccountMap .EVM → Prop where
  | nil (world : AccountMap .EVM) (cached : List Item) :
      EnvelopeCredits world cached [] world
  | cons {before mid after : AccountMap .EVM} {cached : List Item}
      {b : Block} {rest : List Block} {listed : List Item}
      (env : VerifiedEnvelope b cached listed)
      (here : ApplyBodyWithdrawals before mid listed)
      (tail : EnvelopeCredits mid (cacheAfter cached b) rest after) :
      EnvelopeCredits before cached (b::rest) after

theorem envelopeCredits_flat {before after : AccountMap .EVM} {cached : List Item}
    {blocks : List Block} (run : EnvelopeCredits before cached blocks after)
    (bound : cached.length ≤ 16) :
    Dispatch before ((cachedPayloadsFrom cached bound blocks).flatMap (·.items)) after := by
  induction run with
  | nil world c =>
    simp only [cachedPayloadsFrom, List.flatMap_nil]
    exact .nil world
  | @cons before mid after cached b rest listed env here tail ih =>
    simp only [cachedPayloadsFrom, List.flatMap_cons]
    have hd : Dispatch before (cacheAfter cached b) mid := by
      rw [←env.honors.decoded]
      exact elCredit_dispatch here.once
    exact dispatch_append hd (ih (cacheAfter_bounded bound b))

/-- Slot Nodup is derived from `AcceptedBlocks`. The consumer `Dispatch` of
the retained-cache lists is derived from verified envelopes plus one
`apply_body` pass each. -/
theorem cached_total_count {pre post : Clock} (blocks : List Block)
    (h : AcceptedBlocks pre blocks post) :
    totalItems (cachedPayloads blocks) ≤ 16*2^64 := by
  apply ProtocolWithdrawalCount.total_count
  rw [cachedPayloads, cached_slots]
  exact ProtocolSlotExtraction.accepted_nodup h

theorem dispatched_counts_from_envelopes {initial before after : AccountMap .EVM}
    {p s c : Nat} {pre post : Clock} (prior : Ledger initial p 0 s c before)
    (blocks : List Block) (h : AcceptedBlocks pre blocks post)
    (run : EnvelopeCredits before [] blocks after)
    (powBound : p ≤ 2^64) (migrationConserving : s = 0) :
    Ledger initial p (totalItems (cachedPayloads blocks)) s
        (c+credits ((cachedPayloads blocks).flatMap (·.items))) after ∧
      Counts p (totalItems (cachedPayloads blocks)) s := by
  refine ProtocolWithdrawalCount.dispatched_counts prior (cachedPayloads blocks)
    ?_ ?_ powBound migrationConserving
  · simpa only [cachedPayloads] using envelopeCredits_flat run (by simp)
  · rw [cachedPayloads, cached_slots]
    exact ProtocolSlotExtraction.accepted_nodup h

/-- Named: the retained-cache mint list is the Item projection of the
same `Withdrawal` objects that `applyTagged` writes. -/
theorem credited_matches_cached
    {s t : DualBalances} {before after : AccountMap .EVM}
    {cached : List Item} {blocks : List Block}
    {ws : List CreditedWithdrawal}
    (bound : cached.length ≤ 16)
    (run : CreditedRun s before ws t after)
    (hflat : (cachedPayloadsFrom cached bound blocks).flatMap (·.items) =
      creditedItems ws) :
    Dispatch before
        ((cachedPayloadsFrom cached bound blocks).flatMap (·.items)) after ∧
      t = applyTagged s (creditedPairs ws) :=
  ⟨by
      rw [hflat]
      exact creditedRun_dispatch run,
    creditedRun_cl run⟩

theorem dispatched_counts_from_credited_envelopes
    {initial before after : AccountMap .EVM} {p mig c : Nat}
    {pre post : Clock} {s0 t0 : DualBalances}
    {ws : List CreditedWithdrawal}
    (prior : Ledger initial p 0 mig c before)
    (blocks : List Block) (hacc : AcceptedBlocks pre blocks post)
    (run : CreditedRun s0 before ws t0 after)
    (hflat : (cachedPayloads blocks).flatMap (·.items) = creditedItems ws)
    (powBound : p ≤ 2 ^ 64) (migrationConserving : mig = 0) :
    Ledger initial p (totalItems (cachedPayloads blocks)) mig
        (c + credits ((cachedPayloads blocks).flatMap (·.items))) after ∧
      Counts p (totalItems (cachedPayloads blocks)) mig := by
  refine ProtocolWithdrawalCount.dispatched_counts prior (cachedPayloads blocks)
    ?_ ?_ powBound migrationConserving
  · simpa only [cachedPayloads] using
      (credited_matches_cached (by simp) run (by simpa [cachedPayloads] using hflat)).1
  · rw [cachedPayloads, cached_slots]
    exact ProtocolSlotExtraction.accepted_nodup hacc

/-- Gloas:1999 / fork.md:221. A full parent assigns a freshly indexed
`expected`; an empty parent remints the cached indexed list and does not
advance `next_withdrawal_index`. -/
def indexedCacheAfter (start : Nat) (cached : List IndexedWithdrawal)
    (b : Block) : List IndexedWithdrawal :=
  if b.parentFull then indexedWithdrawals start (expected b) else cached

def nextIndexAfterCache (start : Nat) (b : Block) : Nat :=
  if b.parentFull then nextIndexAfter start (expected b) else start

theorem indexedCacheAfter_items (start : Nat)
    (cached : List IndexedWithdrawal) (b : Block) :
    (indexedCacheAfter start cached b).map (fun w => w.item) =
      cacheAfter (cached.map (fun w => w.item)) b := by
  unfold indexedCacheAfter cacheAfter
  split
  · exact indexedWithdrawals_items start (expected b)
  · rfl

theorem indexedCacheAfter_empty {start : Nat} {cached : List IndexedWithdrawal}
    {b : Block} (h : b.parentFull = false) :
    indexedCacheAfter start cached b = cached := by
  simp [indexedCacheAfter, h]

theorem nextIndexAfterCache_empty {start : Nat} {b : Block}
    (h : b.parentFull = false) :
    nextIndexAfterCache start b = start := by
  simp [nextIndexAfterCache, h]

theorem nextIndexAfterCache_full {start : Nat} {b : Block}
    (h : b.parentFull = true) :
    nextIndexAfterCache start b = start + (expected b).length := by
  simp [nextIndexAfterCache, h, nextIndexAfter_eq]

/-- Fresh assignment on a full parent is an `indexSeq`, hence Nodup. -/
theorem indexedCacheAfter_full_nodup {start : Nat}
    {cached : List IndexedWithdrawal} {b : Block} (h : b.parentFull = true) :
    ((indexedCacheAfter start cached b).map (fun w => w.index)).Nodup := by
  simp [indexedCacheAfter, h]
  exact indexedWithdrawals_nodup start (expected b)

/-- Computed `items` are `expected` iff the parent is full. Empty parent
(Gloas:1999) therefore contributes no new index to `indexedChain`. -/
theorem indexedChain_empty_step (start : Nat) (b : Block) (bs : List Block)
    (h : b.parentFull = false) :
    indexedChain start (b :: bs) = indexedChain start bs := by
  have hi : items b = [] := items_empty b h
  simp [indexedChain, hi, indexedWithdrawals, nextIndexAfter_nil]

theorem indexedChain_full_step (start : Nat) (b : Block) (bs : List Block)
    (h : b.parentFull = true) :
    indexedChain start (b :: bs) =
      indexedWithdrawals start (expected b) ++
        indexedChain (nextIndexAfter start (expected b)) bs := by
  have hi : items b = expected b := by simp [items, h]
  simp [indexedChain, hi]

/-- Per-block minted indexed lists in retained-cache order, including
Gloas:1999 remints. Cursor advances only on a full parent. -/
def indexedCachedFrom (start : Nat) (cached : List IndexedWithdrawal) :
    List Block → List (List IndexedWithdrawal)
  | [] => []
  | b :: rest =>
      let next := indexedCacheAfter start cached b
      next :: indexedCachedFrom (nextIndexAfterCache start b) next rest

theorem indexedCachedFrom_nil (start : Nat) (cached : List IndexedWithdrawal) :
    indexedCachedFrom start cached [] = [] :=
  rfl

theorem indexedCachedFrom_cons (start : Nat) (cached : List IndexedWithdrawal)
    (b : Block) (rest : List Block) :
    indexedCachedFrom start cached (b :: rest) =
      indexedCacheAfter start cached b ::
        indexedCachedFrom (nextIndexAfterCache start b)
          (indexedCacheAfter start cached b) rest :=
  rfl

/-- Item lists minted in retained-cache order, without the Payload bound
proof. Gloas:1999 remints `cached`; a full parent assigns `expected`. -/
def mintedItemLists (cached : List Item) : List Block → List (List Item)
  | [] => []
  | b :: rest =>
      cacheAfter cached b :: mintedItemLists (cacheAfter cached b) rest

theorem mintedItemLists_eq_payloads (cached : List Item)
    (bound : cached.length ≤ 16) (bs : List Block) :
    mintedItemLists cached bs =
      (cachedPayloadsFrom cached bound bs).map (fun p => p.items) := by
  induction bs generalizing cached bound with
  | nil => rfl
  | cons b rest ih =>
    simp only [mintedItemLists, cachedPayloadsFrom, List.map_cons]
    exact congrArg (cacheAfter cached b :: ·)
      (ih (cacheAfter cached b) (cacheAfter_bounded bound b))

theorem indexedCachedFrom_minted (start : Nat)
    (cached : List IndexedWithdrawal) (blocks : List Block) :
    (indexedCachedFrom start cached blocks).map
        (fun ws => ws.map (fun w => w.item)) =
      mintedItemLists (cached.map (fun w => w.item)) blocks := by
  induction blocks generalizing start cached with
  | nil => rfl
  | cons b rest ih =>
    have hitems := indexedCacheAfter_items start cached b
    have ih' := ih (nextIndexAfterCache start b) (indexedCacheAfter start cached b)
    simp only [indexedCachedFrom, mintedItemLists, List.map_cons]
    rw [hitems]
    rw [hitems] at ih'
    exact congrArg (cacheAfter (cached.map (fun w => w.item)) b :: ·) ih'

theorem flatten_map_eq_flatMap {α β : Type} (f : α → List β) (l : List α) :
    (l.map f).flatten = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.flatten_cons, List.flatMap_cons, ih]

theorem indexedCachedFrom_items (start : Nat)
    (cached : List IndexedWithdrawal) (blocks : List Block)
    (bound : (cached.map (fun w => w.item)).length ≤ 16) :
    (indexedCachedFrom start cached blocks).map
        (fun ws => ws.map (fun w => w.item)) =
      (cachedPayloadsFrom (cached.map (fun w => w.item)) bound blocks).map
        (fun p => p.items) := by
  rw [indexedCachedFrom_minted, mintedItemLists_eq_payloads]

theorem minted_flat_eq_cached_from (cached : List Item)
    (bound : cached.length ≤ 16) (bs : List Block) :
    (mintedItemLists cached bs).flatten =
      (cachedPayloadsFrom cached bound bs).flatMap (fun p => p.items) := by
  induction bs generalizing cached bound with
  | nil => rfl
  | cons b rest ih =>
    simp only [mintedItemLists, cachedPayloadsFrom, List.flatten_cons, List.flatMap_cons]
    exact congrArg (cacheAfter cached b ++ ·)
      (ih (cacheAfter cached b) (cacheAfter_bounded bound b))

theorem minted_flat_eq_cached (bs : List Block) :
    (mintedItemLists [] bs).flatten =
      (cachedPayloads bs).flatMap (fun p => p.items) := by
  unfold cachedPayloads
  exact minted_flat_eq_cached_from [] (by simp) bs

theorem indexedCached_flat_items (start : Nat) (blocks : List Block) :
    (indexedCachedFrom start [] blocks).flatMap
        (fun ws => ws.map (fun w => w.item)) =
      (cachedPayloads blocks).flatMap (fun p => p.items) := by
  have h := congrArg List.flatten (indexedCachedFrom_minted start [] blocks)
  rw [flatten_map_eq_flatMap] at h
  exact h.trans (minted_flat_eq_cached blocks)

theorem indexedCachedFrom_length_eq_flat (start : Nat)
    (cached : List IndexedWithdrawal) (blocks : List Block) :
    ((indexedCachedFrom start cached blocks).map List.length).sum =
      ((indexedCachedFrom start cached blocks).flatMap
        (fun ws => ws.map (fun w => w.item))).length := by
  induction blocks generalizing start cached with
  | nil => simp [indexedCachedFrom]
  | cons b rest ih =>
    simp only [indexedCachedFrom, List.map_cons, List.sum_cons, List.flatMap_cons,
      List.length_append, List.length_map]
    exact congrArg ((indexedCacheAfter start cached b).length + ·)
      (ih (nextIndexAfterCache start b) (indexedCacheAfter start cached b))

theorem indexedCached_flat_length (start : Nat) (blocks : List Block) :
    ((indexedCachedFrom start [] blocks).map List.length).sum =
      totalItems (cachedPayloads blocks) := by
  have h := indexedCached_flat_items start blocks
  have hl := congrArg List.length h
  have hL := indexedCachedFrom_length_eq_flat start [] blocks
  have hR := totalItems_flatMap (cachedPayloads blocks)
  exact hL.trans (hl.trans hR.symm)

/-- The consumer envelope count is the flattened minted indexed lists,
including remints. Fresh `+= 1` uniqueness stays on `indexedChain`
(empty parents add no new index). -/
theorem indexed_cached_total_count {pre post : Clock} (start : Nat)
    (blocks : List Block) (h : AcceptedBlocks pre blocks post) :
    ((indexedCachedFrom start [] blocks).map List.length).sum ≤ 16 * 2 ^ 64 := by
  rw [indexedCached_flat_length]
  exact cached_total_count blocks h

theorem dispatch_of_indexed_cached {before after : AccountMap .EVM}
    {start : Nat} {blocks : List Block}
    (run : Dispatch before
      ((indexedCachedFrom start [] blocks).flatMap
        (fun ws => ws.map (fun w => w.item))) after) :
    Dispatch before ((cachedPayloads blocks).flatMap (fun p => p.items)) after := by
  rwa [indexedCached_flat_items] at run

/-- Gloas:1940: a full-parent `gloasFromBuilders` block assigns the
credited list into the retained cache. -/
theorem cacheAfter_full_gloasFromBuildersBlock (cached : List Item)
    (slot : U64) (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n) :
    cacheAfter cached
        (gloasFromBuildersBlock slot pending partials sweeps flagged) =
      creditedItems (gloasFromBuilders pending partials sweeps n start flagged) := by
  rw [cacheAfter_full cached _
      (gloasFromBuildersBlock_parentFull slot pending partials sweeps flagged),
    expected_of_gloasFromBuildersBlock slot pending partials sweeps n start
      flagged hle]

/-- Gloas:1999: an empty parent remints that credited list and does not
compute a second payload. -/
theorem mintedItemLists_gloas_then_empty (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n)
    {e : Block} (he : e.parentFull = false) :
    mintedItemLists []
        [gloasFromBuildersBlock slot pending partials sweeps flagged, e] =
      [creditedItems (gloasFromBuilders pending partials sweeps n start flagged),
        creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged)] := by
  have hf := cacheAfter_full_gloasFromBuildersBlock [] slot pending partials
    sweeps n start flagged hle
  have hr := cacheAfter_empty
    (creditedItems (gloasFromBuilders pending partials sweeps n start flagged))
    e he
  simp [mintedItemLists, hf, hr]

/-- The remint flatten is the credited list concatenated with itself,
not a consumer `hflat`. -/
theorem minted_flat_gloas_then_empty (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n)
    {e : Block} (he : e.parentFull = false) :
    (mintedItemLists []
        [gloasFromBuildersBlock slot pending partials sweeps flagged, e]).flatten =
      creditedItems
        (gloasFromBuilders pending partials sweeps n start flagged ++
          gloasFromBuilders pending partials sweeps n start flagged) := by
  rw [mintedItemLists_gloas_then_empty slot pending partials sweeps n start
    flagged hle he, creditedItems_append]
  simp

theorem indexedCacheAfter_full_gloasFromBuildersBlock (idx : Nat)
    (cached : List IndexedWithdrawal) (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n) :
    indexedCacheAfter idx cached
        (gloasFromBuildersBlock slot pending partials sweeps flagged) =
      indexedWithdrawals idx
        (creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged)) := by
  simp [indexedCacheAfter,
    gloasFromBuildersBlock_parentFull slot pending partials sweeps flagged,
    expected_of_gloasFromBuildersBlock slot pending partials sweeps n start
      flagged hle]

/-- Gloas:1999 remints the stamped `Withdrawal.index` list. The empty
parent does not assign successors. -/
theorem indexedCachedFrom_gloas_then_empty (idx : Nat) (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n)
    {e : Block} (he : e.parentFull = false) :
    indexedCachedFrom idx []
        [gloasFromBuildersBlock slot pending partials sweeps flagged, e] =
      [indexedWithdrawals idx
          (creditedItems (gloasFromBuilders pending partials sweeps n start
            flagged)),
        indexedWithdrawals idx
          (creditedItems (gloasFromBuilders pending partials sweeps n start
            flagged))] := by
  have hfull := indexedCacheAfter_full_gloasFromBuildersBlock idx [] slot
    pending partials sweeps n start flagged hle
  rw [indexedCachedFrom_cons, hfull, indexedCachedFrom_cons,
    indexedCacheAfter_empty he, indexedCachedFrom_nil]

/-- The reminted copies share the original `indexSeq`, not a continued
cursor. -/
theorem remint_repeats_gloasFromBuilders_indices (idx : Nat) (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n)
    {e : Block} (he : e.parentFull = false) :
    (indexedCachedFrom idx []
        [gloasFromBuildersBlock slot pending partials sweeps flagged, e]).map
        (fun ws => ws.map (fun w => w.index)) =
      [indexSeq idx
          (creditedItems (gloasFromBuilders pending partials sweeps n start
            flagged)).length,
        indexSeq idx
          (creditedItems (gloasFromBuilders pending partials sweeps n start
            flagged)).length] := by
  rw [indexedCachedFrom_gloas_then_empty idx slot pending partials sweeps
    n start flagged hle he]
  simp [indexedWithdrawals_indices]

/-- Remint copies are the stamped archived list, not a second index
walk. -/
theorem remint_stamps_gloasFromBuilders (idx : Nat) (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n)
    {e : Block} (he : e.parentFull = false) :
    indexedCachedFrom idx []
        [gloasFromBuildersBlock slot pending partials sweeps flagged, e] =
      [archivedIndexed
          (stampIndex idx
            (gloasFromBuilders pending partials sweeps n start flagged)),
        archivedIndexed
          (stampIndex idx
            (gloasFromBuilders pending partials sweeps n start flagged))] := by
  rw [indexedCachedFrom_gloas_then_empty idx slot pending partials sweeps
    n start flagged hle he, stampIndex_indexed]

/-- Computed `indexedChain` sees the empty parent as no new index
(Gloas:1999 returns before any list is computed). The remint path is
`indexedCachedFrom`, not this chain. -/
theorem indexedChain_gloas_then_empty (idx : Nat) (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n)
    {e : Block} (he : e.parentFull = false) :
    indexedChain idx
        [gloasFromBuildersBlock slot pending partials sweeps flagged, e] =
      indexedWithdrawals idx
        (creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged)) := by
  have hi := items_of_gloasFromBuildersBlock slot pending partials sweeps
    n start flagged hle
  have he' := items_empty e he
  simp [indexedChain, hi, he']
  rfl

/-- Envelope remint count is two copies of the credited list. Fresh
`+= 1` uniqueness stays on `indexedChain`. -/
theorem remint_count_gloasFromBuilders (idx : Nat) (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n)
    {e : Block} (he : e.parentFull = false) :
    ((indexedCachedFrom idx []
        [gloasFromBuildersBlock slot pending partials sweeps flagged,
          e]).map List.length).sum =
      (creditedItems (gloasFromBuilders pending partials sweeps n start
        flagged)).length +
        (creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged)).length := by
  rw [indexedCachedFrom_gloas_then_empty idx slot pending partials sweeps
    n start flagged hle he]
  have hl :
      (indexedWithdrawals idx
        (creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged))).length =
        (creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged)).length := by
    rw [← List.length_map (fun w : IndexedWithdrawal => w.item),
      indexedWithdrawals_items]
  simp [hl]

/-- Gloas:1999 remint flatten is the cached envelope list consumed by
`ProtocolWithdrawalCount`. `hflat` is derived, not named. -/
theorem cached_flat_gloas_then_empty (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n)
    {e : Block} (he : e.parentFull = false) :
    (cachedPayloads
        [gloasFromBuildersBlock slot pending partials sweeps flagged, e]).flatMap
        (fun p => p.items) =
      creditedItems
        (gloasFromBuilders pending partials sweeps n start flagged ++
          gloasFromBuilders pending partials sweeps n start flagged) := by
  rw [← minted_flat_eq_cached]
  exact minted_flat_gloas_then_empty slot pending partials sweeps n start
    flagged hle he

/-- Envelope `totalItems` is two credited copies. Fresh `+= 1`
uniqueness stays on `indexedChain`. -/
theorem totalItems_gloas_then_empty (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n)
    {e : Block} (he : e.parentFull = false) :
    totalItems (cachedPayloads
        [gloasFromBuildersBlock slot pending partials sweeps flagged, e]) =
      (creditedItems (gloasFromBuilders pending partials sweeps n start
        flagged)).length +
        (creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged)).length := by
  rw [totalItems_flatMap, cached_flat_gloas_then_empty slot pending partials
    sweeps n start flagged hle he, creditedItems_append, List.length_append]

/-- EL remint credits the concatenated credited list. This is
`create_ether` of the retained cache, not a second CL
`apply_withdrawals` (Gloas:1999 returns first). -/
theorem dispatched_counts_from_gloas_remint
    {initial before after : AccountMap .EVM} {p mig c : Nat}
    {pre post : Clock}
    (prior : Ledger initial p 0 mig c before)
    (slot : U64) (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    {e : Block}
    (hle : flagged.length ≤ validatorsSweepLimit n)
    (he : e.parentFull = false)
    (hacc : AcceptedBlocks pre
      [gloasFromBuildersBlock slot pending partials sweeps flagged, e] post)
    (run : Dispatch before
      (creditedItems
        (gloasFromBuilders pending partials sweeps n start flagged ++
          gloasFromBuilders pending partials sweeps n start flagged)) after)
    (powBound : p ≤ 2 ^ 64) (migrationConserving : mig = 0) :
    Ledger initial p
        ((creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged)).length +
          (creditedItems (gloasFromBuilders pending partials sweeps n start
            flagged)).length) mig
        (c + credits
          (creditedItems
            (gloasFromBuilders pending partials sweeps n start flagged ++
              gloasFromBuilders pending partials sweeps n start flagged)))
        after ∧
      Counts p
        ((creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged)).length +
          (creditedItems (gloasFromBuilders pending partials sweeps n start
            flagged)).length) mig := by
  have hitems := cached_flat_gloas_then_empty slot pending partials sweeps
    n start flagged hle he
  have htot := totalItems_gloas_then_empty slot pending partials sweeps
    n start flagged hle he
  have hdc := ProtocolWithdrawalCount.dispatched_counts prior
    (cachedPayloads
      [gloasFromBuildersBlock slot pending partials sweeps flagged, e])
    (by rw [hitems]; exact run)
    (by
      rw [cachedPayloads, cached_slots]
      exact ProtocolSlotExtraction.accepted_nodup hacc)
    powBound migrationConserving
  rw [htot, hitems] at hdc
  exact hdc

/-- fork-choice.md:688 / Gloas:1940: the listed envelope of a full
`gloasFromBuilders` parent is the credited four-stage list. SSZ root
injectivity remains named. -/
theorem verifiedEnvelope_gloasFromBuildersBlock (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n) :
    VerifiedEnvelope
      (gloasFromBuildersBlock slot pending partials sweeps flagged) []
      (creditedItems (gloasFromBuilders pending partials sweeps n start
        flagged)) :=
  ⟨⟨(cacheAfter_full_gloasFromBuildersBlock [] slot pending partials sweeps
      n start flagged hle).symm⟩⟩

/-- fork-choice.md:688 / Gloas:1999: an empty parent lists the retained
cache, not a freshly computed payload. -/
theorem verifiedEnvelope_empty_remint (cached : List Item)
    {e : Block} (he : e.parentFull = false) :
    VerifiedEnvelope e cached cached :=
  ⟨⟨(cacheAfter_empty cached e he).symm⟩⟩

/-- Two `apply_body` passes of the same credited list: full parent
assigns it, empty parent remints it. `listed` is derived from
`WithdrawalsRootMatch`, not named as `hflat`. -/
theorem envelopeCredits_gloas_then_empty
    {before mid after : AccountMap .EVM} (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    {e : Block}
    (hle : flagged.length ≤ validatorsSweepLimit n)
    (he : e.parentFull = false)
    (hfull : ApplyBodyWithdrawals before mid
      (creditedItems (gloasFromBuilders pending partials sweeps n start
        flagged)))
    (hempty : ApplyBodyWithdrawals mid after
      (creditedItems (gloasFromBuilders pending partials sweeps n start
        flagged))) :
    EnvelopeCredits before []
      [gloasFromBuildersBlock slot pending partials sweeps flagged, e]
      after := by
  have htail : EnvelopeCredits mid
      (cacheAfter []
        (gloasFromBuildersBlock slot pending partials sweeps flagged))
      [e] after := by
    rw [cacheAfter_full_gloasFromBuildersBlock [] slot pending partials
      sweeps n start flagged hle]
    exact EnvelopeCredits.cons
      (verifiedEnvelope_empty_remint
        (creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged)) he)
      hempty
      (EnvelopeCredits.nil after
        (cacheAfter
          (creditedItems (gloasFromBuilders pending partials sweeps n start
            flagged))
          e))
  exact EnvelopeCredits.cons
    (verifiedEnvelope_gloasFromBuildersBlock slot pending partials sweeps
      n start flagged hle)
    hfull htail

/-- Envelope flatten of that run is `creditedItems (g ++ g)`. -/
theorem envelopeCredits_gloas_then_empty_flat
    {before after : AccountMap .EVM} {slot : U64}
    {pending : List BuilderPending}
    {partials : List CreditedPartial}
    {sweeps : List BuilderSweepVisit}
    {n start : Nat} {flagged : List (Item × Bool)} {e : Block}
    (hle : flagged.length ≤ validatorsSweepLimit n)
    (he : e.parentFull = false)
    (run : EnvelopeCredits before []
      [gloasFromBuildersBlock slot pending partials sweeps flagged, e]
      after) :
    Dispatch before
      (creditedItems
        (gloasFromBuilders pending partials sweeps n start flagged ++
          gloasFromBuilders pending partials sweeps n start flagged))
      after := by
  have h := envelopeCredits_flat run (by simp)
  simpa [cachedPayloads] using
    (cached_flat_gloas_then_empty slot pending partials sweeps n start
      flagged hle he) ▸ h

/-- `EnvelopeCredits` remint discharges `dispatched_counts`. `hflat` is
not a premise; listed identity is `WithdrawalsRootMatch`. -/
theorem dispatched_counts_from_gloas_remint_envelopes
    {initial before after : AccountMap .EVM} {p mig c : Nat}
    {pre post : Clock} (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    {e : Block}
    (prior : Ledger initial p 0 mig c before)
    (hle : flagged.length ≤ validatorsSweepLimit n)
    (he : e.parentFull = false)
    (hacc : AcceptedBlocks pre
      [gloasFromBuildersBlock slot pending partials sweeps flagged, e] post)
    (run : EnvelopeCredits before []
      [gloasFromBuildersBlock slot pending partials sweeps flagged, e]
      after)
    (powBound : p ≤ 2 ^ 64) (migrationConserving : mig = 0) :
    Ledger initial p
        ((creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged)).length +
          (creditedItems (gloasFromBuilders pending partials sweeps n start
            flagged)).length) mig
        (c + credits
          (creditedItems
            (gloasFromBuilders pending partials sweeps n start flagged ++
              gloasFromBuilders pending partials sweeps n start flagged)))
        after ∧
      Counts p
        ((creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged)).length +
          (creditedItems (gloasFromBuilders pending partials sweeps n start
            flagged)).length) mig := by
  have hdc := dispatched_counts_from_envelopes prior
    [gloasFromBuildersBlock slot pending partials sweeps flagged, e]
    hacc run powBound migrationConserving
  have htot := totalItems_gloas_then_empty slot pending partials sweeps
    n start flagged hle he
  have hitems := cached_flat_gloas_then_empty slot pending partials sweeps
    n start flagged hle he
  rw [htot, hitems] at hdc
  exact hdc

/-- Computed `items` of the pair is one credited copy. Gloas:1999
contributes no CL list. -/
theorem computed_flat_gloas_then_empty (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    (hle : flagged.length ≤ validatorsSweepLimit n)
    {e : Block} (he : e.parentFull = false) :
    List.flatMap items
        [gloasFromBuildersBlock slot pending partials sweeps flagged, e] =
      creditedItems (gloasFromBuilders pending partials sweeps n start
        flagged) := by
  have hi := items_of_gloasFromBuildersBlock slot pending partials sweeps
    n start flagged hle
  have he' := items_empty e he
  simp [List.flatMap_cons, List.flatMap_nil, hi, he']

/-- CL `applyTagged` of a `CreditedRun` of `g` is one fold. The computed
flatten is `g`, not the remint `g ++ g`. -/
theorem applyTagged_computed_gloas_then_empty
    {s t : DualBalances} {before after : AccountMap .EVM} (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    {e : Block}
    (hle : flagged.length ≤ validatorsSweepLimit n)
    (he : e.parentFull = false)
    (run : CreditedRun s before
      (gloasFromBuilders pending partials sweeps n start flagged) t after) :
    t = applyTagged s (creditedPairs
        (gloasFromBuilders pending partials sweeps n start flagged)) ∧
      List.flatMap items
          [gloasFromBuildersBlock slot pending partials sweeps flagged, e] =
        creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged) :=
  ⟨creditedRun_cl run,
    computed_flat_gloas_then_empty slot pending partials sweeps n start
      flagged hle he⟩

/-- fork.py:1111-1118: each reminted envelope is one `ElCredit` of the
credited list. Two `apply_body` passes, not a second CL fold. -/
theorem envelopeCredits_gloas_then_empty_of_elCredit
    {before mid after : AccountMap .EVM} (slot : U64)
    (pending : List BuilderPending)
    (partials : List CreditedPartial)
    (sweeps : List BuilderSweepVisit)
    (n start : Nat) (flagged : List (Item × Bool))
    {e : Block}
    (hle : flagged.length ≤ validatorsSweepLimit n)
    (he : e.parentFull = false)
    (hfull : ElCredit before
      (creditedItems (gloasFromBuilders pending partials sweeps n start
        flagged)) mid)
    (hempty : ElCredit mid
      (creditedItems (gloasFromBuilders pending partials sweeps n start
        flagged)) after) :
    EnvelopeCredits before []
      [gloasFromBuildersBlock slot pending partials sweeps flagged, e]
      after :=
  envelopeCredits_gloas_then_empty slot pending partials sweeps n start
    flagged hle he ⟨hfull⟩ ⟨hempty⟩

/-- Slot Nodup from `AcceptedBlocks`. The minted item list and count
come from the stamped cache, including Gloas:1999 remints. -/
theorem dispatched_counts_from_indexed_envelopes
    {initial before after : AccountMap .EVM}
    {p s c start : Nat} {pre post : Clock}
    (prior : Ledger initial p 0 s c before) (blocks : List Block)
    (h : AcceptedBlocks pre blocks post)
    (run : Dispatch before
      ((indexedCachedFrom start [] blocks).flatMap
        (fun ws => ws.map (fun w => w.item))) after)
    (powBound : p ≤ 2 ^ 64) (migrationConserving : s = 0) :
    Ledger initial p (((indexedCachedFrom start [] blocks).map List.length).sum) s
        (c + credits ((indexedCachedFrom start [] blocks).flatMap
          (fun ws => ws.map (fun w => w.item)))) after ∧
      Counts p (((indexedCachedFrom start [] blocks).map List.length).sum) s := by
  have hitems := indexedCached_flat_items start blocks
  have hlen := indexedCached_flat_length start blocks
  rw [hitems] at run
  have hdc := ProtocolWithdrawalCount.dispatched_counts prior (cachedPayloads blocks)
    run (by
      rw [cachedPayloads, cached_slots]
      exact ProtocolSlotExtraction.accepted_nodup h)
    powBound migrationConserving
  rwa [← hlen, ← hitems] at hdc

/-- Electra:1255-1261, constructed at fork-choice.md:690-698. Only the
decoded withdrawal list is retained; versioned hashes, parent beacon root
and execution_requests ride on the request and are not decoded here. -/
structure NewPayloadRequest where
  listed : List Item

/-- Electra:1318-1336. `emptyTxByte` is `b"" ∈ execution_payload.transactions`.
The other three flags are the implementation-dependent engine predicates. -/
structure EngineChecks where
  emptyTxByte : Bool
  validBlockHash : Bool
  validVersionedHashes : Bool
  notifyOk : Bool

/-- Electra:1318-1336: admit only when every conjunct holds. -/
def engineAdmits (c : EngineChecks) : Bool :=
  !c.emptyTxByte && c.validBlockHash && c.validVersionedHashes && c.notifyOk

theorem engine_rejects_empty_tx (c : EngineChecks) (h : c.emptyTxByte = true) :
    engineAdmits c = false := by
  simp [engineAdmits, h]

theorem engine_rejects_block_hash (c : EngineChecks) (h : c.validBlockHash = false) :
    engineAdmits c = false := by
  simp [engineAdmits, h]

theorem engine_rejects_versioned_hashes (c : EngineChecks)
    (h : c.validVersionedHashes = false) :
    engineAdmits c = false := by
  simp [engineAdmits, h]

theorem engine_rejects_notify (c : EngineChecks) (h : c.notifyOk = false) :
    engineAdmits c = false := by
  simp [engineAdmits, h]

/-- Named: Electra:1336 returned true. Not `create_ether` / fork.py:1118. -/
structure EngineAdmitted (c : EngineChecks) : Prop where
  admits : engineAdmits c = true

theorem engineAdmitted_flags {c : EngineChecks} (h : EngineAdmitted c) :
    c.emptyTxByte = false ∧ c.validBlockHash = true ∧
      c.validVersionedHashes = true ∧ c.notifyOk = true := by
  have := h.admits
  simp [engineAdmits] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

theorem engineAdmitted_not_empty {c : EngineChecks} (h : EngineAdmitted c) :
    c.emptyTxByte = false :=
  (engineAdmitted_flags h).1

theorem engineAdmitted_notify {c : EngineChecks} (h : EngineAdmitted c) :
    c.notifyOk = true :=
  (engineAdmitted_flags h).2.2.2

/-- fork-choice.md:668-682. Signature, header-root and bid-field asserts
are named Boolean outcomes; their hash/signature bodies are not extracted. -/
structure EnvelopeConsistency where
  signatureOk : Bool
  headerConsistent : Bool
  bidConsistent : Bool

def consistencyOk (c : EnvelopeConsistency) : Bool :=
  c.signatureOk && c.headerConsistent && c.bidConsistent

theorem consistency_rejects_signature (c : EnvelopeConsistency)
    (h : c.signatureOk = false) :
    consistencyOk c = false := by
  simp [consistencyOk, h]

/-- Fields read by fork-choice.md:681/685-687. Hash type is uninterpreted. -/
structure PayloadBinding (α : Type) where
  beacon : U64
  elSlot : U64
  genesisTime : U64
  payloadTime : U64
  payloadParent : α
  latest : α
  bid : α
  payloadBlock : α

/-- fork-choice.md:685, 686, 681, 687 as equalities, not free Booleans. -/
structure EnvelopePayloadFacts {α : Type} (p : PayloadBinding α) : Prop where
  slot : VerifiedEnvelopeSlot p.beacon p.elSlot
  parent : p.payloadParent = p.latest
  bidHash : p.payloadBlock = p.bid
  time : EnvelopeTimestamp p.genesisTime p.beacon p.payloadTime

theorem payloadFacts_slot {α : Type} {p : PayloadBinding α}
    (h : EnvelopePayloadFacts p) : p.elSlot = p.beacon :=
  h.slot.same

theorem payloadFacts_time {α : Type} {p : PayloadBinding α}
    (h : EnvelopePayloadFacts p) :
    p.payloadTime.val = p.genesisTime.val + p.beacon.val * 12 :=
  envelope_timestamp h.time

theorem payloadFacts_parent_eq_bid_iff {α : Type} {p : PayloadBinding α}
    (h : EnvelopePayloadFacts p) :
    (p.latest = p.bid) ↔ (p.payloadParent = p.payloadBlock) := by
  constructor
  · intro heq; rw [h.parent, h.bidHash, heq]
  · intro heq; rw [←h.parent, ←h.bidHash, heq]

/-- Gloas:1999: empty parent iff `latest_block_hash != bid.block_hash`.
`Block.parentFull` is that test, named here against the same hashes. -/
structure ParentFullFromHashes {α : Type} [DecidableEq α]
    (b : Block) (latest bid : α) : Prop where
  flag : b.parentFull = decide (latest = bid)

theorem cacheAfter_empty_of_hashes {α : Type} [DecidableEq α]
    {b : Block} {latest bid : α} {cached : List Item}
    (hf : ParentFullFromHashes b latest bid) (hne : latest ≠ bid) :
    cacheAfter cached b = cached := by
  have hfalse : b.parentFull = false := by
    rw [hf.flag]
    exact decide_eq_false hne
  exact cacheAfter_empty cached b hfalse

theorem cacheAfter_full_of_hashes {α : Type} [DecidableEq α]
    {b : Block} {latest bid : α} {cached : List Item}
    (hf : ParentFullFromHashes b latest bid) (heq : latest = bid) :
    cacheAfter cached b = expected b := by
  have htrue : b.parentFull = true := by
    rw [hf.flag]
    exact decide_eq_true heq
  exact cacheAfter_full cached b htrue

theorem parentFull_iff_payload_hashes {α : Type} [DecidableEq α]
    {b : Block} {p : PayloadBinding α}
    (hfacts : EnvelopePayloadFacts p)
    (hflag : ParentFullFromHashes b p.latest p.bid) :
    b.parentFull = decide (p.payloadParent = p.payloadBlock) := by
  rw [hflag.flag]
  have hiff := payloadFacts_parent_eq_bid_iff hfacts
  by_cases h : p.latest = p.bid
  · have hp : p.payloadParent = p.payloadBlock := hiff.mp h
    simp [h, hp]
  · have hp : p.payloadParent ≠ p.payloadBlock := mt hiff.mpr h
    simp [h, hp]

/-- The listed mint is `cacheAfter`, and `cacheAfter` is `expected` iff
`latest = bid` (Gloas:1999 + fork-choice.md:681/686). -/
theorem hash_step_listed {α : Type} [DecidableEq α]
    {b : Block} {cached listed : List Item} {latest bid : α}
    (flag : ParentFullFromHashes b latest bid)
    (env : VerifiedEnvelope b cached listed) :
    listed = cacheAfter cached b ∧
      cacheAfter cached b = if latest = bid then expected b else cached := by
  refine ⟨env.honors.decoded, ?_⟩
  by_cases heq : latest = bid
  · rw [cacheAfter_full_of_hashes flag heq, if_pos heq]
  · rw [cacheAfter_empty_of_hashes flag heq, if_neg heq]

theorem hash_step_listed_empty {α : Type} [DecidableEq α]
    {b : Block} {cached listed : List Item} {latest bid : α}
    (flag : ParentFullFromHashes b latest bid)
    (env : VerifiedEnvelope b cached listed) (hne : latest ≠ bid) :
    listed = cached := by
  have h := hash_step_listed flag env
  rw [h.2, if_neg hne] at h
  exact h.1

theorem hash_step_listed_full {α : Type} [DecidableEq α]
    {b : Block} {cached listed : List Item} {latest bid : α}
    (flag : ParentFullFromHashes b latest bid)
    (env : VerifiedEnvelope b cached listed) (heq : latest = bid) :
    listed = expected b := by
  have h := hash_step_listed flag env
  rw [h.2, if_pos heq] at h
  exact h.1

/-- `EnvelopeCredits` whose `parentFull` flag is the archived 1999 hash test
at every accepted block. Dispatch of the retained-cache lists is still
derived, never assumed. -/
inductive HashEnvelopeCredits (α : Type) [DecidableEq α] :
    AccountMap .EVM → List Item → List Block → AccountMap .EVM → Prop where
  | nil (world : AccountMap .EVM) (cached : List Item) :
      HashEnvelopeCredits α world cached [] world
  | cons {before mid after : AccountMap .EVM} {cached : List Item}
      {b : Block} {rest : List Block} {listed : List Item}
      {latest bid : α}
      (flag : ParentFullFromHashes b latest bid)
      (env : VerifiedEnvelope b cached listed)
      (here : ApplyBodyWithdrawals before mid listed)
      (tail : HashEnvelopeCredits α mid (cacheAfter cached b) rest after) :
      HashEnvelopeCredits α before cached (b::rest) after

theorem hashCredits_to_envelope {α : Type} [DecidableEq α]
    {before after : AccountMap .EVM} {cached : List Item} {blocks : List Block}
    (h : HashEnvelopeCredits α before cached blocks after) :
    EnvelopeCredits before cached blocks after := by
  induction h with
  | nil world c => exact .nil world c
  | cons flag env here tail ih => exact .cons env here ih

theorem hashCredits_cons_listed {α : Type} [DecidableEq α]
    {before after : AccountMap .EVM} {cached : List Item}
    {b : Block} {rest : List Block}
    (h : HashEnvelopeCredits α before cached (b::rest) after) :
    ∃ (mid : AccountMap .EVM) (listed : List Item) (latest bid : α),
      ParentFullFromHashes b latest bid ∧
        listed = cacheAfter cached b ∧
        ApplyBodyWithdrawals before mid listed := by
  cases h with
  | cons flag env here _tail =>
    exact ⟨_, _, _, _, flag, env.honors.decoded, here⟩

/-- Consumer `Dispatch` / Nodup remain derived. The minted lists are the
hash-determined `cacheAfter` values. -/
theorem dispatched_counts_from_hash_envelopes {α : Type} [DecidableEq α]
    {initial before after : AccountMap .EVM} {p s c : Nat} {pre post : Clock}
    (prior : Ledger initial p 0 s c before)
    (blocks : List Block) (h : AcceptedBlocks pre blocks post)
    (run : HashEnvelopeCredits α before [] blocks after)
    (powBound : p ≤ 2^64) (migrationConserving : s = 0) :
    Ledger initial p (totalItems (cachedPayloads blocks)) s
        (c+credits ((cachedPayloads blocks).flatMap (·.items))) after ∧
      Counts p (totalItems (cachedPayloads blocks)) s :=
  dispatched_counts_from_envelopes prior blocks h
    (hashCredits_to_envelope run) powBound migrationConserving

/-- fork-choice.md:690-698: the request carries the same listed withdrawals
that the 688 root check accepted. -/
structure EnvelopeNewPayload (b : Block) (cached listed : List Item)
    (req : NewPayloadRequest) : Prop where
  sameListed : req.listed = listed
  verified : VerifiedEnvelope b cached listed

theorem envelopeNewPayload_listed {b : Block} {cached listed : List Item}
    {req : NewPayloadRequest} (h : EnvelopeNewPayload b cached listed req) :
    req.listed = cacheAfter cached b :=
  h.sameListed.trans h.verified.honors.decoded

/-- fork-choice.md:659-699 withdrawal-relevant conjuncts: consistency,
payload facts (681/685-687), withdrawals root, engine admit. -/
structure VerifyExecutionPayloadEnvelope {α : Type} (b : Block)
    (cached listed : List Item) (cons : EnvelopeConsistency)
    (p : PayloadBinding α) (req : NewPayloadRequest) (eng : EngineChecks) :
    Prop where
  consistent : consistencyOk cons = true
  facts : EnvelopePayloadFacts p
  request : EnvelopeNewPayload b cached listed req
  engine : EngineAdmitted eng
  sameSlot : b.slot = p.beacon

theorem verify_requires_engine {α : Type} {b : Block} {cached listed : List Item}
    {cons : EnvelopeConsistency} {p : PayloadBinding α}
    {req : NewPayloadRequest} {eng : EngineChecks}
    (h : VerifyExecutionPayloadEnvelope b cached listed cons p req eng) :
    engineAdmits eng = true :=
  h.engine.admits

theorem verify_requires_timestamp {α : Type} {b : Block} {cached listed : List Item}
    {cons : EnvelopeConsistency} {p : PayloadBinding α}
    {req : NewPayloadRequest} {eng : EngineChecks}
    (h : VerifyExecutionPayloadEnvelope b cached listed cons p req eng) :
    p.payloadTime.val = p.genesisTime.val + p.beacon.val * 12 :=
  payloadFacts_time h.facts

theorem verify_requires_parent_hash {α : Type} {b : Block} {cached listed : List Item}
    {cons : EnvelopeConsistency} {p : PayloadBinding α}
    {req : NewPayloadRequest} {eng : EngineChecks}
    (h : VerifyExecutionPayloadEnvelope b cached listed cons p req eng) :
    p.payloadParent = p.latest :=
  h.facts.parent

/-- fork-choice.md:1096-1116. Known root (1104) and data availability (1108)
precede verify (1113). The subsequent `store.payloads` write (1116) is not
an EL credit. -/
structure OnExecutionPayloadEnvelope {α : Type} (rootKnown da : Bool) (b : Block)
    (cached listed : List Item) (cons : EnvelopeConsistency)
    (p : PayloadBinding α) (req : NewPayloadRequest) (eng : EngineChecks) :
    Prop where
  known : rootKnown = true
  available : da = true
  verified : VerifyExecutionPayloadEnvelope b cached listed cons p req eng

theorem on_envelope_rejects_unknown {α : Type} {da : Bool} {b : Block}
    {cached listed : List Item} {cons : EnvelopeConsistency}
    {p : PayloadBinding α} {req : NewPayloadRequest} {eng : EngineChecks} :
    ¬ OnExecutionPayloadEnvelope false da b cached listed cons p req eng := by
  intro h
  cases h.known

theorem on_envelope_rejects_unavailable {α : Type} {rootKnown : Bool} {b : Block}
    {cached listed : List Item} {cons : EnvelopeConsistency}
    {p : PayloadBinding α} {req : NewPayloadRequest} {eng : EngineChecks} :
    ¬ OnExecutionPayloadEnvelope rootKnown false b cached listed cons p req eng := by
  intro h
  cases h.available

/-- A verified envelope whose `parentFull` flag is the 1999 hash test.
The minted list is then forced by 681/686/688, not a free `listed`. -/
structure VerifiedHashStep {α : Type} [DecidableEq α]
    (b : Block) (cached listed : List Item)
    (cons : EnvelopeConsistency) (p : PayloadBinding α)
    (req : NewPayloadRequest) (eng : EngineChecks) : Prop where
  verify : VerifyExecutionPayloadEnvelope b cached listed cons p req eng
  flag : ParentFullFromHashes b p.latest p.bid

theorem verifiedHashStep_listed {α : Type} [DecidableEq α]
    {b : Block} {cached listed : List Item}
    {cons : EnvelopeConsistency} {p : PayloadBinding α}
    {req : NewPayloadRequest} {eng : EngineChecks}
    (s : VerifiedHashStep b cached listed cons p req eng) :
    listed = if p.latest = p.bid then expected b else cached := by
  have h := hash_step_listed s.flag s.verify.request.verified
  exact h.1.trans h.2

theorem verifiedHashStep_empty {α : Type} [DecidableEq α]
    {b : Block} {cached listed : List Item}
    {cons : EnvelopeConsistency} {p : PayloadBinding α}
    {req : NewPayloadRequest} {eng : EngineChecks}
    (s : VerifiedHashStep b cached listed cons p req eng)
    (hne : p.latest ≠ p.bid) : listed = cached := by
  rw [verifiedHashStep_listed s, if_neg hne]

theorem verifiedHashStep_full {α : Type} [DecidableEq α]
    {b : Block} {cached listed : List Item}
    {cons : EnvelopeConsistency} {p : PayloadBinding α}
    {req : NewPayloadRequest} {eng : EngineChecks}
    (s : VerifiedHashStep b cached listed cons p req eng)
    (heq : p.latest = p.bid) : listed = expected b := by
  rw [verifiedHashStep_listed s, if_pos heq]

inductive VerifiedHashCredits (α : Type) [DecidableEq α] :
    AccountMap .EVM → List Item → List Block → AccountMap .EVM → Prop where
  | nil (world : AccountMap .EVM) (cached : List Item) :
      VerifiedHashCredits α world cached [] world
  | cons {before mid after : AccountMap .EVM} {cached : List Item}
      {b : Block} {rest : List Block} {listed : List Item}
      {cons : EnvelopeConsistency} {p : PayloadBinding α}
      {req : NewPayloadRequest} {eng : EngineChecks}
      (step : VerifiedHashStep b cached listed cons p req eng)
      (here : ApplyBodyWithdrawals before mid listed)
      (tail : VerifiedHashCredits α mid (cacheAfter cached b) rest after) :
      VerifiedHashCredits α before cached (b::rest) after

theorem verifiedHashCredits_to_hash {α : Type} [DecidableEq α]
    {before after : AccountMap .EVM} {cached : List Item} {blocks : List Block}
    (h : VerifiedHashCredits α before cached blocks after) :
    HashEnvelopeCredits α before cached blocks after := by
  induction h with
  | nil world c => exact .nil world c
  | cons step here tail ih =>
    exact .cons step.flag step.verify.request.verified here ih

theorem verifiedHashCredits_cons_listed {α : Type} [DecidableEq α]
    {before after : AccountMap .EVM} {cached : List Item}
    {b : Block} {rest : List Block}
    (h : VerifiedHashCredits α before cached (b::rest) after) :
    ∃ (mid : AccountMap .EVM) (listed : List Item) (p : PayloadBinding α),
      ParentFullFromHashes b p.latest p.bid ∧
        listed = cacheAfter cached b ∧
        ApplyBodyWithdrawals before mid listed := by
  cases h with
  | cons step here _tail =>
    exact ⟨_, _, _, step.flag, step.verify.request.verified.honors.decoded, here⟩

theorem dispatched_counts_from_verified_hash {α : Type} [DecidableEq α]
    {initial before after : AccountMap .EVM} {p s c : Nat} {pre post : Clock}
    (prior : Ledger initial p 0 s c before)
    (blocks : List Block) (accepted : AcceptedBlocks pre blocks post)
    (run : VerifiedHashCredits α before [] blocks after)
    (powBound : p ≤ 2^64) (migrationConserving : s = 0) :
    Ledger initial p (totalItems (cachedPayloads blocks)) s
        (c+credits ((cachedPayloads blocks).flatMap (·.items))) after ∧
      Counts p (totalItems (cachedPayloads blocks)) s :=
  dispatched_counts_from_hash_envelopes prior blocks accepted
    (verifiedHashCredits_to_hash run) powBound migrationConserving

/-- fork-choice.md:1096-1116 plus the 1999 hash test: a stored envelope
still mints the hash-forced list, and the store write is not the credit. -/
structure OnEnvelopeHashStep {α : Type} [DecidableEq α]
    (rootKnown da : Bool) (b : Block) (cached listed : List Item)
    (cons : EnvelopeConsistency) (p : PayloadBinding α)
    (req : NewPayloadRequest) (eng : EngineChecks) : Prop where
  on : OnExecutionPayloadEnvelope rootKnown da b cached listed cons p req eng
  flag : ParentFullFromHashes b p.latest p.bid

theorem onEnvelopeHash_to_verified {α : Type} [DecidableEq α]
    {rootKnown da : Bool} {b : Block} {cached listed : List Item}
    {cons : EnvelopeConsistency} {p : PayloadBinding α}
    {req : NewPayloadRequest} {eng : EngineChecks}
    (s : OnEnvelopeHashStep rootKnown da b cached listed cons p req eng) :
    VerifiedHashStep b cached listed cons p req eng :=
  ⟨s.on.verified, s.flag⟩

theorem onEnvelopeHashStep_listed {α : Type} [DecidableEq α]
    {rootKnown da : Bool} {b : Block} {cached listed : List Item}
    {cons : EnvelopeConsistency} {p : PayloadBinding α}
    {req : NewPayloadRequest} {eng : EngineChecks}
    (s : OnEnvelopeHashStep rootKnown da b cached listed cons p req eng) :
    listed = if p.latest = p.bid then expected b else cached :=
  verifiedHashStep_listed (onEnvelopeHash_to_verified s)

theorem onEnvelopeHashStep_empty {α : Type} [DecidableEq α]
    {rootKnown da : Bool} {b : Block} {cached listed : List Item}
    {cons : EnvelopeConsistency} {p : PayloadBinding α}
    {req : NewPayloadRequest} {eng : EngineChecks}
    (s : OnEnvelopeHashStep rootKnown da b cached listed cons p req eng)
    (hne : p.latest ≠ p.bid) : listed = cached :=
  verifiedHashStep_empty (onEnvelopeHash_to_verified s) hne

/-- `EnvelopeCredits.cons` is an `apply_body` pass, not a store insert. -/
theorem envelopeCredits_cons_implies_apply
    {before after : AccountMap .EVM} {cached : List Item}
    {b : Block} {rest : List Block}
    (h : EnvelopeCredits before cached (b::rest) after) :
    ∃ mid listed,
      VerifiedEnvelope b cached listed ∧
      ApplyBodyWithdrawals before mid listed ∧
      EnvelopeCredits mid (cacheAfter cached b) rest after := by
  cases h with
  | @cons before mid after cached b rest listed env here tail =>
    exact ⟨mid, listed, env, here, tail⟩

/-- An `EnvelopeCredits` remint is two `create_ether` loops of `g`.
Gloas:1999 does not add a second `applyTagged`. -/
theorem remint_elCredit_twice
    {before after : AccountMap .EVM} {slot : U64}
    {pending : List BuilderPending}
    {partials : List CreditedPartial}
    {sweeps : List BuilderSweepVisit}
    {n start : Nat} {flagged : List (Item × Bool)} {e : Block}
    (hle : flagged.length ≤ validatorsSweepLimit n)
    (he : e.parentFull = false)
    (run : EnvelopeCredits before []
      [gloasFromBuildersBlock slot pending partials sweeps flagged, e]
      after) :
    ∃ mid,
      ElCredit before
        (creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged)) mid ∧
      ElCredit mid
        (creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged)) after := by
  obtain ⟨mid, listed, env, here, tail⟩ :=
    envelopeCredits_cons_implies_apply run
  have hcache := cacheAfter_full_gloasFromBuildersBlock [] slot pending
    partials sweeps n start flagged hle
  have hlist : listed =
      creditedItems (gloasFromBuilders pending partials sweeps n start
        flagged) :=
    env.honors.decoded.trans hcache
  have hfirst : ElCredit before
      (creditedItems (gloasFromBuilders pending partials sweeps n start
        flagged)) mid :=
    hlist ▸ here.once
  have tail' : EnvelopeCredits mid
      (creditedItems (gloasFromBuilders pending partials sweeps n start
        flagged)) [e] after :=
    hcache ▸ tail
  obtain ⟨mid2, listed2, env2, here2, tail2⟩ :=
    envelopeCredits_cons_implies_apply tail'
  have hlist2 : listed2 =
      creditedItems (gloasFromBuilders pending partials sweeps n start
        flagged) :=
    env2.honors.decoded.trans
      (cacheAfter_empty
        (creditedItems (gloasFromBuilders pending partials sweeps n start
          flagged))
        e he)
  cases tail2
  exact ⟨mid, hfirst, hlist2 ▸ here2.once⟩

#print axioms queueStage_guarded
#print axioms queueStage_length
#print axioms guarded_of_length
#print axioms sweepStage_guarded
#print axioms sweepStage_length
#print axioms sweepStage_combined
#print axioms electraPartialsLimit_le_15
#print axioms electraPartials_assert
#print axioms electraPartialLoop_guarded
#print axioms electraPartials_guarded
#print axioms electraPartials_bound
#print axioms electraPartialLoop_ripe
#print axioms electraValidators_assert
#print axioms electraValidators_guarded
#print axioms isEligibleForPartial_flags
#print axioms isEligibleForPartial_rejects_exited
#print axioms isEligibleForPartial_rejects_no_excess
#print axioms isFullyWithdrawable_rejects_zero
#print axioms isFullyWithdrawable_rejects_other_prefix
#print axioms maxEffectiveBalance_compounding
#print axioms maxEffectiveBalance_eth1
#print axioms bls_prefix_byte
#print axioms eth1_prefix_byte
#print axioms compounding_prefix_byte
#print axioms prefix_bytes_distinct
#print axioms credOfByte_eth1
#print axioms credOfByte_compounding
#print axioms credOfByte_bls
#print axioms credOfByte_eq_eth1_iff
#print axioms credOfByte_eq_compounding_iff
#print axioms credOfByte_swap_ne
#print axioms hasEth1Bytes_nil
#print axioms hasEth1Bytes_cons
#print axioms hasEth1Bytes_bls
#print axioms hasCompoundingBytes_cons
#print axioms hasCompoundingBytes_eth1
#print axioms hasExecutionBytes_nil
#print axioms hasExecutionBytes_eth1
#print axioms hasExecutionBytes_compounding
#print axioms hasExecutionBytes_bls
#print axioms hasExecutionCredential_of_byte
#print axioms maxEffective_of_eth1_byte
#print axioms maxEffective_of_compounding_byte
#print axioms prefix_swap_changes_max
#print axioms isFullyWithdrawable_rejects_bls
#print axioms credential_layout
#print axioms address_slice_width
#print axioms credAddressBytes_length
#print axioms eth1Credential_length
#print axioms eth1Credential_hasEth1
#print axioms eth1Credential_hasExecution
#print axioms eth1Credential_pad
#print axioms credAddress_of_eth1
#print axioms cred_address_is_not_take20
#print axioms executionAddress_bits
#print axioms accountAddress_size_eq
#print axioms execution_address_width_matches
#print axioms accountAddress_size_ne_u256
#print axioms bytesBeToNat_nil
#print axioms bytesLeToNat_nil
#print axioms bytesBeToNat_lt
#print axioms pow256_20_eq_two_pow_160
#print axioms executionAddressNat_lt
#print axioms executionAddress_val_eq
#print axioms bytesBeToNat_zeros
#print axioms bytesLeToNat_zeros
#print axioms sample_be_eq
#print axioms sample_le_eq
#print axioms execution_be_ne_le
#print axioms execution_width_ne_credential
#print axioms accountAddress_two_pow_wraps
#print axioms electraPartialOf_skips_exited
#print axioms electraPartialLoop_skips_ineligible
#print axioms balanceAfterWithdrawals_exact
#print axioms withdrawnAmount_nil
#print axioms balanceAfterFits_nil
#print axioms balanceAfter_nil
#print axioms withdrawnAmount_cons_eq
#print axioms withdrawnAmount_cons_ne
#print axioms decreaseBalance_eq_sub
#print axioms builder_min_eq_decrease
#print axioms applyOne_eq_sub
#print axioms GWEI_MOD_pos
#print axioms gweiWrapSub_lt
#print axioms gweiWrapSub_eq_sub
#print axioms gweiWrapSub_of_gt
#print axioms gweiWrapSub_pos_of_gt
#print axioms gweiWrapSub_five_seven
#print axioms decreaseBalance_ne_gweiWrap
#print axioms balanceAfter_ne_wrap_of_gt
#print axioms balanceAfter_eq_wrap_of_fits
#print axioms gweiWrapSub_ne_sub_of_gt
#print axioms BUILDER_INDEX_FLAG_eq
#print axioms BUILDER_INDEX_FLAG_testBit
#print axioms isBuilderIndex_iff
#print axioms isBuilderIndex_zero
#print axioms isBuilderIndex_flag
#print axioms toBuilderIndex_le
#print axioms toBuilderIndex_zero
#print axioms toBuilderIndex_flag
#print axioms toValidatorIndex_zero
#print axioms land_lor_flag
#print axioms toValidatorIndex_is_builder
#print axioms applyOneFromIndex_eq_sub
#print axioms toBuilderIndex_u64
#print axioms builderFlagNotU64_lt
#print axioms builderFlagNotU64_testBit_40
#print axioms toBuilderIndexU64_lt
#print axioms land_flag_eq_ite
#print axioms toBuilderIndex_of_clear_bit
#print axioms toBuilderIndex_of_flag_bit
#print axioms split_of_flag_bit
#print axioms sub_two_pow_of_flag_bit
#print axioms testBit_high_of_flag
#print axioms xor_two_pow_of_flag_bit
#print axioms xor_flag_eq_sub_of_flag_bit
#print axioms toBuilderIndexU64_of_lt
#print axioms toBuilderIndex_eq_u64_of_clear
#print axioms toBuilderIndex_eq_u64_of_lt
#print axioms toBuilderIndex_two_pow
#print axioms toBuilderIndexU64_two_pow
#print axioms toBuilderIndex_two_pow_ne_u64
#print axioms toBuilderIndex_flag_eq_u64
#print axioms toBuilderIndex_three_eq_u64
#print axioms builderIndexFits_flag
#print axioms builderIndexFits_two_pow
#print axioms writtenIndex_builder
#print axioms writtenIndex_validator
#print axioms applyOneWithdrawal_builder_keeps_validators
#print axioms applyOneWithdrawal_validator_keeps_builders
#print axioms applyOneWithdrawal_builder_written
#print axioms applyOneWithdrawal_validator_written
#print axioms applyOneWithdrawal_builder_other
#print axioms applyOneWithdrawal_validator_other
#print axioms applyTagged_nil
#print axioms applyTagged_cons
#print axioms applyTagged_singleton
#print axioms applyTagged_foldl
#print axioms applyOneWithdrawal_validators_fn
#print axioms applyTagged_validators_only
#print axioms applyWithdrawals_nil
#print axioms apply_eq_balanceAfter
#print axioms apply_eq_balanceAfter_sat
#print axioms apply_eq_wrap_of_fits
#print axioms apply_ne_wrap_of_gt
#print axioms balanceAfter_u64
#print axioms balanceAfter_full
#print axioms validatorsSweepLimit_le_sweep
#print axioms validatorsSweepLimit_le_registry
#print axioms nextValidatorIndex_lt
#print axioms nextValidatorIndex_wrap
#print axioms visitRing_length
#print axioms visitRing_get
#print axioms visitRing_mem
#print axioms visitRing_nodup
#print axioms electraVisit_nodup
#print axioms updateNext_partial
#print axioms updateNext_full
#print axioms indexSeq_length
#print axioms indexSeq_pairwise
#print axioms indexSeq_nodup
#print axioms indexSeq_append
#print axioms updateNextWithdrawalIndex_empty
#print axioms updateNextWithdrawalIndex_singleton
#print axioms indexSeq_last
#print axioms updateNextWithdrawalIndex_seq
#print axioms indexSeq_pair_nodup
#print axioms updateNextWithdrawalIndex_u64
#print axioms withdrawalIndexWrap_lt
#print axioms withdrawalIndexWrap_eq_of_lt
#print axioms withdrawalIndexWrap_two_pow
#print axioms indexSeq_upper
#print axioms indexSeq_lt_of_fits
#print axioms indexSeq_eq_wrap_of_fits
#print axioms updateNext_eq_wrap_of_fits
#print axioms updateNext_ne_wrap_of_ge
#print axioms updateNext_last_u64_is_two_pow
#print axioms updateNext_last_u64_ne_wrap
#print axioms indexSeq_last_u64_pair
#print axioms indexSeqWrap_last_u64_pair
#print axioms indexSeq_last_u64_ne_wrap_list
#print axioms withdrawalIndexFits_rejects_last_u64_two
#print axioms validators_prior_lt_16
#print axioms blockOfElectra_slot
#print axioms electraInputs_slot
#print axioms electraInputs_items_bounded
#print axioms total_count_from_electra
#print axioms items_bounded
#print axioms total_count
#print axioms total_blocks
#print axioms dispatched_counts
#print axioms indexedWithdrawals_indices
#print axioms indexedWithdrawals_items
#print axioms indexedWithdrawals_nodup
#print axioms nextIndexAfter_nil
#print axioms nextIndexAfter_eq
#print axioms indexedChain_items
#print axioms indexedChain_indices
#print axioms indexedChain_nodup
#print axioms indexedChain_length
#print axioms indexed_total_count
#print axioms dispatch_of_indexed
#print axioms dispatched_counts_from_indexed
#print axioms create_ether_wei
#print axioms increaseBalance_existing
#print axioms increaseBalance_missing
#print axioms createEther_existing
#print axioms createEther_missing
#print axioms createEther_existing_wei
#print axioms create_ether_gwei_nonzero
#print axioms uint256_add_toNat
#print axioms uint256_add_pos
#print axioms accountNonceBalanceEmpty_balance
#print axioms createEther_existing_balance_pos
#print axioms createEther_existing_not_empty
#print axioms createEther_missing_balance_pos
#print axioms createEther_missing_not_empty
#print axioms create_ether_zero_wei
#print axioms uint256_eq_of_toNat
#print axioms uint256_add_zero
#print axioms createEther_existing_zero
#print axioms createEther_existing_zero_keeps_nonzero
#print axioms default_account_nonce
#print axioms default_account_balance
#print axioms default_nonce_balance_empty
#print axioms createEther_missing_zero
#print axioms createEther_missing_zero_nonce_balance_empty
#print axioms createEther_existing_zero_keeps_empty
#print axioms increaseBalance_present
#print axioms createEther_keeps_present
#print axioms elCredit_singleton
#print axioms elCredit_singleton_existing
#print axioms elCredit_dispatch
#print axioms dispatch_append
#print axioms blockCredits_flat
#print axioms dispatched_counts_from_blocks
#print axioms cacheAfter_empty
#print axioms cacheAfter_bounded
#print axioms cached_slots
#print axioms cached_total_count
#print axioms envelopeCredits_flat
#print axioms dispatched_counts_from_envelopes
#print axioms indexedCacheAfter_items
#print axioms indexedCacheAfter_empty
#print axioms nextIndexAfterCache_empty
#print axioms nextIndexAfterCache_full
#print axioms indexedCacheAfter_full_nodup
#print axioms indexedChain_empty_step
#print axioms indexedChain_full_step
#print axioms mintedItemLists_eq_payloads
#print axioms indexedCachedFrom_minted
#print axioms flatten_map_eq_flatMap
#print axioms minted_flat_eq_cached_from
#print axioms minted_flat_eq_cached
#print axioms indexedCachedFrom_items
#print axioms indexedCachedFrom_length_eq_flat
#print axioms indexedCached_flat_items
#print axioms indexedCached_flat_length
#print axioms indexed_cached_total_count
#print axioms dispatch_of_indexed_cached
#print axioms dispatched_counts_from_indexed_envelopes
#print axioms engine_rejects_empty_tx
#print axioms engine_rejects_notify
#print axioms engineAdmitted_flags
#print axioms engineAdmitted_not_empty
#print axioms engineAdmitted_notify
#print axioms consistency_rejects_signature
#print axioms payloadFacts_slot
#print axioms payloadFacts_time
#print axioms payloadFacts_parent_eq_bid_iff
#print axioms cacheAfter_empty_of_hashes
#print axioms cacheAfter_full_of_hashes
#print axioms parentFull_iff_payload_hashes
#print axioms hash_step_listed
#print axioms hash_step_listed_empty
#print axioms hash_step_listed_full
#print axioms hashCredits_to_envelope
#print axioms hashCredits_cons_listed
#print axioms dispatched_counts_from_hash_envelopes
#print axioms envelopeNewPayload_listed
#print axioms verify_requires_engine
#print axioms verify_requires_timestamp
#print axioms verify_requires_parent_hash
#print axioms on_envelope_rejects_unknown
#print axioms on_envelope_rejects_unavailable
#print axioms verifiedHashStep_listed
#print axioms verifiedHashStep_empty
#print axioms verifiedHashStep_full
#print axioms verifiedHashCredits_to_hash
#print axioms verifiedHashCredits_cons_listed
#print axioms dispatched_counts_from_verified_hash
#print axioms onEnvelopeHash_to_verified
#print axioms onEnvelopeHashStep_listed
#print axioms onEnvelopeHashStep_empty
#print axioms envelopeCredits_cons_implies_apply
#print axioms creditedItems_length
#print axioms creditedPairs_length
#print axioms credited_projection_count
#print axioms creditedItems_nil
#print axioms creditedPairs_nil
#print axioms creditedItems_cons
#print axioms creditedPairs_cons
#print axioms credited_cl_amount_is_gwei
#print axioms credited_el_amount_is_wei
#print axioms creditedRun_cl
#print axioms creditedRun_el
#print axioms creditedRun_dispatch
#print axioms creditedRun_empty
#print axioms creditedRun_singleton
#print axioms applyBody_of_credited
#print axioms dispatched_counts_from_credited
#print axioms credited_matches_cached
#print axioms dispatched_counts_from_credited_envelopes
#print axioms archived_items_of_indexed
#print axioms archived_items_of_credited
#print axioms archived_projection_count
#print axioms sszEl_ignores_index
#print axioms sszEl_ignores_validator
#print axioms sszCl_ignores_address
#print axioms sszEl_ne_validator_as_address
#print axioms sszAsArchived_asCredited
#print axioms sszAsArchived_asIndexed
#print axioms sszAsArchived_pair
#print axioms stampIndex_nil
#print axioms stampIndex_cons
#print axioms stampIndex_length
#print axioms stampIndex_credited
#print axioms stampIndex_items
#print axioms stampIndex_indexed
#print axioms stampIndex_indices
#print axioms stampIndex_nodup
#print axioms creditedRun_of_stamped
#print axioms dispatched_counts_from_stamped
#print axioms stampIndex_validators
#print axioms creditEligible_nil_visits
#print axioms creditEligible_nil_flagged
#print axioms creditEligible_items
#print axioms creditEligible_indices_sublist
#print axioms creditEligible_indices_nodup
#print axioms creditEligible_mem_ring
#print axioms visitRing_lt
#print axioms land_flag_of_lt
#print axioms isBuilderIndex_of_lt
#print axioms visitRing_not_builder
#print axioms creditEligible_not_builder
#print axioms creditEligible_pairs_not_builder
#print axioms creditEligible_apply_validators
#print axioms electraCreditEligible_items
#print axioms electraCreditEligible_nodup
#print axioms electraCreditEligible_stamped_nodup
#print axioms dispatched_counts_from_electra_credits
#print axioms blockOfElectra_empty_stages
#print axioms items_of_electra_validator_block
#print axioms dispatched_counts_from_electra_block
#print axioms creditedItems_append
#print axioms creditQueueStage_items
#print axioms creditPartialLoop_items
#print axioms creditPartials_items
#print axioms creditSweepStage_items
#print axioms creditQueueStage_length
#print axioms creditPartials_length
#print axioms creditSweepStage_length
#print axioms gloasCredited_items
#print axioms items_of_gloas_credited
#print axioms dispatched_counts_from_gloas_credited
#print axioms stampIndex_append
#print axioms stampedChain_items
#print axioms stampedChain_credited
#print axioms stampedChain_indices
#print axioms stampedChain_nodup
#print axioms indexedChain_of_credited
#print axioms items_of_gloasBlock
#print axioms indexedChain_of_gloas_block
#print axioms indexedChain_of_two_gloas
#print axioms dispatched_counts_from_stamped_gloas
#print axioms or_flag_eq_add_of_lt
#print axioms toBuilderIndex_toValidatorIndex_of_lt
#print axioms toValidatorIndex_flag
#print axioms toValidatorIndex_flag_ne_add
#print axioms toBuilderIndex_toValidatorIndex_flag
#print axioms builder_flag_lt_u64
#print axioms toValidatorIndex_lt_of_u64
#print axioms toValidatorIndexU64_lt
#print axioms toValidatorIndex_eq_u64_of_lt
#print axioms toValidatorIndex_two_pow
#print axioms toValidatorIndexU64_two_pow
#print axioms toValidatorIndex_two_pow_ne_u64
#print axioms writtenIndex_of_lt
#print axioms asQueueCredited_is_builder
#print axioms asSweepCredited_is_builder
#print axioms creditBuilderQueue_items
#print axioms creditBuilderQueue_is_builder
#print axioms creditBuilderQueue_keeps_validators
#print axioms creditBuilderSweep_is_builder
#print axioms creditBuilderSweep_keeps_validators
#print axioms creditPartialLoop_indices_sublist
#print axioms creditPartials_not_builder
#print axioms items_of_gloasFromBuilders
#print axioms dispatched_counts_from_gloasFromBuilders
#print axioms applyTagged_append
#print axioms applyTagged_validators_keep_builders
#print axioms applyTagged_validators_eq_of_validators_eq
#print axioms applyTagged_builders_eq_of_builders_eq
#print axioms creditedPairs_append
#print axioms electraCreditEligible_pairs_not_builder
#print axioms electraCreditEligible_keeps_builders
#print axioms creditPartials_pairs_not_builder
#print axioms creditPartials_keeps_builders
#print axioms gloasFromBuilders_eq_stages
#print axioms applyTagged_mixed_validators
#print axioms applyTagged_mixed_builders
#print axioms gloasFromBuilders_applyTagged_validators
#print axioms gloasFromBuilders_applyTagged_builders
#print axioms gloasFromBuildersBlock_parentFull
#print axioms items_of_gloasFromBuildersBlock
#print axioms expected_of_gloasFromBuildersBlock
#print axioms cacheAfter_full_gloasFromBuildersBlock
#print axioms mintedItemLists_gloas_then_empty
#print axioms minted_flat_gloas_then_empty
#print axioms indexedCacheAfter_full_gloasFromBuildersBlock
#print axioms indexedCachedFrom_gloas_then_empty
#print axioms remint_repeats_gloasFromBuilders_indices
#print axioms remint_stamps_gloasFromBuilders
#print axioms indexedChain_gloas_then_empty
#print axioms remint_count_gloasFromBuilders
#print axioms cached_flat_gloas_then_empty
#print axioms totalItems_gloas_then_empty
#print axioms dispatched_counts_from_gloas_remint
#print axioms applyTagged_credited_append
#print axioms verifiedEnvelope_gloasFromBuildersBlock
#print axioms verifiedEnvelope_empty_remint
#print axioms envelopeCredits_gloas_then_empty
#print axioms envelopeCredits_gloas_then_empty_flat
#print axioms dispatched_counts_from_gloas_remint_envelopes
#print axioms computed_flat_gloas_then_empty
#print axioms applyTagged_computed_gloas_then_empty
#print axioms envelopeCredits_gloas_then_empty_of_elCredit
#print axioms remint_elCredit_twice
#print axioms indexInRange_builder
#print axioms indexInRange_validator
#print axioms indexInRange_toValidatorIndex
#print axioms applyTagged_keeps_validator_oob
#print axioms applyTagged_keeps_builder_oob
#print axioms electraCreditEligible_inRange
#print axioms creditBuilderQueue_inRange
#print axioms creditBuilderSweep_inRange
#print axioms creditPartials_inRange
#print axioms gloasFromBuilders_pairs_inRange
#print axioms applyTagged_gloasFromBuilders_keeps_validator_oob
#print axioms applyTagged_gloasFromBuilders_keeps_builder_oob
#print axioms visitRing_pos
#print axioms visitRing_start_mem
#print axioms visitRing_mem_offset
#print axioms visitRing_flag_mem
#print axioms sweepStart_flag_succ
#print axioms visitRing_exists_builder
#print axioms visitRing_mem_flag
#print axioms validatorsSweepLimit_flag_succ
#print axioms electraCreditEligible_gt_flag_credits_flag
#print axioms electraCreditEligible_gt_flag_pairs_are_builder
#print axioms electraCreditEligible_gt_flag_not_all_validators
#print axioms applyTagged_electra_gt_flag_writes_builder_zero
#print axioms nextValidatorIndex_of_zero
#print axioms nextValidatorIndex_zero_not_bound
#print axioms sweepStart_of_zero
#print axioms visitRing_zero_succ
#print axioms visitRing_zero_get
#print axioms visitRing_zero_last
#print axioms visitRing_lt_needs_registry
#print axioms electraCreditEligible_empty_registry
end Eip8282.Audit.Integrator.ProtocolWithdrawalExtraction
