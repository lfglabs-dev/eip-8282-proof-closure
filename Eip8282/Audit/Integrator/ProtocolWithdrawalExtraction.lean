import Eip8282.Audit.Integrator.ProtocolWithdrawalCount
import Eip8282.Audit.Integrator.ProtocolSlotExtraction

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
false, so `modify_state` 583-587 cannot destroy. Destroy after a
zero increment, and line 384 `code_hash == EMPTY_CODE_HASH`, remain
named.

Electra `get_pending_partial_withdrawals` (1360-1398) and
`get_validators_sweep_withdrawals` (1407-1454) are now extracted:
limit `min(prior+8, 15)` (Electra:336-338 / 1366-1368), pending assert
1370, validator `withdrawals_limit = 16` and `prior < 16` (1414-1416).
`partialBound` / `validatorsGuard` are derived for a block built from
those loops (`blockOfElectra`). Eligibility is now the archived Electra
predicates (708-718, 668-677, 688-702), not a free Boolean; remaining
named inputs are SSZ credential bytes and an empty validator registry
(`% 0`). `get_balance_after_withdrawals` underflow is discharged on an
empty prior and whenever `withdrawn ≤ balance` (the Gwei `Uint64` wrap
remains named only when that inequality fails). The sweep cursor
rotation (Electra:1420-1451 / Capella:516-528) is extracted below.

OPEN (explicit hypotheses or adapters, not proved): SSZ withdrawal-
credential byte values (0x01/0x02 prefixes modelled as
`WithdrawalPrefix`); the Gwei `Uint64` wrap of
`get_balance_after_withdrawals` when `withdrawn > balance` (the
saturating `decrease_balance` / builder-`min` path is extracted);
empty-registry `% 0` and SSZ `ValidatorIndex < len(validators)`
for the sweep cursor; `WithdrawalIndex` Uint64 wrap when
`start + n ≥ 2^64` (the successor uniqueness itself is derived);
`indexedChain` / `indexedCachedFrom` produce `Withdrawal.index` on
credited and retained-cache lists here and are not yet imported by
StageExtraction / Makefile;
`get_beacon_proposer_indices` SHA256/seed (Fulu:372-378) of the
lookahead fill (`process_proposer_lookahead` Fulu:481-489 itself is
extracted in the slot module: clock copy plus 64-length shift);
SSZ Gwei/Uint64 decode to `Item`; `WithdrawalsRootMatch` (root equality to
decoded list equality); implementation-dependent engine predicates
`is_valid_block_hash` / `is_valid_versioned_hashes` / `notify_new_payload`;
`notify_new_payload` is not `create_ether`; signature / header / bid-field
bodies behind the named consistency Booleans (fork-choice.md:668-682);
hash *values* are uninterpreted (no Keccak); `TimeFitsU64` outside the
discharged `MIN_GENESIS_TIME`/`2^60` domain; canonical
store contents behind `store.block_states` / `is_data_available`;
`CreateEther` empty-account destroy after a zero increment on an
already-empty or missing recipient (a zero increment on a nonzero
existing balance is the identity);
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
Electra:285 / 635 `COMPOUNDING_WITHDRAWAL_PREFIX = 0x02`. Byte values
are named; only the prefix tag is retained. -/
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

def decreaseAt (b : Nat → Nat) (idx amt : Nat) (j : Nat) : Nat :=
  if j = idx then decreaseBalance (b idx) amt else b j

/-- Capella:498-500 / Gloas:1931 validator branch: fold `decrease_balance`. -/
def applyWithdrawals (b : Nat → Nat) : List (Nat × Nat) → Nat → Nat
  | [], i => b i
  | (idx, amt)::rest, i => applyWithdrawals (decreaseAt b idx amt) rest i

theorem applyWithdrawals_nil (b : Nat → Nat) (i : Nat) :
    applyWithdrawals b [] i = b i :=
  rfl

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
amount. Empty-account destroy after a zero increment
(`account_exists_and_is_empty` 359-385, `modify_state` 583-587) remains
named, as does field identity of Lean `default` vs Python `EMPTY_ACCOUNT`. -/
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
#print axioms applyWithdrawals_nil
#print axioms apply_eq_balanceAfter
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
end Eip8282.Audit.Integrator.ProtocolWithdrawalExtraction
