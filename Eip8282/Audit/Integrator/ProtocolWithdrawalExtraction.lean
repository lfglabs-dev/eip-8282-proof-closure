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
`ApplyBodyWithdrawals` of the listed withdrawals.

OPEN (explicit hypotheses or adapters, not proved): the inherited
`get_pending_partial_withdrawals` and `get_validators_sweep_withdrawals`
bodies are absent from the archived Gloas beacon-chain body; `partialBound`
and `validatorsGuard` remain the archived assert / trace inputs;
SSZ Gwei/Uint64 decode to `Item`; `WithdrawalsRootMatch` (root equality to
decoded list equality); implementation-dependent engine predicates
`is_valid_block_hash` / `is_valid_versioned_hashes` / `notify_new_payload`;
`notify_new_payload` is not `create_ether`; signature / header / bid
consistency bodies (fork-choice.md:668-682); `compute_time_at_slot` and
parent-hash bytes (686-687); canonical store contents behind
`store.block_states` / `is_data_available`; `CreateEther`; PoW count and
migration conservation. -/
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

/-- The withdrawal inputs of one accepted Gloas block. `parentFull` is the
line-1999 test. `pending` and `builders` are the archived loop inputs;
`pendingPartial`/`validators` are the absent inherited helpers' outputs.
`partialBound` is the archived assert at line 1847, executed with the prior
list builder-pending ++ pending-partial; `validatorsGuard` remains an explicit
trace hypothesis for the absent validators sweep. -/
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

/-- fork.py:1118 `create_ether(wd_state, wd.address, U256(wd.amount)*GWEI_TO_WEI)`.
Agreement with Lean `increaseBalance` is the named adapter, not a proved
Python/Lean interpreter equality. -/
structure CreateEther (before : AccountMap .EVM) (item : Item)
    (after : AccountMap .EVM) : Prop where
  agreed : after = before.increaseBalance .EVM item.recipient item.amount

/-- fork.py:1111-1118: one `create_ether` per listed withdrawal, in list order.
`apply_body` fork.py:840 calls this loop exactly once with `block.withdrawals`. -/
inductive ElCredit : AccountMap .EVM → List Item → AccountMap .EVM → Prop where
  | nil (world : AccountMap .EVM) : ElCredit world [] world
  | cons {before mid after : AccountMap .EVM} {item : Item} {rest : List Item}
      (one : CreateEther before item mid) (tail : ElCredit mid rest after) :
      ElCredit before (item::rest) after

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

/-- fork-choice.md:685-687. Slot equality is also `VerifiedEnvelopeSlot`. -/
structure EnvelopePayloadAgree where
  slotOk : Bool
  parentHashOk : Bool
  timestampOk : Bool

def payloadAgreeOk (p : EnvelopePayloadAgree) : Bool :=
  p.slotOk && p.parentHashOk && p.timestampOk

theorem payload_rejects_slot (p : EnvelopePayloadAgree) (h : p.slotOk = false) :
    payloadAgreeOk p = false := by
  simp [payloadAgreeOk, h]

theorem payloadAgree_slot {p : EnvelopePayloadAgree} (h : payloadAgreeOk p = true) :
    p.slotOk = true := by
  simp [payloadAgreeOk] at h
  exact h.1.1

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
payload agrees, withdrawals root, engine admit. -/
structure VerifyExecutionPayloadEnvelope (b : Block) (cached listed : List Item)
    (cons : EnvelopeConsistency) (pay : EnvelopePayloadAgree)
    (req : NewPayloadRequest) (eng : EngineChecks) : Prop where
  consistent : consistencyOk cons = true
  payload : payloadAgreeOk pay = true
  request : EnvelopeNewPayload b cached listed req
  engine : EngineAdmitted eng

theorem verify_requires_engine {b : Block} {cached listed : List Item}
    {cons : EnvelopeConsistency} {pay : EnvelopePayloadAgree}
    {req : NewPayloadRequest} {eng : EngineChecks}
    (h : VerifyExecutionPayloadEnvelope b cached listed cons pay req eng) :
    engineAdmits eng = true :=
  h.engine.admits

/-- fork-choice.md:1096-1116. Known root (1104) and data availability (1108)
precede verify (1113). The subsequent `store.payloads` write (1116) is not
an EL credit. -/
structure OnExecutionPayloadEnvelope (rootKnown da : Bool) (b : Block)
    (cached listed : List Item) (cons : EnvelopeConsistency)
    (pay : EnvelopePayloadAgree) (req : NewPayloadRequest)
    (eng : EngineChecks) : Prop where
  known : rootKnown = true
  available : da = true
  verified : VerifyExecutionPayloadEnvelope b cached listed cons pay req eng

theorem on_envelope_rejects_unknown {da : Bool} {b : Block}
    {cached listed : List Item} {cons : EnvelopeConsistency}
    {pay : EnvelopePayloadAgree} {req : NewPayloadRequest} {eng : EngineChecks} :
    ¬ OnExecutionPayloadEnvelope false da b cached listed cons pay req eng := by
  intro h
  cases h.known

theorem on_envelope_rejects_unavailable {rootKnown : Bool} {b : Block}
    {cached listed : List Item} {cons : EnvelopeConsistency}
    {pay : EnvelopePayloadAgree} {req : NewPayloadRequest} {eng : EngineChecks} :
    ¬ OnExecutionPayloadEnvelope rootKnown false b cached listed cons pay req eng := by
  intro h
  cases h.available

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
#print axioms items_bounded
#print axioms total_count
#print axioms total_blocks
#print axioms dispatched_counts
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
#print axioms engine_rejects_empty_tx
#print axioms engine_rejects_notify
#print axioms engineAdmitted_flags
#print axioms engineAdmitted_not_empty
#print axioms engineAdmitted_notify
#print axioms consistency_rejects_signature
#print axioms payloadAgree_slot
#print axioms envelopeNewPayload_listed
#print axioms verify_requires_engine
#print axioms on_envelope_rejects_unknown
#print axioms on_envelope_rejects_unavailable
#print axioms envelopeCredits_cons_implies_apply
end Eip8282.Audit.Integrator.ProtocolWithdrawalExtraction
