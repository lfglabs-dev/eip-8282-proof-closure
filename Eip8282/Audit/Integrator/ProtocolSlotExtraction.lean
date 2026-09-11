import Eip8282.Audit.Integrator.ResourceBounds
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.Nat.Bitwise

/-! Unique, strictly increasing accepted beacon slots extracted from the
archived consensus transition guards, plus the archived EL header guard.
Archived bodies and SHA256 (no download made): consensus-specs
`specs/phase0/beacon-chain.md` 95bbeca116dfc60ee75c1713d32409e29854de2340a71ee325ff7257f4412483
and `specs/gloas/beacon-chain.md` 10b7decc3dd86a1e4921f8cf49081c87dc528d61631bc83646cb5d6a062c65ce
(bodies in audit/receipts/direct-protocol-current-20260909.json, retrieved at
11f44343a8a282e7a9c2dee46590e273a8a0348a; byte-identical hashes are cited for
ad0058fd0d34c5dcf504fa51ea2f4f11077b9996 in
audit/receipts/direct-protocol-withdrawal-count-binding-20260910.md);
execution-specs `src/ethereum/forks/amsterdam/fork.py`
dd0d069cbd0ba3e60e3f927c0e2d41be40958c6415be039ee29d6074eb2950da at
0cc100eb190b64b23baba72dac0165652eaec252.

Exact guards modelled. phase0:473 `class Slot(Uint64)`. phase0:1762-1776
`state_transition` runs `process_slots(state, block.slot)` then
`process_block(state, block)`. phase0:1788-1796 `process_slots` asserts
`state.slot < slot` and raises `state.slot` to `slot` one step at a time;
phase0:1799-1809 `process_slot` writes only `state_roots`, the cached
`latest_block_header.state_root`, and `block_roots`. phase0:2281-2297
`process_block_header` asserts `block.slot == state.slot`,
`block.slot > state.latest_block_header.slot`, then caches a header whose slot
is `block.slot`. Gloas:1699-1716 `process_block` keeps `process_block_header`
and Gloas:1553-1568 `process_slot` adds only a payload-availability reset.
In both archived files `latest_block_header` is assigned only at genesis
(phase0:1706), in `process_slot` (state_root) and in `process_block_header`.
Amsterdam fork.py:431-486 `validate_header` rejects
`header.number != parent_header.number + 1`; `number` is unbounded `Uint`, and
no guard in that body relates `header.slot_number` to the parent (fork.py:323
only forwards it to the block environment). The Gloas envelope check
(fork-choice.md:685, SHA256
8a17705b70fe413ab474cb2c16a40257a33c253876fcb2cd61b9021da7837d16, archived in
audit/receipts/direct-cl-inheritance-sources-20260910.json)
`assert payload.slot_number == state.slot` is the typed EL/beacon slot
binding for a verified envelope, not for `validate_header`.

Derived here, with no Nodup or count premise: an accepted block sequence has
pairwise strictly increasing typed slots, hence Nodup slots and at most 2^64
accepted blocks. EL numbers are likewise pairwise distinct but carry no width.

Gloas redefines none of `state_transition`, `process_slots`,
`process_block_header` (no such definition in its body).

The `process_slots` while-loop is now derived as successive +1 ticks
(phase0:1790-1795), so `ProcessSlots.reached` is not an extra postulate: it
follows from the Uint64 successor staying below the asserted target. `process_epoch` itself (phase0:1815-1825, Fulu:390-407, Gloas:1578-1598)
contains only callee calls and no clock assignment. Clock preservation of
the function is derived from a finite `PreservingSeq` of per-callee frames
(`EpochPreservesClock`). Fulu introduces `process_proposer_lookahead`
(Fulu:481-489, SHA256
0e72312417d1df6f7aac14f731bb6bd71a3ef2715ced68e0b039d7622abc4490,
archived in audit/receipts/direct-cl-inheritance-sources-20260910.json);
Gloas:1596 calls that body and does not redefine it. The helper assigns
only `state.proposer_lookahead` (shift-out of the first epoch, fill of
the last), so clock preservation is derived from the function, not
named. The epoch-boundary guard phase0:1792-1794
(`(state.slot + 1) % SLOTS_PER_EPOCH == 0`, `SLOTS_PER_EPOCH = 32` at
phase0:614) decides whether that sequence runs; a non-boundary tick
skips it. `SlotTick` follows from `ProcessSlot` plus that optional
epoch plus the archived +1.

OPEN (not proved here): the inherited `process_slots`/`process_block_header`
bodies of the absent intermediate fork files; intermediate-fork variants of
inherited `process_epoch` helpers whose bodies are not in the archived
files — only their non-assignment of the two clock fields is named;
`get_beacon_proposer_indices` SHA256 *values* (Fulu:372-378) remain named;
`compute_shuffled_index` assert / identity init / 90-round Uint8 and
Uint32 preimages / flip involution / LE take-8 pivot / position-max
bit / swap-or-not / shared partner bit / one-round injectivity /
`List.Perm` against `range(n)` / `perm[index]` as the 90-round walk /
`source_by_bucket` cache / same-bucket bit offsets /
cached swap-or-not bit / per-round Uint8 preimage /
round-indexed `BucketCacheOk` / walk hashes each round /
pivot preimage omits Uint32 / pivot LE take-8 /
pivot `% index_count` (phase0:1206; named empty-count Python
`ZeroDivisionError`, Lean `n % 0 = n`)
(phase0:1197-1231) are extracted;
SHA256 pivot and swap-bit *values* stay uninterpreted; `compute_proposer_index`
nonempty assert, `MAX_RANDOM_BYTE` / `MAX_EFFECTIVE_BALANCE` accept
test, and `i // 32` random-byte preimage are extracted; the 32-seed
preimage list, little-endian `uint_to_bytes` / `ENDIANNESS`,
`compute_start_slot_at_epoch` wrap, and `get_seed` mix index
(phase0:1449-1451 / 1414) are extracted;
`get_randao_mix` is the stored VECTOR entry (phase0:1410-1414),
genesis splat (phase0:1707), `process_randao_mixes_reset` copy
(phase0:2237-2243), and `process_randao` xor-write at
`epoch % VECTOR` (phase0:1002-1006 / 2314-2315), then the
`process_epoch` reset copy (phase0:2273 then 1823; BLS verify and
SHA256 reveal *values* stay named);
`compute_epoch_at_slot` / `get_current_epoch` (phase0:1286-1290 /
1368-1372) and the inherited `process_eth1_data_reset` /
`process_slashings_reset` bodies (phase0:2199-2203 / 2228-2231,
called at Gloas:1584 / 1591) are extracted — they do not write the
clock and they accept no withdrawal payload;
`process_historical_roots_update` / `process_historical_summaries_update`
(phase0:2249-2256 / Capella:379-387, Gloas:1593) append only when
`next_epoch % (SLOTS_PER_HISTORICAL_ROOT // SLOTS_PER_EPOCH) == 0`
(`hash_tree_root` values stay named);
`process_participation_record_updates` / `process_participation_flag_updates`
(phase0:2262-2265 / Altair:824-828, Gloas:1594) always rotate and
clear current, not gated on that period;
`process_effective_balance_updates` hysteresis (phase0:2209-2222 /
Electra:1228-1244, Gloas:1590) and `process_sync_committee_updates`
(Altair:836-840, Gloas:1595; `get_next_sync_committee` named) are
extracted — they do not write the clock and they accept no payload;
Gloas:1604-1657 `process_pending_deposits` (16-deposit cap, finalized
slot, dropped Electra Eth1-bridge gate, postpone/churn leftover;
`apply_pending_deposit` named) and Gloas:1664-1676
`process_builder_pending_payments` (first-32 / 6/10 quorum / rotate)
are extracted — they accept no payload;
Electra:1198-1221 `process_pending_consolidations` (inherited; Gloas
does not redefine it) skips slashed sources, stops on
`withdrawable_epoch > next_epoch`, and transfers `min(balance, EB)`;
phase0:1306-1310 `compute_activation_exit_epoch` is `epoch+1+4`;
phase0:1077-1083 `is_active_validator` is `activation ≤ epoch < exit`;
`compute_exit_epoch_and_update_churn` (Electra:910-933 / Gloas:1478)
takes `max(earliest, activation_exit)`, resets leftover on a new
epoch, and ceils overflow with `(x-1)//per+1` (`get_exit_churn_limit`
/ `get_total_active_balance` named; empty `per` is Python
`ZeroDivisionError`);
Electra:1072-1095 `process_slashings` applies only at
`epoch + 8192//2` with Bellatrix multiplier 3 and the Electra
increment formula (phase0 formula is a mutant);
phase0:1886-1900 / Altair:728-750 `process_justification_and_finalization`
skips `epoch ≤ GENESIS_EPOCH+1`; weigh uses `target*3 ≥ total*2`;
Altair:752-775 inactivity / 778-792 rewards skip only genesis;
`is_in_inactivity_leak` is `finality_delay > 4`; HEAD miss has no
flag penalty; attesting balances / `get_block_root` stay named;
Gloas:1999 empty-parent items are counted in the withdrawal module
(exact 0 / parentFull-only bound from `AcceptedBlocks`, no consumer
`Nodup` premise);
SSZ Uint64 decode of an arbitrary stream to `Fin (2^64)` remains named;
canonical chain/fork-choice selection of the accepted sequence;
`validate_header` still does not bind `header.slot_number` (fork.py:323);
that independence is `ElHeader.slotNumber` /
`el_headers_slots_need_not_nodup` (duplicate `slot_number`s are admitted
when `number` increments). The envelope slot equality is derived only for a `VerifiedEnvelopeSlot`
witness of fork-choice.md:685, not for an arbitrary EL header. Engine
admission, parent-hash and store insertion of
`on_execution_payload_envelope` remain in the withdrawal module.
`compute_time_at_slot` (phase0:1278-1280, used at fork-choice.md:687) is
extracted here as Nat arithmetic. The source `Uint64(...)` wrap
(phase0:1275 overflow/underflow note) is `timeAtSlotWrap`. It is the
identity under `TimeFitsU64`, discharged on
`genesis_time ≤ MIN_GENESIS_TIME ∧ slot < 2^60`, still Fits at
`MIN_GENESIS_TIME` + slot `2^60` (so that bound is sufficient not
necessary), and is not the Nat sum at `MIN_GENESIS_TIME` + slot `2^61`
(`2^61 * 12 = 2^64 + 2^63`). -/
namespace Eip8282.Audit.Integrator.ProtocolSlotExtraction
open ResourceBounds (U64)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 400000

/-- The two typed slot fields read or written by the guards:
`state.slot` and `state.latest_block_header.slot` (phase0:473, 920). -/
structure Clock where
  slot : U64
  header : U64

/-- phase0:1788-1796. The loop assigns only `state.slot`; the cached header
slot is untouched by `process_slot` (phase0:1799-1809, Gloas:1553-1568). -/
structure ProcessSlots (pre : Clock) (target : U64) (post : Clock) : Prop where
  advancing : pre.slot < target
  reached : post.slot = target
  header : post.header = pre.header

/-- phase0:2281-2297: the two slot assertions and the header cache write. -/
structure ProcessBlockHeader (pre : Clock) (block : U64) (post : Clock) : Prop where
  sameSlot : block = pre.slot
  newer : pre.header < block
  cached : post.header = block
  slot : post.slot = pre.slot

/-- phase0:1762-1776 composed with Gloas:1699-1716; no other `process_block`
callee assigns `state.slot` or `latest_block_header` in the archived bodies. -/
def StateTransition (pre : Clock) (block : U64) (post : Clock) : Prop :=
  ∃ mid : Clock, ProcessSlots pre block mid ∧ ProcessBlockHeader mid block post

theorem transition_newer {pre post : Clock} {block : U64}
    (h : StateTransition pre block post) :
    pre.header < block ∧ pre.slot < block ∧ post.header = block ∧ post.slot = block := by
  obtain ⟨mid,slots,header⟩ := h
  refine ⟨?_,slots.advancing,header.cached,?_⟩
  · rw [←slots.header]; exact header.newer
  · rw [header.slot,slots.reached]

/-- Blocks accepted consecutively by `state_transition`, in acceptance order.
Empty slots are skipped inside `process_slots`; they contribute no block. -/
inductive Accepted : Clock → List U64 → Clock → Prop where
  | nil (c : Clock) : Accepted c [] c
  | cons {pre mid post : Clock} {block : U64} {rest : List U64}
      (step : StateTransition pre block mid) (tail : Accepted mid rest post) :
      Accepted pre (block::rest) post

theorem accepted_lower {pre post : Clock} {slots : List U64} (h : Accepted pre slots post) :
    ∀ s ∈ slots, pre.header < s := by
  induction h with
  | nil => intro s hs; cases hs
  | cons step tail ih =>
    intro s hs
    obtain ⟨hh,_,hc,_⟩ := transition_newer step
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact hh
    · exact hh.trans (hc ▸ ih s hs')

/-- Strictly increasing accepted slots, derived from the guards alone. -/
theorem accepted_pairwise {pre post : Clock} {slots : List U64} (h : Accepted pre slots post) :
    slots.Pairwise (· < ·) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | cons step tail ih =>
    obtain ⟨_,_,hc,_⟩ := transition_newer step
    exact List.Pairwise.cons (fun s hs => hc ▸ accepted_lower tail s hs) ih

theorem accepted_nodup {pre post : Clock} {slots : List U64} (h : Accepted pre slots post) :
    slots.Nodup :=
  (accepted_pairwise h).imp (fun hlt => Fin.ne_of_lt hlt)

/-- At most 2^64 accepted blocks: the cardinality of typed slots, no premise. -/
theorem accepted_count {pre post : Clock} {slots : List U64} (h : Accepted pre slots post) :
    slots.length ≤ 2^64 := by
  have hs := (accepted_nodup h).length_le_card
  simpa only [Fintype.card_fin] using hs

/-- phase0:1795 `state.slot = state.slot + 1`. The while-guard
`state.slot < slot` (phase0:1790) gives the successor room inside `U64`. -/
theorem succ_lt {a t : U64} (h : a < t) : a.val + 1 < 2^64 :=
  Nat.lt_of_le_of_lt (Nat.succ_le_of_lt h) t.isLt

def succOf {a t : U64} (h : a < t) : U64 := ⟨a.val + 1, succ_lt h⟩

theorem succOf_le {a t : U64} (h : a < t) : succOf h ≤ t :=
  Nat.succ_le_of_lt h

theorem clock_ext {c d : Clock} (hs : c.slot = d.slot) (hh : c.header = d.header) :
    c = d := by
  cases c; cases d; simp_all

/-- phase0:1799-1809 and Gloas:1553-1568. `process_slot` writes `state_roots`,
the cached `latest_block_header.state_root`, `block_roots`, and (Gloas) the
payload-availability bit. Neither body assigns `state.slot` or
`latest_block_header.slot`. -/
structure ProcessSlot (pre post : Clock) : Prop where
  slot : post.slot = pre.slot
  header : post.header = pre.header

/-- Per-callee clock frame: the helper does not write `state.slot` or
`latest_block_header.slot`. Archived bodies that contain no such
assignment: every phase0:1816-1825 callee (1886-2264), Gloas
`process_pending_deposits` 1604-1657 / `process_builder_pending_payments`
1664-1676 / `process_ptc_window` 1682-1692, plus the inherited Altair /
Capella / Electra helpers present in
`direct-cl-inheritance-sources-20260910.json`. `process_proposer_lookahead`
is the archived Fulu:481-489 body (called at Gloas:1596 / Fulu:406);
its clock frame is derived below. Absent intermediate-fork variants of
other helpers remain named. -/
structure EpochPreservesClock (pre post : Clock) : Prop where
  slot : post.slot = pre.slot
  header : post.header = pre.header

/-- Finite composition of clock-preserving callees. `process_epoch` is
exactly such a sequence: phase0:1815-1825 has ten calls, Gloas:1578-1598
has seventeen, and neither body has any other statement. -/
inductive PreservingSeq : Nat → Clock → Clock → Prop where
  | nil (c : Clock) : PreservingSeq 0 c c
  | cons {n : Nat} {pre mid post : Clock}
      (one : EpochPreservesClock pre mid)
      (rest : PreservingSeq n mid post) :
      PreservingSeq (n + 1) pre post

theorem preservingSeq_slot {n : Nat} {pre post : Clock}
    (h : PreservingSeq n pre post) : post.slot = pre.slot := by
  induction h with
  | nil => rfl
  | cons one rest ih => rw [ih, one.slot]

theorem preservingSeq_header {n : Nat} {pre post : Clock}
    (h : PreservingSeq n pre post) : post.header = pre.header := by
  induction h with
  | nil => rfl
  | cons one rest ih => rw [ih, one.header]

theorem preservingSeq_clock {n : Nat} {pre post : Clock}
    (h : PreservingSeq n pre post) : EpochPreservesClock pre post where
  slot := preservingSeq_slot h
  header := preservingSeq_header h

/-- phase0:1815-1825: ten callee calls, no clock assignment. -/
def Phase0ProcessEpoch (pre post : Clock) : Prop := PreservingSeq 10 pre post

/-- Gloas:1578-1598: seventeen callee calls, no clock assignment. -/
def GloasProcessEpoch (pre post : Clock) : Prop := PreservingSeq 17 pre post

/-- Fulu:390-407: fifteen callee calls, last is `process_proposer_lookahead`
(Fulu:406). No clock assignment. Gloas adds `process_builder_pending_payments`
(1589) and `process_ptc_window` (1598) on top of this sequence. -/
def FuluProcessEpoch (pre post : Clock) : Prop := PreservingSeq 15 pre post

theorem phase0_process_epoch_preserves {pre post : Clock}
    (h : Phase0ProcessEpoch pre post) : EpochPreservesClock pre post :=
  preservingSeq_clock h

theorem gloas_process_epoch_preserves {pre post : Clock}
    (h : GloasProcessEpoch pre post) : EpochPreservesClock pre post :=
  preservingSeq_clock h

theorem fulu_process_epoch_preserves {pre post : Clock}
    (h : FuluProcessEpoch pre post) : EpochPreservesClock pre post :=
  preservingSeq_clock h

theorem phase0_process_epoch_same_slot {pre post : Clock}
    (h : Phase0ProcessEpoch pre post) : post.slot = pre.slot :=
  (phase0_process_epoch_preserves h).slot

theorem gloas_process_epoch_same_slot {pre post : Clock}
    (h : GloasProcessEpoch pre post) : post.slot = pre.slot :=
  (gloas_process_epoch_preserves h).slot

theorem fulu_process_epoch_same_slot {pre post : Clock}
    (h : FuluProcessEpoch pre post) : post.slot = pre.slot :=
  (fulu_process_epoch_preserves h).slot

/-- phase0:614 `SLOTS_PER_EPOCH = Slot(2**5)` (= 32). Gloas does not
redefine it. Used at phase0:1793. -/
def SLOTS_PER_EPOCH : Nat := 32

/-- phase0:615 `MIN_SEED_LOOKAHEAD = Epoch(2**0)` (= 1). Fulu:71 uses it
for `ProposerLookahead.LENGTH`. -/
def MIN_SEED_LOOKAHEAD : Nat := 1

/-- Fulu:71 / 230: `(MIN_SEED_LOOKAHEAD + 1) * SLOTS_PER_EPOCH` = 64. -/
def proposerLookaheadLength : Nat := (MIN_SEED_LOOKAHEAD + 1) * SLOTS_PER_EPOCH

theorem proposerLookaheadLength_eq : proposerLookaheadLength = 64 := by
  unfold proposerLookaheadLength MIN_SEED_LOOKAHEAD SLOTS_PER_EPOCH
  decide

/-- Fulu:54-59 `class ProposerIndices` with `LENGTH = SLOTS_PER_EPOCH`. -/
structure ProposerIndices where
  data : List U64
  length_ok : data.length = SLOTS_PER_EPOCH

/-- Fulu:65-71 `class ProposerLookahead` with
`LENGTH = Uint64(MIN_SEED_LOOKAHEAD + 1) * Uint64(SLOTS_PER_EPOCH)`. -/
structure ProposerLookahead where
  data : List U64
  length_ok : data.length = proposerLookaheadLength

/-- Fulu:481-489 assignment: drop the first epoch, append the new
`ProposerIndices` fill. `get_beacon_proposer_indices` (Fulu:372-378)
supplies `filled` via `compute_proposer_indices` (Fulu:343-351): 32
preimages `seed ++ uint_to_bytes(start_slot + i)` then uninterpreted
SHA256 / `compute_proposer_index`. The preimage list and LE encode are
extracted; hash values are not. -/
def shiftAndFill (pre : ProposerLookahead) (filled : ProposerIndices) : List U64 :=
  pre.data.drop SLOTS_PER_EPOCH ++ filled.data

theorem shiftAndFill_length (pre : ProposerLookahead) (filled : ProposerIndices) :
    (shiftAndFill pre filled).length = proposerLookaheadLength := by
  simp only [shiftAndFill, List.length_append, List.length_drop, pre.length_ok,
    filled.length_ok]
  unfold proposerLookaheadLength MIN_SEED_LOOKAHEAD SLOTS_PER_EPOCH
  decide

theorem shiftAndFill_prefix (pre : ProposerLookahead) (filled : ProposerIndices) :
    (shiftAndFill pre filled).take SLOTS_PER_EPOCH =
      pre.data.drop SLOTS_PER_EPOCH := by
  have hdrop : (pre.data.drop SLOTS_PER_EPOCH).length = SLOTS_PER_EPOCH := by
    rw [List.length_drop, pre.length_ok]
    unfold proposerLookaheadLength MIN_SEED_LOOKAHEAD SLOTS_PER_EPOCH
    decide
  simp only [shiftAndFill]
  rw [List.take_left' hdrop]

theorem shiftAndFill_suffix (pre : ProposerLookahead) (filled : ProposerIndices) :
    (shiftAndFill pre filled).drop SLOTS_PER_EPOCH = filled.data := by
  have hdrop : (pre.data.drop SLOTS_PER_EPOCH).length = SLOTS_PER_EPOCH := by
    rw [List.length_drop, pre.length_ok]
    unfold proposerLookaheadLength MIN_SEED_LOOKAHEAD SLOTS_PER_EPOCH
    decide
  simp only [shiftAndFill]
  rw [List.drop_left' hdrop]

/-- Fulu:481-489 reconstructed: only `proposer_lookahead` is written. -/
structure LookaheadFrame where
  clock : Clock
  lookahead : ProposerLookahead

def applyProposerLookahead (s : LookaheadFrame) (filled : ProposerIndices) :
    LookaheadFrame where
  clock := s.clock
  lookahead := ⟨shiftAndFill s.lookahead filled, shiftAndFill_length s.lookahead filled⟩

/-- Clock fields are copied; `state.slot` and `latest_block_header.slot`
are not among the two slice assignments at Fulu:484/489. -/
theorem applyProposerLookahead_clock (s : LookaheadFrame) (filled : ProposerIndices) :
    (applyProposerLookahead s filled).clock = s.clock :=
  rfl

theorem applyProposerLookahead_preserves (s : LookaheadFrame) (filled : ProposerIndices) :
    EpochPreservesClock s.clock (applyProposerLookahead s filled).clock :=
  ⟨rfl, rfl⟩

/-- Fulu:366 `return state.proposer_lookahead[state.slot % SLOTS_PER_EPOCH]`.
The Vector LENGTH (64) makes the index total. -/
def proposerAt (lookahead : ProposerLookahead) (slot : U64) : U64 :=
  lookahead.data[slot.val % SLOTS_PER_EPOCH]'(by
    rw [lookahead.length_ok]
    have hmod : slot.val % SLOTS_PER_EPOCH < SLOTS_PER_EPOCH :=
      Nat.mod_lt slot.val (by decide : 0 < SLOTS_PER_EPOCH)
    unfold proposerLookaheadLength MIN_SEED_LOOKAHEAD SLOTS_PER_EPOCH
    exact Nat.lt_trans hmod (by decide : 32 < 64))

/-- phase0:1793 `(state.slot + 1) % SLOTS_PER_EPOCH == 0`. -/
def epochBoundary (slot : U64) : Bool :=
  decide ((slot.val + 1) % SLOTS_PER_EPOCH = 0)

theorem epochBoundary_iff (slot : U64) :
    epochBoundary slot = true ↔ (slot.val + 1) % SLOTS_PER_EPOCH = 0 := by
  simp [epochBoundary]

/-- phase0:1792-1794: `process_epoch` runs only on an epoch boundary;
otherwise the clock is unchanged by this step. -/
inductive OptionalEpoch (slot : U64) : Clock → Clock → Prop where
  | skip {c : Clock} (h : (slot.val + 1) % SLOTS_PER_EPOCH ≠ 0) :
      OptionalEpoch slot c c
  | run {pre post : Clock} (h : (slot.val + 1) % SLOTS_PER_EPOCH = 0)
      (ep : GloasProcessEpoch pre post) :
      OptionalEpoch slot pre post

theorem optionalEpoch_preserves {slot : U64} {pre post : Clock}
    (h : OptionalEpoch slot pre post) : EpochPreservesClock pre post := by
  cases h with
  | skip _ => exact ⟨rfl, rfl⟩
  | run _ ep => exact gloas_process_epoch_preserves ep

theorem optionalEpoch_skip_same {slot : U64} {c d : Clock}
    (h : OptionalEpoch slot c d)
    (hne : (slot.val + 1) % SLOTS_PER_EPOCH ≠ 0) : c = d := by
  cases h with
  | skip _ => rfl
  | run hb _ => exact (hne hb).elim

/-- One while-body of `process_slots` (phase0:1791-1795): `process_slot`,
optional `process_epoch`, then `state.slot := state.slot + 1`. -/
structure SlotTick (pre post : Clock) : Prop where
  header : post.header = pre.header
  increased : post.slot.val = pre.slot.val + 1

theorem tick_of_parts {pre mid mid' post : Clock}
    (hs : ProcessSlot pre mid) (he : EpochPreservesClock mid mid')
    (hinc : post.slot.val = mid'.slot.val + 1) (hh : post.header = mid'.header) :
    SlotTick pre post where
  header := by rw [hh, he.header, hs.header]
  increased := by rw [hinc, he.slot, hs.slot]

/-- The archived while-body: `process_slot`, optional Gloas `process_epoch`,
then the +1. `reached` is not assumed. -/
def SlotsWhileBody (pre post : Clock) (target : U64) : Prop :=
  pre.slot < target ∧
    ∃ mid mid' : Clock,
      ProcessSlot pre mid ∧ OptionalEpoch pre.slot mid mid' ∧
        post.slot.val = mid'.slot.val + 1 ∧ post.header = mid'.header

theorem slotsWhileBody_tick {pre post : Clock} {target : U64}
    (h : SlotsWhileBody pre post target) : SlotTick pre post := by
  obtain ⟨_, mid, mid', hs, he, hinc, hh⟩ := h
  exact tick_of_parts hs (optionalEpoch_preserves he) hinc hh

theorem slotsWhileBody_live {pre post : Clock} {target : U64}
    (h : SlotsWhileBody pre post target) : pre.slot < target :=
  h.1

/-- The `while state.slot < slot` loop. The `done` constructor is the exit
when the running slot equals the asserted target, matching the source after
the last increment (phase0:1790, 1795). -/
inductive SlotsWhile (target : U64) : Clock → Clock → Prop where
  | done {c : Clock} (eq : c.slot = target) : SlotsWhile target c c
  | step {pre mid post : Clock}
      (live : pre.slot < target) (tick : SlotTick pre mid)
      (rest : SlotsWhile target mid post) :
      SlotsWhile target pre post

theorem slotsWhile_header {target : U64} {pre post : Clock}
    (h : SlotsWhile target pre post) : post.header = pre.header := by
  induction h with
  | done eq => rfl
  | step live tick rest ih => rw [ih, tick.header]

theorem slotsWhile_slot {target : U64} {pre post : Clock}
    (h : SlotsWhile target pre post) : post.slot = target := by
  induction h with
  | done eq => exact eq
  | step live tick rest ih => exact ih

/-- The archived +1 walk from `start` to `target` at a fixed header slot.
This is the executable loop, not an assumed `post.slot = target`. -/
theorem slotsWhile_fill (header : U64) (start target : U64) (hle : start ≤ target) :
    SlotsWhile target ⟨start, header⟩ ⟨target, header⟩ := by
  generalize hn : target.val - start.val = n
  induction n generalizing start with
  | zero =>
    have hleN : start.val ≤ target.val := hle
    have hge : target.val ≤ start.val := Nat.sub_eq_zero_iff_le.mp hn
    have heq : start = target := Fin.eq_of_val_eq (Nat.le_antisymm hleN hge)
    subst heq
    exact .done rfl
  | succ n ih =>
    have hleN : start.val ≤ target.val := hle
    have hltN : start.val < target.val :=
      Nat.lt_of_le_of_ne hleN (fun heq => by
        rw [heq, Nat.sub_self] at hn
        cases hn)
    have hlt : start < target := hltN
    let mid : Clock := ⟨succOf hlt, header⟩
    have htick : SlotTick ⟨start, header⟩ mid := ⟨rfl, rfl⟩
    have hmid : mid.slot ≤ target := succOf_le hlt
    have hdiff : target.val - mid.slot.val = n := by
      change target.val - (start.val + 1) = n
      rw [Nat.sub_add_eq, hn, Nat.add_sub_cancel]
    exact .step hlt htick (ih mid.slot hmid hdiff)

/-- `process_slots` reconstructed from the while-loop. `reached` is derived. -/
def ProcessSlotsByLoop (pre : Clock) (target : U64) (post : Clock) : Prop :=
  pre.slot < target ∧ SlotsWhile target pre post

theorem processSlots_of_loop {pre post : Clock} {target : U64}
    (h : ProcessSlotsByLoop pre target post) : ProcessSlots pre target post where
  advancing := h.1
  reached := slotsWhile_slot h.2
  header := slotsWhile_header h.2

theorem loop_of_processSlots {pre post : Clock} {target : U64}
    (h : ProcessSlots pre target post) : ProcessSlotsByLoop pre target post := by
  refine ⟨h.advancing, ?_⟩
  have hle : pre.slot ≤ target := le_of_lt h.advancing
  have hw := slotsWhile_fill pre.header pre.slot target hle
  have hpost : post = ⟨target, pre.header⟩ :=
    clock_ext (by rw [h.reached]) (by rw [h.header])
  simpa [hpost] using hw

/-- After a nonempty accepted sequence the cached header and state slot are
the last accepted block (phase0:2291-2292 composed with 1795). -/
theorem accepted_last {pre post : Clock} {slots : List U64} {last : U64}
    (h : Accepted pre (slots ++ [last]) post) :
    post.header = last ∧ post.slot = last := by
  induction slots generalizing pre with
  | nil =>
    cases h with
    | cons step tail =>
      cases tail
      exact ⟨(transition_newer step).2.2.1, (transition_newer step).2.2.2⟩
  | cons _ rest ih =>
    cases h with
    | cons _step tail => exact ih tail

theorem accepted_nil_clock {c d : Clock} (h : Accepted c [] d) : c = d := by
  cases h; rfl

/-- Two equal accepted slots are impossible: uniqueness is derived, not assumed. -/
theorem accepted_ne {pre post : Clock} {a b : U64}
    (h : Accepted pre [a, b] post) : a ≠ b := by
  have nd := accepted_nodup h
  simp [List.nodup_cons] at nd
  exact nd

/-- The projection form consumed by every current
`(blocks.map (fun b => b.slot)).Nodup` hypothesis in the history interface. -/
theorem projected_nodup {α : Type} (slot : α → U64) {pre post : Clock} (blocks : List α)
    (h : Accepted pre (blocks.map slot) post) : (blocks.map slot).Nodup :=
  accepted_nodup h

theorem projected_count {α : Type} (slot : α → U64) {pre post : Clock} (blocks : List α)
    (h : Accepted pre (blocks.map slot) post) : blocks.length ≤ 2^64 := by
  have hc := accepted_count h
  simpa only [List.length_map] using hc

/-- Amsterdam fork.py:431-486 `validate_header` for consecutively appended EL
blocks (fork.py:235-270 `state_transition` appends after `execute_block`, whose
first guard is `validate_header(parent_header, block.header)`). Numbers are
`Uint`, so this yields distinctness only, never a width bound. -/
inductive ElAppended : Nat → List Nat → Nat → Prop where
  | nil (parent : Nat) : ElAppended parent [] parent
  | cons {parent last : Nat} {rest : List Nat}
      (tail : ElAppended (parent+1) rest last) : ElAppended parent ((parent+1)::rest) last

theorem el_lower {parent last : Nat} {numbers : List Nat} (h : ElAppended parent numbers last) :
    ∀ n ∈ numbers, parent < n := by
  induction h with
  | nil => intro n hn; cases hn
  | cons tail ih =>
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn'
    · exact Nat.lt_succ_self _
    · exact (Nat.lt_succ_self _).trans (ih n hn')

theorem el_pairwise {parent last : Nat} {numbers : List Nat} (h : ElAppended parent numbers last) :
    numbers.Pairwise (· < ·) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | cons tail ih => exact List.Pairwise.cons (fun n hn => el_lower tail n hn) ih

theorem el_nodup {parent last : Nat} {numbers : List Nat} (h : ElAppended parent numbers last) :
    numbers.Nodup :=
  (el_pairwise h).imp (fun hlt => Nat.ne_of_lt hlt)

theorem el_not_parent {parent last : Nat} {numbers : List Nat}
    (h : ElAppended parent numbers last) : parent ∉ numbers :=
  fun hin => (Nat.lt_irrefl parent) (el_lower h parent hin)

/-- fork.py:323 `slot_number` on the header, forwarded to `block_env`.
`validate_header` (431-486) never reads this field; the only number
relation is fork.py:472 `header.number != parent_header.number + 1`. -/
structure ElHeader where
  number : Nat
  slotNumber : Nat

def elNumbers (hs : List ElHeader) : List Nat :=
  hs.map (·.number)

def elSlotNumbers (hs : List ElHeader) : List Nat :=
  hs.map (·.slotNumber)

/-- `validate_header` uniqueness is the `ElAppended` walk on `number`. -/
def ElHeadersAppended (parent : Nat) (hs : List ElHeader) (last : Nat) : Prop :=
  ElAppended parent (elNumbers hs) last

theorem el_headers_appended_iff {parent last : Nat} {hs : List ElHeader} :
    ElHeadersAppended parent hs last ↔
      ElAppended parent (elNumbers hs) last :=
  Iff.rfl

theorem el_headers_number_nodup {parent last : Nat} {hs : List ElHeader}
    (h : ElHeadersAppended parent hs last) :
    (elNumbers hs).Nodup :=
  el_nodup h

/-- Relabeling `slot_number` does not change `validate_header` admission. -/
theorem el_headers_relabel_slot {parent last : Nat} {hs hs' : List ElHeader}
    (hn : elNumbers hs = elNumbers hs')
    (h : ElHeadersAppended parent hs last) :
    ElHeadersAppended parent hs' last := by
  simpa [ElHeadersAppended, hn] using h

/-- Two successive numbers with a repeated `slot_number`. fork.py:472
admits this pair; fork-choice.md:685 would not if these were envelope
slots against distinct beacon slots. -/
def sampleElDupSlots : List ElHeader :=
  [{ number := 1, slotNumber := 7 }, { number := 2, slotNumber := 7 }]

def sampleElRelabeled : List ElHeader :=
  [{ number := 1, slotNumber := 99 }, { number := 2, slotNumber := 1 }]

theorem sampleEl_appended :
    ElHeadersAppended 0 sampleElDupSlots 2 := by
  unfold ElHeadersAppended sampleElDupSlots elNumbers
  exact ElAppended.cons (ElAppended.cons (ElAppended.nil 2))

theorem sampleEl_relabeled_appended :
    ElHeadersAppended 0 sampleElRelabeled 2 := by
  unfold ElHeadersAppended sampleElRelabeled elNumbers
  exact ElAppended.cons (ElAppended.cons (ElAppended.nil 2))

theorem sampleEl_same_numbers :
    elNumbers sampleElDupSlots = elNumbers sampleElRelabeled := by
  simp [elNumbers, sampleElDupSlots, sampleElRelabeled]

theorem sampleEl_different_slots :
    elSlotNumbers sampleElDupSlots ≠ elSlotNumbers sampleElRelabeled := by
  simp [elSlotNumbers, sampleElDupSlots, sampleElRelabeled]

/-- fork.py:323/472. Duplicate `slot_number`s are not rejected. -/
theorem el_headers_slots_need_not_nodup :
    ∃ parent last : Nat, ∃ hs : List ElHeader,
      ElHeadersAppended parent hs last ∧
      ¬ (elSlotNumbers hs).Nodup :=
  ⟨0, 2, sampleElDupSlots, sampleEl_appended, by
    unfold sampleElDupSlots elSlotNumbers
    exact (by decide : ¬ ([7, 7] : List Nat).Nodup)⟩

/-- A mutant that treats `validate_header` as binding `slot_number`
uniqueness is false. -/
theorem validate_header_slots_not_nodup :
    ¬ ∀ (hs : List ElHeader) (parent last : Nat),
      ElHeadersAppended parent hs last → (elSlotNumbers hs).Nodup := by
  intro h
  obtain ⟨parent, last, hs, happ, hdup⟩ := el_headers_slots_need_not_nodup
  exact hdup (h hs parent last happ)

/-- Gloas fork-choice.md:685 `assert payload.slot_number == state.slot`
inside `verify_execution_payload_envelope` (659-699), called from
`on_execution_payload_envelope` (1096-1116). This is not the Amsterdam
`validate_header` guard. -/
structure VerifiedEnvelopeSlot (beacon el : U64) : Prop where
  same : el = beacon

theorem envelope_slot {beacon el : U64} (h : VerifiedEnvelopeSlot beacon el) :
    el = beacon := h.same

theorem envelope_slots {α : Type} (beacon el : α → U64) {pre post : Clock}
    (envelopes : List α)
    (accepted : Accepted pre (envelopes.map beacon) post)
    (each : ∀ e ∈ envelopes, VerifiedEnvelopeSlot (beacon e) (el e)) :
    (envelopes.map el).Nodup := by
  have heq : ∀ es : List α,
      (∀ e ∈ es, VerifiedEnvelopeSlot (beacon e) (el e)) →
        es.map el = es.map beacon := by
    intro es
    induction es with
    | nil => intro _; rfl
    | cons e rest ih =>
      intro hall
      have hs := (hall e List.mem_cons_self).same
      have ht : ∀ x ∈ rest, VerifiedEnvelopeSlot (beacon x) (el x) :=
        fun x hx => hall x (List.mem_cons_of_mem e hx)
      simp only [List.map_cons, hs, ih ht]
  rw [heq envelopes each]
  exact accepted_nodup accepted

#print axioms accepted_pairwise
#print axioms accepted_nodup
#print axioms accepted_count
#print axioms projected_nodup
#print axioms el_nodup
#print axioms processSlots_of_loop
#print axioms loop_of_processSlots
#print axioms slotsWhile_fill
#print axioms preservingSeq_clock
#print axioms phase0_process_epoch_preserves
#print axioms gloas_process_epoch_preserves
#print axioms phase0_process_epoch_same_slot
#print axioms gloas_process_epoch_same_slot
#print axioms epochBoundary_iff
#print axioms optionalEpoch_preserves
#print axioms optionalEpoch_skip_same
#print axioms slotsWhileBody_tick
#print axioms slotsWhileBody_live
#print axioms accepted_last
#print axioms accepted_ne
#print axioms el_not_parent
#print axioms el_headers_appended_iff
#print axioms el_headers_number_nodup
#print axioms el_headers_relabel_slot
#print axioms sampleEl_appended
#print axioms sampleEl_relabeled_appended
#print axioms sampleEl_same_numbers
#print axioms sampleEl_different_slots
#print axioms el_headers_slots_need_not_nodup
#print axioms validate_header_slots_not_nodup
#print axioms envelope_slot
#print axioms envelope_slots

/-- phase0:542 `GENESIS_SLOT = Slot(0)`. -/
def GENESIS_SLOT : U64 := ⟨0, by decide⟩

/-- phase0:678 `MIN_GENESIS_TIME = Uint64(1606824000)` (Dec 1, 2020, 12pm UTC). -/
def MIN_GENESIS_TIME : Nat := 1606824000

/-- phase0:686 `SLOT_DURATION_MS = Uint64(12000)`. -/
def SLOT_DURATION_MS : Nat := 12000

/-- phase0:1278-1280 before the `Uint64` constructor. `GENESIS_SLOT` is 0,
so Nat subtraction does not saturate. -/
def timeAtSlotNat (genesisTime slot : U64) : Nat :=
  genesisTime.val + (slot.val - GENESIS_SLOT.val) * SLOT_DURATION_MS / 1000

theorem timeAtSlotNat_spec (genesisTime slot : U64) :
    timeAtSlotNat genesisTime slot = genesisTime.val + slot.val * 12 := by
  unfold timeAtSlotNat GENESIS_SLOT SLOT_DURATION_MS
  change genesisTime.val + (slot.val - 0) * 12000 / 1000 =
    genesisTime.val + slot.val * 12
  rw [Nat.sub_zero]
  have hmul : slot.val * 12000 = slot.val * 12 * 1000 := by
    omega
  rw [hmul, Nat.mul_div_cancel]
  exact Nat.succ_pos 999

/-- Named adapter for the source `Uint64(...)` wrap (phase0:1275, 1280). -/
structure TimeFitsU64 (genesisTime slot : U64) : Prop where
  fits : timeAtSlotNat genesisTime slot < 2^64

def timeAtSlot (genesisTime slot : U64) (h : TimeFitsU64 genesisTime slot) : U64 :=
  ⟨timeAtSlotNat genesisTime slot, h.fits⟩

theorem timeAtSlot_spec {genesisTime slot : U64} (h : TimeFitsU64 genesisTime slot) :
    (timeAtSlot genesisTime slot h).val = genesisTime.val + slot.val * 12 :=
  timeAtSlotNat_spec genesisTime slot

/-- fork-choice.md:687 `payload.timestamp == compute_time_at_slot(state, state.slot)`. -/
structure EnvelopeTimestamp (genesisTime beacon payloadTime : U64) : Prop where
  fits : TimeFitsU64 genesisTime beacon
  same : payloadTime = timeAtSlot genesisTime beacon fits

theorem envelope_timestamp {genesisTime beacon payloadTime : U64}
    (h : EnvelopeTimestamp genesisTime beacon payloadTime) :
    payloadTime.val = genesisTime.val + beacon.val * 12 := by
  rw [h.same, timeAtSlot_spec]

/-- phase0:1275/1280: the `Uint64(...)` wrap is exactly the Nat bound. -/
theorem timeFits_iff (genesisTime slot : U64) :
    TimeFitsU64 genesisTime slot ↔ genesisTime.val + slot.val * 12 < 2 ^ 64 := by
  constructor
  · intro h
    simpa [timeAtSlotNat_spec] using h.fits
  · intro h
    exact ⟨by simpa [timeAtSlotNat_spec] using h⟩

/-- Concrete discharge of the wrap: any genesis at most the archived
mainnet `MIN_GENESIS_TIME` and any slot below `2^60` (far above any
scheduled horizon) fits in `Uint64`. `2^60 * 12 + 1606824000 < 2^64`. -/
theorem timeFits_of_bounded {genesisTime slot : U64}
    (hgen : genesisTime.val ≤ MIN_GENESIS_TIME)
    (hslot : slot.val < 2 ^ 60) : TimeFitsU64 genesisTime slot := by
  refine ⟨?_⟩
  rw [timeAtSlotNat_spec]
  have hmul : slot.val * 12 < 2 ^ 60 * 12 :=
    Nat.mul_lt_mul_of_pos_right hslot (by decide)
  have hle : genesisTime.val + slot.val * 12 ≤ MIN_GENESIS_TIME + slot.val * 12 :=
    Nat.add_le_add_right hgen _
  have hlt : MIN_GENESIS_TIME + slot.val * 12 < MIN_GENESIS_TIME + 2 ^ 60 * 12 :=
    Nat.add_lt_add_left hmul _
  have hbound : MIN_GENESIS_TIME + 2 ^ 60 * 12 < 2 ^ 64 := by decide
  exact Nat.lt_of_le_of_lt hle (hlt.trans hbound)

/-- phase0:678 + slot 0: `compute_time_at_slot` is genesis time itself. -/
theorem timeFits_min_genesis_zero :
    TimeFitsU64 ⟨MIN_GENESIS_TIME, by decide⟩ ⟨0, by decide⟩ :=
  timeFits_of_bounded (le_rfl) (by decide)

/-- phase0:1275: the maximal `Slot` overflows the `Uint64` wrap when
genesis is 0, because `(2^64-1)*12 ≥ 2^64`. -/
theorem timeFits_rejects_max_slot :
    ¬ TimeFitsU64 ⟨0, by decide⟩ ⟨2 ^ 64 - 1, by decide⟩ := by
  intro h
  have hf := h.fits
  rw [timeAtSlotNat_spec] at hf
  exact (by decide : ¬ (0 + (2 ^ 64 - 1) * 12 < 2 ^ 64)) hf

/-- phase0:473 `Uint64` modulus of `compute_time_at_slot`. -/
def TIME_MOD : Nat := 2 ^ 64

theorem TIME_MOD_pos : 0 < TIME_MOD := by
  decide

theorem TIME_MOD_eq : TIME_MOD = 2 ^ 64 :=
  rfl

/-- phase0:1275. Python `Uint64(...)` wrap of the Nat sum. -/
def timeAtSlotWrap (genesisTime slot : U64) : Nat :=
  timeAtSlotNat genesisTime slot % TIME_MOD

theorem timeAtSlotWrap_lt (genesisTime slot : U64) :
    timeAtSlotWrap genesisTime slot < TIME_MOD :=
  Nat.mod_lt _ TIME_MOD_pos

/-- Under `TimeFitsU64` the wrap is the identity. Lean `timeAtSlot`
agrees with Python `Uint64` on that domain. -/
theorem timeAtSlotWrap_eq_of_fits {genesisTime slot : U64}
    (h : TimeFitsU64 genesisTime slot) :
    timeAtSlotWrap genesisTime slot = timeAtSlotNat genesisTime slot :=
  Nat.mod_eq_of_lt (by simpa [TIME_MOD] using h.fits)

theorem timeAtSlot_eq_wrap {genesisTime slot : U64}
    (h : TimeFitsU64 genesisTime slot) :
    (timeAtSlot genesisTime slot h).val = timeAtSlotWrap genesisTime slot := by
  rw [timeAtSlotWrap_eq_of_fits h]
  rfl

/-- phase0:678 + slot `2^60`: still Fits, but `slot < 2^60` fails.
`timeFits_of_bounded` is sufficient, not necessary. -/
theorem timeFits_min_genesis_two_pow_60 :
    TimeFitsU64 ⟨MIN_GENESIS_TIME, by decide⟩ ⟨2 ^ 60, by decide⟩ := by
  refine ⟨?_⟩
  rw [timeAtSlotNat_spec]
  exact (by decide : MIN_GENESIS_TIME + 2 ^ 60 * 12 < 2 ^ 64)

/-- genesis `MIN_GENESIS_TIME + 1` at slot 0 Fits, but
`genesis ≤ MIN_GENESIS_TIME` fails. -/
theorem timeFits_above_min_genesis_zero :
    TimeFitsU64 ⟨MIN_GENESIS_TIME + 1, by decide⟩ ⟨0, by decide⟩ := by
  refine ⟨?_⟩
  rw [timeAtSlotNat_spec]
  exact (by decide : MIN_GENESIS_TIME + 1 + 0 * 12 < 2 ^ 64)

/-- The discharged bound is not an `iff`. Witness: mainnet genesis at
slot `2^60`. -/
theorem timeFits_of_bounded_not_necessary :
    ¬ ∀ genesisTime slot : U64,
      TimeFitsU64 genesisTime slot →
        genesisTime.val ≤ MIN_GENESIS_TIME ∧ slot.val < 2 ^ 60 := by
  intro h
  have hf := h ⟨MIN_GENESIS_TIME, by decide⟩ ⟨2 ^ 60, by decide⟩
    timeFits_min_genesis_two_pow_60
  exact (by decide : ¬ ((2 ^ 60 : Nat) < 2 ^ 60)) hf.2

/-- phase0:1275. `2^61 * 12 = 3 * 2^63 = 2^64 + 2^63`. -/
theorem two_pow_61_mul_12 : 2 ^ 61 * 12 = 2 ^ 64 + 2 ^ 63 := by
  decide

/-- phase0:1275. Slot `2^61` at mainnet genesis overflows `Uint64`. -/
theorem timeFits_rejects_min_genesis_two_pow_61 :
    ¬ TimeFitsU64 ⟨MIN_GENESIS_TIME, by decide⟩ ⟨2 ^ 61, by decide⟩ := by
  intro h
  have hf := h.fits
  rw [timeAtSlotNat_spec] at hf
  exact (by decide : ¬ (MIN_GENESIS_TIME + 2 ^ 61 * 12 < 2 ^ 64)) hf

theorem timeAtSlotNat_min_genesis_two_pow_61 :
    timeAtSlotNat ⟨MIN_GENESIS_TIME, by decide⟩ ⟨2 ^ 61, by decide⟩ =
      MIN_GENESIS_TIME + 2 ^ 64 + 2 ^ 63 := by
  rw [timeAtSlotNat_spec, two_pow_61_mul_12]
  ac_rfl

/-- The wrap of that overflow is `MIN_GENESIS_TIME + 2^63`, not the Nat
sum. -/
theorem timeAtSlotWrap_min_genesis_two_pow_61 :
    timeAtSlotWrap ⟨MIN_GENESIS_TIME, by decide⟩ ⟨2 ^ 61, by decide⟩ =
      MIN_GENESIS_TIME + 2 ^ 63 := by
  unfold timeAtSlotWrap
  rw [timeAtSlotNat_min_genesis_two_pow_61]
  have hsum : MIN_GENESIS_TIME + 2 ^ 64 + 2 ^ 63 =
      MIN_GENESIS_TIME + 2 ^ 63 + 2 ^ 64 := by
    ac_rfl
  rw [hsum, TIME_MOD_eq, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by decide : MIN_GENESIS_TIME + 2 ^ 63 < 2 ^ 64)

theorem timeAtSlotNat_ne_wrap_two_pow_61 :
    timeAtSlotNat ⟨MIN_GENESIS_TIME, by decide⟩ ⟨2 ^ 61, by decide⟩ ≠
      timeAtSlotWrap ⟨MIN_GENESIS_TIME, by decide⟩ ⟨2 ^ 61, by decide⟩ := by
  rw [timeAtSlotNat_min_genesis_two_pow_61, timeAtSlotWrap_min_genesis_two_pow_61]
  exact (by decide :
    MIN_GENESIS_TIME + 2 ^ 64 + 2 ^ 63 ≠ MIN_GENESIS_TIME + 2 ^ 63)

/-- phase0:1296-1300 `compute_start_slot_at_epoch`: `Slot(epoch) * SLOTS_PER_EPOCH`. -/
def startSlotAtEpoch (epoch : Nat) : Nat :=
  epoch * SLOTS_PER_EPOCH

theorem startSlotAtEpoch_spec (epoch : Nat) :
    startSlotAtEpoch epoch = epoch * 32 := by
  unfold startSlotAtEpoch SLOTS_PER_EPOCH
  rfl

/-- phase0:1286-1290 `compute_epoch_at_slot`: `Epoch(slot // SLOTS_PER_EPOCH)`.
The Python `Epoch(...)` wrap is the identity on every `U64` slot
(`slot / 32 < 2^64`). -/
def computeEpochAtSlot (slot : U64) : Nat :=
  slot.val / SLOTS_PER_EPOCH

theorem computeEpochAtSlot_spec (slot : U64) :
    computeEpochAtSlot slot = slot.val / 32 := by
  unfold computeEpochAtSlot SLOTS_PER_EPOCH
  rfl

theorem computeEpochAtSlot_lt (slot : U64) :
    computeEpochAtSlot slot < 2 ^ 64 := by
  unfold computeEpochAtSlot SLOTS_PER_EPOCH
  have h := slot.isLt
  omega

/-- phase0:1296 then 1286. The start slot of the containing epoch is
`≤ slot`. -/
theorem startSlot_of_computeEpoch (slot : U64) :
    startSlotAtEpoch (computeEpochAtSlot slot) ≤ slot.val := by
  unfold startSlotAtEpoch computeEpochAtSlot SLOTS_PER_EPOCH
  simpa [Nat.mul_comm] using Nat.mul_div_le slot.val 32

/-- phase0:1368-1372 `get_current_epoch`: reads `state.slot` only. -/
def getCurrentEpoch (c : Clock) : Nat :=
  computeEpochAtSlot c.slot

theorem getCurrentEpoch_eq_slot (c : Clock) :
    getCurrentEpoch c = c.slot.val / SLOTS_PER_EPOCH :=
  rfl

/-- Python `Slot(...)` wrap of that product (phase0:473 / 1300). -/
def startSlotAtEpochU64 (epoch : Nat) : Nat :=
  startSlotAtEpoch epoch % (2 ^ 64)

def StartSlotFits (epoch : Nat) : Prop :=
  startSlotAtEpoch epoch < 2 ^ 64

theorem startSlotFits_iff (epoch : Nat) :
    StartSlotFits epoch ↔ epoch < 2 ^ 59 := by
  unfold StartSlotFits startSlotAtEpoch SLOTS_PER_EPOCH
  have hpow : 32 * 2 ^ 59 = 2 ^ 64 := by
    rw [show 32 = 2 ^ 5 from rfl, ← Nat.pow_add]
  constructor
  · intro h
    have : epoch * 32 < 2 ^ 59 * 32 := by
      rw [Nat.mul_comm (2 ^ 59), hpow]
      exact h
    exact Nat.lt_of_mul_lt_mul_right this
  · intro h
    have : epoch * 32 < 2 ^ 59 * 32 :=
      Nat.mul_lt_mul_of_pos_right h (by decide : 0 < 32)
    rw [Nat.mul_comm (2 ^ 59), hpow] at this
    exact this

theorem startSlot_eq_of_fits {epoch : Nat} (h : StartSlotFits epoch) :
    startSlotAtEpochU64 epoch = startSlotAtEpoch epoch :=
  Nat.mod_eq_of_lt h

/-- Epoch `2^59`: Nat product is `2^64`, wrap is 0. -/
theorem startSlot_two_pow_59_nat :
    startSlotAtEpoch (2 ^ 59) = 2 ^ 64 := by
  unfold startSlotAtEpoch SLOTS_PER_EPOCH
  rw [show 32 = 2 ^ 5 from rfl, ← Nat.pow_add]

theorem startSlot_two_pow_59_wraps :
    startSlotAtEpochU64 (2 ^ 59) = 0 := by
  unfold startSlotAtEpochU64
  rw [startSlot_two_pow_59_nat]
  exact Nat.mod_self _

theorem startSlot_two_pow_59_ne_wrap :
    startSlotAtEpoch (2 ^ 59) ≠ startSlotAtEpochU64 (2 ^ 59) := by
  rw [startSlot_two_pow_59_nat, startSlot_two_pow_59_wraps]
  exact Nat.ne_of_gt (Nat.two_pow_pos 64)

/-- phase0:547 `ENDIANNESS = 'little'`. phase0:1012-1016 `uint_to_bytes`
is `ssz_serialize`; the `ssz_serialize` body is not in the archived
beacon-chain files. This is the 8-byte little-endian serialization that
`bytes_to_uint64` (phase0:1024-1028) inverts. -/
def uintToBytes : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, n => (n % 256) :: uintToBytes k (n / 256)

def uintFromBytes : List Nat → Nat
  | [] => 0
  | b :: bs => (b % 256) + 256 * uintFromBytes bs

def uintToBytes8 (n : Nat) : List Nat :=
  uintToBytes 8 n

def uintToBytes8Be (n : Nat) : List Nat :=
  (uintToBytes8 n).reverse

theorem uintToBytes_length (k n : Nat) :
    (uintToBytes k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp [uintToBytes, ih]

theorem uintToBytes8_length (n : Nat) :
    (uintToBytes8 n).length = 8 :=
  uintToBytes_length 8 n

theorem mul_add_mod_of_lt {a b c m : Nat}
    (_ha : 0 < a) (hm : 0 < m) (hc : c < a) :
    (a * b + c) % (a * m) = a * (b % m) + c := by
  have hrm : b % m < m := Nat.mod_lt b hm
  have hlt : a * (b % m) + c < a * m := by
    have hstep : a * (b % m) + c < a * (b % m) + a :=
      Nat.add_lt_add_left hc _
    have hmul : a * (b % m) + a = a * (b % m + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    have hle : a * (b % m + 1) ≤ a * m :=
      Nat.mul_le_mul_left a (Nat.succ_le_of_lt hrm)
    exact Nat.lt_of_lt_of_le (hmul ▸ hstep) hle
  have hexp : a * b + c = (b / m) * (a * m) + (a * (b % m) + c) := by
    have hb : m * (b / m) + b % m = b := Nat.div_add_mod b m
    have hre : a * (m * (b / m)) = (b / m) * (a * m) := by
      rw [← Nat.mul_assoc, Nat.mul_comm]
    calc
      a * b + c
          = a * (m * (b / m) + b % m) + c := by rw [hb]
      _ = a * (m * (b / m)) + a * (b % m) + c := by
        rw [Nat.mul_add]
      _ = (b / m) * (a * m) + a * (b % m) + c := by rw [hre]
      _ = (b / m) * (a * m) + (a * (b % m) + c) := Nat.add_assoc _ _ _
  rw [hexp, Nat.add_comm, Nat.mul_comm (b / m), Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hlt]

theorem uintFrom_to (k n : Nat) :
    uintFromBytes (uintToBytes k n) = n % 256 ^ k := by
  induction k generalizing n with
  | zero =>
    simp [uintToBytes, uintFromBytes]
    exact (Nat.mod_one n).symm
  | succ k ih =>
    have hp : 0 < 256 := by decide
    have hpow : 0 < 256 ^ k := Nat.pow_pos hp
    simp only [uintToBytes, uintFromBytes, ih, Nat.mod_mod]
    have hn : 256 * (n / 256) + n % 256 = n := Nat.div_add_mod n 256
    calc
      n % 256 + 256 * ((n / 256) % 256 ^ k)
          = 256 * ((n / 256) % 256 ^ k) + n % 256 := Nat.add_comm _ _
      _ = (256 * (n / 256) + n % 256) % (256 * 256 ^ k) :=
        (mul_add_mod_of_lt hp hpow (Nat.mod_lt n hp)).symm
      _ = n % (256 * 256 ^ k) := by rw [hn]
      _ = n % 256 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

theorem pow256_8_eq_two_pow_64 : 256 ^ 8 = 2 ^ 64 := by
  have h : 256 = 2 ^ 8 := rfl
  rw [h, ← Nat.pow_mul]

theorem uintFrom_to8 (n : Nat) :
    uintFromBytes (uintToBytes8 n) = n % (2 ^ 64) := by
  unfold uintToBytes8
  rw [uintFrom_to, pow256_8_eq_two_pow_64]

theorem uintToBytes8_inj {a b : Nat}
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : uintToBytes8 a = uintToBytes8 b) : a = b := by
  have := congrArg uintFromBytes h
  rw [uintFrom_to8, uintFrom_to8, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact this

theorem uintToBytes8_one :
    uintToBytes8 1 = [1, 0, 0, 0, 0, 0, 0, 0] := by
  simp [uintToBytes8, uintToBytes]

theorem uintToBytes8Be_one :
    uintToBytes8Be 1 = [0, 0, 0, 0, 0, 0, 0, 1] := by
  simp [uintToBytes8Be, uintToBytes8_one]

/-- A big-endian mutant of phase0:547 / 1028 is not `uint_to_bytes`. -/
theorem uint_to_bytes_is_not_be :
    uintToBytes8 1 ≠ uintToBytes8Be 1 := by
  rw [uintToBytes8_one, uintToBytes8Be_one]
  decide

theorem mod_eq_sub_of_lt_two {n M : Nat} (h1 : M ≤ n) (h2 : n < 2 * M) :
    n % M = n - M := by
  have hn : n = M + (n - M) := (Nat.add_sub_of_le h1).symm
  have hsub : n - M < M := by
    have : M + (n - M) < M + M := by
      rw [← hn]
      rwa [Nat.two_mul] at h2
    exact Nat.lt_of_add_lt_add_left this
  rw [hn, Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_mod_right,
    Nat.mod_eq_of_lt hsub]

theorem add_mod_eq_self_of_lt {start d M : Nat}
    (hM : 0 < M) (hd : d < M)
    (h : (start + d) % M = start % M) : d = 0 := by
  have hadd : (start % M + d) % M = start % M := by
    have := Nat.add_mod start d M
    rw [this, Nat.mod_eq_of_lt hd] at h
    exact h
  have hr : start % M < M := Nat.mod_lt start hM
  by_cases hlt : start % M + d < M
  · have : start % M + d = start % M := by
      rw [← Nat.mod_eq_of_lt hlt, hadd]
    exact Nat.add_eq_left.mp this
  · have hge : M ≤ start % M + d := Nat.le_of_not_gt hlt
    have h2 : start % M + d < 2 * M := by
      have hlt1 : start % M + d < M + d := Nat.add_lt_add_right hr d
      have hlt2 : M + d < M + M := Nat.add_lt_add_left hd M
      have h2m : M + M = 2 * M := (Nat.two_mul M).symm
      exact Nat.lt_trans hlt1 (h2m ▸ hlt2)
    have hsub : (start % M + d) % M = start % M + d - M :=
      mod_eq_sub_of_lt_two hge h2
    have heq : start % M + d - M = start % M := by
      rw [← hsub, hadd]
    have hsum : start % M + d = start % M + M :=
      (Nat.sub_eq_iff_eq_add hge).mp heq
    have hdM : d = M := Nat.add_left_cancel hsum
    exact False.elim (Nat.lt_irrefl M (hdM ▸ hd))

/-- Fulu:350 `start_slot + i` as Python `Uint64`. 32 consecutive values
remain distinct even when the window wraps `2^64`. -/
theorem seed_slot_u64_inj {start i j : Nat}
    (hi : i < SLOTS_PER_EPOCH) (hj : j < SLOTS_PER_EPOCH)
    (h : (start + i) % (2 ^ 64) = (start + j) % (2 ^ 64)) : i = j := by
  unfold SLOTS_PER_EPOCH at hi hj
  have hM : (32 : Nat) < 2 ^ 64 := by decide
  wlog hle : i ≤ j generalizing i j
  · exact (this hj hi h.symm (Nat.le_of_not_ge hle)).symm
  have hd : j - i < 32 := Nat.lt_of_le_of_lt (Nat.sub_le j i) hj
  have hji : i + (j - i) = j := Nat.add_sub_of_le hle
  have hsum : start + j = start + i + (j - i) := by
    rw [Nat.add_assoc, hji]
  have hwin : (start + i + (j - i)) % (2 ^ 64) = (start + i) % (2 ^ 64) := by
    rw [← hsum, h]
  have hd0 : j - i = 0 :=
    add_mod_eq_self_of_lt (by decide : 0 < 2 ^ 64) (Nat.lt_trans hd hM) hwin
  exact Nat.le_antisymm hle (Nat.le_of_sub_eq_zero hd0)

def seedSlotU64 (start i : Nat) : Nat :=
  (start + i) % (2 ^ 64)

def seedSlotU64s (start : Nat) : List Nat :=
  (List.range SLOTS_PER_EPOCH).map (seedSlotU64 start)

theorem seedSlotU64s_length (start : Nat) :
    (seedSlotU64s start).length = SLOTS_PER_EPOCH := by
  simp [seedSlotU64s, List.length_map, List.length_range]

theorem nodup_map_on {α : Type _} {β : Type _} {f : α → β} {l : List α}
    (h : l.Nodup)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) :
    (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih h.2 (fun x hx y hy =>
      hinj x (List.mem_cons.mpr (Or.inr hx)) y (List.mem_cons.mpr (Or.inr hy)))⟩
    intro hf
    obtain ⟨b, hb, hfeq⟩ := List.mem_map.mp hf
    have hab : a = b :=
      hinj a (List.mem_cons.mpr (Or.inl rfl)) b (List.mem_cons.mpr (Or.inr hb)) hfeq.symm
    exact h.1 (hab ▸ hb)

theorem seedSlotU64s_nodup (start : Nat) :
    (seedSlotU64s start).Nodup := by
  refine nodup_map_on (List.nodup_range : (List.range SLOTS_PER_EPOCH).Nodup) ?_
  intro i hi j hj heq
  have hi' : i < SLOTS_PER_EPOCH := List.mem_range.mp hi
  have hj' : j < SLOTS_PER_EPOCH := List.mem_range.mp hj
  exact seed_slot_u64_inj hi' hj' heq

/-- Wrap window still distinct: last 16 slots of `Uint64` plus the first 16. -/
theorem seedSlotU64s_wrap_nodup :
    (seedSlotU64s (2 ^ 64 - 16)).Nodup :=
  seedSlotU64s_nodup (2 ^ 64 - 16)

theorem seedSlotU64_succ_ne (start : Nat) :
    seedSlotU64 start 0 ≠ seedSlotU64 start 1 := by
  intro h
  have := seed_slot_u64_inj
    (by decide : 0 < SLOTS_PER_EPOCH)
    (by decide : 1 < SLOTS_PER_EPOCH) h
  exact (by decide : ¬ (0 = 1)) this

/-- Fulu:350 preimage `seed + uint_to_bytes(start_slot + i)`. -/
def proposerSeedPreimage (epochSeed : List Nat) (start i : Nat) : List Nat :=
  epochSeed ++ uintToBytes8 (seedSlotU64 start i)

def proposerSeedPreimages (epochSeed : List Nat) (start : Nat) : List (List Nat) :=
  (List.range SLOTS_PER_EPOCH).map (proposerSeedPreimage epochSeed start)

theorem proposerSeedPreimages_length (epochSeed : List Nat) (start : Nat) :
    (proposerSeedPreimages epochSeed start).length = SLOTS_PER_EPOCH := by
  simp [proposerSeedPreimages, List.length_map, List.length_range]

theorem proposerSeedPreimage_inj {epochSeed : List Nat} {start i j : Nat}
    (hi : i < SLOTS_PER_EPOCH) (hj : j < SLOTS_PER_EPOCH)
    (h : proposerSeedPreimage epochSeed start i =
      proposerSeedPreimage epochSeed start j) : i = j := by
  have hsuf :
      uintToBytes8 (seedSlotU64 start i) = uintToBytes8 (seedSlotU64 start j) :=
    List.append_cancel_left h
  have hi64 : seedSlotU64 start i < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hj64 : seedSlotU64 start j < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hslot : seedSlotU64 start i = seedSlotU64 start j :=
    uintToBytes8_inj hi64 hj64 hsuf
  exact seed_slot_u64_inj hi hj hslot

theorem proposerSeedPreimages_nodup (epochSeed : List Nat) (start : Nat) :
    (proposerSeedPreimages epochSeed start).Nodup := by
  refine nodup_map_on (List.nodup_range : (List.range SLOTS_PER_EPOCH).Nodup) ?_
  intro i hi j hj heq
  exact proposerSeedPreimage_inj (List.mem_range.mp hi) (List.mem_range.mp hj) heq

/-- A no-`+ i` mutant of Fulu:350 repeats the same preimage 32 times. -/
def constantSlotPreimages (epochSeed : List Nat) (start : Nat) : List (List Nat) :=
  List.replicate SLOTS_PER_EPOCH (proposerSeedPreimage epochSeed start 0)

theorem constantSlotPreimages_not_nodup (epochSeed : List Nat) (start : Nat) :
    ¬ (constantSlotPreimages epochSeed start).Nodup := by
  unfold constantSlotPreimages SLOTS_PER_EPOCH
  exact List.not_nodup_cons_of_mem (List.mem_replicate.mpr ⟨by decide, rfl⟩)

/-- Preimage order is `seed ++ slot`, not `slot ++ seed`. -/
theorem proposerSeedPreimage_ne_reversed :
    proposerSeedPreimage [9] 0 0 ≠ uintToBytes8 (seedSlotU64 0 0) ++ [9] := by
  simp [proposerSeedPreimage, uintToBytes8, uintToBytes, seedSlotU64]

/-- phase0:560-561. DomainType hex is the 4-byte sequence. -/
def DOMAIN_BEACON_PROPOSER : List Nat := [0, 0, 0, 0]
def DOMAIN_BEACON_ATTESTER : List Nat := [1, 0, 0, 0]

theorem domain_proposer_ne_attester :
    DOMAIN_BEACON_PROPOSER ≠ DOMAIN_BEACON_ATTESTER := by
  decide

/-- phase0:1452 `sha256(domain_type + uint_to_bytes(epoch) + mix)`.
The digest is uninterpreted; this is the concatenated preimage. -/
def getSeedPreimage (domain : List Nat) (epoch : Nat) (mix : List Nat) : List Nat :=
  domain ++ uintToBytes8 (epoch % (2 ^ 64)) ++ mix

theorem getSeedPreimage_uses_proposer :
    getSeedPreimage DOMAIN_BEACON_PROPOSER 0 [7] ≠
      getSeedPreimage DOMAIN_BEACON_ATTESTER 0 [7] := by
  simp [getSeedPreimage, DOMAIN_BEACON_PROPOSER, DOMAIN_BEACON_ATTESTER,
    uintToBytes8, uintToBytes]

/-- Fulu:350 seeds after `compute_start_slot_at_epoch`. -/
def computeProposerSeedInputs (epochSeed : List Nat) (epoch : Nat) : List (List Nat) :=
  proposerSeedPreimages epochSeed (startSlotAtEpochU64 epoch)

theorem computeProposerSeedInputs_length (epochSeed : List Nat) (epoch : Nat) :
    (computeProposerSeedInputs epochSeed epoch).length = SLOTS_PER_EPOCH :=
  proposerSeedPreimages_length epochSeed _

theorem computeProposerSeedInputs_nodup (epochSeed : List Nat) (epoch : Nat) :
    (computeProposerSeedInputs epochSeed epoch).Nodup :=
  proposerSeedPreimages_nodup epochSeed _

/-- phase0:1036-1040. Digest values stay uninterpreted. -/
def proposerSeeds (hash : List Nat → List Nat) (epochSeed : List Nat) (epoch : Nat) :
    List (List Nat) :=
  (computeProposerSeedInputs epochSeed epoch).map hash

theorem proposerSeeds_length (hash : List Nat → List Nat)
    (epochSeed : List Nat) (epoch : Nat) :
    (proposerSeeds hash epochSeed epoch).length = SLOTS_PER_EPOCH := by
  simp [proposerSeeds, computeProposerSeedInputs, proposerSeedPreimages,
    List.length_map, List.length_range]

/-- Fulu:351. `choose` is `compute_proposer_index` (named). Fill length
is the archived `range(SLOTS_PER_EPOCH)`, not an extra `ProposerIndices`
premise. -/
def proposerIndicesOfSeeds (hash : List Nat → List Nat) (choose : List Nat → U64)
    (epochSeed : List Nat) (epoch : Nat) : ProposerIndices where
  data := (proposerSeeds hash epochSeed epoch).map choose
  length_ok := by
    simp [proposerSeeds, computeProposerSeedInputs, proposerSeedPreimages,
      List.length_map, List.length_range]

theorem proposerIndicesOfSeeds_length (hash : List Nat → List Nat)
    (choose : List Nat → U64) (epochSeed : List Nat) (epoch : Nat) :
    (proposerIndicesOfSeeds hash choose epochSeed epoch).data.length =
      SLOTS_PER_EPOCH :=
  (proposerIndicesOfSeeds hash choose epochSeed epoch).length_ok

theorem proposerLookahead_fill_from_seeds (hash : List Nat → List Nat)
    (choose : List Nat → U64) (epochSeed : List Nat) (epoch : Nat)
    (pre : ProposerLookahead) :
    (shiftAndFill pre (proposerIndicesOfSeeds hash choose epochSeed epoch)).length =
      proposerLookaheadLength :=
  shiftAndFill_length pre _

/-- phase0:625 `EPOCHS_PER_HISTORICAL_VECTOR = Epoch(2**16)` (= 65536). -/
def EPOCHS_PER_HISTORICAL_VECTOR : Nat := 2 ^ 16

theorem epochsPerHistoricalVector_eq :
    EPOCHS_PER_HISTORICAL_VECTOR = 65536 := by
  decide

/-- phase0:1449-1451 `epoch + VECTOR - MIN_SEED_LOOKAHEAD - 1`.
The `+ VECTOR` avoids underflow at genesis (phase0:1451 note). -/
def getSeedMixEpoch (epoch : Nat) : Nat :=
  epoch + EPOCHS_PER_HISTORICAL_VECTOR - MIN_SEED_LOOKAHEAD - 1

theorem getSeedMixEpoch_spec (epoch : Nat) :
    getSeedMixEpoch epoch = epoch + 65534 := by
  unfold getSeedMixEpoch EPOCHS_PER_HISTORICAL_VECTOR MIN_SEED_LOOKAHEAD
  have h1 : 1 ≤ 2 ^ 16 := by decide
  have h2 : 1 ≤ 2 ^ 16 - 1 := by decide
  have hc : (2 ^ 16 - 1) - 1 = 65534 := by decide
  rw [Nat.add_sub_assoc h1, Nat.add_sub_assoc h2, hc]

/-- phase0:1414 `state.randao_mixes[epoch % VECTOR]`. -/
def getRandaoMixIndex (epoch : Nat) : Nat :=
  epoch % EPOCHS_PER_HISTORICAL_VECTOR

def getSeedMixIndex (epoch : Nat) : Nat :=
  getRandaoMixIndex (getSeedMixEpoch epoch)

theorem getSeedMixIndex_eq (epoch : Nat) :
    getSeedMixIndex epoch = (epoch + 65534) % 65536 := by
  unfold getSeedMixIndex getRandaoMixIndex
  rw [getSeedMixEpoch_spec, epochsPerHistoricalVector_eq]

theorem getSeedMixIndex_lt (epoch : Nat) :
    getSeedMixIndex epoch < EPOCHS_PER_HISTORICAL_VECTOR :=
  Nat.mod_lt _ (by decide : 0 < EPOCHS_PER_HISTORICAL_VECTOR)

/-- Genesis: mix index is 65534, not the current-epoch slot 0. -/
theorem getSeedMixIndex_genesis :
    getSeedMixIndex 0 = 65534 :=
  getSeedMixIndex_eq 0

theorem getRandaoMixIndex_zero :
    getRandaoMixIndex 0 = 0 :=
  Nat.zero_mod _

/-- Epoch 2 wraps the mix ring back to index 0. -/
theorem getSeedMixIndex_epoch_two :
    getSeedMixIndex 2 = 0 :=
  getSeedMixIndex_eq 2

/-- A current-epoch mutant of phase0:1450 is not `get_seed`. -/
theorem getSeedMix_ne_current (epoch : Nat)
    (h : getRandaoMixIndex epoch ≠ (epoch + 65534) % 65536) :
    getSeedMixIndex epoch ≠ getRandaoMixIndex epoch := by
  rw [getSeedMixIndex_eq]
  exact Ne.symm h

theorem getSeedMix_ne_current_genesis :
    getSeedMixIndex 0 ≠ getRandaoMixIndex 0 := by
  rw [getSeedMixIndex_genesis, getRandaoMixIndex_zero]
  exact (by decide : 65534 ≠ 0)

/-- Dropping `+ VECTOR` saturates at genesis (Lean `0 - 1 = 0`), not 65534. -/
def getSeedMixEpochNoVector (epoch : Nat) : Nat :=
  epoch - MIN_SEED_LOOKAHEAD - 1

theorem getSeedMix_needs_vector :
    getSeedMixEpoch 0 ≠ getSeedMixEpochNoVector 0 := by
  rw [getSeedMixEpoch_spec]
  unfold getSeedMixEpochNoVector MIN_SEED_LOOKAHEAD
  decide

/-- `MIN_SEED_LOOKAHEAD = 0` reads index 65535 at genesis, not 65534. -/
def getSeedMixEpochNoLookahead (epoch : Nat) : Nat :=
  epoch + EPOCHS_PER_HISTORICAL_VECTOR - 1

theorem getSeedMix_uses_lookahead :
    getSeedMixIndex 0 ≠
      getRandaoMixIndex (getSeedMixEpochNoLookahead 0) := by
  unfold getRandaoMixIndex getSeedMixEpochNoLookahead
    EPOCHS_PER_HISTORICAL_VECTOR
  rw [getSeedMixIndex_genesis]
  decide

/-- phase0:1452. Mix bytes are the VECTOR entry at `getSeedMixIndex`.
SHA256 of the concatenated preimage stays uninterpreted. -/
def getSeedPreimageFromMixes (domain : List Nat) (epoch : Nat)
    (mixes : List (List Nat))
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) : List Nat :=
  getSeedPreimage domain epoch (mixes[getSeedMixIndex epoch]'(by
    rw [hlen]
    exact getSeedMixIndex_lt epoch))

theorem getSeedPreimageFromMixes_eq (domain : List Nat) (epoch : Nat)
    (mixes : List (List Nat))
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) :
    getSeedPreimageFromMixes domain epoch mixes hlen =
      getSeedPreimage domain epoch (mixes[getSeedMixIndex epoch]'(by
        rw [hlen]; exact getSeedMixIndex_lt epoch)) :=
  rfl

/-- phase0:1410-1414. The mix is the stored VECTOR entry. -/
def getRandaoMix (mixes : List (List Nat)) (epoch : Nat)
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) : List Nat :=
  mixes[getRandaoMixIndex epoch]'(by
    rw [hlen]
    exact Nat.mod_lt _ (by decide : 0 < EPOCHS_PER_HISTORICAL_VECTOR))

theorem getRandaoMixIndex_lt (epoch : Nat) :
    getRandaoMixIndex epoch < EPOCHS_PER_HISTORICAL_VECTOR :=
  Nat.mod_lt _ (by decide : 0 < EPOCHS_PER_HISTORICAL_VECTOR)

theorem getRandaoMixIndex_wraps :
    getRandaoMixIndex EPOCHS_PER_HISTORICAL_VECTOR = 0 :=
  Nat.mod_self _

theorem getRandaoMixIndex_add (epoch : Nat) :
    getRandaoMixIndex (epoch + EPOCHS_PER_HISTORICAL_VECTOR) =
      getRandaoMixIndex epoch :=
  Nat.add_mod_right epoch _

theorem getRandaoMix_alias (mixes : List (List Nat))
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) (epoch : Nat) :
    getRandaoMix mixes (epoch + EPOCHS_PER_HISTORICAL_VECTOR) hlen =
      getRandaoMix mixes epoch hlen := by
  unfold getRandaoMix
  simp [getRandaoMixIndex_add]

/-- phase0:1707. Genesis fills every slot with `eth1_block_hash`. -/
def genesisRandaoMixes (eth1 : List Nat) : List (List Nat) :=
  List.replicate EPOCHS_PER_HISTORICAL_VECTOR eth1

theorem genesisRandaoMixes_length (eth1 : List Nat) :
    (genesisRandaoMixes eth1).length = EPOCHS_PER_HISTORICAL_VECTOR := by
  simp [genesisRandaoMixes]

/-- phase0:1414 / 1707. At genesis every epoch reads the same hash. -/
theorem getRandaoMix_genesis (eth1 : List Nat) (epoch : Nat) :
    getRandaoMix (genesisRandaoMixes eth1) epoch
      (genesisRandaoMixes_length eth1) = eth1 := by
  unfold getRandaoMix genesisRandaoMixes
  apply List.getElem_replicate

/-- phase0:1449-1452. `get_seed` concatenates that VECTOR entry. -/
theorem getSeedPreimageFromMixes_eq_randao (domain : List Nat)
    (epoch : Nat) (mixes : List (List Nat))
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) :
    getSeedPreimageFromMixes domain epoch mixes hlen =
      getSeedPreimage domain epoch
        (getRandaoMix mixes (getSeedMixEpoch epoch) hlen) :=
  rfl

/-- Mutant: always read `randao_mixes[0]`. -/
def getRandaoMixAtZero (mixes : List (List Nat))
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) : List Nat :=
  mixes[0]'(by
    rw [hlen]
    decide)

/-- phase0:2237-2243. Copy the current mix into `next_epoch % VECTOR`. -/
def processRandaoMixesReset (mixes : List (List Nat)) (current : Nat)
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) : List (List Nat) :=
  mixes.set (getRandaoMixIndex (current + 1)) (getRandaoMix mixes current hlen)

theorem processRandaoMixesReset_length (mixes : List (List Nat))
    (current : Nat) (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) :
    (processRandaoMixesReset mixes current hlen).length =
      EPOCHS_PER_HISTORICAL_VECTOR := by
  simp [processRandaoMixesReset, hlen]

/-- phase0:2241-2243. After the reset, `next_epoch` reads the old current. -/
theorem processRandaoMixesReset_next (mixes : List (List Nat))
    (current : Nat) (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) :
    getRandaoMix (processRandaoMixesReset mixes current hlen) (current + 1)
      (processRandaoMixesReset_length mixes current hlen) =
      getRandaoMix mixes current hlen := by
  unfold getRandaoMix processRandaoMixesReset
  rw [List.getElem_set]
  simp
  rfl

theorem getRandaoMixIndex_succ_ne (epoch : Nat) :
    getRandaoMixIndex (epoch + 1) ≠ getRandaoMixIndex epoch := by
  unfold getRandaoMixIndex
  intro h
  have hn : 0 < EPOCHS_PER_HISTORICAL_VECTOR := by decide
  have h1 : 1 < EPOCHS_PER_HISTORICAL_VECTOR := by decide
  have hadd :
      (epoch + 1) % EPOCHS_PER_HISTORICAL_VECTOR =
        (epoch % EPOCHS_PER_HISTORICAL_VECTOR + 1) %
          EPOCHS_PER_HISTORICAL_VECTOR := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt h1]
  rw [hadd] at h
  set k := epoch % EPOCHS_PER_HISTORICAL_VECTOR
  have hk : k < EPOCHS_PER_HISTORICAL_VECTOR := Nat.mod_lt _ hn
  have hle : k + 1 ≤ EPOCHS_PER_HISTORICAL_VECTOR := Nat.succ_le_of_lt hk
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · rw [Nat.mod_eq_of_lt hlt] at h
    exact (Nat.succ_ne_self k) h
  · rw [heq, Nat.mod_self] at h
    have : k = EPOCHS_PER_HISTORICAL_VECTOR - 1 := by omega
    rw [this] at h
    simp [EPOCHS_PER_HISTORICAL_VECTOR] at h

/-- phase0:2241 writes `next_epoch % VECTOR` only. -/
theorem processRandaoMixesReset_other (mixes : List (List Nat))
    (current e : Nat) (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR)
    (hne : getRandaoMixIndex e ≠ getRandaoMixIndex (current + 1)) :
    getRandaoMix (processRandaoMixesReset mixes current hlen) e
      (processRandaoMixesReset_length mixes current hlen) =
      getRandaoMix mixes e hlen := by
  unfold getRandaoMix processRandaoMixesReset
  rw [List.getElem_set]
  split_ifs with h
  · exact (hne h.symm).elim
  · rfl

theorem set_replicate_self {α : Type} (a : α) (n i : Nat)
    (_hi : i < n) :
    (List.replicate n a).set i a = List.replicate n a := by
  apply List.ext_getElem
  · simp
  · intro j hj
    rw [List.getElem_set]
    split_ifs
    · intro h₂
      exact (List.getElem_replicate h₂).symm
    · intro _h₂
      rfl

/-- phase0:1707 / 2237-2243. A genesis splat makes the copy a no-op. -/
theorem processRandaoMixesReset_genesis (eth1 : List Nat) (current : Nat) :
    processRandaoMixesReset (genesisRandaoMixes eth1) current
      (genesisRandaoMixes_length eth1) = genesisRandaoMixes eth1 := by
  unfold processRandaoMixesReset
  rw [getRandaoMix_genesis]
  unfold genesisRandaoMixes
  exact set_replicate_self eth1 _ _ (getRandaoMixIndex_lt (current + 1))

/-- phase0:1002-1006. Bytewise `a ^ b` via `zip`. Named: Python
`zip(..., strict=True)` raises on length mismatch; Lean `zipWith`
truncates to `min`. -/
def bytesXor (xs ys : List Nat) : List Nat :=
  List.zipWith Nat.xor xs ys

theorem bytesXor_length (xs ys : List Nat) :
    (bytesXor xs ys).length = min xs.length ys.length := by
  simp [bytesXor]

/-- phase0:1006. Unequal lengths truncate here; Python raises. -/
theorem bytesXor_truncates :
    bytesXor [1, 2] [3] = [Nat.xor 1 3] := by
  simp [bytesXor]

theorem bytesXor_zeros_left (ys : List Nat) :
    bytesXor (List.replicate ys.length 0) ys = ys := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp [bytesXor, List.replicate_succ, Nat.zero_xor]
    exact ih

theorem bytesXor_zeros_right (xs : List Nat) :
    bytesXor xs (List.replicate xs.length 0) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [bytesXor, List.replicate_succ, Nat.xor_zero]
    exact ih

theorem bytesXor_self (xs : List Nat) :
    bytesXor xs xs = List.replicate xs.length 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [bytesXor, Nat.xor_self, List.replicate_succ, ih]

/--
phase0:2314 `xor(get_randao_mix(state, epoch), sha256(reveal))`.
SHA256 values stay uninterpreted. phase0:2312 `bls.Verify` is named
and not extracted: Python writes only after that assert.
-/
def processRandaoMix (hash : List Nat → List Nat) (mixes : List (List Nat))
    (epoch : Nat) (reveal : List Nat)
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) : List Nat :=
  bytesXor (getRandaoMix mixes epoch hlen) (hash reveal)

/-- phase0:2315. Write the xor at `epoch % VECTOR`, not `next_epoch`. -/
def processRandao (hash : List Nat → List Nat) (mixes : List (List Nat))
    (epoch : Nat) (reveal : List Nat)
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) : List (List Nat) :=
  mixes.set (getRandaoMixIndex epoch)
    (processRandaoMix hash mixes epoch reveal hlen)

theorem processRandao_length (hash : List Nat → List Nat)
    (mixes : List (List Nat)) (epoch : Nat) (reveal : List Nat)
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) :
    (processRandao hash mixes epoch reveal hlen).length =
      EPOCHS_PER_HISTORICAL_VECTOR := by
  simp [processRandao, hlen]

/-- phase0:2314-2315. After the write, the current epoch reads the xor. -/
theorem processRandao_current (hash : List Nat → List Nat)
    (mixes : List (List Nat)) (epoch : Nat) (reveal : List Nat)
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) :
    getRandaoMix (processRandao hash mixes epoch reveal hlen) epoch
      (processRandao_length hash mixes epoch reveal hlen) =
      processRandaoMix hash mixes epoch reveal hlen := by
  unfold getRandaoMix processRandao
  rw [List.getElem_set]
  simp

/-- phase0:2315. A different ring slot is unchanged. -/
theorem processRandao_other (hash : List Nat → List Nat)
    (mixes : List (List Nat)) (epoch e : Nat) (reveal : List Nat)
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR)
    (hne : getRandaoMixIndex e ≠ getRandaoMixIndex epoch) :
    getRandaoMix (processRandao hash mixes epoch reveal hlen) e
      (processRandao_length hash mixes epoch reveal hlen) =
      getRandaoMix mixes e hlen := by
  unfold getRandaoMix processRandao
  rw [List.getElem_set]
  split_ifs with h
  · exact (hne h.symm).elim
  · rfl

/-- Mutant: write a copy of the current mix, like the epoch reset. -/
def processRandaoCopy (mixes : List (List Nat)) (epoch : Nat)
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) : List (List Nat) :=
  mixes.set (getRandaoMixIndex epoch) (getRandaoMix mixes epoch hlen)

theorem processRandaoCopy_length (mixes : List (List Nat)) (epoch : Nat)
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) :
    (processRandaoCopy mixes epoch hlen).length = EPOCHS_PER_HISTORICAL_VECTOR := by
  simp [processRandaoCopy, hlen]

theorem processRandaoCopy_current (mixes : List (List Nat)) (epoch : Nat)
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) :
    getRandaoMix (processRandaoCopy mixes epoch hlen) epoch
      (processRandaoCopy_length mixes epoch hlen) =
      getRandaoMix mixes epoch hlen := by
  unfold getRandaoMix processRandaoCopy
  rw [List.getElem_set]
  simp
  unfold getRandaoMix
  rfl

theorem getRandaoMix_congr_list {mixes mixes' : List (List Nat)}
    {epoch : Nat} {hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR}
    {hlen' : mixes'.length = EPOCHS_PER_HISTORICAL_VECTOR}
    (h : mixes = mixes') :
    getRandaoMix mixes epoch hlen = getRandaoMix mixes' epoch hlen' := by
  cases h
  rfl

/--
Temporal order of the archived callees: `process_block` phase0:2273
`process_randao`, then on an epoch boundary `process_epoch` phase0:1823
`process_randao_mixes_reset`. They are not the same function.
-/
def processRandaoThenReset (hash : List Nat → List Nat)
    (mixes : List (List Nat)) (epoch : Nat) (reveal : List Nat)
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) : List (List Nat) :=
  processRandaoMixesReset (processRandao hash mixes epoch reveal hlen) epoch
    (processRandao_length hash mixes epoch reveal hlen)

/-- Mutant: reset first, then xor. That is not the archived order. -/
def processResetThenRandao (hash : List Nat → List Nat)
    (mixes : List (List Nat)) (epoch : Nat) (reveal : List Nat)
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) : List (List Nat) :=
  processRandao hash (processRandaoMixesReset mixes epoch hlen) epoch reveal
    (processRandaoMixesReset_length mixes epoch hlen)

theorem processRandaoThenReset_length (hash : List Nat → List Nat)
    (mixes : List (List Nat)) (epoch : Nat) (reveal : List Nat)
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) :
    (processRandaoThenReset hash mixes epoch reveal hlen).length =
      EPOCHS_PER_HISTORICAL_VECTOR := by
  simp [processRandaoThenReset, processRandaoMixesReset_length]

theorem processResetThenRandao_length (hash : List Nat → List Nat)
    (mixes : List (List Nat)) (epoch : Nat) (reveal : List Nat)
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) :
    (processResetThenRandao hash mixes epoch reveal hlen).length =
      EPOCHS_PER_HISTORICAL_VECTOR := by
  simp [processResetThenRandao, processRandao_length]

/-- phase0:2273 then 1823. Current epoch still holds the xor; reset
writes `next_epoch` only. -/
theorem processRandaoThenReset_current (hash : List Nat → List Nat)
    (mixes : List (List Nat)) (epoch : Nat) (reveal : List Nat)
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) :
    getRandaoMix (processRandaoThenReset hash mixes epoch reveal hlen) epoch
      (processRandaoThenReset_length hash mixes epoch reveal hlen) =
      processRandaoMix hash mixes epoch reveal hlen := by
  unfold processRandaoThenReset
  rw [processRandaoMixesReset_other _ _ _ _
    (getRandaoMixIndex_succ_ne epoch).symm]
  exact processRandao_current hash mixes epoch reveal hlen

/-- phase0:1823. After the reset, `next_epoch` reads the xor'd current. -/
theorem processRandaoThenReset_next (hash : List Nat → List Nat)
    (mixes : List (List Nat)) (epoch : Nat) (reveal : List Nat)
    (hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR) :
    getRandaoMix (processRandaoThenReset hash mixes epoch reveal hlen)
      (epoch + 1)
      (processRandaoThenReset_length hash mixes epoch reveal hlen) =
      processRandaoMix hash mixes epoch reveal hlen := by
  unfold processRandaoThenReset
  rw [processRandaoMixesReset_next, processRandao_current]

/-- phase0:1244 `MAX_RANDOM_BYTE = 2**8 - 1`. -/
def MAX_RANDOM_BYTE : Nat := 2 ^ 8 - 1

/-- phase0:606 `MAX_EFFECTIVE_BALANCE = Gwei(2**5 * 10**9)` (= 32e9). -/
def MAX_EFFECTIVE_BALANCE : Nat := 2 ^ 5 * 10 ^ 9

theorem maxRandomByte_eq : MAX_RANDOM_BYTE = 255 := by
  decide

theorem maxEffectiveBalance_eq : MAX_EFFECTIVE_BALANCE = 32 * 10 ^ 9 := by
  decide

/-- phase0:1243. The sampling loop indexes `i % total`; empty `indices`
is asserted out. -/
def ProposerIndicesNonempty (indices : List U64) : Prop :=
  0 < indices.length

theorem empty_proposer_indices :
    ¬ ProposerIndicesNonempty [] := by
  simp [ProposerIndicesNonempty]

theorem sample_mod_lt {i total : Nat} (h : 0 < total) :
    i % total < total :=
  Nat.mod_lt i h

/-- phase0:1251
`effective_balance * MAX_RANDOM_BYTE >= MAX_EFFECTIVE_BALANCE * random_byte`. -/
def proposerAccepts (effectiveBalance randomByte : Nat) : Bool :=
  decide
    (effectiveBalance * MAX_RANDOM_BYTE ≥
      MAX_EFFECTIVE_BALANCE * randomByte)

/-- A `>` mutant of phase0:1251. -/
def proposerAcceptsStrict (effectiveBalance randomByte : Nat) : Bool :=
  decide
    (effectiveBalance * MAX_RANDOM_BYTE >
      MAX_EFFECTIVE_BALANCE * randomByte)

theorem proposerAccepts_max {b : Nat} (hb : b ≤ MAX_RANDOM_BYTE) :
    proposerAccepts MAX_EFFECTIVE_BALANCE b = true := by
  simp [proposerAccepts]
  exact Nat.mul_le_mul_left MAX_EFFECTIVE_BALANCE hb

/-- At max effective balance the first sampled byte always passes.
`compute_shuffled_index` stays named. -/
theorem max_eb_accepts_any_byte {b : Nat} (hb : b < 256) :
    proposerAccepts MAX_EFFECTIVE_BALANCE b = true :=
  proposerAccepts_max (Nat.lt_succ_iff.mp hb)

theorem proposerAccepts_eq_boundary :
    proposerAccepts MAX_EFFECTIVE_BALANCE MAX_RANDOM_BYTE = true :=
  proposerAccepts_max le_rfl

theorem proposerAcceptsStrict_boundary :
    proposerAcceptsStrict MAX_EFFECTIVE_BALANCE MAX_RANDOM_BYTE = false := by
  simp [proposerAcceptsStrict]

/-- The archived test is `>=`, not `>`. Equality at the max byte accepts. -/
theorem proposerAccepts_ge_not_gt :
    proposerAccepts MAX_EFFECTIVE_BALANCE MAX_RANDOM_BYTE ≠
      proposerAcceptsStrict MAX_EFFECTIVE_BALANCE MAX_RANDOM_BYTE := by
  rw [proposerAccepts_eq_boundary, proposerAcceptsStrict_boundary]
  decide

theorem proposerAccepts_zero_zero :
    proposerAccepts 0 0 = true := by
  simp [proposerAccepts]

theorem proposerAccepts_zero_pos {b : Nat} (hb : 0 < b) :
    proposerAccepts 0 b = false := by
  simp [proposerAccepts]
  exact ⟨by decide, Nat.pos_iff_ne_zero.mp hb⟩

/-- phase0:1249 `sha256(seed + uint_to_bytes(Uint64(i // 32)))[i % 32]`. -/
def HASH32_BYTES : Nat := 32

def randomBytePreimage (seed : List Nat) (i : Nat) : List Nat :=
  seed ++ uintToBytes8 (i / HASH32_BYTES)

def randomByteOffset (i : Nat) : Nat :=
  i % HASH32_BYTES

theorem randomByteOffset_lt (i : Nat) :
    randomByteOffset i < HASH32_BYTES :=
  Nat.mod_lt i (by decide : 0 < HASH32_BYTES)

theorem randomBytePreimage_chunk (seed : List Nat) {i j : Nat}
    (h : i / HASH32_BYTES = j / HASH32_BYTES) :
    randomBytePreimage seed i = randomBytePreimage seed j := by
  simp [randomBytePreimage, h]

theorem randomBytePreimage_zero_eq_thirtyone (seed : List Nat) :
    randomBytePreimage seed 0 = randomBytePreimage seed 31 :=
  randomBytePreimage_chunk seed (by decide : 0 / 32 = 31 / 32)

theorem uintToBytes8_zero :
    uintToBytes8 0 = [0, 0, 0, 0, 0, 0, 0, 0] := by
  simp [uintToBytes8, uintToBytes]

theorem randomBytePreimage_zero_ne_thirtytwo (seed : List Nat) :
    randomBytePreimage seed 0 ≠ randomBytePreimage seed 32 := by
  intro h
  have hsuf : uintToBytes8 0 = uintToBytes8 1 := by
    have := congrArg (fun xs => xs.drop seed.length) h
    simp [randomBytePreimage, HASH32_BYTES] at this
    exact this
  rw [uintToBytes8_zero, uintToBytes8_one] at hsuf
  exact (by decide : ¬ ([0, 0, 0, 0, 0, 0, 0, 0] = [1, 0, 0, 0, 0, 0, 0, 0])) hsuf

/-- A mutant that hashes `i % 32` instead of `i // 32`. -/
def randomBytePreimageMod (seed : List Nat) (i : Nat) : List Nat :=
  seed ++ uintToBytes8 (i % HASH32_BYTES)

theorem random_byte_uses_div_not_mod (seed : List Nat) :
    randomBytePreimage seed 32 ≠ randomBytePreimageMod seed 32 := by
  intro h
  have hsuf : uintToBytes8 1 = uintToBytes8 0 := by
    have := congrArg (fun xs => xs.drop seed.length) h
    simp [randomBytePreimage, randomBytePreimageMod, HASH32_BYTES] at this
    exact this
  rw [uintToBytes8_one, uintToBytes8_zero] at hsuf
  exact (by decide : ¬ ([1, 0, 0, 0, 0, 0, 0, 0] = [0, 0, 0, 0, 0, 0, 0, 0])) hsuf

/-- Named: phase0:1036 returns `Bytes32`; values stay uninterpreted. -/
structure Hash32Like (hash : List Nat → List Nat) : Prop where
  length : ∀ data, (hash data).length = HASH32_BYTES
  bounded : ∀ data b, b ∈ hash data → b < 256

def randomByteOf (hash : List Nat → List Nat) (seed : List Nat) (i : Nat) : Nat :=
  ((hash (randomBytePreimage seed i))[randomByteOffset i]?).getD 0

theorem randomByteOf_is_byte {hash : List Nat → List Nat}
    (hh : Hash32Like hash) (seed : List Nat) (i : Nat) :
    randomByteOf hash seed i < 256 := by
  unfold randomByteOf randomByteOffset
  have hlen : (hash (randomBytePreimage seed i)).length = HASH32_BYTES :=
    hh.length _
  have hi : i % HASH32_BYTES < (hash (randomBytePreimage seed i)).length := by
    rw [hlen]
    exact Nat.mod_lt i (by decide : 0 < HASH32_BYTES)
  have hsome :
      (hash (randomBytePreimage seed i))[i % HASH32_BYTES]? =
        some ((hash (randomBytePreimage seed i))[i % HASH32_BYTES]'hi) :=
    List.getElem?_eq_getElem hi
  rw [hsome, Option.getD_some]
  exact hh.bounded _ _ (List.getElem_mem hi)

/-- phase0:1251 at `i = 0` with max effective balance: the first
sampled candidate is accepted for any `Bytes32` digest. The shuffle
that selects the candidate remains named. -/
theorem max_eb_accepts_first_byte {hash : List Nat → List Nat}
    (hh : Hash32Like hash) (seed : List Nat) :
    proposerAccepts MAX_EFFECTIVE_BALANCE (randomByteOf hash seed 0) = true :=
  max_eb_accepts_any_byte (randomByteOf_is_byte hh seed 0)

/-- phase0:588 `SHUFFLE_ROUND_COUNT = Uint64(90)`. -/
def SHUFFLE_ROUND_COUNT : Nat := 90

theorem shuffleRoundCount_eq : SHUFFLE_ROUND_COUNT = 90 :=
  rfl

theorem shuffleRoundCount_ne_hash32 :
    SHUFFLE_ROUND_COUNT ≠ HASH32_BYTES := by
  decide

/-- phase0:1203 identity `range(index_count)` before the 90 rounds. -/
def identityPerm (n : Nat) : List Nat :=
  List.range n

theorem identityPerm_length (n : Nat) :
    (identityPerm n).length = n :=
  List.length_range

theorem identityPerm_get {n i : Nat} (h : i < n) :
    (identityPerm n)[i]? = some i := by
  simp [identityPerm, h]

/-- phase0:1230 `assert index < index_count`. -/
def ShuffledIndexOk (index count : Nat) : Prop :=
  index < count

theorem shuffled_index_rejects_eq (n : Nat) :
    ¬ ShuffledIndexOk n n :=
  Nat.lt_irrefl n

theorem shuffled_index_rejects_empty (i : Nat) :
    ¬ ShuffledIndexOk i 0 :=
  Nat.not_lt_zero i

/-- phase0:1231: after the assert, the result is `perm[index]`.
A 0-round mutant is the identity; the archived body runs 90 rounds. -/
def shuffledIndexOf (perm : List Nat) (index : Nat) : Option Nat :=
  perm[index]?

theorem shuffledIndexOf_identity {n i : Nat} (h : i < n) :
    shuffledIndexOf (identityPerm n) i = some i :=
  identityPerm_get h

/-- phase0:1205 `uint_to_bytes(Uint8(current_round))` is width 1, not 8. -/
theorem uintToBytes1_five : uintToBytes 1 5 = [5] := by
  simp [uintToBytes]

theorem uintToBytes8_five :
    uintToBytes 8 5 = [5, 0, 0, 0, 0, 0, 0, 0] := by
  simp [uintToBytes]

theorem round_bytes_is_not_u64 :
    uintToBytes 1 5 ≠ uintToBytes 8 5 := by
  rw [uintToBytes1_five, uintToBytes8_five]
  decide

/-- phase0:1214 `uint_to_bytes(Uint32(position_bucket))` is width 4. -/
theorem uintToBytes4_one :
    uintToBytes 4 1 = [1, 0, 0, 0] := by
  simp [uintToBytes]

theorem bucket_bytes_is_not_u64 :
    uintToBytes 4 1 ≠ uintToBytes 8 1 := by
  rw [uintToBytes4_one]
  change [1, 0, 0, 0] ≠ uintToBytes8 1
  rw [uintToBytes8_one]
  decide

def shuffleRoundBytes (round : Nat) : List Nat :=
  uintToBytes 1 round

def shufflePivotPreimage (seed : List Nat) (round : Nat) : List Nat :=
  seed ++ shuffleRoundBytes round

/-- phase0:1211 `position // 256`. -/
def shuffleBucket (position : Nat) : Nat :=
  position / 256

def shuffleBucketPreimage (seed : List Nat) (round bucket : Nat) : List Nat :=
  seed ++ shuffleRoundBytes round ++ uintToBytes 4 bucket

theorem shufflePivotPreimage_ne_bucket (seed : List Nat) :
    shufflePivotPreimage seed 3 ≠ shuffleBucketPreimage seed 3 0 := by
  intro h
  have := congrArg List.length h
  simp [shufflePivotPreimage, shuffleBucketPreimage, shuffleRoundBytes,
    uintToBytes] at this

/-- phase0:1209 `flip = (pivot + index_count - indices[i]) % index_count`. -/
def shuffleFlip (pivot count idx : Nat) : Nat :=
  (pivot + count - idx % count) % count

theorem shuffleFlip_lt {pivot count idx : Nat} (h : 0 < count) :
    shuffleFlip pivot count idx < count :=
  Nat.mod_lt _ h

theorem shuffleFlip_of_lt {pivot count idx : Nat}
    (_hcount : 0 < count) (hidx : idx < count) :
    shuffleFlip pivot count idx = (pivot + count - idx) % count := by
  unfold shuffleFlip
  rw [Nat.mod_eq_of_lt hidx]

/-- The swap partner is an involution on `{0, …, count-1}`. -/
theorem shuffleFlip_involutive {pivot count idx : Nat}
    (hcount : 0 < count) (hidx : idx < count) :
    shuffleFlip pivot count (shuffleFlip pivot count idx) = idx := by
  have hflip := shuffleFlip_of_lt (pivot := pivot) hcount hidx
  have hlt : shuffleFlip pivot count idx < count := shuffleFlip_lt hcount
  rw [shuffleFlip_of_lt (pivot := pivot) hcount hlt, hflip]
  set r := (pivot + count - idx) % count
  have hr : r < count := Nat.mod_lt _ hcount
  have hle : idx ≤ pivot + count :=
    Nat.le_trans (Nat.le_of_lt hidx) (Nat.le_add_left count pivot)
  have hdiv : count * ((pivot + count - idx) / count) + r =
      pivot + count - idx := Nat.div_add_mod (pivot + count - idx) count
  have hsum : count * ((pivot + count - idx) / count) + r + idx =
      pivot + count := by
    rw [hdiv, Nat.sub_add_cancel hle]
  have hback : pivot + count - r =
      count * ((pivot + count - idx) / count) + idx := by
    have hassoc :
        count * ((pivot + count - idx) / count) + r + idx =
          count * ((pivot + count - idx) / count) + idx + r := by
      ac_rfl
    calc
      pivot + count - r
          = count * ((pivot + count - idx) / count) + r + idx - r := by
        rw [hsum]
      _ = count * ((pivot + count - idx) / count) + idx + r - r := by
        rw [hassoc]
      _ = count * ((pivot + count - idx) / count) + idx :=
        Nat.add_sub_cancel (count * ((pivot + count - idx) / count) + idx) r
  rw [hback, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hidx]

/-- Concrete swap-or-not partner: pivot 3, count 8, index 1 ↔ 2. -/
theorem shuffleFlip_sample :
    shuffleFlip 3 8 1 = 2 ∧ shuffleFlip 3 8 2 = 1 := by
  decide

/-- phase0:1024-1028 `bytes_to_uint64` is little-endian `int.from_bytes`.
The note at phase0:1021 allows a prefix shorter than eight bytes; every
byte is reduced modulo 256, so the value is `< 256^len`. -/
theorem uintFromBytes_lt : ∀ xs : List Nat, uintFromBytes xs < 256 ^ xs.length
  | [] => by
    simp [uintFromBytes]
  | b :: bs => by
    have ih := uintFromBytes_lt bs
    unfold uintFromBytes
    have hb : b % 256 < 256 := Nat.mod_lt _ (by decide : 0 < 256)
    have hstep : b % 256 + 256 * uintFromBytes bs < 256 + 256 * uintFromBytes bs :=
      Nat.add_lt_add_right hb _
    have hmul : 256 + 256 * uintFromBytes bs = 256 * (uintFromBytes bs + 1) := by
      rw [Nat.add_comm, Nat.mul_succ]
    have hle : uintFromBytes bs + 1 ≤ 256 ^ bs.length :=
      Nat.succ_le_of_lt ih
    have hbound : 256 * (uintFromBytes bs + 1) ≤ 256 * 256 ^ bs.length :=
      Nat.mul_le_mul_left 256 hle
    have hpow : 256 * 256 ^ bs.length = 256 ^ (bs.length + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    calc
      b % 256 + 256 * uintFromBytes bs
          < 256 + 256 * uintFromBytes bs := hstep
      _ = 256 * (uintFromBytes bs + 1) := hmul
      _ ≤ 256 * 256 ^ bs.length := hbound
      _ = 256 ^ (bs.length + 1) := hpow

/-- phase0:1206 `[0:8]` of a `Bytes32`; under `Hash32Like` the prefix has
length 8 and `bytes_to_uint64` of it is `< 2^64`. -/
theorem uintFromBytes_take8_lt (xs : List Nat) (hlen : 8 ≤ xs.length) :
    uintFromBytes (xs.take 8) < 2 ^ 64 := by
  have h8 : (xs.take 8).length = 8 := by
    rw [List.length_take, Nat.min_eq_left hlen]
  have hlt := uintFromBytes_lt (xs.take 8)
  rw [h8, pow256_8_eq_two_pow_64] at hlt
  exact hlt

theorem hash32_take8_length {hash : List Nat → List Nat}
    (hh : Hash32Like hash) (data : List Nat) :
    ((hash data).take 8).length = 8 := by
  rw [List.length_take, hh.length]
  exact Nat.min_eq_left (by decide : 8 ≤ HASH32_BYTES)

/-- phase0:1206 `bytes_to_uint64(sha256(seed + round_bytes)[0:8])`. -/
def shufflePivotRaw (hash : List Nat → List Nat) (seed : List Nat)
    (round : Nat) : Nat :=
  uintFromBytes ((hash (shufflePivotPreimage seed round)).take 8)

/-- Mutant: first eight digest bytes as big-endian. -/
def shufflePivotRawBe (hash : List Nat → List Nat) (seed : List Nat)
    (round : Nat) : Nat :=
  uintFromBytes (((hash (shufflePivotPreimage seed round)).take 8).reverse)

/-- phase0:1206 `% index_count`. Named: Python `% 0` is `ZeroDivisionError`;
Lean `n % 0 = n`. -/
def shufflePivot (hash : List Nat → List Nat) (seed : List Nat)
    (round count : Nat) : Nat :=
  shufflePivotRaw hash seed round % count

def shufflePivotBe (hash : List Nat → List Nat) (seed : List Nat)
    (round count : Nat) : Nat :=
  shufflePivotRawBe hash seed round % count

/-- Mutant: omit `% index_count` after `bytes_to_uint64`. -/
def shufflePivotNoMod (hash : List Nat → List Nat) (seed : List Nat)
    (round _count : Nat) : Nat :=
  shufflePivotRaw hash seed round

theorem shufflePivotRaw_lt {hash : List Nat → List Nat}
    (hh : Hash32Like hash) (seed : List Nat) (round : Nat) :
    shufflePivotRaw hash seed round < 2 ^ 64 := by
  unfold shufflePivotRaw
  have hlen : 8 ≤ (hash (shufflePivotPreimage seed round)).length := by
    rw [hh.length]
    decide
  exact uintFromBytes_take8_lt _ hlen

theorem shufflePivot_lt {hash : List Nat → List Nat}
    {seed : List Nat} {round count : Nat} (hcount : 0 < count) :
    shufflePivot hash seed round count < count :=
  Nat.mod_lt _ hcount

theorem shufflePivot_empty (hash : List Nat → List Nat)
    (seed : List Nat) (round : Nat) :
    shufflePivot hash seed round 0 = shufflePivotRaw hash seed round :=
  Nat.mod_zero _

/-- phase0:1206. The archived pivot is exactly `raw % index_count`. -/
theorem shufflePivot_eq_raw_mod (hash : List Nat → List Nat)
    (seed : List Nat) (round count : Nat) :
    shufflePivot hash seed round count =
      shufflePivotRaw hash seed round % count :=
  rfl

/-- phase0:1206. When the raw uint64 is already in range, `%` is identity. -/
theorem shufflePivot_eq_of_lt {hash : List Nat → List Nat}
    {seed : List Nat} {round count : Nat}
    (h : shufflePivotRaw hash seed round < count) :
    shufflePivot hash seed round count = shufflePivotRaw hash seed round :=
  Nat.mod_eq_of_lt h

/-- phase0:1206. A positive `index_count` that does not bound the raw
uint64 makes omitting `%` unequal to the archived pivot. -/
theorem shufflePivot_ne_raw_of_le {hash : List Nat → List Nat}
    {seed : List Nat} {round count : Nat}
    (hcount : 0 < count)
    (hle : count ≤ shufflePivotRaw hash seed round) :
    shufflePivot hash seed round count ≠
      shufflePivotRaw hash seed round := by
  intro h
  have hlt : shufflePivot hash seed round count < count :=
    shufflePivot_lt hcount
  rw [h] at hlt
  exact Nat.not_lt.mpr hle hlt

/-- Concrete `Bytes32` whose first eight bytes are not a palindrome. -/
def samplePivotDigest : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0] ++ List.replicate 24 0

def samplePivotHash (_data : List Nat) : List Nat :=
  samplePivotDigest

theorem samplePivotDigest_length : samplePivotDigest.length = 32 := by
  simp [samplePivotDigest]

theorem samplePivotHash_like : Hash32Like samplePivotHash :=
  { length := fun _ => by
      simp [samplePivotHash, samplePivotDigest, HASH32_BYTES]
    bounded := fun _ b hb => by
      simp [samplePivotHash] at hb
      revert b hb
      decide }

theorem samplePivotRaw_eq :
    shufflePivotRaw samplePivotHash [] 0 = 1 := by
  simp [shufflePivotRaw, samplePivotHash, samplePivotDigest, uintFromBytes]

theorem shufflePivot_uses_le_not_be :
    shufflePivot samplePivotHash [] 0 8 ≠
      shufflePivotBe samplePivotHash [] 0 8 := by
  have hbe : shufflePivotRawBe samplePivotHash [] 0 = 2 ^ 56 := by
    simp [shufflePivotRawBe, samplePivotHash, samplePivotDigest, uintFromBytes]
  simp [shufflePivot, shufflePivotBe, samplePivotRaw_eq, hbe]

/-- phase0:1210 `position = max(indices[i], flip)`. -/
def shufflePosition (idx flip : Nat) : Nat :=
  max idx flip

theorem shufflePosition_ge_idx (idx flip : Nat) :
    idx ≤ shufflePosition idx flip :=
  Nat.le_max_left _ _

theorem shufflePosition_ge_flip (idx flip : Nat) :
    flip ≤ shufflePosition idx flip :=
  Nat.le_max_right _ _

/-- phase0:1217 `(position % 256) // 8`. -/
def shuffleBitByteIndex (position : Nat) : Nat :=
  (position % 256) / 8

/-- phase0:1218 `position % 8`. -/
def shuffleBitShift (position : Nat) : Nat :=
  position % 8

theorem shuffleBitByteIndex_lt (position : Nat) :
    shuffleBitByteIndex position < HASH32_BYTES := by
  unfold shuffleBitByteIndex HASH32_BYTES
  have h : position % 256 < 256 := Nat.mod_lt _ (by decide : 0 < 256)
  exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 8)).mpr h

theorem shuffleBitShift_lt (position : Nat) :
    shuffleBitShift position < 8 :=
  Nat.mod_lt _ (by decide : 0 < 8)

/-- A mutant that indexes the bit by the loop `i` instead of `position`. -/
theorem shuffle_bit_uses_position_not_index :
    shuffleBitByteIndex (shufflePosition 0 8) ≠ shuffleBitByteIndex 0 := by
  decide

theorem shuffle_shift_uses_position_not_index :
    shuffleBitShift (shufflePosition 1 8) ≠ shuffleBitShift 1 := by
  decide

/-- phase0:1217-1218 `bit = (byte_val >> (position % 8)) % 2`. -/
def shuffleBitOf (source : List Nat) (position : Nat) : Nat :=
  (((source[shuffleBitByteIndex position]?).getD 0) >>> shuffleBitShift position) % 2

theorem shuffleBitOf_lt (source : List Nat) (position : Nat) :
    shuffleBitOf source position < 2 :=
  Nat.mod_lt _ (by decide : 0 < 2)

theorem shuffleBitOf_is_get {hash : List Nat → List Nat}
    (hh : Hash32Like hash) (data : List Nat) (position : Nat) :
    shuffleBitOf (hash data) position =
      (((hash data)[shuffleBitByteIndex position]'(by
          rw [hh.length]
          exact shuffleBitByteIndex_lt position)) >>>
        shuffleBitShift position) % 2 := by
  unfold shuffleBitOf
  have hi : shuffleBitByteIndex position < (hash data).length := by
    rw [hh.length]
    exact shuffleBitByteIndex_lt position
  rw [List.getElem?_eq_getElem hi, Option.getD_some]

/-- phase0:1219 `indices[i] = flip if bit else indices[i]`. Bit 0 keeps. -/
def shuffleSwapOrNot (idx flip bit : Nat) : Nat :=
  if bit % 2 = 1 then flip else idx

/-- Mutant: swap when the bit is 0. -/
def shuffleSwapOrNotOnZero (idx flip bit : Nat) : Nat :=
  if bit % 2 = 0 then flip else idx

theorem shuffleSwapOrNot_zero (idx flip : Nat) :
    shuffleSwapOrNot idx flip 0 = idx :=
  rfl

theorem shuffleSwapOrNot_one (idx flip : Nat) :
    shuffleSwapOrNot idx flip 1 = flip :=
  rfl

theorem shuffleSwapOrNot_or (idx flip bit : Nat) :
    shuffleSwapOrNot idx flip bit = idx ∨
      shuffleSwapOrNot idx flip bit = flip := by
  unfold shuffleSwapOrNot
  split <;> simp

theorem shuffle_swap_is_not_on_zero :
    shuffleSwapOrNot 3 5 1 ≠ shuffleSwapOrNotOnZero 3 5 1 := by
  decide

/-- phase0:1208-1219 one inner-loop update of `indices[i]`.
SHA256 stays a parameter; the final permutation is not claimed. -/
def shuffleStep (hash : List Nat → List Nat) (seed : List Nat)
    (round count idx : Nat) : Nat :=
  let pivot := shufflePivot hash seed round count
  let flip := shuffleFlip pivot count idx
  let position := shufflePosition idx flip
  let source := hash (shuffleBucketPreimage seed round (shuffleBucket position))
  let bit := shuffleBitOf source position
  shuffleSwapOrNot idx flip bit

theorem shuffleStep_eq_or (hash : List Nat → List Nat)
    (seed : List Nat) (round count idx : Nat) :
    shuffleStep hash seed round count idx = idx ∨
      shuffleStep hash seed round count idx =
        shuffleFlip (shufflePivot hash seed round count) count idx := by
  unfold shuffleStep
  exact shuffleSwapOrNot_or _ _ _

theorem shuffleStep_lt {hash : List Nat → List Nat}
    {seed : List Nat} {round count idx : Nat}
    (hcount : 0 < count) (hidx : idx < count) :
    shuffleStep hash seed round count idx < count := by
  cases shuffleStep_eq_or hash seed round count idx with
  | inl h =>
    rw [h]
    exact hidx
  | inr h =>
    rw [h]
    exact shuffleFlip_lt hcount

/-- phase0:1204 `for current_round in range(SHUFFLE_ROUND_COUNT)`. -/
def shuffleRounds : List Nat :=
  List.range SHUFFLE_ROUND_COUNT

theorem shuffleRounds_length : shuffleRounds.length = 90 := by
  simp [shuffleRounds, SHUFFLE_ROUND_COUNT]

theorem shuffleRounds_ne_empty : shuffleRounds ≠ [] := by
  simp [shuffleRounds, SHUFFLE_ROUND_COUNT]

/-- One array slot through the 90-round walk. Does not claim SHA256
values or the final permutation of the whole list. -/
def shuffleIndexWalk (hash : List Nat → List Nat) (seed : List Nat)
    (count idx : Nat) : Nat :=
  shuffleRounds.foldl (fun acc round => shuffleStep hash seed round count acc) idx

theorem shuffleIndexWalk_zero_rounds (hash : List Nat → List Nat)
    (seed : List Nat) (count idx : Nat) :
    ([] : List Nat).foldl
      (fun acc round => shuffleStep hash seed round count acc) idx = idx :=
  rfl

theorem foldl_shuffleStep_lt {hash : List Nat → List Nat}
    {seed : List Nat} {count idx : Nat} (rounds : List Nat)
    (hcount : 0 < count) (hidx : idx < count) :
    rounds.foldl (fun acc round => shuffleStep hash seed round count acc) idx
      < count := by
  induction rounds generalizing idx with
  | nil => exact hidx
  | cons _r rs ih =>
    exact ih (shuffleStep_lt (hash := hash) (seed := seed) hcount hidx)

theorem shuffleIndexWalk_lt {hash : List Nat → List Nat}
    {seed : List Nat} {count idx : Nat}
    (hcount : 0 < count) (hidx : idx < count) :
    shuffleIndexWalk hash seed count idx < count :=
  foldl_shuffleStep_lt (rounds := shuffleRounds) hcount hidx

/-- phase0:1210 `max` is commutative, so a value and its flip share
`position`. -/
theorem shufflePosition_comm (idx flip : Nat) :
    shufflePosition idx flip = shufflePosition flip idx :=
  Nat.max_comm idx flip

theorem shuffleFlip_shares_position {pivot count idx : Nat}
    (hcount : 0 < count) (hidx : idx < count) :
    shufflePosition idx (shuffleFlip pivot count idx) =
      shufflePosition (shuffleFlip pivot count idx)
        (shuffleFlip pivot count (shuffleFlip pivot count idx)) := by
  rw [shuffleFlip_involutive hcount hidx, shufflePosition_comm]

theorem shuffleFlip_shares_bit_index {pivot count idx : Nat}
    (hcount : 0 < count) (hidx : idx < count) :
    shuffleBitByteIndex (shufflePosition idx (shuffleFlip pivot count idx)) =
      shuffleBitByteIndex (shufflePosition (shuffleFlip pivot count idx)
        (shuffleFlip pivot count (shuffleFlip pivot count idx))) := by
  rw [shuffleFlip_shares_position hcount hidx]

theorem shuffleFlip_sample_shares_position :
    shufflePosition 1 (shuffleFlip 3 8 1) =
      shufflePosition 2 (shuffleFlip 3 8 2) := by
  decide

theorem shuffleFlip_inj {pivot count v w : Nat}
    (hcount : 0 < count) (hv : v < count) (hw : w < count)
    (h : shuffleFlip pivot count v = shuffleFlip pivot count w) : v = w := by
  have := congrArg (shuffleFlip pivot count) h
  rw [shuffleFlip_involutive hcount hv, shuffleFlip_involutive hcount hw] at this
  exact this

theorem shuffleStep_eq (hash : List Nat → List Nat) (seed : List Nat)
    (round count idx : Nat) :
    shuffleStep hash seed round count idx =
      shuffleSwapOrNot idx
        (shuffleFlip (shufflePivot hash seed round count) count idx)
        (shuffleBitOf
          (hash (shuffleBucketPreimage seed round
            (shuffleBucket (shufflePosition idx
              (shuffleFlip (shufflePivot hash seed round count) count idx)))))
          (shufflePosition idx
            (shuffleFlip (shufflePivot hash seed round count) count idx))) := by
  rfl

theorem shuffleStep_pair {hash : List Nat → List Nat}
    {seed : List Nat} {round count idx : Nat}
    (hcount : 0 < count) (hidx : idx < count) :
    (shuffleStep hash seed round count idx = idx ∧
        shuffleStep hash seed round count
          (shuffleFlip (shufflePivot hash seed round count) count idx) =
          shuffleFlip (shufflePivot hash seed round count) count idx) ∨
      (shuffleStep hash seed round count idx =
          shuffleFlip (shufflePivot hash seed round count) count idx ∧
        shuffleStep hash seed round count
          (shuffleFlip (shufflePivot hash seed round count) count idx) = idx) := by
  let p := shufflePivot hash seed round count
  let f := shuffleFlip p count idx
  have hinv : shuffleFlip p count f = idx :=
    shuffleFlip_involutive (pivot := p) hcount hidx
  have hidx_eq : shuffleStep hash seed round count idx =
      shuffleSwapOrNot idx f
        (shuffleBitOf
          (hash (shuffleBucketPreimage seed round
            (shuffleBucket (shufflePosition idx f))))
          (shufflePosition idx f)) := by
    simpa [p, f] using shuffleStep_eq hash seed round count idx
  have hflip_eq : shuffleStep hash seed round count f =
      shuffleSwapOrNot f idx
        (shuffleBitOf
          (hash (shuffleBucketPreimage seed round
            (shuffleBucket (shufflePosition idx f))))
          (shufflePosition idx f)) := by
    simpa [p, f, hinv, shufflePosition_comm] using
      shuffleStep_eq hash seed round count f
  set bit :=
    shuffleBitOf
      (hash (shuffleBucketPreimage seed round
        (shuffleBucket (shufflePosition idx f))))
      (shufflePosition idx f)
  by_cases hbit : bit % 2 = 1
  · refine Or.inr ⟨?_, ?_⟩
    · rw [hidx_eq]
      simp [shuffleSwapOrNot, hbit, p, f]
    · rw [hflip_eq]
      simp [shuffleSwapOrNot, hbit, f]
  · refine Or.inl ⟨?_, ?_⟩
    · rw [hidx_eq]
      simp [shuffleSwapOrNot, hbit, f]
    · rw [hflip_eq]
      simp [shuffleSwapOrNot, hbit, p, f]

theorem shuffleStep_inj {hash : List Nat → List Nat}
    {seed : List Nat} {round count v w : Nat}
    (hcount : 0 < count) (hv : v < count) (hw : w < count)
    (heq : shuffleStep hash seed round count v =
      shuffleStep hash seed round count w) : v = w := by
  have hpairv := shuffleStep_pair (hash := hash) (seed := seed)
    (round := round) hcount hv
  have hpairw := shuffleStep_pair (hash := hash) (seed := seed)
    (round := round) hcount hw
  cases hpairv with
  | inl hkeepv =>
    cases hpairw with
    | inl hkeepw =>
      exact hkeepv.1.symm.trans (heq.trans hkeepw.1)
    | inr hswapw =>
      have hvfw : v = shuffleFlip (shufflePivot hash seed round count) count w :=
        hkeepv.1.symm.trans (heq.trans hswapw.1)
      have hfvw :
          shuffleFlip (shufflePivot hash seed round count) count v = w := by
        have h :=
          congrArg (shuffleFlip (shufflePivot hash seed round count) count) hvfw
        simpa [shuffleFlip_involutive hcount hw] using h
      have hstepw : shuffleStep hash seed round count w = w := by
        simpa [hfvw] using hkeepv.2
      exact hkeepv.1.symm.trans (heq.trans hstepw)
  | inr hswapv =>
    cases hpairw with
    | inl hkeepw =>
      have hwfv : w = shuffleFlip (shufflePivot hash seed round count) count v :=
        hkeepw.1.symm.trans (heq.symm.trans hswapv.1)
      have hfwv :
          shuffleFlip (shufflePivot hash seed round count) count w = v := by
        have h :=
          congrArg (shuffleFlip (shufflePivot hash seed round count) count) hwfv
        simpa [shuffleFlip_involutive hcount hv] using h
      have hstepv : shuffleStep hash seed round count v = v := by
        simpa [hfwv] using hkeepw.2
      exact hstepv.symm.trans (heq.trans hkeepw.1)
    | inr hswapw =>
      exact shuffleFlip_inj hcount hv hw (hswapv.1.symm.trans (heq.trans hswapw.1))

/-- Mutant: index the bit by `idx` instead of `position = max(idx, flip)`. -/
def shuffleStepAtIndex (hash : List Nat → List Nat) (seed : List Nat)
    (round count idx : Nat) : Nat :=
  let pivot := shufflePivot hash seed round count
  let flip := shuffleFlip pivot count idx
  let source := hash (shuffleBucketPreimage seed round (shuffleBucket idx))
  let bit := shuffleBitOf source idx
  shuffleSwapOrNot idx flip bit

/-- Digest whose LE take-8 is 3 and whose bits at offsets 1 and 2 differ. -/
def samplePairDigest : List Nat :=
  [3, 0, 0, 0, 0, 0, 0, 0] ++ List.replicate 24 0

def samplePairHash (_data : List Nat) : List Nat :=
  samplePairDigest

theorem samplePairDigest_length : samplePairDigest.length = 32 := by
  simp [samplePairDigest]

theorem samplePairHash_like : Hash32Like samplePairHash :=
  { length := fun _ => by
      simp [samplePairHash, samplePairDigest, HASH32_BYTES]
    bounded := fun _ b hb => by
      simp [samplePairHash] at hb
      revert b hb
      decide }

theorem shuffleStep_partners_distinct :
    shuffleStep samplePairHash [] 0 8 1 ≠
      shuffleStep samplePairHash [] 0 8 2 := by
  decide

theorem shuffleStep_at_index_collides :
    shuffleStepAtIndex samplePairHash [] 0 8 1 =
      shuffleStepAtIndex samplePairHash [] 0 8 2 ∧ 1 ≠ 2 := by
  decide

/-- phase0:1208-1219 one inner-loop pass is `map` of `shuffleStep`. -/
def shuffleRoundApply (hash : List Nat → List Nat) (seed : List Nat)
    (round count : Nat) (perm : List Nat) : List Nat :=
  perm.map (fun v => shuffleStep hash seed round count v)

theorem shuffleRoundApply_length (hash : List Nat → List Nat)
    (seed : List Nat) (round count : Nat) (perm : List Nat) :
    (shuffleRoundApply hash seed round count perm).length = perm.length :=
  List.length_map _

theorem identityPerm_nodup (n : Nat) : (identityPerm n).Nodup :=
  (List.nodup_range : (List.range n).Nodup)

theorem identityPerm_lt {n : Nat} (v : Nat) (h : v ∈ identityPerm n) : v < n :=
  List.mem_range.mp h

theorem shuffleRoundApply_lt {hash : List Nat → List Nat}
    {seed : List Nat} {round count : Nat} {perm : List Nat}
    (hcount : 0 < count) (hlt : ∀ v ∈ perm, v < count) :
    ∀ v ∈ shuffleRoundApply hash seed round count perm, v < count := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  exact shuffleStep_lt (hash := hash) (seed := seed) hcount (hlt w hw)

theorem shuffleRoundApply_nodup {hash : List Nat → List Nat}
    {seed : List Nat} {round count : Nat} {perm : List Nat}
    (hcount : 0 < count) (hlt : ∀ v ∈ perm, v < count)
    (hnodup : perm.Nodup) :
    (shuffleRoundApply hash seed round count perm).Nodup :=
  nodup_map_on hnodup fun a ha b hb heq =>
    shuffleStep_inj (hash := hash) (seed := seed) (round := round)
      hcount (hlt a ha) (hlt b hb) heq

theorem shuffleRoundApply_identity_nodup {hash : List Nat → List Nat}
    {seed : List Nat} {round n : Nat} (hn : 0 < n) :
    (shuffleRoundApply hash seed round n (identityPerm n)).Nodup :=
  shuffleRoundApply_nodup hn (fun v hv => identityPerm_lt v hv) (identityPerm_nodup n)

/-- phase0:1204-1220 the 90-round walk of the whole list. Values stay
uninterpreted; Nodup / length are derived from the transitions. -/
def shufflePermutation (hash : List Nat → List Nat) (seed : List Nat)
    (n : Nat) : List Nat :=
  shuffleRounds.foldl
    (fun perm round => shuffleRoundApply hash seed round n perm)
    (identityPerm n)

theorem foldl_shuffleRoundApply_length {hash : List Nat → List Nat}
    {seed : List Nat} {n : Nat} (rounds : List Nat) (perm : List Nat) :
    (rounds.foldl (fun p r => shuffleRoundApply hash seed r n p) perm).length =
      perm.length := by
  induction rounds generalizing perm with
  | nil => rfl
  | cons _r rs ih =>
    rw [List.foldl_cons, ih, shuffleRoundApply_length]

theorem foldl_shuffleRoundApply_lt {hash : List Nat → List Nat}
    {seed : List Nat} {n : Nat} (rounds : List Nat) {perm : List Nat}
    (hn : 0 < n) (hlt : ∀ v ∈ perm, v < n) :
    ∀ v ∈ rounds.foldl (fun p r => shuffleRoundApply hash seed r n p) perm,
      v < n := by
  induction rounds generalizing perm with
  | nil => exact hlt
  | cons _r rs ih =>
    exact ih (shuffleRoundApply_lt (hash := hash) (seed := seed) hn hlt)

theorem foldl_shuffleRoundApply_nodup {hash : List Nat → List Nat}
    {seed : List Nat} {n : Nat} (rounds : List Nat) {perm : List Nat}
    (hn : 0 < n) (hlt : ∀ v ∈ perm, v < n) (hnodup : perm.Nodup) :
    (rounds.foldl (fun p r => shuffleRoundApply hash seed r n p) perm).Nodup := by
  induction rounds generalizing perm with
  | nil => exact hnodup
  | cons _r rs ih =>
    exact ih (shuffleRoundApply_lt (hash := hash) (seed := seed) hn hlt)
      (shuffleRoundApply_nodup (hash := hash) (seed := seed) hn hlt hnodup)

theorem shufflePermutation_length {hash : List Nat → List Nat}
    {seed : List Nat} {n : Nat} :
    (shufflePermutation hash seed n).length = n := by
  simp [shufflePermutation, foldl_shuffleRoundApply_length, identityPerm_length]

theorem shufflePermutation_lt {hash : List Nat → List Nat}
    {seed : List Nat} {n : Nat} (hn : 0 < n) :
    ∀ v ∈ shufflePermutation hash seed n, v < n :=
  foldl_shuffleRoundApply_lt shuffleRounds hn fun v hv => identityPerm_lt v hv

theorem shufflePermutation_nodup {hash : List Nat → List Nat}
    {seed : List Nat} {n : Nat} (hn : 0 < n) :
    (shufflePermutation hash seed n).Nodup :=
  foldl_shuffleRoundApply_nodup shuffleRounds hn
    (fun v hv => identityPerm_lt v hv) (identityPerm_nodup n)

theorem shufflePermutation_eq_nil {hash : List Nat → List Nat}
    {seed : List Nat} :
    shufflePermutation hash seed 0 = [] :=
  List.eq_nil_of_length_eq_zero
    (shufflePermutation_length (hash := hash) (seed := seed) (n := 0))

theorem shufflePermutation_nodup_all {hash : List Nat → List Nat}
    {seed : List Nat} {n : Nat} :
    (shufflePermutation hash seed n).Nodup := by
  cases n with
  | zero =>
    simp [shufflePermutation_eq_nil]
  | succ n =>
    exact shufflePermutation_nodup (Nat.succ_pos _)

/-- phase0:1203 `range(index_count)` minus one occupant has length `n-1`. -/
theorem length_range_filter_ne {n a : Nat} (ha : a < n) :
    ((List.range n).filter (fun x => decide (x ≠ a))).length = n - 1 := by
  induction n generalizing a with
  | zero =>
    exact absurd ha (Nat.not_lt_zero _)
  | succ m ih =>
    rw [List.range_succ, List.filter_append]
    by_cases hlt : a < m
    · have hne : m ≠ a := Nat.ne_of_gt hlt
      have hlast : ([m].filter (fun x => decide (x ≠ a))) = [m] := by
        simp [List.filter, hne]
      rw [hlast, List.length_append, List.length_singleton, ih hlt]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.zero_lt_of_lt hlt))
    · have heq : a = m :=
        Nat.le_antisymm (Nat.le_of_lt_succ ha) (Nat.le_of_not_gt hlt)
      rw [heq]
      have hlast : ([m].filter (fun x => decide (x ≠ m))) = [] := by
        simp [List.filter]
      have hpref :
          (List.range m).filter (fun x => decide (x ≠ m)) = List.range m := by
        refine List.filter_eq_self.mpr ?_
        intro x hx
        exact decide_eq_true (Nat.ne_of_lt (List.mem_range.mp hx))
      rw [hlast, hpref, List.length_append, List.length_nil, List.length_range,
        Nat.add_zero]
      exact (Nat.add_sub_cancel m 1).symm

/-- Membership in the 90-round list is exactly `{0, …, n-1}`, derived
from Nodup + length + the bounded image. SHA256 values stay a parameter. -/
theorem shufflePermutation_mem {hash : List Nat → List Nat}
    {seed : List Nat} {n a : Nat} :
    a ∈ shufflePermutation hash seed n ↔ a < n := by
  cases n with
  | zero =>
    simp [shufflePermutation_eq_nil]
  | succ n =>
    have hn : 0 < n + 1 := Nat.succ_pos _
    constructor
    · exact fun ha => shufflePermutation_lt hn a ha
    · intro ha
      by_contra hmiss
      have hsub :
          shufflePermutation hash seed (n + 1) ⊆
            (List.range (n + 1)).filter (fun x => decide (x ≠ a)) := by
        intro x hx
        refine List.mem_filter.mpr
          ⟨List.mem_range.mpr (shufflePermutation_lt hn x hx), ?_⟩
        exact decide_eq_true fun hxa => hmiss (hxa ▸ hx)
      have hsp :
          List.Subperm (shufflePermutation hash seed (n + 1))
            ((List.range (n + 1)).filter (fun x => decide (x ≠ a))) :=
        List.subperm_of_subset (shufflePermutation_nodup hn) hsub
      have hle := List.Subperm.length_le hsp
      have hfl :
          ((List.range (n + 1)).filter (fun x => decide (x ≠ a))).length = n :=
        length_range_filter_ne ha
      have hlen :
          (shufflePermutation hash seed (n + 1)).length = n + 1 :=
        shufflePermutation_length
      omega

/-- phase0:1197-1220 the archived walk is a permutation of
`range(index_count)`. Values remain uninterpreted. -/
theorem shufflePermutation_perm {hash : List Nat → List Nat}
    {seed : List Nat} {n : Nat} :
    List.Perm (shufflePermutation hash seed n) (identityPerm n) := by
  refine (List.perm_ext_iff_of_nodup
      (shufflePermutation_nodup_all (hash := hash) (seed := seed))
      (identityPerm_nodup n)).mpr ?_
  intro a
  simp [identityPerm, List.mem_range, shufflePermutation_mem]

/-- A value outside `{0, …, n-1}` is not a permutation of the identity. -/
theorem out_of_range_not_identity_perm :
    ¬ List.Perm [0, 2] (identityPerm 2) := by
  intro h
  have hmem : 2 ∈ identityPerm 2 :=
    (List.Perm.mem_iff h).mp (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  exact Nat.lt_irrefl _ (identityPerm_lt 2 hmem)

theorem short_not_identity_perm :
    ¬ List.Perm [0] (identityPerm 2) := by
  intro h
  have := List.Perm.length_eq h
  exact (by decide : ¬ (1 = 2)) this

/-- Mapping each round independently commutes with `get`. -/
theorem foldl_map_getElem? (f : Nat → Nat → Nat) (rounds start : List Nat)
    (i : Nat) :
    (rounds.foldl (fun p r => p.map (f r)) start)[i]? =
      start[i]?.map (fun x => rounds.foldl (fun acc r => f r acc) x) := by
  induction rounds generalizing start with
  | nil =>
    simp
  | cons r rs ih =>
    rw [List.foldl_cons, ih, List.getElem?_map]
    cases h : start[i]? with
    | none => simp
    | some _ => simp [List.foldl]

/-- phase0:1231 `return compute_shuffled_permutation(...)[index]`.
The slot at `index` is the 90-round walk of that slot's initial value. -/
theorem shuffledIndexOf_walk {hash : List Nat → List Nat}
    {seed : List Nat} {n i : Nat} (hi : i < n) :
    shuffledIndexOf (shufflePermutation hash seed n) i =
      some (shuffleIndexWalk hash seed n i) := by
  unfold shuffledIndexOf shufflePermutation shuffleIndexWalk shuffleRoundApply
  have h := foldl_map_getElem? (fun r v => shuffleStep hash seed r n v)
    shuffleRounds (identityPerm n) i
  rw [identityPerm_get hi] at h
  simpa using h

/-- phase0:1213-1215 `sha256(seed + round_bytes + uint_to_bytes(Uint32(position_bucket)))`. -/
def sourceByBucket (hash : List Nat → List Nat) (seed : List Nat)
    (round bucket : Nat) : List Nat :=
  hash (shuffleBucketPreimage seed round bucket)

theorem sourceByBucket_eq_fresh (hash : List Nat → List Nat)
    (seed : List Nat) (round bucket : Nat) :
    sourceByBucket hash seed round bucket =
      hash (shuffleBucketPreimage seed round bucket) :=
  rfl

/-- phase0:1211 a 256-wide window shares one bucket. -/
theorem shuffleBucket_window_zero :
    shuffleBucket 0 = shuffleBucket 255 := by
  decide

theorem shuffleBucket_next_window :
    shuffleBucket 255 ≠ shuffleBucket 256 := by
  decide

theorem shuffleBucket_256 : shuffleBucket 256 = 1 := by
  decide

/-- phase0:1211 the cache key is `position // 256`, not `position`. -/
theorem cache_key_is_bucket_not_position :
    shuffleBucket 255 ≠ 255 := by
  decide

theorem sourceByBucket_same_window (hash : List Nat → List Nat)
    (seed : List Nat) (round : Nat) :
    sourceByBucket hash seed round (shuffleBucket 0) =
      sourceByBucket hash seed round (shuffleBucket 255) := by
  simp [sourceByBucket, shuffleBucket]

/-- Mutant: hash `Uint32(position)` instead of `Uint32(position // 256)`. -/
def sourceAtPosition (hash : List Nat → List Nat) (seed : List Nat)
    (round position : Nat) : List Nat :=
  hash (seed ++ shuffleRoundBytes round ++ uintToBytes 4 position)

theorem uintToBytes4_256 : uintToBytes 4 256 = [0, 1, 0, 0] := by
  simp [uintToBytes]

theorem source_preimage_uses_bucket (seed : List Nat) :
    shuffleBucketPreimage seed 0 (shuffleBucket 256) ≠
      seed ++ shuffleRoundBytes 0 ++ uintToBytes 4 256 := by
  intro h
  have hsuf :=
    congrArg (fun xs => (xs.drop seed.length).drop 1) h
  simp [shuffleBucketPreimage, shuffleRoundBytes, uintToBytes, shuffleBucket] at hsuf

theorem source_uses_bucket_not_position (hash : List Nat → List Nat)
    (seed : List Nat) :
    sourceByBucket hash seed 0 (shuffleBucket 256) ≠
      sourceAtPosition hash seed 0 256 ∨
        shuffleBucketPreimage seed 0 1 ≠
          seed ++ shuffleRoundBytes 0 ++ uintToBytes 4 256 :=
  Or.inr (source_preimage_uses_bucket seed)

theorem shuffleFlip_shares_bucket {pivot count idx : Nat}
    (hcount : 0 < count) (hidx : idx < count) :
    shuffleBucket (shufflePosition idx (shuffleFlip pivot count idx)) =
      shuffleBucket (shufflePosition (shuffleFlip pivot count idx)
        (shuffleFlip pivot count (shuffleFlip pivot count idx))) := by
  rw [shuffleFlip_shares_position hcount hidx]

/-- phase0:1207-1216 `if position_bucket not in source_by_bucket`. -/
def bucketCacheGet (cache : List (Nat × List Nat)) (bucket : Nat) :
    Option (List Nat) :=
  match cache.find? (fun p => decide (p.1 = bucket)) with
  | some p => some p.2
  | none => none

def sourceCacheStep (hash : List Nat → List Nat) (seed : List Nat)
    (round : Nat) (cache : List (Nat × List Nat)) (bucket : Nat) :
    List Nat × List (Nat × List Nat) :=
  match bucketCacheGet cache bucket with
  | some src => (src, cache)
  | none =>
      let src := hash (shuffleBucketPreimage seed round bucket)
      (src, cache ++ [(bucket, src)])

/-- Stored entries are the hash of their bucket preimage. -/
def BucketCacheOk (hash : List Nat → List Nat) (seed : List Nat)
    (round : Nat) (cache : List (Nat × List Nat)) : Prop :=
  ∀ p ∈ cache, p.2 = hash (shuffleBucketPreimage seed round p.1)

theorem BucketCacheOk_nil (hash : List Nat → List Nat)
    (seed : List Nat) (round : Nat) :
    BucketCacheOk hash seed round [] := by
  intro _p hp
  cases hp

theorem bucketCacheGet_nil (bucket : Nat) :
    bucketCacheGet [] bucket = none := by
  simp [bucketCacheGet]

theorem bucketCacheGet_singleton (bucket : Nat) (src : List Nat) :
    bucketCacheGet [(bucket, src)] bucket = some src := by
  simp [bucketCacheGet]

theorem sourceCacheStep_miss (hash : List Nat → List Nat)
    (seed : List Nat) (round : Nat) (cache : List (Nat × List Nat))
    (bucket : Nat) (hmiss : bucketCacheGet cache bucket = none) :
    (sourceCacheStep hash seed round cache bucket).1 =
      hash (shuffleBucketPreimage seed round bucket) ∧
      (sourceCacheStep hash seed round cache bucket).2 =
        cache ++ [(bucket, hash (shuffleBucketPreimage seed round bucket))] := by
  simp [sourceCacheStep, hmiss]

theorem sourceCacheStep_hit (hash : List Nat → List Nat)
    (seed : List Nat) (round : Nat) (cache : List (Nat × List Nat))
    (bucket : Nat) (src : List Nat)
    (hhit : bucketCacheGet cache bucket = some src) :
    (sourceCacheStep hash seed round cache bucket).1 = src ∧
      (sourceCacheStep hash seed round cache bucket).2 = cache := by
  simp [sourceCacheStep, hhit]

theorem bucketCacheGet_mem {cache : List (Nat × List Nat)}
    {bucket : Nat} {src : List Nat}
    (h : bucketCacheGet cache bucket = some src) :
    ∃ p ∈ cache, p.1 = bucket ∧ p.2 = src := by
  unfold bucketCacheGet at h
  cases hfind : cache.find? (fun p => decide (p.1 = bucket)) with
  | none =>
    simp [hfind] at h
  | some p =>
    simp [hfind] at h
    have hmem := List.mem_of_find?_eq_some hfind
    have hpred := List.find?_some hfind
    exact ⟨p, hmem, of_decide_eq_true hpred, h⟩

theorem bucketCacheGet_ok {hash : List Nat → List Nat}
    {seed : List Nat} {round : Nat} {cache : List (Nat × List Nat)}
    {bucket : Nat} {src : List Nat}
    (hok : BucketCacheOk hash seed round cache)
    (hhit : bucketCacheGet cache bucket = some src) :
    src = hash (shuffleBucketPreimage seed round bucket) := by
  obtain ⟨p, hp, hkey, hval⟩ := bucketCacheGet_mem hhit
  have := hok p hp
  rw [hval.symm, this, hkey]

/-- Under a well-formed cache, a hit or miss returns the fresh digest.
This is the archived insert-if-absent, not an extra SHA256 postulate. -/
theorem sourceCacheStep_eq_fresh {hash : List Nat → List Nat}
    {seed : List Nat} {round : Nat} {cache : List (Nat × List Nat)}
    {bucket : Nat} (hok : BucketCacheOk hash seed round cache) :
    (sourceCacheStep hash seed round cache bucket).1 =
      hash (shuffleBucketPreimage seed round bucket) := by
  cases h : bucketCacheGet cache bucket with
  | none =>
    simp [sourceCacheStep, h]
  | some src =>
    have hsrc := bucketCacheGet_ok hok h
    simp [sourceCacheStep, h, hsrc]

theorem sourceCacheStep_preserves {hash : List Nat → List Nat}
    {seed : List Nat} {round : Nat} {cache : List (Nat × List Nat)}
    {bucket : Nat} (hok : BucketCacheOk hash seed round cache) :
    BucketCacheOk hash seed round
      (sourceCacheStep hash seed round cache bucket).2 := by
  cases h : bucketCacheGet cache bucket with
  | none =>
    intro p hp
    simp [sourceCacheStep, h] at hp
    cases hp with
    | inl hmem =>
      exact hok p hmem
    | inr hpeq =>
      simp [hpeq]
  | some _src =>
    simp [sourceCacheStep, h]
    exact hok

theorem sourceCache_empty_then_hit (hash : List Nat → List Nat)
    (seed : List Nat) (round bucket : Nat) :
    (sourceCacheStep hash seed round [] bucket).1 =
      hash (shuffleBucketPreimage seed round bucket) ∧
      (sourceCacheStep hash seed round
          (sourceCacheStep hash seed round [] bucket).2 bucket).1 =
        (sourceCacheStep hash seed round [] bucket).1 ∧
      (sourceCacheStep hash seed round
          (sourceCacheStep hash seed round [] bucket).2 bucket).2 =
        (sourceCacheStep hash seed round [] bucket).2 := by
  have h1 := sourceCacheStep_miss hash seed round [] bucket
    (bucketCacheGet_nil bucket)
  have hhit :
      bucketCacheGet (sourceCacheStep hash seed round [] bucket).2 bucket =
        some (sourceCacheStep hash seed round [] bucket).1 := by
    rw [h1.2, h1.1, List.nil_append]
    exact bucketCacheGet_singleton bucket _
  have h2 := sourceCacheStep_hit hash seed round
    (sourceCacheStep hash seed round [] bucket).2 bucket
    (sourceCacheStep hash seed round [] bucket).1 hhit
  exact ⟨h1.1, h2.1, h2.2⟩

/-- phase0:1216 `source = source_by_bucket[position_bucket]` is the
fresh digest of that bucket under a well-formed cache. -/
theorem shuffleStep_source_eq_cache {hash : List Nat → List Nat}
    {seed : List Nat} {round count idx : Nat}
    {cache : List (Nat × List Nat)}
    (hok : BucketCacheOk hash seed round cache) :
    let pivot := shufflePivot hash seed round count
    let flip := shuffleFlip pivot count idx
    let position := shufflePosition idx flip
    let bucket := shuffleBucket position
    (sourceCacheStep hash seed round cache bucket).1 =
      hash (shuffleBucketPreimage seed round bucket) :=
  sourceCacheStep_eq_fresh hok

/--
Archived `compute_shuffled_permutation` phase0:1218: `position % 8`
equals the intra-window offset because `8 ∣ 256`.
-/
theorem shuffleBitShift_eq_window (position : Nat) :
    shuffleBitShift position = (position % 256) % 8 := by
  unfold shuffleBitShift
  have hsplit : position % 256 + 256 * (position / 256) = position :=
    Nat.mod_add_div position 256
  have h8 : 256 % 8 = 0 := rfl
  calc
    position % 8
        = (position % 256 + 256 * (position / 256)) % 8 := by rw [hsplit]
      _ = ((position % 256) % 8 + (256 * (position / 256)) % 8) % 8 :=
        Nat.add_mod _ _ 8
      _ = ((position % 256) % 8 + (256 % 8 * ((position / 256) % 8)) % 8) % 8 := by
        rw [Nat.mul_mod]
      _ = ((position % 256) % 8 + 0) % 8 := by simp [h8]
      _ = (position % 256) % 8 := by simp

/--
Archived `compute_shuffled_permutation` phase0:1217-1218:
`position % 256 = 8 * ((position % 256) // 8) + (position % 8)`.
-/
theorem shuffleBit_decomp (position : Nat) :
    position % 256 =
      8 * shuffleBitByteIndex position + shuffleBitShift position := by
  unfold shuffleBitByteIndex
  rw [shuffleBitShift_eq_window]
  exact (Nat.div_add_mod (position % 256) 8).symm

/--
Archived `compute_shuffled_permutation` phase0:1213-1214: same
`position // 256` means the same cached source.
-/
theorem same_bucket_same_source (hash : List Nat → List Nat)
    (seed : List Nat) (round p q : Nat)
    (h : shuffleBucket p = shuffleBucket q) :
    sourceByBucket hash seed round (shuffleBucket p) =
      sourceByBucket hash seed round (shuffleBucket q) := by
  rw [h]

/-- Same 256-window, different source byte: positions 0 and 8. -/
theorem same_bucket_distinct_byte :
    shuffleBucket 0 = shuffleBucket 8 ∧
      shuffleBitByteIndex 0 ≠ shuffleBitByteIndex 8 := by
  decide

/-- Same source byte, different shift: positions 0 and 1. -/
theorem same_bucket_distinct_shift :
    shuffleBucket 0 = shuffleBucket 1 ∧
      shuffleBitByteIndex 0 = shuffleBitByteIndex 1 ∧
      shuffleBitShift 0 ≠ shuffleBitShift 1 := by
  decide

/--
Archived `compute_shuffled_permutation` phase0:1211 / 1217-1218:
the first 256-window spans byte 0 shift 0 through byte 31 shift 7.
-/
theorem same_bucket_window_offsets :
    shuffleBucket 0 = shuffleBucket 255 ∧
      shuffleBitByteIndex 0 = 0 ∧
      shuffleBitByteIndex 255 = 31 ∧
      shuffleBitShift 0 = 0 ∧
      shuffleBitShift 255 = 7 := by
  decide

/-- Mutant: index the byte by `position // 8`, not `(position % 256) // 8`. -/
def shuffleBitByteIndexRaw (position : Nat) : Nat :=
  position / 8

theorem bit_byte_uses_mod_256 :
    shuffleBitByteIndex 256 ≠ shuffleBitByteIndexRaw 256 := by
  decide

theorem bit_byte_raw_not_in_hash32 :
    ¬ shuffleBitByteIndexRaw 256 < HASH32_BYTES := by
  decide

/-- Mutant: one bit per bucket, ignoring the intra-window offset. -/
def shuffleBitOfBucket (source : List Nat) (_position : Nat) : Nat :=
  ((source[0]?).getD 0) % 2

/--
Archived `compute_shuffled_permutation` phase0:1217-1218: same-bucket
strangers share a source but not necessarily the swap bit. Positions
0 and 8 both sit in bucket 0 and read distinct bytes of
`samplePairDigest`.
-/
theorem shared_source_bits_differ :
    shuffleBitOf samplePairDigest 0 ≠ shuffleBitOf samplePairDigest 8 := by
  decide

theorem bit_uses_offset_not_bucket_only :
    shuffleBitOf samplePairDigest 8 ≠
      shuffleBitOfBucket samplePairDigest 8 := by
  decide

/-- Under `Hash32Like`, every intra-window byte index exists on the digest. -/
theorem shared_source_byte_defined {hash : List Nat → List Nat}
    (hh : Hash32Like hash) (data : List Nat) (position : Nat) :
    (hash data)[shuffleBitByteIndex position]? ≠ none := by
  have hi : shuffleBitByteIndex position < (hash data).length := by
    rw [hh.length]
    exact shuffleBitByteIndex_lt position
  rw [List.getElem?_eq_getElem hi]
  exact Option.some_ne_none _

/--
Under `Hash32Like`, a cached bucket digest supplies every intra-window
byte index of every position that shares that bucket. SHA256 *values*
stay uninterpreted.
-/
theorem shared_source_offsets_defined {hash : List Nat → List Nat}
    (hh : Hash32Like hash) (seed : List Nat) (round p q : Nat)
    (hb : shuffleBucket p = shuffleBucket q) :
    (sourceByBucket hash seed round (shuffleBucket p))[shuffleBitByteIndex p]? ≠ none ∧
      (sourceByBucket hash seed round (shuffleBucket p))[shuffleBitByteIndex q]? ≠ none := by
  have hsrc :
      sourceByBucket hash seed round (shuffleBucket p) =
        hash (shuffleBucketPreimage seed round (shuffleBucket p)) :=
    rfl
  refine ⟨?_, ?_⟩
  · rw [hsrc]
    exact shared_source_byte_defined hh _ p
  · have hsrcq :
        sourceByBucket hash seed round (shuffleBucket p) =
          hash (shuffleBucketPreimage seed round (shuffleBucket q)) := by
      rw [same_bucket_same_source hash seed round p q hb]
      rfl
    rw [hsrcq]
    exact shared_source_byte_defined hh _ q

/--
Archived `compute_shuffled_permutation` phase0:1213-1219: the
swap-or-not bit is `shuffleBitOf` of the cached `source_by_bucket`
digest at `position = max(idx, flip)`.
-/
def shuffleStepBit (hash : List Nat → List Nat) (seed : List Nat)
    (round count idx : Nat) : Nat :=
  shuffleBitOf
    (sourceByBucket hash seed round
      (shuffleBucket (shufflePosition idx
        (shuffleFlip (shufflePivot hash seed round count) count idx))))
    (shufflePosition idx
      (shuffleFlip (shufflePivot hash seed round count) count idx))

/-- The inlined `hash(preimage(bucket))` of `shuffleStep` is the cache. -/
theorem shuffleStep_source_eq_sourceByBucket (hash : List Nat → List Nat)
    (seed : List Nat) (round count idx : Nat) :
    hash (shuffleBucketPreimage seed round
        (shuffleBucket (shufflePosition idx
          (shuffleFlip (shufflePivot hash seed round count) count idx)))) =
      sourceByBucket hash seed round
        (shuffleBucket (shufflePosition idx
          (shuffleFlip (shufflePivot hash seed round count) count idx))) :=
  rfl

theorem shuffleStep_uses_cached_bit (hash : List Nat → List Nat)
    (seed : List Nat) (round count idx : Nat) :
    shuffleStep hash seed round count idx =
      shuffleSwapOrNot idx
        (shuffleFlip (shufflePivot hash seed round count) count idx)
        (shuffleStepBit hash seed round count idx) := by
  unfold shuffleStep shuffleStepBit sourceByBucket
  rfl

/-- Same-bucket positions read the bit of `p` from `q`'s cached digest. -/
theorem same_bucket_bit_source (hash : List Nat → List Nat)
    (seed : List Nat) (round p q : Nat)
    (h : shuffleBucket p = shuffleBucket q) :
    shuffleBitOf (sourceByBucket hash seed round (shuffleBucket p)) p =
      shuffleBitOf (sourceByBucket hash seed round (shuffleBucket q)) p := by
  rw [same_bucket_same_source hash seed round p q h]

/--
Archived `compute_shuffled_permutation` phase0:1210 / 1213-1219:
idx and flip share `position`, hence the same cached source.
-/
theorem partners_share_cached_source {hash : List Nat → List Nat}
    {seed : List Nat} {round count idx : Nat}
    (hcount : 0 < count) (hidx : idx < count) :
    sourceByBucket hash seed round
        (shuffleBucket (shufflePosition idx
          (shuffleFlip (shufflePivot hash seed round count) count idx))) =
      sourceByBucket hash seed round
        (shuffleBucket (shufflePosition
          (shuffleFlip (shufflePivot hash seed round count) count idx)
          (shuffleFlip (shufflePivot hash seed round count) count
            (shuffleFlip (shufflePivot hash seed round count) count idx)))) := by
  rw [shuffleFlip_shares_position hcount hidx]

theorem partners_share_cached_bit {hash : List Nat → List Nat}
    {seed : List Nat} {round count idx : Nat}
    (hcount : 0 < count) (hidx : idx < count) :
    shuffleStepBit hash seed round count idx =
      shuffleStepBit hash seed round count
        (shuffleFlip (shufflePivot hash seed round count) count idx) := by
  unfold shuffleStepBit
  rw [shuffleFlip_involutive (pivot := shufflePivot hash seed round count)
    hcount hidx, shufflePosition_comm]

/-- Mutant: take the swap bit from `hash(Uint32(position))`, not the bucket. -/
def shuffleBitAtPosition (hash : List Nat → List Nat) (seed : List Nat)
    (round position : Nat) : Nat :=
  shuffleBitOf (sourceAtPosition hash seed round position) position

/-- `Hash32Like` dummy that copies preimage byte 1 into digest byte 0.
Bucket `Uint32(1)` and `Uint32(256)` therefore yield distinct bits at
position 256, which reads that byte. SHA256 values stay uninterpreted. -/
def echoByteHash (data : List Nat) : List Nat :=
  ((data[1]?).getD 0 % 256) :: List.replicate 31 0

theorem echoByteHash_like : Hash32Like echoByteHash where
  length := fun _ => by
    simp [echoByteHash, HASH32_BYTES]
  bounded := fun _data b hb => by
    unfold echoByteHash at hb
    cases List.mem_cons.mp hb with
    | inl h =>
      subst h
      exact Nat.mod_lt _ (by decide : 0 < 256)
    | inr h =>
      have hb0 : b = 0 := (List.mem_replicate.mp h).2
      subst hb0
      decide

/-- phase0:1213-1217. Hashing `Uint32(position)` is not the cached bucket. -/
theorem cached_bit_ne_position_bit :
    shuffleBitOf (sourceByBucket echoByteHash [] 0 (shuffleBucket 256)) 256 ≠
      shuffleBitAtPosition echoByteHash [] 0 256 := by
  decide

/-- phase0:1205 / 1214 `uint_to_bytes(Uint8(current_round))`. -/
theorem shuffleRoundBytes_eq (r : Nat) :
    shuffleRoundBytes r = [r % 256] := by
  simp [shuffleRoundBytes, uintToBytes]

theorem shuffleRoundBytes_ne {r r' : Nat} (h : r % 256 ≠ r' % 256) :
    shuffleRoundBytes r ≠ shuffleRoundBytes r' := by
  simp [shuffleRoundBytes_eq]
  exact h

/--
Archived `compute_shuffled_permutation` phase0:1213-1215: the cache
preimage includes `Uint8(current_round)`. Distinct residues give
distinct preimages, so a cache cannot be reused across those rounds.
-/
theorem shuffleBucketPreimage_round_ne (seed : List Nat) (r r' bucket : Nat)
    (h : r % 256 ≠ r' % 256) :
    shuffleBucketPreimage seed r bucket ≠
      shuffleBucketPreimage seed r' bucket := by
  intro heq
  have hdrop := congrArg (fun xs => xs.drop seed.length) heq
  simp [shuffleBucketPreimage, shuffleRoundBytes, uintToBytes] at hdrop
  exact h hdrop

theorem sourceByBucket_rounds_0_1 (seed : List Nat) (bucket : Nat) :
    shuffleBucketPreimage seed 0 bucket ≠
      shuffleBucketPreimage seed 1 bucket :=
  shuffleBucketPreimage_round_ne seed 0 1 bucket (by decide)

/-- Mutant: drop `Uint8(round)` from the source preimage. -/
def sourceByBucketIgnoreRound (hash : List Nat → List Nat) (seed : List Nat)
    (_round bucket : Nat) : List Nat :=
  hash (seed ++ uintToBytes 4 bucket)

theorem source_preimage_uses_round (seed : List Nat) (bucket : Nat) :
    shuffleBucketPreimage seed 1 bucket ≠
      seed ++ uintToBytes 4 bucket := by
  intro h
  have hlen := congrArg List.length h
  simp [shuffleBucketPreimage, shuffleRoundBytes, uintToBytes] at hlen

/-- The archived 90 rounds all sit below 256, so `Uint8` does not wrap. -/
theorem mem_shuffleRounds_lt {r : Nat} (h : r ∈ shuffleRounds) : r < 90 := by
  simpa [shuffleRounds, SHUFFLE_ROUND_COUNT] using h

theorem mem_shuffleRounds_no_wrap {r : Nat} (h : r ∈ shuffleRounds) :
    r % 256 = r :=
  Nat.mod_eq_of_lt (Nat.lt_trans (mem_shuffleRounds_lt h) (by decide : 90 < 256))

theorem shuffleRounds_round_bytes_inj {r r' : Nat}
    (hr : r ∈ shuffleRounds) (hr' : r' ∈ shuffleRounds) (hne : r ≠ r') :
    shuffleRoundBytes r ≠ shuffleRoundBytes r' :=
  shuffleRoundBytes_ne (by
    rw [mem_shuffleRounds_no_wrap hr, mem_shuffleRounds_no_wrap hr']
    exact hne)

/-- phase0:1204 `range(SHUFFLE_ROUND_COUNT)` yields 90 distinct Uint8 encodings. -/
theorem shuffleRounds_map_bytes_nodup :
    (shuffleRounds.map shuffleRoundBytes).Nodup := by
  refine nodup_map_on (by
      simp [shuffleRounds, SHUFFLE_ROUND_COUNT]
      exact (List.nodup_range : (List.range 90).Nodup)) ?_
  intro a ha b hb heq
  have : a % 256 = b % 256 := by
    simpa [shuffleRoundBytes, uintToBytes] using heq
  rw [mem_shuffleRounds_no_wrap ha, mem_shuffleRounds_no_wrap hb] at this
  exact this

/-- Mutant: 256 rounds wrap `Uint8(256)` onto `Uint8(0)`. -/
theorem uint8_round_256_collides_zero :
    shuffleRoundBytes 256 = shuffleRoundBytes 0 := by
  simp [shuffleRoundBytes, uintToBytes]

/-- `Hash32Like` dummy that copies the preimage head (the Uint8 round
when `seed = []`). SHA256 values stay uninterpreted. -/
def echoHeadHash (data : List Nat) : List Nat :=
  ((data.head?).getD 0 % 256) :: List.replicate 31 0

theorem echoHeadHash_like : Hash32Like echoHeadHash where
  length := fun _ => by
    simp [echoHeadHash, HASH32_BYTES]
  bounded := fun _data b hb => by
    unfold echoHeadHash at hb
    cases List.mem_cons.mp hb with
    | inl h =>
      subst h
      exact Nat.mod_lt _ (by decide : 0 < 256)
    | inr h =>
      have hb0 : b = 0 := (List.mem_replicate.mp h).2
      subst hb0
      decide

/-- phase0:1213-1215. Round 0 and round 1 do not share a cached source. -/
theorem sourceByBucket_round_ne_echo :
    sourceByBucket echoHeadHash [] 0 0 ≠
      sourceByBucket echoHeadHash [] 1 0 := by
  decide

/--
Archived `compute_shuffled_permutation` phase0:1207
`source_by_bucket: Dict = {}` at the start of every round.
-/
theorem source_by_bucket_starts_empty (hash : List Nat → List Nat)
    (seed : List Nat) (round : Nat) :
    BucketCacheOk hash seed round [] :=
  BucketCacheOk_nil hash seed round

theorem each_round_starts_empty (hash : List Nat → List Nat)
    (seed : List Nat) (r r' : Nat) :
    BucketCacheOk hash seed r [] ∧ BucketCacheOk hash seed r' [] :=
  ⟨BucketCacheOk_nil hash seed r, BucketCacheOk_nil hash seed r'⟩

theorem BucketCacheOk_singleton (hash : List Nat → List Nat)
    (seed : List Nat) (round bucket : Nat) :
    BucketCacheOk hash seed round
      [(bucket, hash (shuffleBucketPreimage seed round bucket))] := by
  intro p hp
  have hp' : p = (bucket, hash (shuffleBucketPreimage seed round bucket)) :=
    List.mem_singleton.mp hp
  simp [hp']

/--
If a nonempty cache is well-formed for two rounds, the hash identifies
those two preimages. Transferring the dict is not free.
-/
theorem BucketCacheOk_two_rounds_hash_eq {hash : List Nat → List Nat}
    {seed : List Nat} {r r' : Nat} {cache : List (Nat × List Nat)}
    (hok : BucketCacheOk hash seed r cache)
    (hok' : BucketCacheOk hash seed r' cache)
    {bucket src : _} (hmem : (bucket, src) ∈ cache) :
    hash (shuffleBucketPreimage seed r bucket) =
      hash (shuffleBucketPreimage seed r' bucket) :=
  (hok (bucket, src) hmem).symm.trans (hok' (bucket, src) hmem)

/--
A singleton filled at round `r` is not well-formed at `r'` when the
hash distinguishes the two `Uint8(round)` preimages.
-/
theorem BucketCacheOk_fresh_not_other_round {hash : List Nat → List Nat}
    {seed : List Nat} {r r' bucket : Nat}
    (hne : hash (shuffleBucketPreimage seed r bucket) ≠
      hash (shuffleBucketPreimage seed r' bucket)) :
    ¬ BucketCacheOk hash seed r'
      [(bucket, hash (shuffleBucketPreimage seed r bucket))] := by
  intro hok
  exact hne (hok (bucket, hash (shuffleBucketPreimage seed r bucket))
    (List.mem_cons.mpr (Or.inl rfl)))

theorem BucketCacheOk_echo_round_0_not_1 :
    BucketCacheOk echoHeadHash [] 0
        [(0, sourceByBucket echoHeadHash [] 0 0)] ∧
      ¬ BucketCacheOk echoHeadHash [] 1
        [(0, sourceByBucket echoHeadHash [] 0 0)] := by
  refine ⟨?_, ?_⟩
  · simpa [sourceByBucket] using
      BucketCacheOk_singleton echoHeadHash [] 0 0
  · simpa [sourceByBucket] using
      BucketCacheOk_fresh_not_other_round (hash := echoHeadHash) (seed := [])
        (r := 0) (r' := 1) (bucket := 0) sourceByBucket_round_ne_echo

/--
Mutant: reuse the previous round's dict. A hit returns the stale
round-0 digest instead of hashing `Uint8(1)`.
-/
theorem sourceCacheStep_stale_round_hit :
    (sourceCacheStep echoHeadHash [] 1
        [(0, sourceByBucket echoHeadHash [] 0 0)] 0).1 =
      sourceByBucket echoHeadHash [] 0 0 ∧
      sourceByBucket echoHeadHash [] 0 0 ≠
        sourceByBucket echoHeadHash [] 1 0 := by
  refine ⟨?_, sourceByBucket_round_ne_echo⟩
  exact (sourceCacheStep_hit echoHeadHash [] 1
    [(0, sourceByBucket echoHeadHash [] 0 0)] 0
    (sourceByBucket echoHeadHash [] 0 0)
    (bucketCacheGet_singleton 0 _)).1

/--
Archived `compute_shuffled_permutation` phase0:1207: each `shuffleStep`
hashes that round's preimage, which is the empty-cache insert-if-absent.
No previous-round dict is carried.
-/
theorem shuffleStep_source_eq_empty_cache (hash : List Nat → List Nat)
    (seed : List Nat) (round count idx : Nat) :
    hash (shuffleBucketPreimage seed round
        (shuffleBucket (shufflePosition idx
          (shuffleFlip (shufflePivot hash seed round count) count idx)))) =
      (sourceCacheStep hash seed round []
        (shuffleBucket (shufflePosition idx
          (shuffleFlip (shufflePivot hash seed round count) count idx)))).1 :=
  (sourceCacheStep_miss hash seed round [] _
    (bucketCacheGet_nil _)).1

theorem shuffleStep_eq_empty_cache (hash : List Nat → List Nat)
    (seed : List Nat) (round count idx : Nat) :
    shuffleStep hash seed round count idx =
      shuffleSwapOrNot idx
        (shuffleFlip (shufflePivot hash seed round count) count idx)
        (shuffleBitOf
          (sourceCacheStep hash seed round []
            (shuffleBucket (shufflePosition idx
              (shuffleFlip (shufflePivot hash seed round count) count idx)))).1
          (shufflePosition idx
            (shuffleFlip (shufflePivot hash seed round count) count idx))) := by
  rw [shuffleStep_eq]
  rw [shuffleStep_source_eq_empty_cache (hash := hash) seed round count idx]

theorem foldl_shuffleStep_cons (hash : List Nat → List Nat)
    (seed : List Nat) (count idx r : Nat) (rs : List Nat) :
    (r :: rs).foldl (fun acc round => shuffleStep hash seed round count acc) idx =
      rs.foldl (fun acc round => shuffleStep hash seed round count acc)
        (shuffleStep hash seed r count idx) :=
  rfl

theorem shuffleRounds_cons :
    shuffleRounds = 0 :: (List.range 89).map Nat.succ := by
  unfold shuffleRounds SHUFFLE_ROUND_COUNT
  exact List.range_succ_eq_map

/-- The 90-round walk starts with an independent round-0 step, then
each later round is its own `shuffleStep`. -/
theorem shuffleIndexWalk_first_step (hash : List Nat → List Nat)
    (seed : List Nat) (count idx : Nat) :
    shuffleIndexWalk hash seed count idx =
      ((List.range 89).map Nat.succ).foldl
        (fun acc r => shuffleStep hash seed r count acc)
        (shuffleStep hash seed 0 count idx) := by
  unfold shuffleIndexWalk
  rw [shuffleRounds_cons]
  exact foldl_shuffleStep_cons hash seed count idx 0 _

/-- Mutant: reuse round 0 for every step of the walk. -/
def shuffleIndexWalkFixedRound (hash : List Nat → List Nat)
    (seed : List Nat) (count idx : Nat) : Nat :=
  shuffleRounds.foldl (fun acc _r => shuffleStep hash seed 0 count acc) idx

/-- `Hash32Like` dummy that splatters the preimage head across 32 bytes.
SHA256 values stay uninterpreted. -/
def echoSplatHash (data : List Nat) : List Nat :=
  List.replicate HASH32_BYTES ((data.head?).getD 0 % 256)

theorem echoSplatHash_like : Hash32Like echoSplatHash where
  length := fun _ => by
    simp [echoSplatHash, HASH32_BYTES]
  bounded := fun _data b hb => by
    unfold echoSplatHash at hb
    have hb0 : b = (_data.head?).getD 0 % 256 :=
      (List.mem_replicate.mp hb).2
    subst hb0
    exact Nat.mod_lt _ (by decide : 0 < 256)

/--
phase0:1204-1207. Two successive rounds are not two copies of round 0.
count 255, idx 0: round 1 swaps 0 to 8; repeating round 0 stays at 0.
-/
theorem shuffleStep_splat_round0_idx0 :
    shuffleStep echoSplatHash [] 0 255 0 = 0 := by
  decide

theorem shuffleStep_splat_round1_idx0 :
    shuffleStep echoSplatHash [] 1 255 0 = 8 := by
  decide

theorem two_rounds_not_fixed_round :
    [0, 1].foldl (fun acc r => shuffleStep echoSplatHash [] r 255 acc) 0 ≠
      [0, 1].foldl (fun acc _r => shuffleStep echoSplatHash [] 0 255 acc) 0 := by
  have hL :
      [0, 1].foldl (fun acc r => shuffleStep echoSplatHash [] r 255 acc) 0 =
        shuffleStep echoSplatHash [] 1 255
          (shuffleStep echoSplatHash [] 0 255 0) :=
    rfl
  have hR :
      [0, 1].foldl (fun acc _r => shuffleStep echoSplatHash [] 0 255 acc) 0 =
        shuffleStep echoSplatHash [] 0 255
          (shuffleStep echoSplatHash [] 0 255 0) :=
    rfl
  rw [hL, hR, shuffleStep_splat_round0_idx0, shuffleStep_splat_round1_idx0]
  decide

/-- phase0:1206 `sha256(seed + round_bytes)` has length `len(seed)+1`. -/
theorem shufflePivotPreimage_length (seed : List Nat) (round : Nat) :
    (shufflePivotPreimage seed round).length = seed.length + 1 := by
  simp [shufflePivotPreimage, shuffleRoundBytes, uintToBytes]

/-- phase0:1213-1215 `seed + round_bytes + uint_to_bytes(Uint32(bucket))`. -/
theorem shuffleBucketPreimage_length (seed : List Nat) (round bucket : Nat) :
    (shuffleBucketPreimage seed round bucket).length = seed.length + 5 := by
  simp [shuffleBucketPreimage, shuffleRoundBytes, uintToBytes]

/--
Archived `compute_shuffled_permutation` phase0:1206 vs 1213-1215:
the bucket preimage is the pivot preimage plus `Uint32(bucket)`.
-/
theorem shuffleBucketPreimage_eq_pivot_append
    (seed : List Nat) (round bucket : Nat) :
    shuffleBucketPreimage seed round bucket =
      shufflePivotPreimage seed round ++ uintToBytes 4 bucket := by
  simp [shuffleBucketPreimage, shufflePivotPreimage]

theorem shufflePivotPreimage_isPrefix (seed : List Nat)
    (round bucket : Nat) :
    shufflePivotPreimage seed round <+:
      shuffleBucketPreimage seed round bucket := by
  rw [shuffleBucketPreimage_eq_pivot_append]
  exact List.prefix_append _ _

theorem shufflePivotPreimage_ne_bucket_forall
    (seed : List Nat) (round bucket : Nat) :
    shufflePivotPreimage seed round ≠
      shuffleBucketPreimage seed round bucket := by
  intro h
  have hlen := congrArg List.length h
  simp [shufflePivotPreimage_length, shuffleBucketPreimage_length] at hlen

/-- Mutant: hash the bucket preimage (with `Uint32`) as the pivot. -/
def shufflePivotPreimageWithBucket (seed : List Nat)
    (round bucket : Nat) : List Nat :=
  shuffleBucketPreimage seed round bucket

theorem pivot_preimage_omits_bucket (seed : List Nat)
    (round bucket : Nat) :
    shufflePivotPreimage seed round ≠
      shufflePivotPreimageWithBucket seed round bucket :=
  shufflePivotPreimage_ne_bucket_forall seed round bucket

/-- Distinct `Uint8(round)` residues give distinct pivot preimages. -/
theorem shufflePivotPreimage_round_ne (seed : List Nat) (r r' : Nat)
    (h : r % 256 ≠ r' % 256) :
    shufflePivotPreimage seed r ≠ shufflePivotPreimage seed r' := by
  intro heq
  have hdrop := congrArg (fun xs => xs.drop seed.length) heq
  simp [shufflePivotPreimage, shuffleRoundBytes, uintToBytes] at hdrop
  exact h hdrop

/-- `Hash32Like` dummy that copies the preimage length into digest byte 0.
SHA256 values stay uninterpreted. -/
def echoLenHash (data : List Nat) : List Nat :=
  (data.length % 256) :: List.replicate 31 0

theorem echoLenHash_like : Hash32Like echoLenHash where
  length := fun _ => by
    simp [echoLenHash, HASH32_BYTES]
  bounded := fun _data b hb => by
    unfold echoLenHash at hb
    cases List.mem_cons.mp hb with
    | inl h =>
      subst h
      exact Nat.mod_lt _ (by decide : 0 < 256)
    | inr h =>
      have hb0 : b = 0 := (List.mem_replicate.mp h).2
      subst hb0
      decide

/-- phase0:1206 vs 1213-1215. The LE take-8 of the two preimages differs. -/
theorem pivot_raw_ne_bucket_echoLen :
    shufflePivotRaw echoLenHash [] 1 ≠
      uintFromBytes ((echoLenHash (shuffleBucketPreimage [] 1 0)).take 8) := by
  decide

/-- phase0:1206 `[0:8]` is exactly eight bytes under `Hash32Like`. -/
theorem hash32_drop8_length {hash : List Nat → List Nat}
    (hh : Hash32Like hash) (data : List Nat) :
    ((hash data).drop 8).length = 24 := by
  rw [List.length_drop, hh.length]
  decide

theorem hash32_drop24_length {hash : List Nat → List Nat}
    (hh : Hash32Like hash) (data : List Nat) :
    ((hash data).drop 24).length = 8 := by
  rw [List.length_drop, hh.length]
  decide

theorem uintFromBytes_take8_congr {xs ys : List Nat}
    (h : xs.take 8 = ys.take 8) :
    uintFromBytes (xs.take 8) = uintFromBytes (ys.take 8) :=
  congrArg uintFromBytes h

/--
Archived `compute_shuffled_permutation` phase0:1206 /
`bytes_to_uint64` phase0:1024-1028: the pivot is `int.from_bytes` of
`digest[0:8]` only. Digests that agree on that prefix agree as pivots.
-/
theorem shufflePivotRaw_eq_of_take8 {hash hash' : List Nat → List Nat}
    {seed : List Nat} {round : Nat}
    (h : (hash (shufflePivotPreimage seed round)).take 8 =
      (hash' (shufflePivotPreimage seed round)).take 8) :
    shufflePivotRaw hash seed round = shufflePivotRaw hash' seed round := by
  unfold shufflePivotRaw
  exact congrArg uintFromBytes h

/-- Mutant: `bytes_to_uint64(digest[8:16])`. -/
def shufflePivotRawDrop8 (hash : List Nat → List Nat) (seed : List Nat)
    (round : Nat) : Nat :=
  uintFromBytes (((hash (shufflePivotPreimage seed round)).drop 8).take 8)

/-- Mutant: `bytes_to_uint64(digest[24:32])`. -/
def shufflePivotRawTail (hash : List Nat → List Nat) (seed : List Nat)
    (round : Nat) : Nat :=
  uintFromBytes ((hash (shufflePivotPreimage seed round)).drop 24)

/-- Digest whose prefix LE is 1 and whose last byte is 7. -/
def sampleTailDigest : List Nat :=
  [1, 0, 0, 0, 0, 0, 0, 0] ++ List.replicate 23 0 ++ [7]

def sampleTailHash (_data : List Nat) : List Nat :=
  sampleTailDigest

theorem sampleTailDigest_length : sampleTailDigest.length = 32 := by
  simp [sampleTailDigest]

theorem sampleTailHash_like : Hash32Like sampleTailHash :=
  { length := fun _ => by
      simp [sampleTailHash, sampleTailDigest, HASH32_BYTES]
    bounded := fun _ b hb => by
      simp [sampleTailHash] at hb
      revert b hb
      decide }

/-- phase0:1024-1028 / 1206. Changing a suffix byte does not change `[0:8]`. -/
theorem take8_ignores_suffix_byte :
    samplePivotDigest.take 8 = sampleTailDigest.take 8 ∧
      samplePivotDigest ≠ sampleTailDigest := by
  decide

theorem shufflePivotRaw_same_prefix :
    shufflePivotRaw samplePivotHash [] 0 =
      shufflePivotRaw sampleTailHash [] 0 :=
  shufflePivotRaw_eq_of_take8 take8_ignores_suffix_byte.1

/-- phase0:1206. `[8:16]` is not `[0:8]`. -/
theorem pivot_raw_ne_drop8 :
    shufflePivotRaw sampleTailHash [] 0 ≠
      shufflePivotRawDrop8 sampleTailHash [] 0 := by
  decide

/-- phase0:1206. `[24:32]` is not `[0:8]`. -/
theorem pivot_raw_ne_tail :
    shufflePivotRaw sampleTailHash [] 0 ≠
      shufflePivotRawTail sampleTailHash [] 0 := by
  decide

/--
Archived `compute_shuffled_permutation` phase0:1206:
`pivot = bytes_to_uint64(...) % index_count`.
`shuffleFlip` already reduces modulo `index_count`, so omitting `%` on
the pivot does not change the partner. The load-bearing fact is
`pivot < index_count`.
-/
theorem shuffleFlip_of_raw_eq_mod {raw count idx : Nat}
    (hcount : 0 < count) :
    shuffleFlip raw count idx = shuffleFlip (raw % count) count idx := by
  unfold shuffleFlip
  set k := idx % count
  have hk : k ≤ count := Nat.le_of_lt (Nat.mod_lt idx hcount)
  rw [Nat.add_sub_assoc hk raw, Nat.add_sub_assoc hk (raw % count)]
  have hleft : (raw + (count - k)) % count =
      (raw % count + (count - k) % count) % count :=
    Nat.add_mod raw (count - k) count
  have hright : (raw % count + (count - k)) % count =
      ((raw % count) % count + (count - k) % count) % count :=
    Nat.add_mod (raw % count) (count - k) count
  rw [hleft, hright, Nat.mod_mod]

theorem shuffleFlip_no_mod_eq {hash : List Nat → List Nat}
    {seed : List Nat} {round count idx : Nat} (hcount : 0 < count) :
    shuffleFlip (shufflePivotNoMod hash seed round count) count idx =
      shuffleFlip (shufflePivot hash seed round count) count idx := by
  unfold shufflePivotNoMod shufflePivot
  exact shuffleFlip_of_raw_eq_mod hcount

/-- phase0:1206. `samplePivotHash` LE take-8 is 1, so `% 1` is 0. -/
theorem shufflePivot_sample_mod_one :
    shufflePivot samplePivotHash [] 0 1 = 0 := by
  simp [shufflePivot, samplePivotRaw_eq]

theorem shufflePivotNoMod_sample :
    shufflePivotNoMod samplePivotHash [] 0 1 = 1 := by
  simp [shufflePivotNoMod, samplePivotRaw_eq]

/-- Kill-line: omitting `% index_count` at count 1 with raw 1
is not `< index_count`. The archived pivot is. -/
theorem shufflePivotNoMod_not_lt :
    ¬ shufflePivotNoMod samplePivotHash [] 0 1 < 1 := by
  simp [shufflePivotNoMod_sample]

theorem shufflePivot_sample_lt :
    shufflePivot samplePivotHash [] 0 1 < 1 := by
  simp [shufflePivot_sample_mod_one]

theorem shufflePivot_uses_mod :
    shufflePivot samplePivotHash [] 0 1 ≠
      shufflePivotNoMod samplePivotHash [] 0 1 := by
  simp [shufflePivot_sample_mod_one, shufflePivotNoMod_sample]

/--
Named: Python `bytes_to_uint64(...) % 0` is `ZeroDivisionError`.
Lean `n % 0 = n`. The archived `assert index < index_count`
(phase0:1230) already rejects `index_count = 0`. This names the
exception; it does not claim Python's raise.
-/
theorem shuffle_empty_count_named_div0 (i : Nat) :
    shufflePivot samplePivotHash [] 0 0 =
      shufflePivotRaw samplePivotHash [] 0 ∧
      ¬ ShuffledIndexOk i 0 :=
  ⟨shufflePivot_empty _ _ _, shuffled_index_rejects_empty i⟩

/-- Distinct VECTOR head versus the remaining zeros. -/
def sampleMixZero : List Nat :=
  List.replicate 32 0

def sampleMixOne : List Nat :=
  [1] ++ List.replicate 31 0

def sampleMixes (head : List Nat) : List (List Nat) :=
  head :: List.replicate (EPOCHS_PER_HISTORICAL_VECTOR - 1) sampleMixZero

theorem sampleMixes_length (head : List Nat) :
    (sampleMixes head).length = EPOCHS_PER_HISTORICAL_VECTOR := by
  unfold sampleMixes EPOCHS_PER_HISTORICAL_VECTOR
  rw [List.length_cons, List.length_replicate]
  decide

theorem sampleMixes_zero (head : List Nat) :
    (sampleMixes head)[0]'(by
      rw [sampleMixes_length]; decide) = head :=
  rfl

theorem sampleMixes_pos (head : List Nat) {i : Nat}
    (h0 : 0 < i) (hi : i < EPOCHS_PER_HISTORICAL_VECTOR) :
    (sampleMixes head)[i]'(by
      rw [sampleMixes_length]; exact hi) = sampleMixZero := by
  cases i with
  | zero => exact (Nat.lt_irrefl 0 h0).elim
  | succ k =>
    unfold sampleMixes
    rw [List.getElem_cons_succ]
    apply List.getElem_replicate

/-- phase0:1414. Epoch 0 reads the head of this VECTOR. -/
theorem getRandaoMix_sample_zero :
    getRandaoMix (sampleMixes sampleMixOne) 0 (sampleMixes_length _) =
      sampleMixOne :=
  sampleMixes_zero _

/-- phase0:1414. A later slot of this VECTOR is the zero mix. -/
theorem getRandaoMix_sample_pos :
    getRandaoMix (sampleMixes sampleMixOne) 1 (sampleMixes_length _) =
      sampleMixZero :=
  sampleMixes_pos _ (by decide) (by decide)

/-- phase0:1449-1451 / 1414. Genesis `get_seed` reads index 65534, not 0. -/
theorem getRandaoMix_seed_genesis_not_head :
    getRandaoMix (sampleMixes sampleMixOne) (getSeedMixEpoch 0)
      (sampleMixes_length _) = sampleMixZero := by
  have hidx : getRandaoMixIndex (getSeedMixEpoch 0) = 65534 := by
    rw [getSeedMixEpoch_spec]
    decide
  unfold getRandaoMix
  have : getRandaoMixIndex (getSeedMixEpoch 0) = 65534 := hidx
  refine Eq.trans ?_ (sampleMixes_pos (i := 65534) sampleMixOne
    (by decide) (by decide))
  congr 1

/-- phase0:1414 vs a `[0]` mutant. The seed mix is not `randao_mixes[0]`. -/
theorem getRandaoMix_seed_ne_zero_slot :
    getRandaoMix (sampleMixes sampleMixOne) (getSeedMixEpoch 0)
      (sampleMixes_length _) ≠
      getRandaoMixAtZero (sampleMixes sampleMixOne) (sampleMixes_length _) := by
  rw [getRandaoMix_seed_genesis_not_head]
  change sampleMixZero ≠ (sampleMixes sampleMixOne)[0]' _
  rw [sampleMixes_zero]
  decide

/-- phase0:1414 / 1707. The mix is the stored hash, not `uint_to_bytes(epoch)`. -/
theorem getRandaoMix_genesis_ne_epoch_bytes :
    getRandaoMix (genesisRandaoMixes sampleMixOne) 3
      (genesisRandaoMixes_length _) ≠ uintToBytes8 3 := by
  rw [getRandaoMix_genesis]
  simp [sampleMixOne, uintToBytes8, uintToBytes]

/-- phase0:1414. `epoch + VECTOR` aliases `epoch`. -/
theorem getRandaoMix_sample_wraps :
    getRandaoMix (sampleMixes sampleMixOne) EPOCHS_PER_HISTORICAL_VECTOR
      (sampleMixes_length _) =
      getRandaoMix (sampleMixes sampleMixOne) 0 (sampleMixes_length _) :=
  getRandaoMix_alias _ _ 0

/-- phase0:1452. Epoch 2 reads index 0, so a different head changes the
seed preimage. SHA256 of that preimage stays uninterpreted. -/
theorem getSeedPreimage_tracks_mix_head :
    getSeedPreimageFromMixes DOMAIN_BEACON_PROPOSER 2
      (sampleMixes sampleMixOne) (sampleMixes_length _) ≠
      getSeedPreimageFromMixes DOMAIN_BEACON_PROPOSER 2
        (sampleMixes sampleMixZero) (sampleMixes_length _) := by
  have hidx : getSeedMixEpoch 2 = EPOCHS_PER_HISTORICAL_VECTOR := by
    rw [getSeedMixEpoch_spec]
    decide
  have hz : getRandaoMix (sampleMixes sampleMixOne) (getSeedMixEpoch 2)
      (sampleMixes_length _) = sampleMixOne := by
    rw [hidx]
    exact (getRandaoMix_alias (sampleMixes sampleMixOne)
      (sampleMixes_length _) 0).trans getRandaoMix_sample_zero
  have hz' : getRandaoMix (sampleMixes sampleMixZero) (getSeedMixEpoch 2)
      (sampleMixes_length _) = sampleMixZero := by
    rw [hidx]
    exact (getRandaoMix_alias (sampleMixes sampleMixZero)
      (sampleMixes_length _) 0).trans (sampleMixes_zero _)
  rw [getSeedPreimageFromMixes_eq_randao, getSeedPreimageFromMixes_eq_randao,
    hz, hz']
  simp [getSeedPreimage, sampleMixOne, sampleMixZero]

theorem sampleMixZero_length : sampleMixZero.length = 32 := by
  simp [sampleMixZero]

theorem samplePivotDigest_eq_mixOne : samplePivotDigest = sampleMixOne := by
  simp [samplePivotDigest, sampleMixOne]

/-- phase0:1006 / 2314. Xor of the zero mix with the sample digest is
the digest. -/
theorem bytesXor_zero_pivot :
    bytesXor sampleMixZero samplePivotDigest = samplePivotDigest := by
  have h : sampleMixZero = List.replicate samplePivotDigest.length 0 := by
    simp [sampleMixZero, samplePivotDigest]
  rw [h]
  exact bytesXor_zeros_left _

/-- phase0:2314-2315. Genesis zeros xor `samplePivotHash` writes the
digest at the current epoch. -/
theorem processRandao_genesis_current :
    getRandaoMix
      (processRandao samplePivotHash (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _))
      0
      (processRandao_length samplePivotHash (genesisRandaoMixes sampleMixZero)
        0 [] (genesisRandaoMixes_length _)) =
      samplePivotDigest := by
  rw [processRandao_current]
  unfold processRandaoMix
  rw [getRandaoMix_genesis]
  simp [samplePivotHash]
  exact bytesXor_zero_pivot

/-- phase0:2314. The xor is not a copy of the old mix. -/
theorem processRandao_not_copy :
    getRandaoMix
      (processRandao samplePivotHash (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _))
      0
      (processRandao_length samplePivotHash (genesisRandaoMixes sampleMixZero)
        0 [] (genesisRandaoMixes_length _)) ≠
      getRandaoMix (genesisRandaoMixes sampleMixZero) 0
        (genesisRandaoMixes_length _) := by
  rw [processRandao_genesis_current, getRandaoMix_genesis]
  simp [samplePivotDigest, sampleMixZero]

/-- phase0:2315 vs 2241. `process_randao` writes the current slot;
the epoch reset writes `next_epoch`. -/
theorem processRandao_next_unchanged :
    getRandaoMix
      (processRandao samplePivotHash (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _))
      1
      (processRandao_length samplePivotHash (genesisRandaoMixes sampleMixZero)
        0 [] (genesisRandaoMixes_length _)) =
      getRandaoMix (genesisRandaoMixes sampleMixZero) 1
        (genesisRandaoMixes_length _) :=
  processRandao_other samplePivotHash _ 0 1 [] _
    (by decide : getRandaoMixIndex 1 ≠ getRandaoMixIndex 0)

/-- phase0:2314-2315 vs 2237-2243. On a genesis splat the reset is a
no-op; `process_randao` changes the current mix. -/
theorem processRandao_ne_reset :
    getRandaoMix
      (processRandao samplePivotHash (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _))
      0
      (processRandao_length samplePivotHash (genesisRandaoMixes sampleMixZero)
        0 [] (genesisRandaoMixes_length _)) ≠
      getRandaoMix
        (processRandaoMixesReset (genesisRandaoMixes sampleMixZero) 0
          (genesisRandaoMixes_length _))
        0 (processRandaoMixesReset_length _ 0 (genesisRandaoMixes_length _)) := by
  rw [processRandao_genesis_current]
  rw [getRandaoMix_congr_list (hlen' := genesisRandaoMixes_length _)
    (processRandaoMixesReset_genesis sampleMixZero 0)]
  rw [getRandaoMix_genesis]
  simp [samplePivotDigest, sampleMixZero]

/-- phase0:2314 vs a copy mutant. Writing the old mix is not xor. -/
theorem processRandao_ne_copy_mutant :
    getRandaoMix
      (processRandao samplePivotHash (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _))
      0
      (processRandao_length samplePivotHash (genesisRandaoMixes sampleMixZero)
        0 [] (genesisRandaoMixes_length _)) ≠
      getRandaoMix
        (processRandaoCopy (genesisRandaoMixes sampleMixZero) 0
          (genesisRandaoMixes_length _))
        0 (processRandaoCopy_length _ 0 (genesisRandaoMixes_length _)) := by
  rw [processRandao_genesis_current, processRandaoCopy_current,
    getRandaoMix_genesis]
  simp [samplePivotDigest, sampleMixZero]

/-- phase0:2273 then 1823. After xor+reset, next epoch reads the xor. -/
theorem processRandaoThenReset_genesis_next :
    getRandaoMix
      (processRandaoThenReset samplePivotHash
        (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _))
      1
      (processRandaoThenReset_length samplePivotHash
        (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _)) = samplePivotDigest := by
  rw [processRandaoThenReset_next]
  unfold processRandaoMix
  rw [getRandaoMix_genesis]
  simp [samplePivotHash]
  exact bytesXor_zero_pivot

/-- Mutant order: reset first. On a genesis splat the copy is a no-op,
so next stays zero. -/
theorem processResetThenRandao_genesis_next :
    getRandaoMix
      (processResetThenRandao samplePivotHash
        (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _))
      1
      (processResetThenRandao_length samplePivotHash
        (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _)) = sampleMixZero := by
  unfold processResetThenRandao
  rw [processRandao_other samplePivotHash _ 0 1 [] _
    (by decide : getRandaoMixIndex 1 ≠ getRandaoMixIndex 0)]
  rw [getRandaoMix_congr_list (hlen' := genesisRandaoMixes_length _)
    (processRandaoMixesReset_genesis sampleMixZero 0)]
  exact getRandaoMix_genesis sampleMixZero 1

/-- phase0:2273 then 1823, not the reverse. Next epoch differs. -/
theorem processRandaoThenReset_ne_swapped :
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
          (genesisRandaoMixes_length _)) := by
  rw [processRandaoThenReset_genesis_next, processResetThenRandao_genesis_next]
  simp [samplePivotDigest, sampleMixZero]

/-- phase0:2273 then 1823. Current epoch still holds the xor. -/
theorem processRandaoThenReset_genesis_current :
    getRandaoMix
      (processRandaoThenReset samplePivotHash
        (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _))
      0
      (processRandaoThenReset_length samplePivotHash
        (genesisRandaoMixes sampleMixZero) 0 []
        (genesisRandaoMixes_length _)) = samplePivotDigest := by
  rw [processRandaoThenReset_current]
  unfold processRandaoMix
  rw [getRandaoMix_genesis]
  simp [samplePivotHash]
  exact bytesXor_zero_pivot

/-- phase0:618 `EPOCHS_PER_ETH1_VOTING_PERIOD = Epoch(2**6)` (= 64). -/
def EPOCHS_PER_ETH1_VOTING_PERIOD : Nat := 64

/-- phase0:626 `EPOCHS_PER_SLASHINGS_VECTOR = Epoch(2**13)` (= 8,192). -/
def EPOCHS_PER_SLASHINGS_VECTOR : Nat := 8192

theorem eth1VotingPeriod_ne_slashingsVector :
    EPOCHS_PER_ETH1_VOTING_PERIOD ≠ EPOCHS_PER_SLASHINGS_VECTOR := by
  decide

theorem slashingsVector_ne_historical :
    EPOCHS_PER_SLASHINGS_VECTOR ≠ EPOCHS_PER_HISTORICAL_VECTOR := by
  decide

/-- phase0:2202. Reset only when `next_epoch % 64 == 0`. -/
def eth1VotingPeriodReset (nextEpoch : Nat) : Bool :=
  decide (nextEpoch % EPOCHS_PER_ETH1_VOTING_PERIOD = 0)

/-- phase0:2199-2203 `process_eth1_data_reset`. Inherited at Gloas:1584
(no Gloas redefinition). Writes `eth1_data_votes`, not the clock. -/
def processEth1DataReset {α : Type} (votes : List α) (currentEpoch : Nat) :
    List α :=
  if (currentEpoch + 1) % EPOCHS_PER_ETH1_VOTING_PERIOD = 0 then [] else votes

theorem processEth1DataReset_keeps {α : Type} (votes : List α)
    (currentEpoch : Nat)
    (h : (currentEpoch + 1) % EPOCHS_PER_ETH1_VOTING_PERIOD ≠ 0) :
    processEth1DataReset votes currentEpoch = votes := by
  simp [processEth1DataReset, h]

theorem processEth1DataReset_clears {α : Type} (votes : List α)
    (currentEpoch : Nat)
    (h : (currentEpoch + 1) % EPOCHS_PER_ETH1_VOTING_PERIOD = 0) :
    processEth1DataReset votes currentEpoch = [] := by
  simp [processEth1DataReset, h]

/-- Mutant: always clear votes, ignoring the voting-period guard. -/
def processEth1DataResetAlways {α : Type} (votes : List α) (_currentEpoch : Nat) :
    List α := []

/-- phase0:2200-2202. Epoch 0 has `next_epoch = 1`, and `1 % 64 ≠ 0`. -/
theorem processEth1DataReset_epoch_zero {α : Type} (votes : List α) :
    processEth1DataReset votes 0 = votes :=
  processEth1DataReset_keeps votes 0 (by decide)

/-- phase0:2202. `next_epoch = 64` is a voting-period boundary. -/
theorem processEth1DataReset_epoch_sixty_three {α : Type} (votes : List α) :
    processEth1DataReset votes 63 = [] :=
  processEth1DataReset_clears votes 63 (by decide)

theorem processEth1DataReset_ne_always :
    processEth1DataReset [1] 0 ≠ processEth1DataResetAlways [1] 0 := by
  simp [processEth1DataReset_epoch_zero, processEth1DataResetAlways]

/-- phase0:2231. Ring index of the next epoch. -/
def getSlashingsIndex (epoch : Nat) : Nat :=
  epoch % EPOCHS_PER_SLASHINGS_VECTOR

theorem getSlashingsIndex_lt (epoch : Nat) :
    getSlashingsIndex epoch < EPOCHS_PER_SLASHINGS_VECTOR :=
  Nat.mod_lt epoch (by decide : 0 < EPOCHS_PER_SLASHINGS_VECTOR)

/-- phase0:2228-2231 `process_slashings_reset`. Inherited at Gloas:1591.
Writes `slashings[next_epoch % VECTOR] = 0`, not the clock, and not a
copy of the current entry (unlike `process_randao_mixes_reset`). -/
def processSlashingsReset (slashings : List Nat) (currentEpoch : Nat)
    (hlen : slashings.length = EPOCHS_PER_SLASHINGS_VECTOR) : List Nat :=
  slashings.set (getSlashingsIndex (currentEpoch + 1)) 0

theorem processSlashingsReset_length (slashings : List Nat)
    (currentEpoch : Nat)
    (hlen : slashings.length = EPOCHS_PER_SLASHINGS_VECTOR) :
    (processSlashingsReset slashings currentEpoch hlen).length =
      EPOCHS_PER_SLASHINGS_VECTOR := by
  simpa [processSlashingsReset, hlen] using
    (List.length_set (l := slashings) (i := getSlashingsIndex (currentEpoch + 1)) (a := 0))

theorem processSlashingsReset_writes_zero (slashings : List Nat)
    (currentEpoch : Nat)
    (hlen : slashings.length = EPOCHS_PER_SLASHINGS_VECTOR) :
    (processSlashingsReset slashings currentEpoch hlen)[getSlashingsIndex (currentEpoch + 1)]'(by
      rw [processSlashingsReset_length slashings currentEpoch hlen]
      exact getSlashingsIndex_lt (currentEpoch + 1)) = 0 := by
  unfold processSlashingsReset
  rw [List.getElem_set]
  simp

theorem processSlashingsReset_other (slashings : List Nat)
    (currentEpoch e : Nat)
    (hlen : slashings.length = EPOCHS_PER_SLASHINGS_VECTOR)
    (he : e < EPOCHS_PER_SLASHINGS_VECTOR)
    (hne : getSlashingsIndex e ≠ getSlashingsIndex (currentEpoch + 1)) :
    (processSlashingsReset slashings currentEpoch hlen)[getSlashingsIndex e]'(by
      rw [processSlashingsReset_length slashings currentEpoch hlen]
      exact getSlashingsIndex_lt e) =
      slashings[getSlashingsIndex e]'(hlen ▸ getSlashingsIndex_lt e) := by
  unfold processSlashingsReset
  rw [List.getElem_set]
  split_ifs with h
  · exact (hne h.symm).elim
  · rfl

/-- Mutant: copy the current entry into next, like the randao reset. -/
def processSlashingsResetCopy (slashings : List Nat) (currentEpoch : Nat)
    (hlen : slashings.length = EPOCHS_PER_SLASHINGS_VECTOR) : List Nat :=
  slashings.set (getSlashingsIndex (currentEpoch + 1))
    (slashings[getSlashingsIndex currentEpoch]'(hlen ▸ getSlashingsIndex_lt currentEpoch))

theorem processSlashingsResetCopy_length (slashings : List Nat)
    (currentEpoch : Nat)
    (hlen : slashings.length = EPOCHS_PER_SLASHINGS_VECTOR) :
    (processSlashingsResetCopy slashings currentEpoch hlen).length =
      EPOCHS_PER_SLASHINGS_VECTOR := by
  simpa [processSlashingsResetCopy, hlen] using
    (List.length_set (l := slashings) (i := getSlashingsIndex (currentEpoch + 1))
      (a := slashings[getSlashingsIndex currentEpoch]'(hlen ▸ getSlashingsIndex_lt currentEpoch)))

theorem processSlashingsResetCopy_next (slashings : List Nat)
    (currentEpoch : Nat)
    (hlen : slashings.length = EPOCHS_PER_SLASHINGS_VECTOR) :
    (processSlashingsResetCopy slashings currentEpoch hlen)[getSlashingsIndex (currentEpoch + 1)]'(by
      rw [processSlashingsResetCopy_length slashings currentEpoch hlen]
      exact getSlashingsIndex_lt (currentEpoch + 1)) =
    slashings[getSlashingsIndex currentEpoch]'(hlen ▸ getSlashingsIndex_lt currentEpoch) := by
  unfold processSlashingsResetCopy
  rw [List.getElem_set]
  simp

def sampleSlashings (v : Nat) : List Nat :=
  List.replicate EPOCHS_PER_SLASHINGS_VECTOR v

theorem sampleSlashings_length (v : Nat) :
    (sampleSlashings v).length = EPOCHS_PER_SLASHINGS_VECTOR := by
  simp [sampleSlashings]

/-- phase0:2231 vs a copy mutant. Writing 0 is not copying the current
entry when that entry is nonzero. -/
theorem processSlashingsReset_ne_copy :
    (processSlashingsReset (sampleSlashings 7) 0
        (sampleSlashings_length 7))[getSlashingsIndex (0 + 1)]'(by
          rw [processSlashingsReset_length (sampleSlashings 7) 0
            (sampleSlashings_length 7)]
          exact getSlashingsIndex_lt (0 + 1)) = 0 ∧
    (processSlashingsResetCopy (sampleSlashings 7) 0
        (sampleSlashings_length 7))[getSlashingsIndex (0 + 1)]'(by
          rw [processSlashingsResetCopy_length (sampleSlashings 7) 0
            (sampleSlashings_length 7)]
          exact getSlashingsIndex_lt (0 + 1)) = 7 := by
  refine ⟨processSlashingsReset_writes_zero (sampleSlashings 7) 0
    (sampleSlashings_length 7), ?_⟩
  have hc := processSlashingsResetCopy_next (sampleSlashings 7) 0
    (sampleSlashings_length 7)
  exact hc.trans (List.getElem_replicate (by
    change getSlashingsIndex 0 < (sampleSlashings 7).length
    rw [sampleSlashings_length]
    exact getSlashingsIndex_lt 0))

/-- phase0:619 `SLOTS_PER_HISTORICAL_ROOT = Slot(2**13)` (= 8,192).
Same numeric value as `EPOCHS_PER_SLASHINGS_VECTOR`, different role. -/
def SLOTS_PER_HISTORICAL_ROOT : Nat := 8192

/-- phase0:2252 / Capella:382
`SLOTS_PER_HISTORICAL_ROOT // SLOTS_PER_EPOCH` = 256. -/
def HISTORICAL_PERIOD : Nat :=
  SLOTS_PER_HISTORICAL_ROOT / SLOTS_PER_EPOCH

theorem historicalPeriod_eq : HISTORICAL_PERIOD = 256 := by
  unfold HISTORICAL_PERIOD SLOTS_PER_HISTORICAL_ROOT SLOTS_PER_EPOCH
  decide

theorem historicalPeriod_ne_eth1 :
    HISTORICAL_PERIOD ≠ EPOCHS_PER_ETH1_VOTING_PERIOD := by
  decide

theorem historicalPeriod_ne_slashings :
    HISTORICAL_PERIOD ≠ EPOCHS_PER_SLASHINGS_VECTOR := by
  decide

/-- Same number, different modulus: historical *slots* vs slashings *epochs*. -/
theorem slotsHistorical_eq_slashingsVector :
    SLOTS_PER_HISTORICAL_ROOT = EPOCHS_PER_SLASHINGS_VECTOR :=
  rfl

/-- phase0:2252 / Capella:382. Append only on the 256-epoch boundary. -/
def historicalPeriodReset (nextEpoch : Nat) : Bool :=
  decide (nextEpoch % HISTORICAL_PERIOD = 0)

/-- phase0:2249-2256 `process_historical_roots_update`. `root` is the
named `hash_tree_root(HistoricalBatch)`. Gloas:1593 calls the Capella
summaries helper instead of this body. -/
def processHistoricalRootsUpdate {α : Type} (roots : List α)
    (currentEpoch : Nat) (root : α) : List α :=
  if (currentEpoch + 1) % HISTORICAL_PERIOD = 0 then roots ++ [root] else roots

/-- Capella:379-387 `process_historical_summaries_update`. The two
roots are named `hash_tree_root` values. Inherited at Gloas:1593. -/
structure HistoricalSummary where
  blockSummaryRoot : List Nat
  stateSummaryRoot : List Nat

def processHistoricalSummariesUpdate (summaries : List HistoricalSummary)
    (currentEpoch : Nat) (summary : HistoricalSummary) :
    List HistoricalSummary :=
  if (currentEpoch + 1) % HISTORICAL_PERIOD = 0 then
    summaries ++ [summary]
  else summaries

/-- Mutant: use `SLOTS_PER_HISTORICAL_ROOT` as the epoch modulus,
forgetting `// SLOTS_PER_EPOCH`. -/
def processHistoricalRootsUpdateNoDiv {α : Type} (roots : List α)
    (currentEpoch : Nat) (root : α) : List α :=
  if (currentEpoch + 1) % SLOTS_PER_HISTORICAL_ROOT = 0 then
    roots ++ [root]
  else roots

theorem processHistoricalRootsUpdate_keeps {α : Type} (roots : List α)
    (currentEpoch : Nat) (root : α)
    (h : (currentEpoch + 1) % HISTORICAL_PERIOD ≠ 0) :
    processHistoricalRootsUpdate roots currentEpoch root = roots := by
  simp [processHistoricalRootsUpdate, h]

theorem processHistoricalRootsUpdate_appends {α : Type} (roots : List α)
    (currentEpoch : Nat) (root : α)
    (h : (currentEpoch + 1) % HISTORICAL_PERIOD = 0) :
    processHistoricalRootsUpdate roots currentEpoch root = roots ++ [root] := by
  simp [processHistoricalRootsUpdate, h]

theorem processHistoricalSummariesUpdate_keeps
    (summaries : List HistoricalSummary) (currentEpoch : Nat)
    (summary : HistoricalSummary)
    (h : (currentEpoch + 1) % HISTORICAL_PERIOD ≠ 0) :
    processHistoricalSummariesUpdate summaries currentEpoch summary =
      summaries := by
  simp [processHistoricalSummariesUpdate, h]

theorem processHistoricalSummariesUpdate_appends
    (summaries : List HistoricalSummary) (currentEpoch : Nat)
    (summary : HistoricalSummary)
    (h : (currentEpoch + 1) % HISTORICAL_PERIOD = 0) :
    processHistoricalSummariesUpdate summaries currentEpoch summary =
      summaries ++ [summary] := by
  simp [processHistoricalSummariesUpdate, h]

/-- phase0:2251-2252. Epoch 0 has `next_epoch = 1`, and `1 % 256 ≠ 0`. -/
theorem processHistoricalRootsUpdate_epoch_zero {α : Type}
    (roots : List α) (root : α) :
    processHistoricalRootsUpdate roots 0 root = roots :=
  processHistoricalRootsUpdate_keeps roots 0 root (by decide)

/-- phase0:2252. `next_epoch = 256` is a historical-period boundary. -/
theorem processHistoricalRootsUpdate_epoch_255 {α : Type}
    (roots : List α) (root : α) :
    processHistoricalRootsUpdate roots 255 root = roots ++ [root] :=
  processHistoricalRootsUpdate_appends roots 255 root (by decide)

/-- Forgetting `// 32` misses the epoch-255 append: `256 % 8192 ≠ 0`. -/
theorem processHistoricalRootsUpdate_ne_noDiv :
    processHistoricalRootsUpdate ([] : List Nat) 255 7 ≠
      processHistoricalRootsUpdateNoDiv ([] : List Nat) 255 7 := by
  simp [processHistoricalRootsUpdate_epoch_255, processHistoricalRootsUpdateNoDiv,
    SLOTS_PER_HISTORICAL_ROOT]

theorem processHistoricalSummariesUpdate_epoch_zero
    (summary : HistoricalSummary) :
    processHistoricalSummariesUpdate [] 0 summary = [] :=
  processHistoricalSummariesUpdate_keeps [] 0 summary (by decide)

/-- phase0:2262-2265 `process_participation_record_updates`. Always
rotates; not gated on `HISTORICAL_PERIOD`. -/
def processParticipationRecordUpdates {α : Type}
    (current : List α) : List α × List α :=
  (current, [])

/-- Altair:824-828 `process_participation_flag_updates`. Inherited at
Gloas:1594. Current flags become previous; current is zeros of registry
length. -/
def processParticipationFlagUpdates (current : List Nat) (n : Nat) :
    List Nat × List Nat :=
  (current, List.replicate n 0)

theorem processParticipationRecordUpdates_spec {α : Type}
    (current : List α) :
    processParticipationRecordUpdates current = (current, []) :=
  rfl

theorem processParticipationFlagUpdates_spec (current : List Nat) (n : Nat) :
    processParticipationFlagUpdates current n =
      (current, List.replicate n 0) :=
  rfl

/-- Participation rotates at epoch 0; historical does not append. -/
theorem participation_rotates_when_historical_keeps {α : Type}
    (current : List α) (roots : List Nat) (root : Nat) :
    processParticipationRecordUpdates current = (current, []) ∧
      processHistoricalRootsUpdate roots 0 root = roots :=
  ⟨rfl, processHistoricalRootsUpdate_epoch_zero roots root⟩

/-- phase0:607 `EFFECTIVE_BALANCE_INCREMENT = Gwei(10**9)`. -/
def EFFECTIVE_BALANCE_INCREMENT : Nat := 10 ^ 9

/-- phase0:589-591. -/
def HYSTERESIS_QUOTIENT : Nat := 4
def HYSTERESIS_DOWNWARD_MULTIPLIER : Nat := 1
def HYSTERESIS_UPWARD_MULTIPLIER : Nat := 5

/-- phase0:2213 `EFFECTIVE_BALANCE_INCREMENT // HYSTERESIS_QUOTIENT`. -/
def hysteresisIncrement : Nat :=
  EFFECTIVE_BALANCE_INCREMENT / HYSTERESIS_QUOTIENT

theorem hysteresisIncrement_eq : hysteresisIncrement = 250000000 := by
  unfold hysteresisIncrement EFFECTIVE_BALANCE_INCREMENT HYSTERESIS_QUOTIENT
  decide

theorem hysteresisIncrement_ne_increment :
    hysteresisIncrement ≠ EFFECTIVE_BALANCE_INCREMENT := by
  decide

/-- phase0:2214-2215. Downward 1, upward 5: the band is not symmetric. -/
def downwardThreshold : Nat :=
  hysteresisIncrement * HYSTERESIS_DOWNWARD_MULTIPLIER

def upwardThreshold : Nat :=
  hysteresisIncrement * HYSTERESIS_UPWARD_MULTIPLIER

theorem downwardThreshold_eq : downwardThreshold = 250000000 := by
  unfold downwardThreshold HYSTERESIS_DOWNWARD_MULTIPLIER hysteresisIncrement
    EFFECTIVE_BALANCE_INCREMENT HYSTERESIS_QUOTIENT
  decide

theorem upwardThreshold_eq : upwardThreshold = 1250000000 := by
  unfold upwardThreshold HYSTERESIS_UPWARD_MULTIPLIER hysteresisIncrement
    EFFECTIVE_BALANCE_INCREMENT HYSTERESIS_QUOTIENT
  decide

theorem hysteresis_band_asymmetric :
    downwardThreshold ≠ upwardThreshold := by
  decide

/-- phase0:2216-2218. Update only outside the hysteresis band. -/
def effectiveBalanceOutOfBand (balance effective : Nat) : Bool :=
  decide (balance + downwardThreshold < effective ∨
    effective + upwardThreshold < balance)

/-- phase0:2220-2221. Floor to the increment, then cap. `maxEB` is
phase0 `MAX_EFFECTIVE_BALANCE` or Electra `get_max_effective_balance`. -/
def effectiveBalanceCandidate (balance maxEB : Nat) : Nat :=
  min (balance - balance % EFFECTIVE_BALANCE_INCREMENT) maxEB

/-- phase0:2209-2222 / Electra:1228-1244. One validator step. Does not
write the clock and is not a withdrawal payload. -/
def processEffectiveBalanceUpdate (balance effective maxEB : Nat) : Nat :=
  if effectiveBalanceOutOfBand balance effective then
    effectiveBalanceCandidate balance maxEB
  else effective

/-- Mutant: always write the floored candidate, ignoring the band. -/
def processEffectiveBalanceUpdateAlways (balance effective maxEB : Nat) : Nat :=
  effectiveBalanceCandidate balance maxEB

theorem processEffectiveBalanceUpdate_keeps
    (balance effective maxEB : Nat)
    (h : effectiveBalanceOutOfBand balance effective = false) :
    processEffectiveBalanceUpdate balance effective maxEB = effective := by
  simp [processEffectiveBalanceUpdate, h]

theorem processEffectiveBalanceUpdate_writes
    (balance effective maxEB : Nat)
    (h : effectiveBalanceOutOfBand balance effective = true) :
    processEffectiveBalanceUpdate balance effective maxEB =
      effectiveBalanceCandidate balance maxEB := by
  simp [processEffectiveBalanceUpdate, h]

/-- 31.8e9 vs 32e9 sits inside the band: 31.8e9 + 0.25e9 ≱ 32e9 and
32e9 + 1.25e9 ≱ 31.8e9. -/
theorem effectiveBalanceOutOfBand_in_band_318 :
    effectiveBalanceOutOfBand (318 * 10 ^ 8) (32 * 10 ^ 9) = false := by
  unfold effectiveBalanceOutOfBand downwardThreshold upwardThreshold
    hysteresisIncrement EFFECTIVE_BALANCE_INCREMENT HYSTERESIS_QUOTIENT
    HYSTERESIS_DOWNWARD_MULTIPLIER HYSTERESIS_UPWARD_MULTIPLIER
  decide

/-- In-band 31.8e9 vs 32e9: archived keeps 32e9. -/
theorem processEffectiveBalanceUpdate_in_band_keeps :
    processEffectiveBalanceUpdate (318 * 10 ^ 8) (32 * 10 ^ 9)
      MAX_EFFECTIVE_BALANCE = 32 * 10 ^ 9 :=
  processEffectiveBalanceUpdate_keeps _ _ _ effectiveBalanceOutOfBand_in_band_318

/-- Ignoring the band floors 31.8e9 to 31e9 (`318e8 % 1e9 = 8e8`). -/
theorem processEffectiveBalanceUpdateAlways_in_band_floors :
    processEffectiveBalanceUpdateAlways (318 * 10 ^ 8) (32 * 10 ^ 9)
      MAX_EFFECTIVE_BALANCE = 31 * 10 ^ 9 := by
  unfold processEffectiveBalanceUpdateAlways effectiveBalanceCandidate
    EFFECTIVE_BALANCE_INCREMENT MAX_EFFECTIVE_BALANCE
  decide

theorem processEffectiveBalanceUpdate_ne_always :
    processEffectiveBalanceUpdate (318 * 10 ^ 8) (32 * 10 ^ 9)
      MAX_EFFECTIVE_BALANCE ≠
    processEffectiveBalanceUpdateAlways (318 * 10 ^ 8) (32 * 10 ^ 9)
      MAX_EFFECTIVE_BALANCE := by
  rw [processEffectiveBalanceUpdate_in_band_keeps,
    processEffectiveBalanceUpdateAlways_in_band_floors]
  decide

/-- Zero balance vs 32e9 is downward out-of-band and writes 0. -/
theorem processEffectiveBalanceUpdate_zero_clears :
    processEffectiveBalanceUpdate 0 (32 * 10 ^ 9) MAX_EFFECTIVE_BALANCE = 0 := by
  unfold processEffectiveBalanceUpdate effectiveBalanceOutOfBand
    effectiveBalanceCandidate downwardThreshold upwardThreshold
    hysteresisIncrement EFFECTIVE_BALANCE_INCREMENT HYSTERESIS_QUOTIENT
    HYSTERESIS_DOWNWARD_MULTIPLIER HYSTERESIS_UPWARD_MULTIPLIER
    MAX_EFFECTIVE_BALANCE
  decide

/-- phase0 cap: 40e9 is upward out-of-band and writes `min(40e9, 32e9)`. -/
theorem processEffectiveBalanceUpdate_phase0_caps :
    processEffectiveBalanceUpdate (40 * 10 ^ 9) (32 * 10 ^ 9)
      MAX_EFFECTIVE_BALANCE = MAX_EFFECTIVE_BALANCE := by
  unfold processEffectiveBalanceUpdate effectiveBalanceOutOfBand
    effectiveBalanceCandidate downwardThreshold upwardThreshold
    hysteresisIncrement EFFECTIVE_BALANCE_INCREMENT HYSTERESIS_QUOTIENT
    HYSTERESIS_DOWNWARD_MULTIPLIER HYSTERESIS_UPWARD_MULTIPLIER
    MAX_EFFECTIVE_BALANCE
  decide

/-- phase0:2211. One pass of the validator loop. -/
def processEffectiveBalanceUpdates (rows : List (Nat × Nat × Nat)) : List Nat :=
  rows.map (fun r => processEffectiveBalanceUpdate r.1 r.2.1 r.2.2)

theorem processEffectiveBalanceUpdates_length (rows : List (Nat × Nat × Nat)) :
    (processEffectiveBalanceUpdates rows).length = rows.length := by
  simp [processEffectiveBalanceUpdates]

theorem processEffectiveBalanceUpdates_in_band_keeps :
    processEffectiveBalanceUpdates
      [(318 * 10 ^ 8, 32 * 10 ^ 9, MAX_EFFECTIVE_BALANCE)] =
      [32 * 10 ^ 9] := by
  simp [processEffectiveBalanceUpdates]
  exact processEffectiveBalanceUpdate_in_band_keeps

/-- Altair:180 `EPOCHS_PER_SYNC_COMMITTEE_PERIOD = Epoch(2**8)` (= 256). -/
def EPOCHS_PER_SYNC_COMMITTEE_PERIOD : Nat := 256

theorem syncCommitteePeriod_eq : EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 256 := rfl

/-- Same number as `HISTORICAL_PERIOD`, different archived constant. -/
theorem syncCommitteePeriod_eq_historical :
    EPOCHS_PER_SYNC_COMMITTEE_PERIOD = HISTORICAL_PERIOD := by
  rw [syncCommitteePeriod_eq, historicalPeriod_eq]

/-- Altair:836-840 `process_sync_committee_updates`. Inherited at
Gloas:1595. `fresh` is named `get_next_sync_committee`. -/
def processSyncCommitteeUpdates {α : Type} (current next : α)
    (currentEpoch : Nat) (fresh : α) : α × α :=
  if (currentEpoch + 1) % EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0 then
    (next, fresh)
  else (current, next)

theorem processSyncCommitteeUpdates_keeps {α : Type}
    (current next fresh : α) (currentEpoch : Nat)
    (h : (currentEpoch + 1) % EPOCHS_PER_SYNC_COMMITTEE_PERIOD ≠ 0) :
    processSyncCommitteeUpdates current next currentEpoch fresh =
      (current, next) := by
  simp [processSyncCommitteeUpdates, h]

theorem processSyncCommitteeUpdates_rotates {α : Type}
    (current next fresh : α) (currentEpoch : Nat)
    (h : (currentEpoch + 1) % EPOCHS_PER_SYNC_COMMITTEE_PERIOD = 0) :
    processSyncCommitteeUpdates current next currentEpoch fresh =
      (next, fresh) := by
  simp [processSyncCommitteeUpdates, h]

theorem processSyncCommitteeUpdates_epoch_zero {α : Type}
    (current next fresh : α) :
    processSyncCommitteeUpdates current next 0 fresh = (current, next) :=
  processSyncCommitteeUpdates_keeps current next fresh 0 (by decide)

theorem processSyncCommitteeUpdates_epoch_255 {α : Type}
    (current next fresh : α) :
    processSyncCommitteeUpdates current next 255 fresh = (next, fresh) :=
  processSyncCommitteeUpdates_rotates current next fresh 255 (by decide)

/-- Mutant: always rotate, ignoring the sync period. -/
def processSyncCommitteeUpdatesAlways {α : Type} (_current next : α)
    (_currentEpoch : Nat) (fresh : α) : α × α :=
  (next, fresh)

theorem processSyncCommitteeUpdates_ne_always :
    processSyncCommitteeUpdates (0 : Nat) 1 0 2 ≠
      processSyncCommitteeUpdatesAlways 0 1 0 2 := by
  simp [processSyncCommitteeUpdates_epoch_zero, processSyncCommitteeUpdatesAlways]

/-- Altair:836-840. `fresh` is the named `get_next_sync_committee` result.
The body (Altair:204-230) is not extracted. -/
abbrev GetNextSyncCommittee (α : Type) := α

theorem processSyncCommitteeUpdates_fresh_named {α : Type}
    (current next : α) (fresh : GetNextSyncCommittee α) :
    processSyncCommitteeUpdates current next 255 fresh = (next, fresh) :=
  processSyncCommitteeUpdates_epoch_255 current next fresh

/-- Electra:344 `MAX_PENDING_DEPOSITS_PER_EPOCH = Uint64(2**4)` (= 16).
Used at Gloas:1621. -/
def MAX_PENDING_DEPOSITS_PER_EPOCH : Nat := 16

theorem maxPendingDepositsPerEpoch_eq : MAX_PENDING_DEPOSITS_PER_EPOCH = 16 :=
  rfl

/-- Fields read by Gloas:1604-1657. `apply_pending_deposit` (Electra:1098)
and its BLS signature stay named. -/
structure PendingDepositView where
  slot : Nat
  amount : Nat
  withdrawn : Bool
  exited : Bool
  deriving DecidableEq

/-- Gloas:1617-1622. Unfinalized slot or the 16-deposit cap stops the
walk before this entry. -/
def pendingDepositStops (d : PendingDepositView) (finalizedSlot index : Nat) :
    Bool :=
  decide (finalizedSlot < d.slot) ||
    decide (MAX_PENDING_DEPOSITS_PER_EPOCH ≤ index)

/-- Electra:1140-1148. Gloas dropped this Eth1-bridge gate.
`GENESIS_SLOT.val = 0` (phase0:542). -/
def pendingDepositElectraBridgeStops (d : PendingDepositView)
    (eth1DepositIndex depositRequestsStart : Nat) : Bool :=
  decide (GENESIS_SLOT.val < d.slot) &&
    decide (eth1DepositIndex < depositRequestsStart)

def takePendingDeposits (finalizedSlot : Nat) :
    Nat → List PendingDepositView → List PendingDepositView
  | _, [] => []
  | i, d :: rest =>
    if pendingDepositStops d finalizedSlot i then []
    else d :: takePendingDeposits finalizedSlot (i + 1) rest

def takePendingDepositsElectra (finalizedSlot eth1 start : Nat) :
    Nat → List PendingDepositView → List PendingDepositView
  | _, [] => []
  | i, d :: rest =>
    if pendingDepositElectraBridgeStops d eth1 start then []
    else if pendingDepositStops d finalizedSlot i then []
    else d :: takePendingDepositsElectra finalizedSlot eth1 start (i + 1) rest

def takePendingDepositsChurn (finalizedSlot available : Nat) :
    Nat → Nat → List PendingDepositView → List PendingDepositView
  | _, _, [] => []
  | i, processed, d :: rest =>
    if pendingDepositStops d finalizedSlot i then []
    else if d.withdrawn then
      d :: takePendingDepositsChurn finalizedSlot available (i + 1) processed rest
    else if d.exited then
      d :: takePendingDepositsChurn finalizedSlot available (i + 1) processed rest
    else if available < processed + d.amount then []
    else
      d :: takePendingDepositsChurn finalizedSlot available (i + 1)
        (processed + d.amount) rest

/-- Gloas:1652. Exited and not yet withdrawn entries are postponed. -/
def isPostponedDeposit (d : PendingDepositView) : Bool :=
  !d.withdrawn && d.exited

/-- Gloas:1655 `pending_deposits[next_deposit_index:] + deposits_to_postpone`. -/
def rewritePendingDeposits (all taken : List PendingDepositView) :
    List PendingDepositView :=
  all.drop taken.length ++ taken.filter (fun d => isPostponedDeposit d)

/-- Gloas:1658-1661. Leftover churn only if the limit was hit. -/
def depositBalanceToConsume (churnHit : Bool) (available processed : Nat) : Nat :=
  if churnHit then available - processed else 0

def depositBalanceToConsumeAlways (available processed : Nat) : Nat :=
  available - processed

theorem pendingDepositStops_of_le
    (d : PendingDepositView) (finalizedSlot index : Nat)
    (hs : d.slot ≤ finalizedSlot) (hi : index < MAX_PENDING_DEPOSITS_PER_EPOCH) :
    pendingDepositStops d finalizedSlot index = false := by
  simp [pendingDepositStops, Nat.not_lt.mpr hs, Nat.not_le.mpr hi]

theorem pendingDepositStops_of_unfinalized
    (d : PendingDepositView) (finalizedSlot index : Nat)
    (h : finalizedSlot < d.slot) :
    pendingDepositStops d finalizedSlot index = true := by
  simp [pendingDepositStops, h]

theorem pendingDepositStops_of_cap
    (d : PendingDepositView) (finalizedSlot index : Nat)
    (h : MAX_PENDING_DEPOSITS_PER_EPOCH ≤ index) :
    pendingDepositStops d finalizedSlot index = true := by
  simp [pendingDepositStops, h]

theorem takePendingDeposits_unfinalized (d : PendingDepositView)
    (finalizedSlot : Nat) (h : finalizedSlot < d.slot) :
    takePendingDeposits finalizedSlot 0 [d] = [] := by
  simp [takePendingDeposits, pendingDepositStops_of_unfinalized d finalizedSlot 0 h]

theorem takePendingDeposits_finalized (d : PendingDepositView)
    (finalizedSlot : Nat) (hs : d.slot ≤ finalizedSlot) :
    takePendingDeposits finalizedSlot 0 [d] = [d] := by
  have hstop := pendingDepositStops_of_le d finalizedSlot 0 hs (by decide)
  simp [takePendingDeposits, hstop]

theorem takePendingDeposits_replicate
    (d : PendingDepositView) (finalizedSlot : Nat)
    (hs : d.slot ≤ finalizedSlot) (i n : Nat)
    (hcap : i + n ≤ MAX_PENDING_DEPOSITS_PER_EPOCH) :
    takePendingDeposits finalizedSlot i (List.replicate n d) =
      List.replicate n d := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    have hi : i < MAX_PENDING_DEPOSITS_PER_EPOCH := by omega
    have hstop := pendingDepositStops_of_le d finalizedSlot i hs hi
    rw [List.replicate_succ, takePendingDeposits, hstop]
    exact congrArg (List.cons d) (ih (i + 1) (by omega))

theorem takePendingDeposits_sixteen
    (d : PendingDepositView) (finalizedSlot : Nat)
    (hs : d.slot ≤ finalizedSlot) :
    takePendingDeposits finalizedSlot 0 (List.replicate 16 d) =
      List.replicate 16 d :=
  takePendingDeposits_replicate d finalizedSlot hs 0 16 (by decide)

/-- Gloas:1621. Index 16 stops before the next deposit. -/
theorem takePendingDeposits_caps_at_sixteen
    (d : PendingDepositView) (finalizedSlot : Nat)
    (rest : List PendingDepositView) :
    takePendingDeposits finalizedSlot MAX_PENDING_DEPOSITS_PER_EPOCH (d :: rest) =
      [] := by
  simp [takePendingDeposits,
    pendingDepositStops_of_cap d finalizedSlot MAX_PENDING_DEPOSITS_PER_EPOCH
      (by decide)]

/-- A request after genesis is still taken by Gloas when the Electra
bridge would stop. -/
theorem takePendingDeposits_gloas_drops_eth1_bridge
    (d : PendingDepositView) (finalizedSlot : Nat)
    (hs : d.slot ≤ finalizedSlot) (hgen : GENESIS_SLOT.val < d.slot) :
    takePendingDeposits finalizedSlot 0 [d] = [d] ∧
      takePendingDepositsElectra finalizedSlot 0 1 0 [d] = [] := by
  have hstop := pendingDepositStops_of_le d finalizedSlot 0 hs (by decide)
  have hbridge : pendingDepositElectraBridgeStops d 0 1 = true := by
    simp [pendingDepositElectraBridgeStops, hgen]
  refine ⟨?_, ?_⟩
  · simp [takePendingDeposits, hstop]
  · simp [takePendingDepositsElectra, hbridge]

/-- Churn overflow leaves the overflowing deposit in the queue. -/
theorem takePendingDepositsChurn_overflow_stops
    (d : PendingDepositView) (finalizedSlot : Nat)
    (hs : d.slot ≤ finalizedSlot) (hw : d.withdrawn = false)
    (he : d.exited = false) (ha : 0 < d.amount) :
    takePendingDepositsChurn finalizedSlot 0 0 0 [d] = [] := by
  have hstop := pendingDepositStops_of_le d finalizedSlot 0 hs (by decide)
  rw [takePendingDepositsChurn, hstop, hw, he]
  exact if_pos (Nat.lt_of_lt_of_le ha (Nat.le_of_eq (Nat.zero_add d.amount).symm))

theorem rewritePendingDeposits_postpones_exited
    (ok ex : PendingDepositView)
    (hok : isPostponedDeposit ok = false) (hex : isPostponedDeposit ex = true) :
    rewritePendingDeposits [ok, ex] [ok, ex] = [ex] := by
  simp [rewritePendingDeposits, hok, hex]

theorem depositBalanceToConsume_clears :
    depositBalanceToConsume false 5 1 = 0 :=
  rfl

theorem depositBalanceToConsume_ne_always :
    depositBalanceToConsume false 5 1 ≠
      depositBalanceToConsumeAlways 5 1 := by
  decide

/-- Gloas:571-572 / 1416-1422. `get_total_active_balance` is the input. -/
def BUILDER_PAYMENT_THRESHOLD_NUMERATOR : Nat := 6
def BUILDER_PAYMENT_THRESHOLD_DENOMINATOR : Nat := 10

def builderPaymentQuorum (totalActive : Nat) : Nat :=
  (totalActive / SLOTS_PER_EPOCH * BUILDER_PAYMENT_THRESHOLD_NUMERATOR) /
    BUILDER_PAYMENT_THRESHOLD_DENOMINATOR

/-- Mutant: omit `// SLOTS_PER_EPOCH`. -/
def builderPaymentQuorumNoSlot (totalActive : Nat) : Nat :=
  (totalActive * BUILDER_PAYMENT_THRESHOLD_NUMERATOR) /
    BUILDER_PAYMENT_THRESHOLD_DENOMINATOR

theorem builderPaymentQuorum_ne_noSlot :
    builderPaymentQuorum (32 * 10) ≠ builderPaymentQuorumNoSlot (32 * 10) := by
  decide

/-- Gloas:1669. Only the previous-epoch window (first 32) is credited. -/
def creditedBuilderWeights (weights : List Nat) (quorum : Nat) : List Nat :=
  (weights.take SLOTS_PER_EPOCH).filter (fun w => decide (quorum ≤ w))

/-- Mutant: scan the whole 64-entry vector. -/
def creditedBuilderWeightsAll (weights : List Nat) (quorum : Nat) : List Nat :=
  weights.filter (fun w => decide (quorum ≤ w))

theorem creditedBuilderWeights_first_window :
    creditedBuilderWeights (List.replicate 32 0 ++ [7]) 1 = [] := by
  have htake : (List.replicate 32 0 ++ [7]).take SLOTS_PER_EPOCH =
      List.replicate 32 0 :=
    List.take_left' (by simp [SLOTS_PER_EPOCH])
  rw [creditedBuilderWeights, htake, List.filter_replicate]
  decide

theorem creditedBuilderWeights_ne_all :
    creditedBuilderWeights (List.replicate 32 0 ++ [7]) 1 ≠
      creditedBuilderWeightsAll (List.replicate 32 0 ++ [7]) 1 := by
  rw [creditedBuilderWeights_first_window]
  simp [creditedBuilderWeightsAll]

/-- Gloas:1673-1676. First window ← second window; second ← empties. -/
def rotateBuilderPayments {α : Type} (payments : List α) (empty : α) : List α :=
  payments.drop SLOTS_PER_EPOCH ++ List.replicate SLOTS_PER_EPOCH empty

theorem rotateBuilderPayments_length {α : Type} (empty : α)
    (payments : List α) (h : payments.length = 2 * SLOTS_PER_EPOCH) :
    (rotateBuilderPayments payments empty).length = 2 * SLOTS_PER_EPOCH := by
  simp [rotateBuilderPayments, List.length_append, List.length_drop,
    List.length_replicate, h, SLOTS_PER_EPOCH]

theorem rotateBuilderPayments_prefix {α : Type} (empty : α)
    (second : List α) (h : second.length = SLOTS_PER_EPOCH) :
    (rotateBuilderPayments (List.replicate SLOTS_PER_EPOCH empty ++ second)
        empty).take SLOTS_PER_EPOCH = second := by
  have hdrop :
      (List.replicate SLOTS_PER_EPOCH empty ++ second).drop SLOTS_PER_EPOCH =
        second :=
    List.drop_left' (by simp)
  simp [rotateBuilderPayments, hdrop]
  exact List.take_left' h

theorem rotateBuilderPayments_suffix {α : Type} (empty : α)
    (payments : List α) (h : payments.length = 2 * SLOTS_PER_EPOCH) :
    (rotateBuilderPayments payments empty).drop SLOTS_PER_EPOCH =
      List.replicate SLOTS_PER_EPOCH empty := by
  have hlen : (payments.drop SLOTS_PER_EPOCH).length = SLOTS_PER_EPOCH := by
    simp [h, SLOTS_PER_EPOCH]
  simp [rotateBuilderPayments]
  exact List.drop_left' hlen

/-- phase0:616 `MAX_SEED_LOOKAHEAD = Epoch(2**2)` (= 4). -/
def MAX_SEED_LOOKAHEAD : Nat := 4

/-- phase0:688 `MIN_VALIDATOR_WITHDRAWABILITY_DELAY = Epoch(2**8)` (= 256). -/
def MIN_VALIDATOR_WITHDRAWABILITY_DELAY : Nat := 256

/-- phase0:696 `EJECTION_BALANCE = Gwei(2**4 * 10**9)` (= 16e9). -/
def EJECTION_BALANCE : Nat := 16 * 10 ^ 9

theorem maxSeedLookahead_eq : MAX_SEED_LOOKAHEAD = 4 :=
  rfl

theorem withdrawabilityDelay_eq : MIN_VALIDATOR_WITHDRAWABILITY_DELAY = 256 :=
  rfl

theorem ejectionBalance_eq : EJECTION_BALANCE = 16 * 10 ^ 9 :=
  rfl

theorem ejectionBalance_ne_maxEB :
    EJECTION_BALANCE ≠ MAX_EFFECTIVE_BALANCE := by
  decide

/-- phase0:1306-1310. Activations/exits initiated at `epoch` take
effect at `epoch + 1 + MAX_SEED_LOOKAHEAD`. -/
def computeActivationExitEpoch (epoch : Nat) : Nat :=
  epoch + 1 + MAX_SEED_LOOKAHEAD

/-- Mutant: drop the lookahead. -/
def computeActivationExitEpochNoLookahead (epoch : Nat) : Nat :=
  epoch + 1

theorem computeActivationExitEpoch_spec (epoch : Nat) :
    computeActivationExitEpoch epoch = epoch + 5 := by
  simp [computeActivationExitEpoch, MAX_SEED_LOOKAHEAD]

theorem computeActivationExitEpoch_epoch_zero :
    computeActivationExitEpoch 0 = 5 :=
  computeActivationExitEpoch_spec 0

theorem computeActivationExitEpoch_ne_noLookahead :
    computeActivationExitEpoch 0 ≠
      computeActivationExitEpochNoLookahead 0 := by
  decide

/-- phase0:1077-1083. Active on `[activation, exit)`. -/
def isActiveValidator (activationEpoch exitEpoch epoch : Nat) : Bool :=
  decide (activationEpoch ≤ epoch) && decide (epoch < exitEpoch)

theorem isActiveValidator_inside :
    isActiveValidator 3 10 3 = true := by
  decide

theorem isActiveValidator_at_exit :
    isActiveValidator 0 5 5 = false := by
  decide

theorem isActiveValidator_before_activation :
    isActiveValidator 3 10 2 = false := by
  decide

/-- phase0:1077. `epoch = exit` is not active; a `≤` mutant is. -/
def isActiveValidatorClosed (activationEpoch exitEpoch epoch : Nat) : Bool :=
  decide (activationEpoch ≤ epoch) && decide (epoch ≤ exitEpoch)

theorem isActiveValidator_ne_closed :
    isActiveValidator 0 5 5 ≠ isActiveValidatorClosed 0 5 5 := by
  decide

/-- Electra:1198-1221. Source fields read by the consolidation walk.
`decrease_balance` / `increase_balance` stay named. -/
structure PendingConsolidationView where
  slashed : Bool
  withdrawableEpoch : Nat
  sourceBalance : Nat
  sourceEffective : Nat
  deriving DecidableEq

/-- Electra:1210-1213. Excess above effective stays on the source. -/
def consolidationAmount (c : PendingConsolidationView) : Nat :=
  min c.sourceBalance c.sourceEffective

inductive ConsolidationStep where
  | skip
  | stop
  | transfer (amount : Nat)
  deriving DecidableEq

/-- Electra:1203-1217. Slashed sources are skipped; an unwithdrawable
unslashed source stops the walk. -/
def consolidationStep (c : PendingConsolidationView) (nextEpoch : Nat) :
    ConsolidationStep :=
  if c.slashed then .skip
  else if nextEpoch < c.withdrawableEpoch then .stop
  else .transfer (consolidationAmount c)

/-- Mutant: transfer slashed sources too. -/
def consolidationStepTransferSlashed (c : PendingConsolidationView)
    (nextEpoch : Nat) : ConsolidationStep :=
  if nextEpoch < c.withdrawableEpoch then .stop
  else .transfer (consolidationAmount c)

def consumedPendingConsolidations (nextEpoch : Nat) :
    List PendingConsolidationView → Nat
  | [] => 0
  | c :: rest =>
    match consolidationStep c nextEpoch with
    | .stop => 0
    | _ => 1 + consumedPendingConsolidations nextEpoch rest

def rewritePendingConsolidations (all : List PendingConsolidationView)
    (nextEpoch : Nat) : List PendingConsolidationView :=
  all.drop (consumedPendingConsolidations nextEpoch all)

def slashedUnwithdrawable : PendingConsolidationView where
  slashed := true
  withdrawableEpoch := 10
  sourceBalance := 40 * 10 ^ 9
  sourceEffective := 32 * 10 ^ 9

def readyUnslashed : PendingConsolidationView where
  slashed := false
  withdrawableEpoch := 1
  sourceBalance := 40 * 10 ^ 9
  sourceEffective := 32 * 10 ^ 9

def blockedUnslashed : PendingConsolidationView where
  slashed := false
  withdrawableEpoch := 10
  sourceBalance := 40 * 10 ^ 9
  sourceEffective := 32 * 10 ^ 9

theorem consolidationAmount_is_min :
    consolidationAmount readyUnslashed = 32 * 10 ^ 9 := by
  simp [consolidationAmount, readyUnslashed]

theorem consolidationStep_skips_slashed :
    consolidationStep slashedUnwithdrawable 2 = .skip := by
  simp [consolidationStep, slashedUnwithdrawable]

theorem consolidationStep_stops_unwithdrawable :
    consolidationStep blockedUnslashed 2 = .stop := by
  simp [consolidationStep, blockedUnslashed]

theorem consolidationStep_transfers_ready :
    consolidationStep readyUnslashed 2 =
      .transfer (32 * 10 ^ 9) := by
  simp [consolidationStep, consolidationAmount, readyUnslashed]

theorem consolidationStep_ne_transferSlashed :
    consolidationStep slashedUnwithdrawable 2 ≠
      consolidationStepTransferSlashed slashedUnwithdrawable 2 := by
  simp [consolidationStep, consolidationStepTransferSlashed,
    consolidationAmount, slashedUnwithdrawable]

/-- A slashed source is consumed even when withdrawable is still in
the future, so a later ready consolidation can run. -/
theorem consumedPendingConsolidations_skips_slashed :
    consumedPendingConsolidations 2 [slashedUnwithdrawable, readyUnslashed] =
      2 := by
  simp [consumedPendingConsolidations, consolidationStep,
    consolidationAmount, slashedUnwithdrawable, readyUnslashed]

/-- An unwithdrawable unslashed source stops before later entries. -/
theorem consumedPendingConsolidations_stops :
    consumedPendingConsolidations 2 [blockedUnslashed, readyUnslashed] =
      0 := by
  simp [consumedPendingConsolidations, consolidationStep, blockedUnslashed]

theorem rewritePendingConsolidations_keeps_blocked :
    rewritePendingConsolidations [blockedUnslashed, readyUnslashed] 2 =
      [blockedUnslashed, readyUnslashed] := by
  simp [rewritePendingConsolidations, consumedPendingConsolidations,
    consolidationStep, blockedUnslashed]

/-- Electra:358 `MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA = Gwei(2**7 * 10**9)`. -/
def MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA : Nat := 128 * 10 ^ 9

/-- phase0:698 `CHURN_LIMIT_QUOTIENT = Uint64(2**16)` (= 65536). -/
def CHURN_LIMIT_QUOTIENT : Nat := 2 ^ 16

/-- Gloas:626 `CHURN_LIMIT_QUOTIENT_GLOAS = Uint64(2**15)` (= 32768). -/
def CHURN_LIMIT_QUOTIENT_GLOAS : Nat := 2 ^ 15

/-- Electra:359 `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT = Gwei(2**8 * 10**9)`. -/
def MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT : Nat := 256 * 10 ^ 9

theorem churnQuotient_gloas_is_half :
    CHURN_LIMIT_QUOTIENT_GLOAS * 2 = CHURN_LIMIT_QUOTIENT :=
  rfl

def alignEffectiveIncrement (n : Nat) : Nat :=
  n - n % EFFECTIVE_BALANCE_INCREMENT

/-- Electra:748-757. `get_total_active_balance` is the input. -/
def balanceChurnLimit (totalActive : Nat) : Nat :=
  alignEffectiveIncrement
    (max MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
      (totalActive / CHURN_LIMIT_QUOTIENT))

/-- Electra:761-765. -/
def activationExitChurnLimit (totalActive : Nat) : Nat :=
  min MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT (balanceChurnLimit totalActive)

/-- Gloas:1444-1453. Same min, Gloas quotient. -/
def exitChurnLimitGloas (totalActive : Nat) : Nat :=
  alignEffectiveIncrement
    (max MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
      (totalActive / CHURN_LIMIT_QUOTIENT_GLOAS))

theorem exitChurnLimitGloas_ne_electra_quotient :
    exitChurnLimitGloas (CHURN_LIMIT_QUOTIENT * (200 * 10 ^ 9)) ≠
      balanceChurnLimit (CHURN_LIMIT_QUOTIENT * (200 * 10 ^ 9)) := by
  decide

/-- Electra:910-933 / Gloas:1478-1501. `perEpochChurn` is named
`get_activation_exit_churn_limit` (Electra) or `get_exit_churn_limit`
(Gloas). Empty `per` is Python `ZeroDivisionError`; Lean `n / 0 = 0`. -/
structure ExitChurnState where
  earliestExitEpoch : Nat
  exitBalanceToConsume : Nat
  deriving DecidableEq

def additionalExitEpochs (overflow per : Nat) : Nat :=
  (overflow - 1) / per + 1

/-- Mutant: floor instead of the archived ceil. -/
def additionalExitEpochsFloor (overflow per : Nat) : Nat :=
  overflow / per

theorem additionalExitEpochs_ceils :
    additionalExitEpochs 150 100 = 2 :=
  rfl

theorem additionalExitEpochs_ne_floor :
    additionalExitEpochs 150 100 ≠ additionalExitEpochsFloor 150 100 := by
  decide

def computeExitEpochAndUpdateChurn (s : ExitChurnState)
    (currentEpoch exitBalance perEpochChurn : Nat) : ExitChurnState :=
  let earliest :=
    max s.earliestExitEpoch (computeActivationExitEpoch currentEpoch)
  let consume :=
    if s.earliestExitEpoch < earliest then perEpochChurn
    else s.exitBalanceToConsume
  if consume < exitBalance then
    let extra := additionalExitEpochs (exitBalance - consume) perEpochChurn
    { earliestExitEpoch := earliest + extra
      exitBalanceToConsume :=
        consume + extra * perEpochChurn - exitBalance }
  else
    { earliestExitEpoch := earliest
      exitBalanceToConsume := consume - exitBalance }

/-- Mutant: always keep leftover instead of resetting on a new epoch. -/
def computeExitEpochAndUpdateChurnKeep (s : ExitChurnState)
    (currentEpoch exitBalance perEpochChurn : Nat) : ExitChurnState :=
  let earliest :=
    max s.earliestExitEpoch (computeActivationExitEpoch currentEpoch)
  let consume := s.exitBalanceToConsume
  if consume < exitBalance then
    let extra := additionalExitEpochs (exitBalance - consume) perEpochChurn
    { earliestExitEpoch := earliest + extra
      exitBalanceToConsume :=
        consume + extra * perEpochChurn - exitBalance }
  else
    { earliestExitEpoch := earliest
      exitBalanceToConsume := consume - exitBalance }

/-- New activation-exit epoch resets leftover to `per`.
current 0 → activation-exit 5; leftover 999 is discarded. -/
theorem computeExitEpochAndUpdateChurn_resets_new_epoch :
    computeExitEpochAndUpdateChurn
        { earliestExitEpoch := 0, exitBalanceToConsume := 999 } 0 40 100 =
      { earliestExitEpoch := 5, exitBalanceToConsume := 60 } := by
  unfold computeExitEpochAndUpdateChurn computeActivationExitEpoch
    MAX_SEED_LOOKAHEAD additionalExitEpochs
  decide

theorem computeExitEpochAndUpdateChurn_ne_keep :
    computeExitEpochAndUpdateChurn
        { earliestExitEpoch := 0, exitBalanceToConsume := 999 } 0 40 100 ≠
      computeExitEpochAndUpdateChurnKeep
        { earliestExitEpoch := 0, exitBalanceToConsume := 999 } 0 40 100 := by
  unfold computeExitEpochAndUpdateChurn computeExitEpochAndUpdateChurnKeep
    computeActivationExitEpoch MAX_SEED_LOOKAHEAD additionalExitEpochs
  decide

/-- Same earliest epoch keeps leftover. leftover 60, exit 40 → 20. -/
theorem computeExitEpochAndUpdateChurn_keeps_leftover :
    computeExitEpochAndUpdateChurn
        { earliestExitEpoch := 5, exitBalanceToConsume := 60 } 0 40 100 =
      { earliestExitEpoch := 5, exitBalanceToConsume := 20 } := by
  unfold computeExitEpochAndUpdateChurn computeActivationExitEpoch
    MAX_SEED_LOOKAHEAD additionalExitEpochs
  decide

/-- Overflow 250 vs leftover 60 / per 100: extra = ceil(190/100) = 2. -/
theorem computeExitEpochAndUpdateChurn_overflow_ceils :
    computeExitEpochAndUpdateChurn
        { earliestExitEpoch := 5, exitBalanceToConsume := 60 } 0 250 100 =
      { earliestExitEpoch := 7, exitBalanceToConsume := 10 } := by
  unfold computeExitEpochAndUpdateChurn computeActivationExitEpoch
    MAX_SEED_LOOKAHEAD additionalExitEpochs
  decide

/-- Bellatrix:127 `PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX = 3`. -/
def PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX : Nat := 3

/-- phase0:639 `PROPORTIONAL_SLASHING_MULTIPLIER = 1`. -/
def PROPORTIONAL_SLASHING_MULTIPLIER : Nat := 1

/-- Electra:1076 / phase0:2184. Mid-vector withdrawable window. -/
def slashingPenaltyOffset : Nat := EPOCHS_PER_SLASHINGS_VECTOR / 2

theorem slashingPenaltyOffset_eq : slashingPenaltyOffset = 4096 := by
  unfold slashingPenaltyOffset EPOCHS_PER_SLASHINGS_VECTOR
  decide

def appliesSlashingPenalty (slashed : Bool) (epoch withdrawable : Nat) : Bool :=
  slashed && decide (epoch + slashingPenaltyOffset = withdrawable)

/-- Mutant: wait the full vector, not half. -/
def appliesSlashingPenaltyFull (slashed : Bool) (epoch withdrawable : Nat) : Bool :=
  slashed && decide (epoch + EPOCHS_PER_SLASHINGS_VECTOR = withdrawable)

theorem appliesSlashingPenalty_mid :
    appliesSlashingPenalty true 0 4096 = true := by
  simp [appliesSlashingPenalty, slashingPenaltyOffset, EPOCHS_PER_SLASHINGS_VECTOR]

theorem appliesSlashingPenalty_not_slashed :
    appliesSlashingPenalty false 0 4096 = false := by
  simp [appliesSlashingPenalty]

theorem appliesSlashingPenalty_ne_full :
    appliesSlashingPenalty true 0 4096 ≠
      appliesSlashingPenaltyFull true 0 4096 := by
  simp [appliesSlashingPenalty, appliesSlashingPenaltyFull,
    slashingPenaltyOffset, EPOCHS_PER_SLASHINGS_VECTOR]

def adjustedSlashingBalance (sumSlash total multiplier : Nat) : Nat :=
  min (sumSlash * multiplier) total

/-- Electra:1079-1086. `get_total_active_balance` is `total`. -/
def slashingPenaltyElectra (adjusted total eb : Nat) : Nat :=
  let inc := EFFECTIVE_BALANCE_INCREMENT
  adjusted / (total / inc) * (eb / inc)

/-- phase0:2188-2193. -/
def slashingPenaltyPhase0 (adjusted total eb : Nat) : Nat :=
  let inc := EFFECTIVE_BALANCE_INCREMENT
  (eb / inc * adjusted) / total * inc

theorem slashingPenaltyElectra_ne_phase0 :
    slashingPenaltyElectra (32 * 10 ^ 9) (321 * 10 ^ 8) (32 * 10 ^ 9) ≠
      slashingPenaltyPhase0 (32 * 10 ^ 9) (321 * 10 ^ 8) (32 * 10 ^ 9) := by
  unfold slashingPenaltyElectra slashingPenaltyPhase0 EFFECTIVE_BALANCE_INCREMENT
  decide

/-- phase0:543 `GENESIS_EPOCH = Epoch(0)`. -/
def GENESIS_EPOCH : Nat := 0

/-- phase0:546 `JUSTIFICATION_BITS_LENGTH = Uint64(4)`. -/
def JUSTIFICATION_BITS_LENGTH : Nat := 4

/-- phase0:617 `MIN_EPOCHS_TO_INACTIVITY_PENALTY = Epoch(2**2)` (= 4). -/
def MIN_EPOCHS_TO_INACTIVITY_PENALTY : Nat := 4

/-- Altair:188-189. -/
def INACTIVITY_SCORE_BIAS : Nat := 4
def INACTIVITY_SCORE_RECOVERY_RATE : Nat := 16

/-- Altair:131-133 / 139-144. -/
def TIMELY_SOURCE_FLAG_INDEX : Nat := 0
def TIMELY_TARGET_FLAG_INDEX : Nat := 1
def TIMELY_HEAD_FLAG_INDEX : Nat := 2
def TIMELY_SOURCE_WEIGHT : Nat := 14
def TIMELY_TARGET_WEIGHT : Nat := 26
def TIMELY_HEAD_WEIGHT : Nat := 14
def WEIGHT_DENOMINATOR : Nat := 64

theorem genesisEpoch_eq : GENESIS_EPOCH = 0 :=
  rfl

theorem justificationBitsLength_eq : JUSTIFICATION_BITS_LENGTH = 4 :=
  rfl

/-- phase0:1378-1384. Genesis stays 0; otherwise `current - 1`. -/
def getPreviousEpoch (currentEpoch : Nat) : Nat :=
  if currentEpoch = GENESIS_EPOCH then GENESIS_EPOCH else currentEpoch - 1

theorem getPreviousEpoch_genesis : getPreviousEpoch 0 = 0 :=
  rfl

theorem getPreviousEpoch_succ (e : Nat) (h : e ≠ 0) :
    getPreviousEpoch e = e - 1 := by
  simp [getPreviousEpoch, GENESIS_EPOCH, h]

/-- phase0:1889-1891 / Altair:731-733. Skip the first two epochs. -/
def skipsJustification (epoch : Nat) : Bool :=
  decide (epoch ≤ GENESIS_EPOCH + 1)

/-- Altair:754-755 / 780-781. Inactivity and rewards skip genesis only. -/
def skipsInactivityUpdates (epoch : Nat) : Bool :=
  decide (epoch = GENESIS_EPOCH)

def skipsRewardsAndPenalties (epoch : Nat) : Bool :=
  skipsInactivityUpdates epoch

theorem skipsJustification_epoch_one :
    skipsJustification 1 = true := by
  decide

theorem skipsInactivityUpdates_epoch_one :
    skipsInactivityUpdates 1 = false := by
  decide

theorem skipsJustification_ne_inactivity_at_one :
    skipsJustification 1 ≠ skipsInactivityUpdates 1 := by
  decide

/-- phase0:1933 / 1938. Supermajority is `≥ 2/3`, not `>`. -/
def justifiesSupermajority (target total : Nat) : Bool :=
  decide (target * 3 ≥ total * 2)

def justifiesSupermajorityStrict (target total : Nat) : Bool :=
  decide (target * 3 > total * 2)

theorem justifiesSupermajority_exact_two_thirds :
    justifiesSupermajority 2 3 = true := by
  decide

theorem justifiesSupermajority_ne_strict :
    justifiesSupermajority 2 3 ≠ justifiesSupermajorityStrict 2 3 := by
  decide

/-- phase0:1928-1930. `bits[1:] = bits[:3]`; `bits[0] = False`. -/
def shiftJustificationBits (bits : List Bool) : List Bool :=
  false :: bits.take (JUSTIFICATION_BITS_LENGTH - 1)

/-- Mutant: rotate the other way. -/
def shiftJustificationBitsRev (bits : List Bool) : List Bool :=
  bits.drop 1 ++ [false]

theorem shiftJustificationBits_spec :
    shiftJustificationBits [true, true, false, true] =
      [false, true, true, false] := by
  simp [shiftJustificationBits, JUSTIFICATION_BITS_LENGTH]

theorem shiftJustificationBits_ne_rev :
    shiftJustificationBits [true, true, false, true] ≠
      shiftJustificationBitsRev [true, true, false, true] := by
  simp [shiftJustificationBits, shiftJustificationBitsRev, JUSTIFICATION_BITS_LENGTH]

/-- phase0:1944-1946. 2nd/3rd/4th bits set and source is `current-3`. -/
def finalizeK4 (bits : List Bool) (oldPrev current : Nat) : Bool :=
  decide ((bits.drop 1).take 3 = [true, true, true]) &&
    decide (oldPrev + 3 = current)

theorem finalizeK4_hits :
    finalizeK4 [false, true, true, true] 0 3 = true := by
  decide

theorem finalizeK4_needs_source :
    finalizeK4 [false, true, true, true] 0 2 = false := by
  decide

/-- phase0:1934-1935. 2nd/3rd most recent justified; source is `current-2`. -/
def finalizeK3 (bits : List Bool) (oldPrev current : Nat) : Bool :=
  decide ((bits.drop 1).take 2 = [true, true]) &&
    decide (oldPrev + 2 = current)

/-- Mutant: reuse the k=4 `+ 3` offset. -/
def finalizeK3AsK4 (bits : List Bool) (oldPrev current : Nat) : Bool :=
  decide ((bits.drop 1).take 2 = [true, true]) &&
    decide (oldPrev + 3 = current)

theorem finalizeK3_hits :
    finalizeK3 [false, true, true, false] 0 2 = true := by
  decide

theorem finalizeK3_ne_asK4 :
    finalizeK3 [false, true, true, false] 0 3 ≠
      finalizeK3AsK4 [false, true, true, false] 0 3 := by
  decide

/-- phase0:1937-1938. 1st/2nd/3rd justified; source is old current + 2. -/
def finalizeK2FromOldCurr (bits : List Bool) (oldCurr current : Nat) : Bool :=
  decide (bits.take 3 = [true, true, true]) &&
    decide (oldCurr + 2 = current)

/-- Mutant: source from old previous. -/
def finalizeK2FromOldPrev (bits : List Bool) (oldPrev current : Nat) : Bool :=
  decide (bits.take 3 = [true, true, true]) &&
    decide (oldPrev + 2 = current)

theorem finalizeK2FromOldCurr_hits :
    finalizeK2FromOldCurr [true, true, true, false] 0 2 = true := by
  decide

theorem finalizeK2FromOldCurr_ne_oldPrev :
    finalizeK2FromOldCurr [true, true, true, false] 0 2 ≠
      finalizeK2FromOldPrev [true, true, true, false] 1 2 := by
  decide

/-- phase0:1940-1941. 1st/2nd justified; source is old current + 1. -/
def finalizeK2Recent (bits : List Bool) (oldCurr current : Nat) : Bool :=
  decide (bits.take 2 = [true, true]) &&
    decide (oldCurr + 1 = current)

theorem finalizeK2Recent_hits :
    finalizeK2Recent [true, true, false, false] 5 6 = true := by
  decide

theorem finalizeK2Recent_ne_requiresThird :
    finalizeK2Recent [true, true, false, false] 5 6 ≠
      finalizeK2FromOldCurr [true, true, false, false] 5 6 := by
  decide

/-- phase0:1931-1941. Independent `if`s; later windows overwrite.
0 = none, 1 = old previous, 2 = old current. -/
def finalizedEpochSource (bits : List Bool) (oldPrev oldCurr current : Nat) : Nat :=
  let afterK4 := if finalizeK4 bits oldPrev current then 1 else 0
  let afterK3 := if finalizeK3 bits oldPrev current then 1 else afterK4
  let afterK2a := if finalizeK2FromOldCurr bits oldCurr current then 2 else afterK3
  if finalizeK2Recent bits oldCurr current then 2 else afterK2a

/-- Mutant: `elif` so the first matching window wins. -/
def finalizedEpochSourceElif (bits : List Bool) (oldPrev oldCurr current : Nat) : Nat :=
  if finalizeK4 bits oldPrev current then 1
  else if finalizeK3 bits oldPrev current then 1
  else if finalizeK2FromOldCurr bits oldCurr current then 2
  else if finalizeK2Recent bits oldCurr current then 2
  else 0

theorem finalizedEpochSource_later_overwrites :
    finalizedEpochSource [true, true, true, true] 0 1 3 = 2 := by
  decide

theorem finalizedEpochSource_ne_elif :
    finalizedEpochSource [true, true, true, true] 0 1 3 ≠
      finalizedEpochSourceElif [true, true, true, true] 0 1 3 := by
  decide

/-- phase0:1966-1972. Leak when delay `> 4`. -/
def getFinalityDelay (previousEpoch finalizedEpoch : Nat) : Nat :=
  previousEpoch - finalizedEpoch

def isInInactivityLeak (previousEpoch finalizedEpoch : Nat) : Bool :=
  decide (MIN_EPOCHS_TO_INACTIVITY_PENALTY <
    getFinalityDelay previousEpoch finalizedEpoch)

theorem isInInactivityLeak_at_four :
    isInInactivityLeak 5 1 = false := by
  decide

theorem isInInactivityLeak_at_five :
    isInInactivityLeak 6 1 = true := by
  decide

/-- Altair:760-775. Participate decrements 1; else +bias; recover off-leak. -/
def inactivityScoreStep (score : Nat) (participated leak : Bool) : Nat :=
  let after :=
    if participated then score - min 1 score else score + INACTIVITY_SCORE_BIAS
  if leak then after
  else after - min INACTIVITY_SCORE_RECOVERY_RATE after

/-- Mutant: recover even during a leak. -/
def inactivityScoreStepAlwaysRecover (score : Nat) (participated : Bool) : Nat :=
  let after :=
    if participated then score - min 1 score else score + INACTIVITY_SCORE_BIAS
  after - min INACTIVITY_SCORE_RECOVERY_RATE after

theorem inactivityScoreStep_leak_keeps_bias :
    inactivityScoreStep 10 false true = 14 := by
  simp [inactivityScoreStep, INACTIVITY_SCORE_BIAS]

theorem inactivityScoreStep_ne_alwaysRecover :
    inactivityScoreStep 10 false true ≠
      inactivityScoreStepAlwaysRecover 10 false := by
  simp [inactivityScoreStep, inactivityScoreStepAlwaysRecover,
    INACTIVITY_SCORE_BIAS, INACTIVITY_SCORE_RECOVERY_RATE]

/-- Altair:481-482. Missing HEAD is not penalized. -/
def flagMissPenalty (flagIndex weight baseReward : Nat) : Nat :=
  if flagIndex = TIMELY_HEAD_FLAG_INDEX then 0
  else baseReward * weight / WEIGHT_DENOMINATOR

theorem flagMissPenalty_head_zero :
    flagMissPenalty TIMELY_HEAD_FLAG_INDEX TIMELY_HEAD_WEIGHT 64 = 0 :=
  rfl

theorem flagMissPenalty_target_nonzero :
    flagMissPenalty TIMELY_TARGET_FLAG_INDEX TIMELY_TARGET_WEIGHT 64 ≠ 0 := by
  decide

/-- Altair:477-480. Participating + leak pays 0; else
`base * weight * partInc // (activeInc * WEIGHT_DENOMINATOR)`.
Empty `activeInc` is Python `ZeroDivisionError`; Lean `n / 0 = 0`. -/
def flagReward (base weight partInc activeInc : Nat) (leak : Bool) : Nat :=
  if leak then 0
  else (base * weight * partInc) / (activeInc * WEIGHT_DENOMINATOR)

/-- Mutant: still pay the numerator during a leak. -/
def flagRewardAlwaysPay (base weight partInc activeInc : Nat) : Nat :=
  (base * weight * partInc) / (activeInc * WEIGHT_DENOMINATOR)

theorem flagReward_leak_zero :
    flagReward 64 TIMELY_TARGET_WEIGHT 32 32 true = 0 :=
  rfl

theorem flagReward_ne_alwaysPay :
    flagReward 64 TIMELY_TARGET_WEIGHT 32 32 true ≠
      flagRewardAlwaysPay 64 TIMELY_TARGET_WEIGHT 32 32 := by
  decide

theorem flagReward_empty_active_lean_zero :
    flagReward 64 TIMELY_TARGET_WEIGHT 32 0 false = 0 := by
  decide

/-- Altair:171 `INACTIVITY_PENALTY_QUOTIENT_ALTAIR = Uint64(3 * 2**24)`. -/
def INACTIVITY_PENALTY_QUOTIENT_ALTAIR : Nat := 3 * 2 ^ 24

/-- Bellatrix:125 `INACTIVITY_PENALTY_QUOTIENT_BELLATRIX = Uint64(2**24)`. -/
def INACTIVITY_PENALTY_QUOTIENT_BELLATRIX : Nat := 2 ^ 24

theorem inactivityPenaltyQuotient_bellatrix_is_third :
    INACTIVITY_PENALTY_QUOTIENT_BELLATRIX * 3 =
      INACTIVITY_PENALTY_QUOTIENT_ALTAIR :=
  rfl

/-- Altair:501-505. Matching-target skip and
`get_unslashed_participating_indices` stay named. -/
def inactivityPenaltyAltair (eb score : Nat) : Nat :=
  (eb * score) / (INACTIVITY_SCORE_BIAS * INACTIVITY_PENALTY_QUOTIENT_ALTAIR)

/-- Bellatrix:298-303. Gloas/Electra archived files do not redefine this
helper, so Gloas inherits the Bellatrix quotient. -/
def inactivityPenaltyBellatrix (eb score : Nat) : Nat :=
  (eb * score) / (INACTIVITY_SCORE_BIAS * INACTIVITY_PENALTY_QUOTIENT_BELLATRIX)

theorem inactivityPenalty_inherited_ne_altair :
    inactivityPenaltyBellatrix (32 * 10 ^ 9) 1 ≠
      inactivityPenaltyAltair (32 * 10 ^ 9) 1 := by
  decide

/-- phase0:634 `BASE_REWARD_FACTOR = Uint64(2**6)` (= 64). -/
def BASE_REWARD_FACTOR : Nat := 64

/-- Altair:386-391. `increments * get_base_reward_per_increment(state)`.
`integer_squareroot` / `get_total_active_balance` stay named on
`perIncrement`. -/
def baseRewardIncrements (eb : Nat) : Nat :=
  eb / EFFECTIVE_BALANCE_INCREMENT

def baseReward (eb perIncrement : Nat) : Nat :=
  baseRewardIncrements eb * perIncrement

/-- Mutant: multiply raw EB, dropping increment accounting. -/
def baseRewardNoIncrement (eb perIncrement : Nat) : Nat :=
  eb * perIncrement

theorem baseReward_is_increments :
    baseReward (32 * 10 ^ 9) 64 = 32 * 64 := by
  decide

theorem baseReward_ne_noIncrement :
    baseReward (32 * 10 ^ 9) 64 ≠
      baseRewardNoIncrement (32 * 10 ^ 9) 64 := by
  decide

/-- phase0:540 `UINT64_MAX = Uint64(2**64 - 1)`. -/
def UINT64_MAX : Nat := 2 ^ 64 - 1

/-- phase0:541 `UINT64_MAX_SQRT = Uint64(4294967295)`. -/
def UINT64_MAX_SQRT : Nat := 4294967295

/-- phase0:991-996. Newton iteration. `n = 0` returns 0 because
`y = (0 + 1) // 2` is not `< 0`. -/
def integerSquareRootNewton (n : Nat) : Nat :=
  if n = 0 then 0
  else
    let rec go : Nat → Nat → Nat
      | 0, x => x
      | fuel + 1, x =>
        let y := (x + n / x) / 2
        if y < x then go fuel y else x
    go n n

/-- phase0:985-996. The `UINT64_MAX` shortcut exists because Python
Uint64 `x + n // x` overflows; on `Nat` the Newton body agrees. -/
def integerSquareRoot (n : Nat) : Nat :=
  if n = UINT64_MAX then UINT64_MAX_SQRT
  else integerSquareRootNewton n

theorem integerSquareRoot_zero :
    integerSquareRoot 0 = 0 :=
  rfl

theorem integerSquareRoot_one :
    integerSquareRoot 1 = 1 :=
  rfl

theorem integerSquareRoot_nine :
    integerSquareRoot 9 = 3 :=
  rfl

theorem integerSquareRoot_ten :
    integerSquareRoot 10 = 3 :=
  rfl

theorem integerSquareRoot_uint64_max :
    integerSquareRoot UINT64_MAX = UINT64_MAX_SQRT :=
  rfl

theorem uint64MaxSqrt_squared_le :
    UINT64_MAX_SQRT * UINT64_MAX_SQRT ≤ UINT64_MAX := by
  decide

theorem uint64MaxSqrt_succ_squared_gt :
    UINT64_MAX < (UINT64_MAX_SQRT + 1) * (UINT64_MAX_SQRT + 1) := by
  decide

/-- Mutant: identity instead of the largest `x` with `x^2 ≤ n`. -/
theorem integerSquareRoot_ne_identity :
    integerSquareRoot 10 ≠ 10 := by
  decide

/-- Altair:369-374. `get_total_active_balance` is the input.
Empty active (sqrt 0) is Python `ZeroDivisionError`; Lean `n / 0 = 0`. -/
def baseRewardPerIncrement (totalActive : Nat) : Nat :=
  EFFECTIVE_BALANCE_INCREMENT * BASE_REWARD_FACTOR /
    integerSquareRoot totalActive

/-- Mutant: divide by raw total instead of `integer_squareroot`. -/
def baseRewardPerIncrementNoSqrt (totalActive : Nat) : Nat :=
  EFFECTIVE_BALANCE_INCREMENT * BASE_REWARD_FACTOR / totalActive

theorem baseRewardPerIncrement_ne_noSqrt :
    baseRewardPerIncrement 4 ≠ baseRewardPerIncrementNoSqrt 4 := by
  decide

theorem baseRewardPerIncrement_empty_lean_zero :
    baseRewardPerIncrement 0 = 0 :=
  rfl

/-- phase0:1508-1518. Empty indices still credit the increment
minimum so later divisions do not see 0. -/
def totalBalance (ebs : List Nat) : Nat :=
  max EFFECTIVE_BALANCE_INCREMENT ebs.sum

/-- Mutant: empty sum is 0. -/
def totalBalanceNoMin (ebs : List Nat) : Nat :=
  ebs.sum

theorem totalBalance_empty_is_increment :
    totalBalance [] = EFFECTIVE_BALANCE_INCREMENT :=
  rfl

theorem totalBalance_ne_noMin :
    totalBalance [] ≠ totalBalanceNoMin [] := by
  decide

/-- phase0:1525-1532. Active total is `get_total_balance` of the
active set; `get_active_validator_indices` stays named. -/
def totalActiveBalance (activeEbs : List Nat) : Nat :=
  totalBalance activeEbs

/-- phase0:1976-1983. Eligible if active at previous or slashed
and not yet withdrawable (`previous + 1 < withdrawable`). -/
structure EligibleView where
  activationEpoch : Nat
  exitEpoch : Nat
  slashed : Bool
  withdrawableEpoch : Nat

def isEligibleValidator (v : EligibleView) (previousEpoch : Nat) : Bool :=
  isActiveValidator v.activationEpoch v.exitEpoch previousEpoch ||
    (v.slashed && decide (previousEpoch + 1 < v.withdrawableEpoch))

/-- Mutant: drop the slashed-and-withdrawing disjunct. -/
def isEligibleValidatorActiveOnly (v : EligibleView) (previousEpoch : Nat) : Bool :=
  isActiveValidator v.activationEpoch v.exitEpoch previousEpoch

def exitedSlashedWithdrawing : EligibleView where
  activationEpoch := 0
  exitEpoch := 5
  slashed := true
  withdrawableEpoch := 10

def exitedUnslashed : EligibleView where
  activationEpoch := 0
  exitEpoch := 5
  slashed := false
  withdrawableEpoch := 10

theorem isEligibleValidator_slashed_withdrawing :
    isEligibleValidator exitedSlashedWithdrawing 5 = true := by
  decide

theorem isEligibleValidator_ne_activeOnly :
    isEligibleValidator exitedSlashedWithdrawing 5 ≠
      isEligibleValidatorActiveOnly exitedSlashedWithdrawing 5 := by
  decide

theorem isEligibleValidator_unslashed_exited :
    isEligibleValidator exitedUnslashed 5 = false := by
  decide

theorem isEligibleValidator_after_withdrawable :
    isEligibleValidator exitedSlashedWithdrawing 9 = false := by
  decide

/-- Altair:283 / 294. `flag = 2**flag_index`. -/
def flagBit (flagIndex : Nat) : Nat :=
  2 ^ flagIndex

/-- Altair:279-284. `flags | flag`. -/
def addFlag (flags flagIndex : Nat) : Nat :=
  flags ||| flagBit flagIndex

/-- Mutant: XOR toggles instead of OR. -/
def addFlagXor (flags flagIndex : Nat) : Nat :=
  flags ^^^ flagBit flagIndex

/-- Altair:290-295. `flags & flag == flag`. -/
def hasFlag (flags flagIndex : Nat) : Bool :=
  decide (flags &&& flagBit flagIndex = flagBit flagIndex)

/-- Mutant: require the whole byte to equal the single bit. -/
def hasFlagExact (flags flagIndex : Nat) : Bool :=
  decide (flags = flagBit flagIndex)

theorem land_lor_flagBit (flags index : Nat) :
    (flags ||| flagBit index) &&& flagBit index = flagBit index := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_land, Nat.testBit_lor]
  cases hf : (flagBit index).testBit j <;> simp [hf]

theorem addFlag_has (flags index : Nat) :
    hasFlag (addFlag flags index) index = true := by
  simp [hasFlag, addFlag, land_lor_flagBit]

theorem addFlag_ne_xor :
    addFlag 1 TIMELY_SOURCE_FLAG_INDEX ≠
      addFlagXor 1 TIMELY_SOURCE_FLAG_INDEX := by
  decide

theorem hasFlag_target_with_others :
    hasFlag 7 TIMELY_TARGET_FLAG_INDEX = true := by
  decide

theorem hasFlag_ne_exact :
    hasFlag 7 TIMELY_TARGET_FLAG_INDEX ≠
      hasFlagExact 7 TIMELY_TARGET_FLAG_INDEX := by
  decide

/-- phase0:1420-1426. Indices where `is_active_validator` holds. -/
def activeValidatorIndices (vs : List EligibleView) (epoch : Nat) : List Nat :=
  (vs.zip (List.range vs.length)).filterMap fun p =>
    if isActiveValidator p.1.activationEpoch p.1.exitEpoch epoch then some p.2
    else none

/-- Mutant: every registry index is active. -/
def allValidatorIndices (vs : List EligibleView) : List Nat :=
  List.range vs.length

def activatingLater : EligibleView where
  activationEpoch := 5
  exitEpoch := 10
  slashed := false
  withdrawableEpoch := 20

def activeNow : EligibleView where
  activationEpoch := 0
  exitEpoch := 10
  slashed := false
  withdrawableEpoch := 20

theorem activeValidatorIndices_filters :
    activeValidatorIndices [activatingLater, activeNow] 3 = [1] := by
  decide

theorem activeValidatorIndices_ne_all :
    activeValidatorIndices [activatingLater, activeNow] 3 ≠
      allValidatorIndices [activatingLater, activeNow] := by
  decide

/-- Altair:403. Epoch must be previous or current. -/
def participationEpochOk (epoch previousEpoch currentEpoch : Nat) : Bool :=
  decide (epoch = previousEpoch) || decide (epoch = currentEpoch)

theorem participationEpochOk_rejects_other :
    participationEpochOk 3 4 5 = false := by
  decide

/-- Altair:404-407. Current epoch reads current participation. -/
def participationBuffer (current previous : List Nat) (epoch currentEpoch : Nat) :
    List Nat :=
  if epoch = currentEpoch then current else previous

/-- Mutant: always the current buffer. -/
def participationBufferAlwaysCurrent (current _previous : List Nat)
    (_epoch _currentEpoch : Nat) : List Nat :=
  current

theorem participationBuffer_previous :
    participationBuffer [1] [2] 4 5 = [2] :=
  rfl

theorem participationBuffer_ne_alwaysCurrent :
    participationBuffer [1] [2] 4 5 ≠
      participationBufferAlwaysCurrent [1] [2] 4 5 := by
  decide

/-- Altair:408-412. Active, flagged, and not slashed. -/
structure ParticipatingView where
  active : Bool
  flags : Nat
  slashed : Bool

def isUnslashedParticipating (v : ParticipatingView) (flagIndex : Nat) : Bool :=
  v.active && hasFlag v.flags flagIndex && !v.slashed

/-- Mutant: keep slashed participants. -/
def isParticipatingKeepSlashed (v : ParticipatingView) (flagIndex : Nat) : Bool :=
  v.active && hasFlag v.flags flagIndex

def slashedTarget : ParticipatingView where
  active := true
  flags := flagBit TIMELY_TARGET_FLAG_INDEX
  slashed := true

def inactiveTarget : ParticipatingView where
  active := false
  flags := flagBit TIMELY_TARGET_FLAG_INDEX
  slashed := false

theorem isUnslashedParticipating_rejects_slashed :
    isUnslashedParticipating slashedTarget TIMELY_TARGET_FLAG_INDEX = false := by
  decide

theorem isUnslashedParticipating_ne_keepSlashed :
    isUnslashedParticipating slashedTarget TIMELY_TARGET_FLAG_INDEX ≠
      isParticipatingKeepSlashed slashedTarget TIMELY_TARGET_FLAG_INDEX := by
  decide

theorem isUnslashedParticipating_rejects_inactive :
    isUnslashedParticipating inactiveTarget TIMELY_TARGET_FLAG_INDEX = false := by
  decide

/-- phase0:613 `MIN_ATTESTATION_INCLUSION_DELAY = Slot(2**0)` (= 1). -/
def MIN_ATTESTATION_INCLUSION_DELAY : Nat := 1

/-- phase0:1403. `slot < state.slot ≤ slot + SLOTS_PER_HISTORICAL_ROOT`. -/
def blockRootSlotOk (slot stateSlot : Nat) : Bool :=
  decide (slot < stateSlot) &&
    decide (stateSlot ≤ slot + SLOTS_PER_HISTORICAL_ROOT)

/-- Mutant: allow `slot == state.slot`. -/
def blockRootSlotOkClosed (slot stateSlot : Nat) : Bool :=
  decide (slot ≤ stateSlot) &&
    decide (stateSlot ≤ slot + SLOTS_PER_HISTORICAL_ROOT)

theorem blockRootSlotOk_rejects_current :
    blockRootSlotOk 10 10 = false := by
  decide

theorem blockRootSlotOk_ne_closed :
    blockRootSlotOk 10 10 ≠ blockRootSlotOkClosed 10 10 := by
  decide

theorem blockRootSlotOk_accepts_window :
    blockRootSlotOk 0 SLOTS_PER_HISTORICAL_ROOT = true := by
  decide

theorem blockRootSlotOk_rejects_stale :
    blockRootSlotOk 0 (SLOTS_PER_HISTORICAL_ROOT + 1) = false := by
  decide

/-- phase0:1404. Index is `slot % SLOTS_PER_HISTORICAL_ROOT`. -/
def blockRootIndex (slot : Nat) : Nat :=
  slot % SLOTS_PER_HISTORICAL_ROOT

/-- Mutant: divide instead of mod. -/
def blockRootIndexDiv (slot : Nat) : Nat :=
  slot / SLOTS_PER_HISTORICAL_ROOT

theorem blockRootIndex_ne_div :
    blockRootIndex SLOTS_PER_HISTORICAL_ROOT ≠
      blockRootIndexDiv SLOTS_PER_HISTORICAL_ROOT := by
  decide

/-- phase0:1389-1393. Epoch root is the start-slot root, not the last slot. -/
def blockRootEpochSlot (epoch : Nat) : Nat :=
  startSlotAtEpoch epoch

/-- Mutant: last slot of the epoch. -/
def blockRootEpochSlotLast (epoch : Nat) : Nat :=
  startSlotAtEpoch (epoch + 1) - 1

theorem blockRootEpochSlot_ne_last :
    blockRootEpochSlot 1 ≠ blockRootEpochSlotLast 1 := by
  decide

/-- phase0:1843-1850. Target list keeps source atts whose root is the
epoch block root. `get_block_root` values stay named. -/
def matchingTarget (sourceAtts : List (Nat × Nat)) (epochRoot : Nat) :
    List (Nat × Nat) :=
  sourceAtts.filter fun a => a.2 = epochRoot

/-- Mutant: skip the target-root filter. -/
def matchingTargetNoRoot (sourceAtts : List (Nat × Nat)) (_epochRoot : Nat) :
    List (Nat × Nat) :=
  sourceAtts

theorem matchingTarget_filters :
    matchingTarget [(0, 1), (1, 9)] 1 = [(0, 1)] := by
  decide

theorem matchingTarget_ne_noRoot :
    matchingTarget [(0, 1), (1, 9)] 1 ≠
      matchingTargetNoRoot [(0, 1), (1, 9)] 1 := by
  decide

/-- Altair:444 / Gloas:1365. Source delay `≤ integer_squareroot(32)` (= 5). -/
def timelySourceDelayOk (delay : Nat) : Bool :=
  decide (delay ≤ integerSquareRoot SLOTS_PER_EPOCH)

/-- Altair:446. Target delay `≤ SLOTS_PER_EPOCH`. -/
def timelyTargetDelayOkAltair (delay : Nat) : Bool :=
  decide (delay ≤ SLOTS_PER_EPOCH)

/-- Gloas:1367. Target has no inclusion-delay bound. -/
def timelyTargetDelayOkGloas (_delay : Nat) : Bool :=
  true

/-- Altair:448 / Gloas:1369. Head delay `== MIN_ATTESTATION_INCLUSION_DELAY`. -/
def timelyHeadDelayOk (delay : Nat) : Bool :=
  decide (delay = MIN_ATTESTATION_INCLUSION_DELAY)

/-- Mutant: `≤` instead of `==`. -/
def timelyHeadDelayOkLe (delay : Nat) : Bool :=
  decide (delay ≤ MIN_ATTESTATION_INCLUSION_DELAY)

theorem timelySourceDelayOk_sqrt32 :
    timelySourceDelayOk 5 = true ∧ timelySourceDelayOk 6 = false := by
  decide

theorem timelyTarget_altair_ne_gloas :
    timelyTargetDelayOkAltair 33 ≠ timelyTargetDelayOkGloas 33 := by
  decide

theorem timelyHeadDelayOk_eq_one :
    timelyHeadDelayOk 1 = true ∧ timelyHeadDelayOk 0 = false := by
  decide

theorem timelyHeadDelayOk_ne_le :
    timelyHeadDelayOk 0 ≠ timelyHeadDelayOkLe 0 := by
  decide

/-- Altair:439. Head is target ∧ head-root. -/
def isMatchingHeadAltair (target head : Bool) : Bool :=
  target && head

/-- Gloas:1360. Head also requires payload availability. -/
def isMatchingHeadGloas (target head payload : Bool) : Bool :=
  target && head && payload

theorem isMatchingHead_gloas_needs_payload :
    isMatchingHeadGloas true true false ≠
      isMatchingHeadAltair true true := by
  decide

/-- Gloas:1348-1350. Same-slot attestations assert `data.index == 0`
and treat payload as matching. -/
def sameSlotIndexOk (index : Nat) : Bool :=
  decide (index = 0)

theorem sameSlotIndexOk_rejects_nonzero :
    sameSlotIndexOk 1 = false := by
  decide

/-- Gloas:1063-1074. Slot 0 is same-slot; else root equals this slot
and differs from the previous slot. Roots stay named. -/
def isAttestationSameSlot (dataSlot blockroot slotRoot prevRoot : Nat) : Bool :=
  if dataSlot = 0 then true
  else decide (blockroot = slotRoot) && decide (blockroot ≠ prevRoot)

/-- Mutant: ignore the previous-slot inequality (skipped slots). -/
def isAttestationSameSlotNoPrev (dataSlot blockroot slotRoot : Nat) : Bool :=
  if dataSlot = 0 then true
  else decide (blockroot = slotRoot)

theorem isAttestationSameSlot_genesis :
    isAttestationSameSlot 0 1 2 3 = true :=
  rfl

theorem isAttestationSameSlot_ne_noPrev :
    isAttestationSameSlot 5 7 7 7 ≠
      isAttestationSameSlotNoPrev 5 7 7 := by
  decide

/-- Altair:443-449. -/
def participationFlagsAltair (matchSource matchTarget matchHead : Bool)
    (delay : Nat) : List Nat :=
  let src :=
    if matchSource && timelySourceDelayOk delay then [TIMELY_SOURCE_FLAG_INDEX] else []
  let tgt :=
    if matchTarget && timelyTargetDelayOkAltair delay then [TIMELY_TARGET_FLAG_INDEX] else []
  let hd :=
    if matchHead && timelyHeadDelayOk delay then [TIMELY_HEAD_FLAG_INDEX] else []
  src ++ tgt ++ hd

/-- Gloas:1364-1370. Target drops the Altair delay bound. -/
def participationFlagsGloas (matchSource matchTarget matchHead : Bool)
    (delay : Nat) : List Nat :=
  let src :=
    if matchSource && timelySourceDelayOk delay then [TIMELY_SOURCE_FLAG_INDEX] else []
  let tgt :=
    if matchTarget then [TIMELY_TARGET_FLAG_INDEX] else []
  let hd :=
    if matchHead && timelyHeadDelayOk delay then [TIMELY_HEAD_FLAG_INDEX] else []
  src ++ tgt ++ hd

theorem participationFlags_gloas_target_no_delay :
    participationFlagsAltair true true true 33 ≠
      participationFlagsGloas true true true 33 := by
  decide

#print axioms timeAtSlotNat_spec
#print axioms timeAtSlot_spec
#print axioms envelope_timestamp
#print axioms fulu_process_epoch_preserves
#print axioms fulu_process_epoch_same_slot
#print axioms proposerLookaheadLength_eq
#print axioms shiftAndFill_length
#print axioms shiftAndFill_prefix
#print axioms shiftAndFill_suffix
#print axioms applyProposerLookahead_clock
#print axioms applyProposerLookahead_preserves
#print axioms timeFits_iff
#print axioms timeFits_of_bounded
#print axioms timeFits_min_genesis_zero
#print axioms timeFits_rejects_max_slot
#print axioms TIME_MOD_pos
#print axioms TIME_MOD_eq
#print axioms timeAtSlotWrap_lt
#print axioms timeAtSlotWrap_eq_of_fits
#print axioms timeAtSlot_eq_wrap
#print axioms timeFits_min_genesis_two_pow_60
#print axioms timeFits_above_min_genesis_zero
#print axioms timeFits_of_bounded_not_necessary
#print axioms two_pow_61_mul_12
#print axioms timeFits_rejects_min_genesis_two_pow_61
#print axioms timeAtSlotNat_min_genesis_two_pow_61
#print axioms timeAtSlotWrap_min_genesis_two_pow_61
#print axioms timeAtSlotNat_ne_wrap_two_pow_61
#print axioms startSlotAtEpoch_spec
#print axioms startSlotFits_iff
#print axioms startSlot_eq_of_fits
#print axioms startSlot_two_pow_59_nat
#print axioms startSlot_two_pow_59_wraps
#print axioms startSlot_two_pow_59_ne_wrap
#print axioms uintToBytes_length
#print axioms uintToBytes8_length
#print axioms uintFrom_to
#print axioms uintFrom_to8
#print axioms uintToBytes8_inj
#print axioms uintToBytes8_one
#print axioms uint_to_bytes_is_not_be
#print axioms seed_slot_u64_inj
#print axioms seedSlotU64s_length
#print axioms seedSlotU64s_nodup
#print axioms seedSlotU64s_wrap_nodup
#print axioms seedSlotU64_succ_ne
#print axioms proposerSeedPreimages_length
#print axioms proposerSeedPreimages_nodup
#print axioms constantSlotPreimages_not_nodup
#print axioms proposerSeedPreimage_ne_reversed
#print axioms domain_proposer_ne_attester
#print axioms getSeedPreimage_uses_proposer
#print axioms computeProposerSeedInputs_length
#print axioms computeProposerSeedInputs_nodup
#print axioms proposerSeeds_length
#print axioms proposerIndicesOfSeeds_length
#print axioms proposerLookahead_fill_from_seeds
#print axioms epochsPerHistoricalVector_eq
#print axioms getSeedMixEpoch_spec
#print axioms getSeedMixIndex_eq
#print axioms getSeedMixIndex_lt
#print axioms getSeedMixIndex_genesis
#print axioms getSeedMixIndex_epoch_two
#print axioms getSeedMix_ne_current_genesis
#print axioms getSeedMix_needs_vector
#print axioms getSeedMix_uses_lookahead
#print axioms getSeedPreimageFromMixes_eq
#print axioms maxRandomByte_eq
#print axioms maxEffectiveBalance_eq
#print axioms empty_proposer_indices
#print axioms sample_mod_lt
#print axioms proposerAccepts_max
#print axioms max_eb_accepts_any_byte
#print axioms proposerAccepts_eq_boundary
#print axioms proposerAcceptsStrict_boundary
#print axioms proposerAccepts_ge_not_gt
#print axioms proposerAccepts_zero_zero
#print axioms proposerAccepts_zero_pos
#print axioms randomByteOffset_lt
#print axioms randomBytePreimage_zero_eq_thirtyone
#print axioms randomBytePreimage_zero_ne_thirtytwo
#print axioms random_byte_uses_div_not_mod
#print axioms randomByteOf_is_byte
#print axioms max_eb_accepts_first_byte
#print axioms shuffleRoundCount_eq
#print axioms shuffleRoundCount_ne_hash32
#print axioms identityPerm_length
#print axioms identityPerm_get
#print axioms shuffled_index_rejects_eq
#print axioms shuffled_index_rejects_empty
#print axioms shuffledIndexOf_identity
#print axioms round_bytes_is_not_u64
#print axioms bucket_bytes_is_not_u64
#print axioms shufflePivotPreimage_ne_bucket
#print axioms shuffleFlip_lt
#print axioms shuffleFlip_of_lt
#print axioms shuffleFlip_involutive
#print axioms shuffleFlip_sample
#print axioms uintFromBytes_lt
#print axioms uintFromBytes_take8_lt
#print axioms hash32_take8_length
#print axioms shufflePivotRaw_lt
#print axioms shufflePivot_lt
#print axioms shufflePivot_empty
#print axioms samplePivotDigest_length
#print axioms samplePivotHash_like
#print axioms shufflePivot_uses_le_not_be
#print axioms shufflePosition_ge_idx
#print axioms shufflePosition_ge_flip
#print axioms shuffleBitByteIndex_lt
#print axioms shuffleBitShift_lt
#print axioms shuffle_bit_uses_position_not_index
#print axioms shuffle_shift_uses_position_not_index
#print axioms shuffleBitOf_lt
#print axioms shuffleBitOf_is_get
#print axioms shuffleSwapOrNot_zero
#print axioms shuffleSwapOrNot_one
#print axioms shuffleSwapOrNot_or
#print axioms shuffle_swap_is_not_on_zero
#print axioms shuffleStep_eq_or
#print axioms shuffleStep_lt
#print axioms shuffleRounds_length
#print axioms shuffleRounds_ne_empty
#print axioms shuffleIndexWalk_zero_rounds
#print axioms foldl_shuffleStep_lt
#print axioms shuffleIndexWalk_lt
#print axioms shufflePosition_comm
#print axioms shuffleFlip_shares_position
#print axioms shuffleFlip_shares_bit_index
#print axioms shuffleFlip_sample_shares_position
#print axioms shuffleFlip_inj
#print axioms shuffleStep_eq
#print axioms shuffleStep_pair
#print axioms shuffleStep_inj
#print axioms samplePairDigest_length
#print axioms samplePairHash_like
#print axioms shuffleStep_partners_distinct
#print axioms shuffleStep_at_index_collides
#print axioms shuffleRoundApply_length
#print axioms identityPerm_nodup
#print axioms identityPerm_lt
#print axioms shuffleRoundApply_lt
#print axioms shuffleRoundApply_nodup
#print axioms shuffleRoundApply_identity_nodup
#print axioms foldl_shuffleRoundApply_length
#print axioms foldl_shuffleRoundApply_lt
#print axioms foldl_shuffleRoundApply_nodup
#print axioms shufflePermutation_length
#print axioms shufflePermutation_lt
#print axioms shufflePermutation_nodup
#print axioms shufflePermutation_eq_nil
#print axioms shufflePermutation_nodup_all
#print axioms length_range_filter_ne
#print axioms shufflePermutation_mem
#print axioms shufflePermutation_perm
#print axioms out_of_range_not_identity_perm
#print axioms short_not_identity_perm
#print axioms foldl_map_getElem?
#print axioms shuffledIndexOf_walk
#print axioms sourceByBucket_eq_fresh
#print axioms shuffleBucket_window_zero
#print axioms shuffleBucket_next_window
#print axioms shuffleBucket_256
#print axioms cache_key_is_bucket_not_position
#print axioms sourceByBucket_same_window
#print axioms uintToBytes4_256
#print axioms source_preimage_uses_bucket
#print axioms source_uses_bucket_not_position
#print axioms shuffleFlip_shares_bucket
#print axioms BucketCacheOk_nil
#print axioms bucketCacheGet_nil
#print axioms bucketCacheGet_singleton
#print axioms sourceCacheStep_miss
#print axioms sourceCacheStep_hit
#print axioms bucketCacheGet_mem
#print axioms bucketCacheGet_ok
#print axioms sourceCacheStep_eq_fresh
#print axioms sourceCacheStep_preserves
#print axioms sourceCache_empty_then_hit
#print axioms shuffleStep_source_eq_cache
#print axioms shuffleBitShift_eq_window
#print axioms shuffleBit_decomp
#print axioms same_bucket_same_source
#print axioms same_bucket_distinct_byte
#print axioms same_bucket_distinct_shift
#print axioms same_bucket_window_offsets
#print axioms bit_byte_uses_mod_256
#print axioms bit_byte_raw_not_in_hash32
#print axioms shared_source_bits_differ
#print axioms bit_uses_offset_not_bucket_only
#print axioms shared_source_byte_defined
#print axioms shared_source_offsets_defined
#print axioms shuffleStep_source_eq_sourceByBucket
#print axioms shuffleStep_uses_cached_bit
#print axioms same_bucket_bit_source
#print axioms partners_share_cached_source
#print axioms partners_share_cached_bit
#print axioms echoByteHash_like
#print axioms cached_bit_ne_position_bit
#print axioms shuffleRoundBytes_eq
#print axioms shuffleRoundBytes_ne
#print axioms shuffleBucketPreimage_round_ne
#print axioms sourceByBucket_rounds_0_1
#print axioms source_preimage_uses_round
#print axioms mem_shuffleRounds_lt
#print axioms mem_shuffleRounds_no_wrap
#print axioms shuffleRounds_round_bytes_inj
#print axioms shuffleRounds_map_bytes_nodup
#print axioms uint8_round_256_collides_zero
#print axioms echoHeadHash_like
#print axioms sourceByBucket_round_ne_echo
#print axioms source_by_bucket_starts_empty
#print axioms each_round_starts_empty
#print axioms BucketCacheOk_singleton
#print axioms BucketCacheOk_two_rounds_hash_eq
#print axioms BucketCacheOk_fresh_not_other_round
#print axioms BucketCacheOk_echo_round_0_not_1
#print axioms sourceCacheStep_stale_round_hit
#print axioms shuffleStep_source_eq_empty_cache
#print axioms shuffleStep_eq_empty_cache
#print axioms foldl_shuffleStep_cons
#print axioms shuffleRounds_cons
#print axioms shuffleIndexWalk_first_step
#print axioms echoSplatHash_like
#print axioms shuffleStep_splat_round0_idx0
#print axioms shuffleStep_splat_round1_idx0
#print axioms two_rounds_not_fixed_round
#print axioms shufflePivotPreimage_length
#print axioms shuffleBucketPreimage_length
#print axioms shuffleBucketPreimage_eq_pivot_append
#print axioms shufflePivotPreimage_isPrefix
#print axioms shufflePivotPreimage_ne_bucket_forall
#print axioms pivot_preimage_omits_bucket
#print axioms shufflePivotPreimage_round_ne
#print axioms echoLenHash_like
#print axioms pivot_raw_ne_bucket_echoLen
#print axioms hash32_drop8_length
#print axioms hash32_drop24_length
#print axioms uintFromBytes_take8_congr
#print axioms shufflePivotRaw_eq_of_take8
#print axioms sampleTailDigest_length
#print axioms sampleTailHash_like
#print axioms take8_ignores_suffix_byte
#print axioms shufflePivotRaw_same_prefix
#print axioms pivot_raw_ne_drop8
#print axioms pivot_raw_ne_tail
#print axioms shufflePivot_eq_raw_mod
#print axioms shufflePivot_eq_of_lt
#print axioms shufflePivot_ne_raw_of_le
#print axioms samplePivotRaw_eq
#print axioms shuffleFlip_of_raw_eq_mod
#print axioms shuffleFlip_no_mod_eq
#print axioms shufflePivot_sample_mod_one
#print axioms shufflePivotNoMod_sample
#print axioms shufflePivotNoMod_not_lt
#print axioms shufflePivot_sample_lt
#print axioms shufflePivot_uses_mod
#print axioms shuffle_empty_count_named_div0
#print axioms getRandaoMixIndex_lt
#print axioms getRandaoMixIndex_wraps
#print axioms getRandaoMixIndex_add
#print axioms getRandaoMix_alias
#print axioms genesisRandaoMixes_length
#print axioms getRandaoMix_genesis
#print axioms getSeedPreimageFromMixes_eq_randao
#print axioms processRandaoMixesReset_length
#print axioms processRandaoMixesReset_next
#print axioms set_replicate_self
#print axioms processRandaoMixesReset_genesis
#print axioms sampleMixes_length
#print axioms sampleMixes_zero
#print axioms sampleMixes_pos
#print axioms getRandaoMix_sample_zero
#print axioms getRandaoMix_sample_pos
#print axioms getRandaoMix_seed_genesis_not_head
#print axioms getRandaoMix_seed_ne_zero_slot
#print axioms getRandaoMix_genesis_ne_epoch_bytes
#print axioms getRandaoMix_sample_wraps
#print axioms getSeedPreimage_tracks_mix_head
#print axioms bytesXor_length
#print axioms bytesXor_truncates
#print axioms bytesXor_zeros_left
#print axioms bytesXor_zeros_right
#print axioms bytesXor_self
#print axioms processRandao_length
#print axioms processRandao_current
#print axioms processRandao_other
#print axioms processRandaoCopy_length
#print axioms processRandaoCopy_current
#print axioms getRandaoMix_congr_list
#print axioms sampleMixZero_length
#print axioms samplePivotDigest_eq_mixOne
#print axioms bytesXor_zero_pivot
#print axioms processRandao_genesis_current
#print axioms processRandao_not_copy
#print axioms processRandao_next_unchanged
#print axioms processRandao_ne_reset
#print axioms processRandao_ne_copy_mutant
#print axioms getRandaoMixIndex_succ_ne
#print axioms processRandaoMixesReset_other
#print axioms processRandaoThenReset_length
#print axioms processResetThenRandao_length
#print axioms processRandaoThenReset_current
#print axioms processRandaoThenReset_next
#print axioms processRandaoThenReset_genesis_next
#print axioms processResetThenRandao_genesis_next
#print axioms processRandaoThenReset_ne_swapped
#print axioms processRandaoThenReset_genesis_current
#print axioms computeEpochAtSlot_spec
#print axioms computeEpochAtSlot_lt
#print axioms startSlot_of_computeEpoch
#print axioms getCurrentEpoch_eq_slot
#print axioms eth1VotingPeriod_ne_slashingsVector
#print axioms slashingsVector_ne_historical
#print axioms processEth1DataReset_keeps
#print axioms processEth1DataReset_clears
#print axioms processEth1DataReset_epoch_zero
#print axioms processEth1DataReset_epoch_sixty_three
#print axioms processEth1DataReset_ne_always
#print axioms getSlashingsIndex_lt
#print axioms processSlashingsReset_length
#print axioms processSlashingsReset_writes_zero
#print axioms processSlashingsReset_other
#print axioms processSlashingsResetCopy_length
#print axioms processSlashingsResetCopy_next
#print axioms processSlashingsReset_ne_copy
#print axioms historicalPeriod_eq
#print axioms historicalPeriod_ne_eth1
#print axioms historicalPeriod_ne_slashings
#print axioms slotsHistorical_eq_slashingsVector
#print axioms processHistoricalRootsUpdate_keeps
#print axioms processHistoricalRootsUpdate_appends
#print axioms processHistoricalSummariesUpdate_keeps
#print axioms processHistoricalSummariesUpdate_appends
#print axioms processHistoricalRootsUpdate_epoch_zero
#print axioms processHistoricalRootsUpdate_epoch_255
#print axioms processHistoricalRootsUpdate_ne_noDiv
#print axioms processHistoricalSummariesUpdate_epoch_zero
#print axioms processParticipationRecordUpdates_spec
#print axioms processParticipationFlagUpdates_spec
#print axioms participation_rotates_when_historical_keeps
#print axioms hysteresisIncrement_eq
#print axioms hysteresisIncrement_ne_increment
#print axioms downwardThreshold_eq
#print axioms upwardThreshold_eq
#print axioms hysteresis_band_asymmetric
#print axioms processEffectiveBalanceUpdate_keeps
#print axioms processEffectiveBalanceUpdate_writes
#print axioms effectiveBalanceOutOfBand_in_band_318
#print axioms processEffectiveBalanceUpdate_in_band_keeps
#print axioms processEffectiveBalanceUpdateAlways_in_band_floors
#print axioms processEffectiveBalanceUpdate_ne_always
#print axioms processEffectiveBalanceUpdate_zero_clears
#print axioms processEffectiveBalanceUpdate_phase0_caps
#print axioms processEffectiveBalanceUpdates_length
#print axioms processEffectiveBalanceUpdates_in_band_keeps
#print axioms syncCommitteePeriod_eq
#print axioms syncCommitteePeriod_eq_historical
#print axioms processSyncCommitteeUpdates_keeps
#print axioms processSyncCommitteeUpdates_rotates
#print axioms processSyncCommitteeUpdates_epoch_zero
#print axioms processSyncCommitteeUpdates_epoch_255
#print axioms processSyncCommitteeUpdates_ne_always
#print axioms processSyncCommitteeUpdates_fresh_named
#print axioms maxPendingDepositsPerEpoch_eq
#print axioms takePendingDeposits_unfinalized
#print axioms takePendingDeposits_finalized
#print axioms takePendingDeposits_replicate
#print axioms takePendingDeposits_sixteen
#print axioms takePendingDeposits_caps_at_sixteen
#print axioms takePendingDeposits_gloas_drops_eth1_bridge
#print axioms takePendingDepositsChurn_overflow_stops
#print axioms rewritePendingDeposits_postpones_exited
#print axioms depositBalanceToConsume_clears
#print axioms depositBalanceToConsume_ne_always
#print axioms builderPaymentQuorum_ne_noSlot
#print axioms creditedBuilderWeights_first_window
#print axioms creditedBuilderWeights_ne_all
#print axioms rotateBuilderPayments_length
#print axioms rotateBuilderPayments_prefix
#print axioms rotateBuilderPayments_suffix
#print axioms maxSeedLookahead_eq
#print axioms withdrawabilityDelay_eq
#print axioms ejectionBalance_eq
#print axioms ejectionBalance_ne_maxEB
#print axioms computeActivationExitEpoch_spec
#print axioms computeActivationExitEpoch_epoch_zero
#print axioms computeActivationExitEpoch_ne_noLookahead
#print axioms isActiveValidator_inside
#print axioms isActiveValidator_at_exit
#print axioms isActiveValidator_before_activation
#print axioms isActiveValidator_ne_closed
#print axioms consolidationAmount_is_min
#print axioms consolidationStep_skips_slashed
#print axioms consolidationStep_stops_unwithdrawable
#print axioms consolidationStep_transfers_ready
#print axioms consolidationStep_ne_transferSlashed
#print axioms consumedPendingConsolidations_skips_slashed
#print axioms consumedPendingConsolidations_stops
#print axioms rewritePendingConsolidations_keeps_blocked
#print axioms churnQuotient_gloas_is_half
#print axioms exitChurnLimitGloas_ne_electra_quotient
#print axioms additionalExitEpochs_ceils
#print axioms additionalExitEpochs_ne_floor
#print axioms computeExitEpochAndUpdateChurn_resets_new_epoch
#print axioms computeExitEpochAndUpdateChurn_ne_keep
#print axioms computeExitEpochAndUpdateChurn_keeps_leftover
#print axioms computeExitEpochAndUpdateChurn_overflow_ceils
#print axioms slashingPenaltyOffset_eq
#print axioms appliesSlashingPenalty_mid
#print axioms appliesSlashingPenalty_not_slashed
#print axioms appliesSlashingPenalty_ne_full
#print axioms slashingPenaltyElectra_ne_phase0
#print axioms genesisEpoch_eq
#print axioms justificationBitsLength_eq
#print axioms getPreviousEpoch_genesis
#print axioms getPreviousEpoch_succ
#print axioms skipsJustification_epoch_one
#print axioms skipsInactivityUpdates_epoch_one
#print axioms skipsJustification_ne_inactivity_at_one
#print axioms justifiesSupermajority_exact_two_thirds
#print axioms justifiesSupermajority_ne_strict
#print axioms shiftJustificationBits_spec
#print axioms shiftJustificationBits_ne_rev
#print axioms finalizeK4_hits
#print axioms finalizeK4_needs_source
#print axioms isInInactivityLeak_at_four
#print axioms isInInactivityLeak_at_five
#print axioms inactivityScoreStep_leak_keeps_bias
#print axioms inactivityScoreStep_ne_alwaysRecover
#print axioms flagMissPenalty_head_zero
#print axioms flagMissPenalty_target_nonzero
#print axioms finalizeK3_hits
#print axioms finalizeK3_ne_asK4
#print axioms finalizeK2FromOldCurr_hits
#print axioms finalizeK2FromOldCurr_ne_oldPrev
#print axioms finalizeK2Recent_hits
#print axioms finalizeK2Recent_ne_requiresThird
#print axioms finalizedEpochSource_later_overwrites
#print axioms finalizedEpochSource_ne_elif
#print axioms flagReward_leak_zero
#print axioms flagReward_ne_alwaysPay
#print axioms flagReward_empty_active_lean_zero
#print axioms inactivityPenaltyQuotient_bellatrix_is_third
#print axioms inactivityPenalty_inherited_ne_altair
#print axioms baseReward_is_increments
#print axioms baseReward_ne_noIncrement
#print axioms integerSquareRoot_zero
#print axioms integerSquareRoot_one
#print axioms integerSquareRoot_nine
#print axioms integerSquareRoot_ten
#print axioms integerSquareRoot_uint64_max
#print axioms uint64MaxSqrt_squared_le
#print axioms uint64MaxSqrt_succ_squared_gt
#print axioms integerSquareRoot_ne_identity
#print axioms baseRewardPerIncrement_ne_noSqrt
#print axioms baseRewardPerIncrement_empty_lean_zero
#print axioms totalBalance_empty_is_increment
#print axioms totalBalance_ne_noMin
#print axioms isEligibleValidator_slashed_withdrawing
#print axioms isEligibleValidator_ne_activeOnly
#print axioms isEligibleValidator_unslashed_exited
#print axioms isEligibleValidator_after_withdrawable
#print axioms land_lor_flagBit
#print axioms addFlag_has
#print axioms addFlag_ne_xor
#print axioms hasFlag_target_with_others
#print axioms hasFlag_ne_exact
#print axioms activeValidatorIndices_filters
#print axioms activeValidatorIndices_ne_all
#print axioms participationEpochOk_rejects_other
#print axioms participationBuffer_previous
#print axioms participationBuffer_ne_alwaysCurrent
#print axioms isUnslashedParticipating_rejects_slashed
#print axioms isUnslashedParticipating_ne_keepSlashed
#print axioms isUnslashedParticipating_rejects_inactive
#print axioms blockRootSlotOk_rejects_current
#print axioms blockRootSlotOk_ne_closed
#print axioms blockRootSlotOk_accepts_window
#print axioms blockRootSlotOk_rejects_stale
#print axioms blockRootIndex_ne_div
#print axioms blockRootEpochSlot_ne_last
#print axioms matchingTarget_filters
#print axioms matchingTarget_ne_noRoot
#print axioms timelySourceDelayOk_sqrt32
#print axioms timelyTarget_altair_ne_gloas
#print axioms timelyHeadDelayOk_eq_one
#print axioms timelyHeadDelayOk_ne_le
#print axioms isMatchingHead_gloas_needs_payload
#print axioms sameSlotIndexOk_rejects_nonzero
#print axioms isAttestationSameSlot_genesis
#print axioms isAttestationSameSlot_ne_noPrev
#print axioms participationFlags_gloas_target_no_delay
end Eip8282.Audit.Integrator.ProtocolSlotExtraction
