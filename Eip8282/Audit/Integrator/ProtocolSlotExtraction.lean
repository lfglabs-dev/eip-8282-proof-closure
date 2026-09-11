import Eip8282.Audit.Integrator.ResourceBounds
import Mathlib.Data.List.Perm.Subperm

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
`source_by_bucket` cache / same-bucket bit offsets
(phase0:1197-1231) are extracted;
SHA256 pivot and swap-bit *values* stay uninterpreted; `compute_proposer_index`
nonempty assert, `MAX_RANDOM_BYTE` / `MAX_EFFECTIVE_BALANCE` accept
test, and `i // 32` random-byte preimage are extracted; the 32-seed
preimage list, little-endian `uint_to_bytes` / `ENDIANNESS`,
`compute_start_slot_at_epoch` wrap, and `get_seed` mix index
(phase0:1449-1451 / 1414) are extracted;
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

theorem shufflePivot_uses_le_not_be :
    shufflePivot samplePivotHash [] 0 8 ≠
      shufflePivotBe samplePivotHash [] 0 8 := by
  have hle : shufflePivotRaw samplePivotHash [] 0 = 1 := by
    simp [shufflePivotRaw, samplePivotHash, samplePivotDigest, uintFromBytes]
  have hbe : shufflePivotRawBe samplePivotHash [] 0 = 2 ^ 56 := by
    simp [shufflePivotRawBe, samplePivotHash, samplePivotDigest, uintFromBytes]
  simp [shufflePivot, shufflePivotBe, hle, hbe]

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
end Eip8282.Audit.Integrator.ProtocolSlotExtraction
