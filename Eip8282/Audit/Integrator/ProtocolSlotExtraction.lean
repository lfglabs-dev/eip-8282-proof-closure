import Eip8282.Audit.Integrator.ResourceBounds

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
follows from the Uint64 successor staying below the asserted target. Optional
`process_epoch` is an explicit clock-preservation adapter
(`EpochPreservesClock`).

OPEN (not proved here): the inherited `process_slots`/`process_block_header`
bodies of the absent intermediate fork files; the bodies of every
`process_epoch` callee (phase0:1815-1826, Gloas:1578-1598) — only their
non-assignment of the two clock fields is named; SSZ Uint64 decode to
`Fin (2^64)`; canonical chain/fork-choice selection of the accepted sequence;
`validate_header` still does not bind `header.slot_number` (fork.py:323).
The envelope slot equality is derived only for a `VerifiedEnvelopeSlot`
witness of fork-choice.md:685, not for an arbitrary EL header. -/
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

/-- Named adapter, not a callee-body extraction: none of the archived
`process_epoch` callees assign the two clock fields (phase0:1815-1826,
Gloas:1578-1598). Intermediate-fork helper bodies are absent. -/
structure EpochPreservesClock (pre post : Clock) : Prop where
  slot : post.slot = pre.slot
  header : post.header = pre.header

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
#print axioms accepted_last
#print axioms accepted_ne
#print axioms el_not_parent
#print axioms envelope_slot
#print axioms envelope_slots
end Eip8282.Audit.Integrator.ProtocolSlotExtraction
