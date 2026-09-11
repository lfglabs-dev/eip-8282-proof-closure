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

OPEN (explicit hypotheses or adapters, not proved): the inherited
`get_pending_partial_withdrawals` and `get_validators_sweep_withdrawals`
bodies are absent from the archived corpus; the partial stage's combined
length bound is taken from the archived assert at line 1847 (`partialBound`),
while the validators-sweep guarded trace stays a structure field
(`validatorsGuard`, no ProgressiveList cap exists); SSZ Gwei/Uint64 decode to
`Item`; the CL-to-EL list transport: lines 2022-2027 remove
`process_execution_payload`, and neither its replacement
`verify_execution_payload_envelope` nor `on_execution_payload_envelope` is in
the archived body, so nowhere in the bundle is EL `block.withdrawals` equated
to `state.payload_expected_withdrawals` (line 1940); on the line-1999 early
return that field is not cleared, so a list computed at one block may be
minted by a later payload — `BlockCredits` follows CL computation order
(`items`), not the retained-cache EL execution order of
`ProtocolWithdrawalExpectationState`; `CreateEther` is the named
create_ether/`increaseBalance` agreement, not a Python interpreter proof;
canonical selection of the accepted sequence; PoW count and migration
conservation, which stay independent inputs of the consumer. -/
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
end Eip8282.Audit.Integrator.ProtocolWithdrawalExtraction
