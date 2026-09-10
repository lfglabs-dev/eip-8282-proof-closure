import Eip8282.Audit.Integrator.ProtocolWithdrawalStageExtraction

/-! The Gloas expected-withdrawal cache is retained on an empty parent.
Pinned CL ad0058fd0d34c5dcf504fa51ea2f4f11077b9996:
beacon-chain.md1999-2011 returns before assignment for an empty parent;
update_payload_expected_withdrawals1937-1940 assigns the computed list otherwise.
fork.md221 initializes it to Withdrawals(). The full bodies are archived in
 direct-cl-inheritance-sources-20260910.json.

This handles the cache state, not merely lists newly computed at each block.
Every later payload may expose the retained list; no at-most-once minting of a
computed list is assumed. Per-payload bounds and distinct accepted slots suffice
for the count. Actual CL candidates, SSZ decoding, root-check-to-list binding,
execution engine admission and canonical EL/CL selection remain producers. -/
namespace Eip8282.Audit.Integrator.ProtocolWithdrawalExpectationState
open EvmYul EvmYul.EVM
open ProtocolWithdrawalCount ProtocolSlotExtraction ProtocolCreditEnvelope
open ProtocolWithdrawalExtraction (Block expected expectedPayload AcceptedBlocks)
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Literal storage update of the cached expected list. -/
def update (cached : List Item) (block : Block) : List Item :=
  if block.parentFull then expected block else cached

theorem expected_bounded (block : Block) : (expected block).length ≤ 16 :=
  (expectedPayload block).bounded

theorem update_bounded {cached : List Item} (bound : cached.length ≤ 16) (block : Block) :
    (update cached block).length ≤ 16 := by
  unfold update
  split
  · exact expected_bounded block
  · exact bound

/-- An empty parent retains the previous expected list; it does not clear it. -/
theorem retained (cached : List Item) (block : Block) (empty : block.parentFull = false) :
    update cached block = cached := by simp [update,empty]

/-- Payload list at each successive accepted beacon slot, computed from the
same cache recurrence. The bound field is produced by the loop proof. -/
def payloadsFrom (cached : List Item) (bound : cached.length ≤ 16) : List Block → List Payload
  | [] => []
  | block::rest =>
    let next := update cached block
    let nextBound := update_bounded bound block
    {slot := block.slot,items := next,bounded := nextBound}::payloadsFrom next nextBound rest

/-- Exact empty initialization in upgrade_to_gloas, followed by arbitrary
finitely many cached-list updates. No initial list-size assumption is supplied. -/
def payloads (blocks : List Block) : List Payload := payloadsFrom [] (by simp) blocks

theorem payload_slots (blocks : List Block) (cached : List Item) (bound : cached.length ≤ 16) :
    (payloadsFrom cached bound blocks).map (·.slot) = blocks.map (·.slot) := by
  induction blocks generalizing cached with
  | nil => rfl
  | cons block rest ih =>
    simp only [payloadsFrom,List.map_cons]
    exact congrArg (block.slot :: ·) (ih _ _)

/-- The complete cached lists, including repetitions after empty parents,
remain bounded by sixteen entries per distinct accepted slot. -/
theorem total_count {pre post : Clock} (blocks : List Block)
    (accepted : AcceptedBlocks pre blocks post) : totalItems (payloads blocks) ≤ 16*2^64 := by
  apply ProtocolWithdrawalCount.total_count
  rw [payloads,payload_slots]
  exact ProtocolSlotExtraction.accepted_nodup accepted

/-- Credit the actual supplied dispatch of these cached lists, with no
filtering or deduplication of equal contents, recipients or amounts. The source
root-check/engine binding must still supply this exact Dispatch premise. -/
theorem dispatched_counts {initial before after : AccountMap .EVM} {p s c : Nat}
    {pre post : Clock} (prior : Ledger initial p 0 s c before) (blocks : List Block)
    (accepted : AcceptedBlocks pre blocks post)
    (run : Dispatch before ((payloads blocks).flatMap (·.items)) after)
    (powBound : p ≤ 2^64) (migrationConserving : s=0) :
    Ledger initial p (totalItems (payloads blocks)) s
      (c+credits ((payloads blocks).flatMap (·.items))) after ∧
    Counts p (totalItems (payloads blocks)) s := by
  apply ProtocolWithdrawalCount.dispatched_counts prior (payloads blocks) run
  · rw [payloads,payload_slots]
    exact ProtocolSlotExtraction.accepted_nodup accepted
  · exact powBound
  · exact migrationConserving

/-- Compose the inherited-loop producers with the persistent cache. Inputs
contain candidates only, with no supplied output-length or guarded-list field. -/
theorem candidate_total_count {pre post : Clock}
    (inputs : List ProtocolWithdrawalStageExtraction.Inputs)
    (accepted : Accepted pre (inputs.map (·.slot)) post) :
    totalItems (payloads (inputs.map ProtocolWithdrawalStageExtraction.block)) ≤ 16*2^64 := by
  apply total_count
  simpa only [AcceptedBlocks,List.map_map,Function.comp_def,
    ProtocolWithdrawalStageExtraction.block_slot] using accepted

/-- The funding consumer now receives the derived guards and retained cache
from raw stage inputs. Actual dispatch/chronology/context extraction stays open. -/
theorem candidate_dispatched_counts {initial before after : AccountMap .EVM} {p s c : Nat}
    {pre post : Clock} (prior : Ledger initial p 0 s c before)
    (inputs : List ProtocolWithdrawalStageExtraction.Inputs)
    (accepted : Accepted pre (inputs.map (·.slot)) post)
    (run : Dispatch before
      ((payloads (inputs.map ProtocolWithdrawalStageExtraction.block)).flatMap (·.items)) after)
    (powBound : p ≤ 2^64) (migrationConserving : s=0) :
    Ledger initial p (totalItems (payloads (inputs.map ProtocolWithdrawalStageExtraction.block))) s
      (c+credits ((payloads (inputs.map ProtocolWithdrawalStageExtraction.block)).flatMap (·.items))) after ∧
    Counts p (totalItems (payloads (inputs.map ProtocolWithdrawalStageExtraction.block))) s := by
  have chronology : AcceptedBlocks pre (inputs.map ProtocolWithdrawalStageExtraction.block) post := by
    simpa only [AcceptedBlocks,List.map_map,Function.comp_def,
      ProtocolWithdrawalStageExtraction.block_slot] using accepted
  exact dispatched_counts prior (inputs.map ProtocolWithdrawalStageExtraction.block) chronology run powBound migrationConserving

#print axioms expected_bounded
#print axioms update_bounded
#print axioms retained
#print axioms payload_slots
#print axioms total_count
#print axioms dispatched_counts
#print axioms candidate_total_count
#print axioms candidate_dispatched_counts
end Eip8282.Audit.Integrator.ProtocolWithdrawalExpectationState
