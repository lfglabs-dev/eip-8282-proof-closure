import Eip8282.Audit.Integrator.ProtocolWithdrawalExtraction

/-! Count guards for the inherited Electra helpers under proposed Gloas at CL
pin ad0058fd0d34c5dcf504fa51ea2f4f11077b9996. Electra beacon-chain.md
SHA256c722ff14969bc58c3b348ff059a40f413d9598509692b470c3832f64662a11a8:
pending helper1360-1398, validators helper1407-1454, pending maximum8 at338.
Gloas beacon-chain.md SHA25610b7decc3dd86a1e4921f8cf49081c87dc528d61631bc83646cb5d6a062c65ce
1879-1917 retains builder pending, pending partial, builder sweep, validator
sweep order. Capella beacon-chain.md138 / mainnet capella preset11 supplies16.

Candidates carry the actual branch results and emitted items as inputs; their
correlation with CL state, balance-after-prior-withdrawals and visit order is
OPEN. Arbitrary eligibility and finite visit counts suffice for this count
bound, not for exact source output extraction. Pending limit is fixed ONCE
from initial prior length; maturity/limit stop occurs before eligibility.
The source8 limit caps appended partial withdrawals, not all ineligible visits.
No output length/guard is supplied to the Block constructor. No Python/SSZ
refinement, canonical adoption, or CL-to-EL dispatch identity is asserted. -/
namespace Eip8282.Audit.Integrator.ProtocolWithdrawalStageExtraction
open EvmYul EvmYul.EVM
open ProtocolWithdrawalCount ProtocolWithdrawalExtraction ProtocolSlotExtraction
open ResourceBounds (U64)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

structure PartialCandidate where
  item : Item
  mature : Bool
  eligible : Bool

/-- The fixed limit is not recomputed from the growing combined count. -/
def pendingLoop (limit prior : Nat) : List PartialCandidate → List Item
  | [] => []
  | candidate::rest =>
    if !candidate.mature || decide (limit ≤ prior) then []
    else if candidate.eligible then candidate.item::pendingLoop limit (prior+1) rest
    else pendingLoop limit prior rest

def pendingStage (prior : Nat) (candidates : List PartialCandidate) : List Item :=
  pendingLoop (min (prior+8) 15) prior candidates

private theorem pendingLoop_guarded (limit : Nat) (candidates : List PartialCandidate) :
    ∀ prior, prior ≤ limit → GuardedAdds limit prior (pendingLoop limit prior candidates) := by
  induction candidates with
  | nil => intro prior bound; exact .nil bound
  | cons candidate rest ih =>
    intro prior bound
    unfold pendingLoop
    split
    · exact .nil bound
    · rename_i keepGoing
      have less : prior < limit := by
        by_contra h
        have reached : limit ≤ prior := by omega
        simp [reached] at keepGoing
      split
      · exact .cons less (ih (prior+1) (by omega))
      · exact ih prior bound

/-- The entry assert and every subsequent append guard follow from prior≤15. -/
theorem pendingStage_guarded (prior : Nat) (candidates : List PartialCandidate)
    (bound : prior ≤ 15) :
    GuardedAdds (min (prior+8) 15) prior (pendingStage prior candidates) := by
  exact pendingLoop_guarded _ candidates prior (by omega)

theorem pendingStage_bound (prior : Nat) (candidates : List PartialCandidate)
    (bound : prior ≤ 15) :
    prior+(pendingStage prior candidates).length ≤ 15 ∧
      (pendingStage prior candidates).length ≤ 8 := by
  have h := guarded_length (pendingStage_guarded prior candidates bound)
  omega

/-- Raw candidate inputs only: no partialBound or validatorsGuard field. -/
structure Inputs where
  slot : U64
  parentFull : Bool
  pending : List Item
  partialCandidates : List PartialCandidate
  builders : List (Item × Bool)
  validators : List (Item × Bool)

/-- Produce the existing block consumer and its two previously supplied guards. -/
def block (input : Inputs) : Block :=
  let first := queueStage 15 0 input.pending
  let partials := pendingStage first.length input.partialCandidates
  let prior := first.length+partials.length
  let builders := sweepStage 15 prior input.builders
  let validatorsPrior := prior+builders.length
  {slot := input.slot, parentFull := input.parentFull, pending := input.pending,
   pendingPartial := partials,
   partialBound := by
     have h := guarded_length (queueStage_guarded 15 input.pending 0 (by omega))
     exact (pendingStage_bound first.length input.partialCandidates (by simpa [first] using h)).1,
   builders := input.builders,
   validators := sweepStage 16 validatorsPrior input.validators,
   validatorsGuard := by
     have hfirst := guarded_length (queueStage_guarded 15 input.pending 0 (by omega))
     have hpartial : prior ≤ 15 :=
       (pendingStage_bound first.length input.partialCandidates (by simpa [first] using hfirst)).1
     have hbuilders := guarded_length (sweepStage_guarded 15 input.builders prior hpartial)
     change prior+builders.length ≤ 15 at hbuilders
     have reserved : validatorsPrior < 16 := by change prior+builders.length < 16; omega
     exact sweepStage_guarded 16 input.validators validatorsPrior (by omega)}

theorem block_slot (input : Inputs) : (block input).slot = input.slot := rfl

/-- Consume the constructed guards in the existing per-block theorem. -/
theorem items_bounded (input : Inputs) : (items (block input)).length ≤ 16 :=
  ProtocolWithdrawalExtraction.items_bounded (block input)

/-- Existing accepted-slot chronology supplies lifetime counting; neither
slot uniqueness nor any output count is introduced as an extra premise. -/
theorem total_count {pre post : Clock} (inputs : List Inputs)
    (accepted : Accepted pre (inputs.map (·.slot)) post) :
    (inputs.map (fun input => (items (block input)).length)).sum ≤ 16*2^64 := by
  have h : AcceptedBlocks pre (inputs.map block) post := by
    simpa only [AcceptedBlocks,List.map_map,Function.comp_def,block_slot] using accepted
  simpa only [List.map_map,Function.comp_def] using ProtocolWithdrawalExtraction.total_count (inputs.map block) h

#print axioms pendingStage_guarded
#print axioms pendingStage_bound
#print axioms block_slot
#print axioms items_bounded
#print axioms total_count
end Eip8282.Audit.Integrator.ProtocolWithdrawalStageExtraction
