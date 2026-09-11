import Eip8282.Audit.Integrator.ReferenceAppendCompletedCost
import Eip8282.Audit.Integrator.ReferenceTransactionWork

/-! Actual completed protected payments supply the leaf costs in a finite
nested resource ledger. Selection denotes a subset of executed completed
frames, not the full protocol occurrence enumeration. In particular skipped
resource runs may contain unselected appends. A retained-history consumer must
produce this selection for every retained occurrence, with its source journals;
that extraction is not assumed complete merely because the arithmetic closes.
Selected child work remains counted when its parent later reverts. -/
namespace Eip8282.Audit.Integrator.ReferenceSelectedAppendWork
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Jumpdests
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceMeterBoundary ReferenceCallGrant ReferenceChildMeter ReferenceCallChildBoundary
open ReferenceExecutionLedger ReferenceCallPotential ReferenceAppendCompletedCost
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

inductive ProtectedPaid : Meter → Meter → Nat → Prop where
  | exit (c : XiCall .exit) {fuel : Nat} {final : EVM.State} {out : ByteArray}
      (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 48)
      (actual : X fuel exitJumpdests c.entry = .ok (.success final out))
      (t : SuccessInversion.SuccessTrace exitJumpdests fuel c.entry final out)
      {p : Parent} {created : Set AccountAddress} {v last : View} {w finalWarm : Warm} {events : List Event}
      (priced : Coupled .exit p created fuel c.entry v w t.trace (t.rem+1) t.exit last finalWarm events)
      {pre post : Meter} (amount : Nat) (paid : runFull (events++[.ordinary amount]) pre = some post) :
      ProtectedPaid pre post (work (events++[.ordinary amount]))
  | deposit (c : XiCall .deposit) {fuel : Nat} {final : EVM.State} {out : ByteArray}
      (user : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr) (size : c.env.calldata.size = 184)
      (actual : X fuel depositJumpdests c.entry = .ok (.success final out))
      (t : SuccessInversion.SuccessTrace depositJumpdests fuel c.entry final out)
      {p : Parent} {created : Set AccountAddress} {v last : View} {w finalWarm : Warm} {events : List Event}
      (priced : Coupled .deposit p created fuel c.entry v w t.trace (t.rem+1) t.exit last finalWarm events)
      {pre post : Meter} (amount : Nat) (paid : runFull (events++[.ordinary amount]) pre = some post) :
      ProtectedPaid pre post (work (events++[.ordinary amount]))

theorem ProtectedPaid.cost {pre post : Meter} {executed : Nat} (h : ProtectedPaid pre post executed) :
    1419 ≤ executed := by
  cases h with
  | exit c user size actual t priced amount paid =>
    have bound := exit_cost c user size actual t priced
    simp only [work,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      eventWork,Nat.add_zero] at bound ⊢
    omega
  | deposit c user size actual t priced amount paid =>
    have bound := deposit_cost c user size actual t priced
    simp only [work,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      eventWork,Nat.add_zero] at bound ⊢
    omega

theorem ProtectedPaid.run {pre post : Meter} {executed : Nat} (h : ProtectedPaid pre post executed) :
    Run pre post executed := by
  cases h with
  | exit c user size actual t priced amount paid => exact .paid _ paid
  | deposit c user size actual t priced amount paid => exact .paid _ paid

/-- Sequential pieces share exact returned meters. A selected protected leaf
contains its whole actual append trace, so it cannot also count a child or a
second overlapping piece of that same resource payment. Protocol occurrence
identity/completeness must still be supplied when constructing this selection. -/
inductive Selected : Meter → Meter → Nat → Nat → Prop where
  | skip {pre post : Meter} {executed : Nat} (h : Run pre post executed) : Selected pre post executed 0
  | append {pre post : Meter} {executed : Nat} (h : ProtectedPaid pre post executed) : Selected pre post executed 1
  | trans {pre mid post : Meter} {first second left right : Nat}
      (head : Selected pre mid first left) (tail : Selected mid post second right) :
      Selected pre post (first+second) (left+right)
  | call {pre charged child final : Meter} {childWork count : Nat}
      (cold delegated delegationCold hasValue deadRecipient : Bool) (memoryCost : Nat)
      (prepared : prepare cold delegated delegationCold hasValue deadRecipient memoryCost pre = some charged)
      (requested : UInt256) (outcome : Outcome)
      (body : Selected (start (split hasValue requested charged)) child childWork count)
      (finished : finish hasValue deadRecipient outcome (split hasValue requested charged) child = some final) :
      Selected pre final (overhead cold delegated delegationCold hasValue memoryCost+childWork) count
  | create {pre child final : Meter} {chargedCore : ReferenceStorageGas.Meter} {childWork count : Nat}
      (stateAmount : Nat) (charged : ReferenceStorageGas.chargeState (core pre) stateAmount = some chargedCore)
      (outcome : Outcome) (newAccount : Bool)
      (body : Selected (start (creationSplit (update pre chargedCore))) child childWork count)
      (finished : finish true newAccount outcome (creationSplit (update pre chargedCore)) child = some final) :
      Selected pre final childWork count

theorem Selected.accounted {pre post : Meter} {executed count : Nat}
    (h : Selected pre post executed count) : Run pre post executed ∧ 1419*count ≤ executed := by
  induction h with
  | skip actual => exact ⟨actual,by simp⟩
  | append actual => exact ⟨actual.run,by simpa using actual.cost⟩
  | trans first second ih1 ih2 => exact ⟨.trans ih1.1 ih2.1,by omega⟩
  | call cold delegated delegationCold hasValue deadRecipient memoryCost prepared requested outcome body finished ih =>
    exact ⟨.call cold delegated delegationCold hasValue deadRecipient memoryCost prepared requested outcome ih.1 finished,by omega⟩
  | create stateAmount charged outcome newAccount body finished ih =>
    exact ⟨.create stateAmount charged outcome newAccount ih.1 finished,ih.2⟩

/-- The structural cost premise of ReferenceTransactionWork is now derived
from the same selected actual completed leaf executions, not supplied as a
numerical bound. Canonical source extraction and source settlement validity
remain explicit external producers for a transaction-history application. -/
theorem transaction_count {txGas intrinsic executed count : Nat} {post : Meter}
    (h : Selected (ReferenceTransactionWork.initial txGas intrinsic) post executed count)
    (affords : intrinsic ≤ txGas) (maximum : intrinsic ≤ 16777216)
    (dataBytes recipientExecution accessTokens gasLeft stateLeft : Nat) (refund : UInt256) (netState : Int) :
    count ≤ 11823 ∧ count ≤
      (ReferenceTransactionGas.settle txGas (ReferenceCalldataAdmission.floor dataBytes recipientExecution accessTokens)
        gasLeft stateLeft refund netState).executionUsed := by
  exact ReferenceTransactionWork.appends_le_execution_charge h.accounted.1 affords maximum h.accounted.2
    dataBytes recipientExecution accessTokens gasLeft stateLeft refund netState

#print axioms ProtectedPaid.cost
#print axioms ProtectedPaid.run
#print axioms Selected.accounted
#print axioms transaction_count
end Eip8282.Audit.Integrator.ReferenceSelectedAppendWork
