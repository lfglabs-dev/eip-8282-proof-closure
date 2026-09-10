import Eip8282.Audit.Integrator.TransactionFunding
import Eip8282.Audit.Integrator.TransactionEventBounds
import Eip8282.Audit.Integrator.FinalizationWorldFrame
import Eip8282.Audit.Integrator.JournalInvariant

/-! Literal transaction checkpoint, provisional evaluator, and finalization
edges. A returned false status is retained. These projections do not assume
per-call invariants or extract protocol admission. -/
namespace Eip8282.Audit.Integrator.TransactionJournalEdges
open EvmYul EvmYul.EVM
open RefundAccounting NestedEvents CodeStorageFrame
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem checkpoint_frame (c : Context) {account : Account .EVM}
    (ha : TransactionFunding.Admission c account) (protectedAddr : AccountAddress) :
    Frame c.world c.checkpoint protectedAddr := by
  rw [TransactionFunding.checkpoint_eq c ha]
  have hl : (c.world.insert c.sender (TransactionFunding.debited c account)).get? protectedAddr =
      if c.sender = protectedAddr then some (TransactionFunding.debited c account)
      else c.world.get? protectedAddr := by
    exact (Std.TreeMap.getElem?_insert (t := c.world) (k := c.sender)
      (a := protectedAddr) (v := TransactionFunding.debited c account)).trans
      (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)
  by_cases he : c.sender = protectedAddr
  · have hold : c.world.get? protectedAddr = some account := he ▸ ha.sender
    constructor
    · intro old ho
      have ho : account = old := Option.some.inj (hold.symm.trans ho)
      subst old
      exact ⟨TransactionFunding.debited c account,by rw [hl,if_pos he],rfl⟩
    · intro slot
      simp only [SystemSpec.worldSlot,hl,if_pos he,hold,Option.map_some,Option.getD_some]
      rfl
  · constructor
    · intro old ho
      exact ⟨old,by rw [hl,if_neg he]; exact ho,rfl⟩
    · intro slot
      simp only [SystemSpec.worldSlot,hl,if_neg he]

theorem settled_frame (c : Context) (world : AccountMap .EVM) (remaining : UInt256)
    (ss : Substate) (protectedAddr : AccountAddress) {old : Account .EVM}
    (ho : world.get? protectedAddr = some old) (hc : old.code ≠ ByteArray.empty)
    (hn : protectedAddr ∉ ss.selfDestructSet) :
    Frame world (TransactionFunding.settledWorld c world remaining ss) protectedAddr := by
  let refundAmount := returnedGas c.transaction.base.gasLimit remaining ss.refundBalance * c.effectivePrice
  let refunded := world.increaseBalance .EVM c.sender refundAmount
  let fee := netGas c.transaction.base.gasLimit remaining ss.refundBalance * c.priorityFee
  let paid := if fee != ⟨0⟩ then refunded.increaseBalance .EVM c.header.beneficiary fee else refunded
  have hr : Frame world refunded protectedAddr := FinalizationWorldFrame.credit_frame _ _ _ _
  have hp : Frame refunded paid protectedAddr := by
    unfold paid
    split
    · exact FinalizationWorldFrame.credit_frame _ _ _ _
    · exact CodeStorageFrame.refl _ _
  have hf := CodeStorageFrame.trans hr hp
  obtain ⟨current,hcur,hcode⟩ := hf.existing old ho
  have hnonempty : current.code ≠ ByteArray.empty := fun he => hc (hcode.symm.trans he)
  exact CodeStorageFrame.trans hf
    (FinalizationWorldFrame.cleanup_frame paid ss protectedAddr hcur hnonempty hn)

theorem settled_codeAt_frame {kind : ReachableCalls.Contract}
    (c : Context) (world : AccountMap .EVM) (remaining : UInt256) (ss : Substate)
    (hc : JournalInvariant.CodeAt kind world)
    (hn : ReachableCalls.address kind ∉ ss.selfDestructSet) :
    Frame world (TransactionFunding.settledWorld c world remaining ss) (ReachableCalls.address kind) := by
  obtain ⟨old,ho,hcode⟩ := hc
  apply settled_frame c world remaining ss _ ho _ hn
  rw [hcode]
  cases kind <;> decide +kernel

/-- Both real provisional branches preserve all four projected result fields.
The extra values are precisely the fields erased by Context.provisional. -/
theorem provisional_cases (c : Context) {world : AccountMap .EVM} {gas : UInt256}
    {ss : Substate} {status : Bool} (hp : c.provisional = .ok (world,gas,ss,status)) :
    (c.transaction.base.recipient = none ∧ ∃ target created out,
      (Request.lambda c.fuel (TransactionEventBounds.creation c)).eval =
        .ok (target,created,world,gas,ss,status,out)) ∨
    (∃ recipient, c.transaction.base.recipient = some recipient ∧ ∃ created out,
      (Request.theta c.fuel (TransactionEventBounds.message c recipient)).eval =
        .ok (created,world,gas,ss,status,out)) := by
  unfold Context.provisional at hp
  split at hp
  · rename_i hr
    left
    refine ⟨hr,?_⟩
    split at hp
    · rename_i target created actualWorld actualGas actualSubstate actualStatus out he
      cases hp
      exact ⟨target,created,out,he⟩
    · cases hp
  · rename_i recipient hr
    right
    refine ⟨recipient,hr,?_⟩
    split at hp
    · rename_i created actualWorld actualGas actualSubstate actualStatus out he
      cases hp
      exact ⟨created,out,he⟩
    · cases hp

#print axioms checkpoint_frame
#print axioms settled_frame
#print axioms settled_codeAt_frame
#print axioms provisional_cases
end Eip8282.Audit.Integrator.TransactionJournalEdges
