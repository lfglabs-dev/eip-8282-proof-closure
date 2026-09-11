import Eip8282.Audit.Integrator.NestedFundingEdges
import Eip8282.Audit.Integrator.TransactionFunding
import Eip8282.Audit.Integrator.TransactionEventBounds

/-!
# Funding at every actual audited nested invocation

Bounds are propagated down literal XiAt edges and through actual completed
continuations. CREATE's alias entry is deliberately not assumed to conserve
funds: its nonzero nonce selects INVALID, which has no audited descendants.
This theorem concerns all actual audited frame entries, including invocations
later reverted, not merely final transaction balances.
-/
namespace Eip8282.Audit.Integrator.NestedFunding
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open NestedEvents TransferFunding
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Correspondence (runtimeCode)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private theorem x_location_guard {fuel : Nat} {vj : Array UInt256} {pre : EVM.State}
    {result : XResult} {tree : EventTree} {path : EventTree.Address}
    {f : Nat} {a : XiArgs} {r : XiResult}
    (loc : XiAt (.x fuel vj pre) result tree path f a r) :
    ∃ mid cost, Z vj (decodeAt pre).1 pre = .ok (mid,cost) := by
  cases loc with
  | xStepError hz _ _ => exact ⟨_,_,hz⟩
  | xNextChild hz _ _ _ _ => exact ⟨_,_,hz⟩
  | xNextTail hz _ _ _ _ => exact ⟨_,_,hz⟩
  | xHalt hz _ _ _ _ => exact ⟨_,_,hz⟩
  | xRevert hz _ _ _ _ => exact ⟨_,_,hz⟩

/-- The potentially inflated alias initializer cannot hide an audited frame. -/
theorem invalid_has_no_audited_frame {fuel : Nat} {outer : XiArgs}
    {result : XiResult} {tree : EventTree} {path : EventTree.Address}
    {f : Nat} {a : XiArgs} {r : XiResult} {kind : Eip8282.Audit.Model.Kind}
    (invalid : outer.env.code = ⟨#[0xfe]⟩)
    (loc : XiAt (.xi fuel outer) result tree path f a r)
    (pinned : a.env.code = runtimeCode kind) : False := by
  cases loc with
  | here body =>
    have hn : runtimeCode kind ≠ (⟨#[0xfe]⟩ : ByteArray) := by
      cases kind <;> decide +kernel
    exact hn (pinned.symm.trans invalid)
  | xi body inner =>
    obtain ⟨mid,cost,hz⟩ := x_location_guard inner
    have hd : decodeAt outer.entry = (.INVALID, none) :=
      decodeAt_of_code_pc invalid rfl (by decide +kernel)
    rw [hd] at hz
    exact OrdinaryGas.accepted_valid hz rfl

/-- Every actual audited Xi entry is funded by the root input. GoodFunding is
needed only for the root request; selected-child gates derive it internally. -/
theorem audited_entry_funds {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {f : Nat} {a : XiArgs} {r : XiResult}
    {kind : Eip8282.Audit.Model.Kind}
    (loc : XiAt q result tree path f a r) (funded : GoodFunding q)
    (pinned : a.env.code = runtimeCode kind) :
    worldFunds a.world ≤ worldFunds (inputWorld q) := by
  induction loc with
  | here body => exact Nat.le_refl _
  | xStepError _ _ _ ih => exact ih trivial pinned
  | xNextChild _ _ _ _ _ ih => exact ih trivial pinned
  | @xNextTail n cost f vj pre mid post result child next path a r hz hs hh ht inner ih =>
    have hp := ExecutionFunding.step_funds n hz (sound hs)
    exact (ih trivial pinned).trans hp
  | xHalt _ _ _ _ _ ih => exact ih trivial pinned
  | xRevert _ _ _ _ _ ih => exact ih trivial pinned
  | xi body inner ih => exact ih trivial pinned
  | @thetaCode n f outer a r bytes tree path hc body inner ih =>
    exact (ih trivial pinned).trans (theta_entry funded bytes)
  | @lambdaInit n f outer a r bytes tree path hp body inner ih =>
    by_cases he : outer.source = CreationSettlement.address bytes
    · have hi := lambda_alias_invalid funded he
      exact False.elim (invalid_has_no_audited_frame hi inner pinned)
    · exact (ih trivial pinned).trans (lambda_entry_distinct funded he)
  | stepChild hc body inner ih =>
    obtain ⟨hf,hb⟩ := selected_child_funding hc
    exact (ih hf pinned).trans hb

/-- Actual Υ admission supplies the root wrapper hypotheses. No funded-child
assertion is added to the transaction interface. -/
theorem admitted_request (c : RefundAccounting.Context) {account : Account .EVM}
    (ha : TransactionFunding.Admission c account) :
    GoodFunding (TransactionEventBounds.request c) := by
  unfold TransactionEventBounds.request
  split
  · exact ⟨TransactionFunding.checkpoint_funded c ha,
      TransactionFunding.checkpoint_nonce c ha⟩
  · exact TransactionFunding.checkpoint_funded c ha

theorem request_world (c : RefundAccounting.Context) :
    inputWorld (TransactionEventBounds.request c) = c.checkpoint := by
  unfold TransactionEventBounds.request
  split <;> rfl

/-- Every audited runtime entry in the actual selected Υ execution is bounded
by the transaction's initial total funds, even after reverted or failed children.
Independent transaction admission is explicit; Ethereum admission adequacy is
not assumed proved by this theorem. -/
theorem transaction_entry_funds (c : RefundAccounting.Context) {account : Account .EVM}
    (ha : TransactionFunding.Admission c account)
    {tree : EventTree} {path : EventTree.Address} {f : Nat} {a : XiArgs} {r : XiResult}
    {kind : Eip8282.Audit.Model.Kind}
    (loc : XiAt (TransactionEventBounds.request c)
      (TransactionEventBounds.request c).eval tree path f a r)
    (pinned : a.env.code = runtimeCode kind) :
    worldFunds a.world ≤ worldFunds c.world := by
  have hb := audited_entry_funds loc (admitted_request c ha) pinned
  rw [request_world] at hb
  have hd := TransactionFunding.checkpoint_debit c ha
  omega

#print axioms admitted_request
#print axioms transaction_entry_funds
#print axioms invalid_has_no_audited_frame
#print axioms audited_entry_funds
end Eip8282.Audit.Integrator.NestedFunding
