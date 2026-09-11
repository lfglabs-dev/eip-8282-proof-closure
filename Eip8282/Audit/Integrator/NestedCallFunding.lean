import Eip8282.Audit.Integrator.NestedFrameFunding
import Eip8282.Audit.Integrator.NestedCallOccurrence
import Eip8282.Audit.Integrator.FundingHistory

/-!
# Actual nested message-call funding, including failed and reverted ancestors

All Theta inputs are located in the actual certified evaluator. The real
selected-child gates supply transfer affordability. Together with the complete
funding history, this removes per-nested-call wealth assumptions; provenance
and bounds of the history's external credits remain explicit protocol inputs.
-/
namespace Eip8282.Audit.Integrator.NestedFunding
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open NestedEvents TransferFunding
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private theorem theta_x_guard {fuel : Nat} {vj : Array UInt256} {pre : EVM.State}
    {result : XResult} {tree : EventTree} {path : EventTree.Address}
    {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt (.x fuel vj pre) result tree path f a r) :
    ∃ mid cost, Z vj (decodeAt pre).1 pre = .ok (mid,cost) := by
  cases loc with
  | xStepError hz _ _ => exact ⟨_,_,hz⟩
  | xNextChild hz _ _ _ _ => exact ⟨_,_,hz⟩
  | xNextTail hz _ _ _ _ => exact ⟨_,_,hz⟩
  | xHalt hz _ _ _ _ => exact ⟨_,_,hz⟩
  | xRevert hz _ _ _ _ => exact ⟨_,_,hz⟩

/-- Alias creation executes INVALID; it cannot contain even a failed message
call, so its potentially inflated temporary entry does not enter this bound. -/
theorem invalid_has_no_call {fuel : Nat} {outer : XiArgs}
    {result : XiResult} {tree : EventTree} {path : EventTree.Address}
    {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (invalid : outer.env.code = ⟨#[0xfe]⟩)
    (loc : ThetaAt (.xi fuel outer) result tree path f a r) : False := by
  cases loc with
  | xi body inner =>
    obtain ⟨mid,cost,hz⟩ := theta_x_guard inner
    have hd : decodeAt outer.entry = (.INVALID, none) :=
      decodeAt_of_code_pc invalid rfl (by decide +kernel)
    rw [hd] at hz
    exact OrdinaryGas.accepted_valid hz rfl

/-- Both affordability and the world's budget are derived at every actual
message-call input, before its transfer and regardless of its final status. -/
theorem call_input_funds {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt q result tree path f a r) (funded : GoodFunding q) :
    GoodFunding (.theta f a) ∧ worldFunds a.world ≤ worldFunds (inputWorld q) := by
  induction loc with
  | here body => exact ⟨funded,Nat.le_refl _⟩
  | xStepError _ _ _ ih => exact ih trivial
  | xNextChild _ _ _ _ _ ih => exact ih trivial
  | @xNextTail n cost f vj pre mid post result child next path a r hz hs hh ht inner ih =>
    obtain ⟨ha,hb⟩ := ih trivial
    exact ⟨ha,hb.trans (ExecutionFunding.step_funds n hz (sound hs))⟩
  | xHalt _ _ _ _ _ ih => exact ih trivial
  | xRevert _ _ _ _ _ ih => exact ih trivial
  | xi body inner ih => exact ih trivial
  | @thetaCode n f outer a r bytes tree path hc body inner ih =>
    obtain ⟨ha,hb⟩ := ih trivial
    exact ⟨ha,hb.trans (theta_entry funded bytes)⟩
  | @lambdaInit n f outer a r bytes tree path hp body inner ih =>
    by_cases he : outer.source = CreationSettlement.address bytes
    · exact False.elim (invalid_has_no_call (lambda_alias_invalid funded he) inner)
    · obtain ⟨ha,hb⟩ := ih trivial
      exact ⟨ha,hb.trans (lambda_entry_distinct funded he)⟩
  | stepChild hc body inner ih =>
    obtain ⟨hf,hb⟩ := selected_child_funding hc
    obtain ⟨ha,hw⟩ := ih hf
    exact ⟨ha,hw.trans hb⟩

/-- This concerns the actual transfer, not a DELEGATECALL's apparent CALLVALUE. -/
theorem call_value_le_root {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt q result tree path f a r) (funded : GoodFunding q) :
    a.value.toNat ≤ worldFunds (inputWorld q) := by
  obtain ⟨ha,hw⟩ := call_input_funds loc funded
  exact (ha.trans (balance_le_funds a.world a.source)).trans hw

theorem transaction_call_value (c : RefundAccounting.Context) {account : Account .EVM}
    (ha : TransactionFunding.Admission c account)
    {tree : EventTree} {path : EventTree.Address} {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt (TransactionEventBounds.request c)
      (TransactionEventBounds.request c).eval tree path f a r) :
    a.value.toNat ≤ worldFunds c.world := by
  have hb := call_value_le_root loc (admitted_request c ha)
  rw [request_world] at hb
  have hd := TransactionFunding.checkpoint_debit c ha
  omega

/-- The complete actual funding history now supplies every nested transfer
ceiling. Only initial funds plus explicit credits need a protocol-derived bound;
no intermediate balance or per-child funding cap is assumed. -/
theorem history_call_value_lt {initial : AccountMap .EVM} {credits : Nat}
    (c : RefundAccounting.Context) {account : Account .EVM}
    (history : FundingHistory.Trace initial credits c.world)
    (ha : TransactionFunding.Admission c account)
    (budget : worldFunds initial + credits < FundedDomain.fundingCeiling)
    {tree : EventTree} {path : EventTree.Address} {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt (TransactionEventBounds.request c)
      (TransactionEventBounds.request c).eval tree path f a r) :
    a.value.toNat < FundedDomain.fundingCeiling :=
  ((transaction_call_value c ha loc).trans (FundingHistory.trace_funds history)).trans_lt budget

#print axioms invalid_has_no_call
#print axioms call_input_funds
#print axioms call_value_le_root
#print axioms transaction_call_value
#print axioms history_call_value_lt
end Eip8282.Audit.Integrator.NestedFunding
