import Eip8282.Audit.Integrator.TransactionFunding
import Eip8282.Audit.Integrator.FundingBounds

/-!
# Funding along linked actual executions and explicit external credits

The history constructors carry literal Υ/Θ receipts or the actual account-map
credit operation. No constructor assumes a balance-sum postcondition. The
credit total is accumulated from those operations. Protocol extraction must
still justify the history, transaction admission and provenance of credits.
-/
namespace Eip8282.Audit.Integrator.FundingHistory
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open TransferFunding
open Eip8282.Audit.EntryReach
open Eip8282.Audit.SymExec
open SuccessInversion
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

/-- Each constructor records an actual operation, with independent input
conditions. `credit` is not asserted to be a particular fork's withdrawal rule. -/
inductive Step : AccountMap .EVM → Nat → AccountMap .EVM → Prop where
  | transaction (c : RefundAccounting.Context) (account : Account .EVM)
      (admission : TransactionFunding.Admission c account)
      {world : AccountMap .EVM} {substate : Substate} {success : Bool} {gas : UInt256}
      (executed : c.result = .ok (world,substate,success,gas)) :
      Step c.world 0 world
  | system (c : MessageCall.Context)
      (sender : c.caller = Eip8282.Audit.EvmRunner.sysAddr) (zero : c.value = ⟨0⟩)
      {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
      {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
      (executed : c.result = .ok (created,world,gas,substate,success,out)) :
      Step c.world 0 world
  | credit (world : AccountMap .EVM) (recipient : AccountAddress) (amount : UInt256) :
      Step world amount.toNat (world.increaseBalance .EVM recipient amount)

/-- Completed operations conserve funds except for their explicit credit. -/
theorem step_funds {before after : AccountMap .EVM} {credit : Nat}
    (h : Step before credit after) : worldFunds after ≤ worldFunds before + credit := by
  cases h with
  | transaction c account ha he =>
      simpa only [Nat.add_zero] using TransactionFunding.result_funds c ha he
  | system c _ hz he =>
      have hf : c.value.toNat ≤ worldBalance c.world c.caller := by rw [hz]; exact Nat.zero_le _
      simpa only [Nat.add_zero] using ExecutionFunding.theta_funds (c.fuel+1) hf he
  | credit world recipient amount => exact FinalizationFunding.credit_le _ recipient amount

/-- Linked actual world transitions. The natural index is the sum of external
credits, not a stipulated supply cap or a desired post-state invariant. -/
inductive Trace (initial : AccountMap .EVM) : Nat → AccountMap .EVM → Prop where
  | initial : Trace initial 0 initial
  | next {credits amount : Nat} {before after : AccountMap .EVM}
      (prior : Trace initial credits before) (step : Step before amount after) :
      Trace initial (credits+amount) after

theorem trace_funds {initial world : AccountMap .EVM} {credits : Nat}
    (h : Trace initial credits world) : worldFunds world ≤ worldFunds initial + credits := by
  induction h with
  | initial => exact Nat.le_add_right _ _
  | next _ hs ih => have hb := step_funds hs; omega

/-- Every balance is bounded using the actual finite-map sum. -/
theorem balance_budget {initial world : AccountMap .EVM} {credits : Nat}
    (h : Trace initial credits world) (address : AccountAddress) :
    worldBalance world address ≤ worldFunds initial + credits :=
  (balance_le_funds world address).trans (trace_funds h)

/-- The independent funding ceiling now needs a bound on initial funds and
explicit credits, not a supplied bound on the resulting world. -/
theorem message_value_lt {initial : AccountMap .EVM} {credits : Nat} (c : MessageCall.Context)
    (history : Trace initial credits c.world)
    (funded : c.value.toNat ≤ worldBalance c.world c.caller)
    (budget : worldFunds initial + credits < FundedDomain.fundingCeiling) :
    c.value.toNat < FundedDomain.fundingCeiling :=
  (funded.trans (balance_budget history c.caller)).trans_lt budget

/-- A transaction's independent prepayment condition supplies its value bound. -/
theorem transaction_value_lt {initial : AccountMap .EVM} {credits : Nat}
    (c : RefundAccounting.Context) {account : Account .EVM}
    (history : Trace initial credits c.world) (admission : TransactionFunding.Admission c account)
    (budget : worldFunds initial + credits < FundedDomain.fundingCeiling) :
    c.transaction.base.value.toNat < FundedDomain.fundingCeiling := by
  have hb := balance_budget history c.sender
  simp only [worldBalance, admission.sender, Option.map_some, Option.getD_some] at hb
  have hf := admission.funded
  omega

/-- The actual Θ entry transfer also stays within the derived history budget. -/
theorem message_entry_budget {initial : AccountMap .EVM} {credits : Nat} (c : MessageCall.Context)
    (history : Trace initial credits c.world)
    (funded : c.value.toNat ≤ worldBalance c.world c.caller) :
    worldFunds c.entryWorld ≤ worldFunds initial + credits :=
  (entry_funds_le c funded).trans (trace_funds history)

/-- Every completed step of a real X prefix is funded monotonically, including
recursive instructions. No assumption on the later success/rollback is needed. -/
theorem xruns_funds {vj : Array UInt256} {fuel rest : Nat} {pre post : EVM.State}
    {labels : List Labelled} (h : XRuns vj fuel pre labels rest post) :
    worldFunds post.accountMap ≤ worldFunds pre.accountMap := by
  induction h with
  | refl => exact Nat.le_refl _
  | cons hs _ ih =>
      obtain ⟨mid,hz,he,_⟩ := hs
      exact ih.trans (ExecutionFunding.step_funds _ hz he)

/-- An encountered instruction's owner is funded by the actual frame's entry
world even when the enclosing frame later reverts or errors. This is a local
prefix result; extraction of every nested frame remains separate. -/
theorem prefix_owner_budget {vj : Array UInt256} {fuel rest : Nat} {pre post : EVM.State}
    {labels : List Labelled} (h : XRuns vj fuel pre labels rest post) :
    worldBalance post.accountMap post.executionEnv.codeOwner ≤ worldFunds pre.accountMap :=
  (balance_le_funds _ _).trans (xruns_funds h)

#print axioms step_funds
#print axioms trace_funds
#print axioms message_value_lt
#print axioms transaction_value_lt
#print axioms message_entry_budget
#print axioms xruns_funds
#print axioms prefix_owner_budget
end Eip8282.Audit.Integrator.FundingHistory
