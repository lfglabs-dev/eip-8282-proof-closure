import Eip8282.Audit.Integrator.Topics.Journal
import Eip8282.Audit.Integrator.ProtectedLogFrame

/-! Exact ordered log contribution of each actual protected call. A failed
call, getter or SYSTEM call contributes no log; a successful nonempty user
call contributes exactly its authentic anonymous record log. Global survival
through ancestors is a separate actual journal composition obligation. -/
namespace Eip8282.Audit.Integrator.ProtectedCallLogSeries
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Correspondence (runtimeCode)
open MessageCall
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def contribution (kind : Kind) (c : Context) (success : Bool) : List LogEntry :=
  if success then
    if c.caller = Eip8282.Audit.EvmRunner.sysAddr then []
    else if c.calldata.size = 0 then []
    else [⟨c.target,#[],AppendDataSpec.record kind c.calldata c.caller⟩]
  else []

/-- Exact full accrued-log series, including the preexisting prefix. -/
theorem completed (kind : Kind) (c : Context) (hcode : c.code = runtimeCode kind)
    (budget : Nat) (hd : DirectGuarantees.Domain kind c budget)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {ss : Substate} {status : Bool} {out : ByteArray}
    (hr : c.result = .ok (created,world,gas,ss,status,out)) :
    ss.logSeries.toList = c.substate.logSeries.toList ++ contribution kind c status := by
  cases status with
  | false =>
    obtain ⟨_,hs,_⟩ := failure_restores_journal c created world gas ss out hr
    simp [contribution,hs]
  | true =>
    by_cases hc : c.caller = Eip8282.Audit.EvmRunner.sysAddr
    · have hl := SystemFrame.logs_preserved kind c hcode hc hr
      simp [contribution,hc,hl]
    · by_cases hn : c.calldata.size = 0
      · have hro : GetterInversion.ReadOnly c created world ss := by
          cases kind with
          | deposit => exact GetterInversion.deposit_getter_readonly c hcode hc hd.ordinaryValue hn hr
          | exit => exact GetterInversion.exit_getter_readonly c hcode hc hd.ordinaryValue hn hr
        simp [contribution,hc,hn,hro.2.2.1]
      · have ha := (DirectAppend.user_append kind c hcode hc hd.ordinaryValue hd.calldataFit hn
          hd.owner budget hd.budgetFit hd.bounded hd.safe hr).1.2.2.1
        change ss.logSeries = c.substate.logSeries.push
          ⟨c.target,#[],AppendDataSpec.record kind c.calldata c.caller⟩ at ha
        simp [contribution,hc,hn,ha,Array.toList_push]

/-- The projection filters only by emitter address and retains every topic;
all newly contributed logs have that actual protected emitter. -/
theorem projected (kind : Kind) (c : Context) (hcode : c.code = runtimeCode kind)
    (budget : Nat) (hd : DirectGuarantees.Domain kind c budget)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {ss : Substate} {status : Bool} {out : ByteArray}
    (hr : c.result = .ok (created,world,gas,ss,status,out)) :
    ProtectedLogFrame.project c.target ss = ProtectedLogFrame.project c.target c.substate ++
      contribution kind c status := by
  have hl := completed kind c hcode budget hd hr
  unfold ProtectedLogFrame.project
  rw [hl,List.filter_append]
  congr 1
  unfold contribution
  split
  · split
    · rfl
    · split
      · rfl
      · simp
  · rfl

/-- The exact transition's journal supplies this contribution's local domain. -/
theorem transition {kind : ReachableCalls.Contract} {before after : AccountMap .EVM}
    (t : ReachableCalls.Transition kind before after) {budget : Nat}
    (hi : JournalInvariant.Invariant kind budget before) (hb : budget < 2^128)
    (fit : t.call.calldata.size < UInt256.size) :
    ProtectedLogFrame.project (ReachableCalls.address kind) t.substate =
      ProtectedLogFrame.project (ReachableCalls.address kind) t.call.substate ++
      contribution (JournalInvariant.modelKind kind) t.call t.success := by
  have hd := (JournalGuarantees.domains t hi hb fit).1
  have hc : t.call.code = runtimeCode (JournalInvariant.modelKind kind) := by cases kind <;> exact t.pinned.code
  have h := projected (JournalInvariant.modelKind kind) t.call hc budget hd t.executed
  rw [t.pinned.target] at h
  exact h

#print axioms completed
#print axioms projected
#print axioms transition
end Eip8282.Audit.Integrator.ProtectedCallLogSeries
