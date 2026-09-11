import Eip8282.Audit.Integrator.SuccessfulSystem
import Eip8282.Audit.Integrator.AppendSpec

/-!
# No added logs and other-account frame for actual SYSTEM success

The statements start from actual successful Θ results at arbitrary resources.
They preserve the real settlement fallback and require no predicted poststate
or owner assumption. Other accounts are compared with the actual entryWorld,
which already contains Θ's value transfer.
-/
namespace Eip8282.Audit.Integrator.SystemFrame

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Correspondence (runtimeCode)
open Eip8282.Audit.Model (Kind)
open MessageCall CallBridge SystemSpec AppendSpec

set_option autoImplicit false
set_option maxHeartbeats 1200000

private theorem frame_touched {kind : Kind} {q : XiCall kind}
    {pre post : EvmYul.State .EVM} (hf : AccountFrame q pre) (ht : Touched pre post) :
    AccountFrame q post := by
  refine ⟨ht.executionEnv.trans hf.1, ?_⟩
  unfold OtherAccountsUnchanged at *
  rw [ht.accountMap]
  exact hf.2

private theorem frame_head {kind : Kind} {q : XiCall kind}
    {pre : EvmYul.State .EVM} (hf : AccountFrame q pre) (head tail count : UInt256) :
    AccountFrame q (headUpdate pre head tail count) := by
  unfold headUpdate
  split
  · exact frame_sstore (frame_sstore hf)
  · exact frame_sstore hf

private theorem head_logs (pre : EvmYul.State .EVM) (head tail count : UInt256) :
    (headUpdate pre head tail count).substate.logSeries = pre.substate.logSeries := by
  unfold headUpdate
  split <;> simp only [logs_sstore]

private theorem final_frame {kind : Kind} (q : XiCall kind)
    (st' stX : EvmYul.State .EVM) (count excess : UInt256)
    (ht : Touched (entrySt q) st')
    (hx : Touched (headUpdate st' (slotW (entrySt q) (UInt256.ofNat 2))
      (slotW (entrySt q) (UInt256.ofNat 3)) count) stX) :
    (controlStore stX excess).substate.logSeries = q.substate.logSeries ∧
      AccountFrame q (controlStore stX excess) := by
  refine ⟨?_, ?_⟩
  · simp only [controlStore, logs_sstore]
    rw [hx.logs, head_logs, ht.logs]
    rfl
  · apply frame_sstore
    apply frame_sstore
    exact frame_touched (frame_head (frame_touched (frame_entry q) ht) _ _ _) hx

/-- The exact published Ξ state supplies both observations without an owner
premise, including raw states where SSTORE finds no executing account. -/
theorem exit_execution (q : XiCall .exit)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hsys : q.env.source = EvmRunner.sysAddr)
    (h : q.result = .ok (.success (created,world,gas,substate) out)) :
    substate.logSeries = q.substate.logSeries ∧ OtherAccountsUnchanged q world := by
  obtain ⟨st',stX,g,ht,hx,hpub,_⟩ := SystemInversion.exit_system_result q hsys h
  have hf := final_frame q st' stX (Exit.drainWord q) (Exit.newExcess q stX) ht hx
  have hw := congrArg (fun p => p.2.1) hpub
  have hs := congrArg (fun p => p.2.2.2) hpub
  dsimp only at hw hs
  refine ⟨?_, ?_⟩
  · rw [hs]; exact hf.1
  · rw [hw]; exact hf.2.2

theorem deposit_execution (q : XiCall .deposit)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hsys : q.env.source = EvmRunner.sysAddr)
    (h : q.result = .ok (.success (created,world,gas,substate) out)) :
    substate.logSeries = q.substate.logSeries ∧ OtherAccountsUnchanged q world := by
  obtain ⟨st',stX,g,ht,hx,hpub,_⟩ := SystemInversion.deposit_system_result q hsys h
  have hf := final_frame q st' stX (Deposit.drainWord q) (Deposit.newExcess q stX) ht hx
  have hw := congrArg (fun p => p.2.1) hpub
  have hs := congrArg (fun p => p.2.2.2) hpub
  dsimp only at hw hs
  refine ⟨?_, ?_⟩
  · rw [hs]; exact hf.1
  · rw [hw]; exact hf.2.2

/-- Algebra of the actual Θ settlement projection. Even in its empty-world
fallback, an unchanged other account cannot be lost: its existence would
contradict the empty-world Boolean test. -/
private theorem settle_frame (c : Context) (ew world : AccountMap .EVM)
    (es substate : Substate)
    (hw : world = if ew == ∅ then c.world else ew)
    (hs : substate = if ew == ∅ then c.substate else es)
    (hl : es.logSeries = c.substate.logSeries)
    (hf : ∀ addr, addr ≠ c.target → ew.get? addr = c.entryWorld.get? addr) :
    substate.logSeries = c.substate.logSeries ∧
      ∀ addr, addr ≠ c.target → world.get? addr = c.entryWorld.get? addr := by
  by_cases hempty : (ew == ∅) = true
  · rw [if_pos hempty] at hw hs
    subst world; subst substate
    refine ⟨rfl, ?_⟩
    intro addr hn
    have he : c.entryWorld.get? addr = none := by
      cases hh : c.entryWorld.get? addr with
      | none => rfl
      | some acc =>
        have hp := (hf addr hn).trans hh
        have hb := WorldNonempty.beq_empty_false_of_get_some hp
        rw [hempty] at hb
        cases hb
    rw [he]
    cases hp : c.world.get? addr with
    | none => rfl
    | some acc =>
      obtain ⟨current, hc⟩ := TransferFrame.entry_keeps_existing c hp
      rw [he] at hc
      cases hc
  · rw [if_neg hempty] at hw hs
    subst world; subst substate
    exact ⟨hl, hf⟩

/-- Actual complete SYSTEM success adds no logs and preserves every other
account exactly relative to the value-transferred entry world. -/
theorem exit_system (c : Context) (hcode : c.code = runtimeCode .exit)
    (hsys : c.caller = EvmRunner.sysAddr)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,true,out)) :
    substate.logSeries = c.substate.logSeries ∧
      ∀ addr, addr ≠ c.target → world.get? addr = c.entryWorld.get? addr := by
  have hp := SuccessfulQuote.positive_fuel c h
  have hsteps : c.fuel = (c.fuel-1)+1 := by omega
  obtain ⟨ew,es,he,hw,hs⟩ := CallSuccess.codeCall_of_success c hcode (c.fuel-1) hsteps h
  obtain ⟨hl,hf⟩ := exit_execution (codeCall c hcode (c.fuel-1)) hsys he
  exact settle_frame c ew world es substate hw hs hl hf

/-- Deposit version of the same complete-call frame, with no resource or
initial-owner premise beyond actual successful execution. -/
theorem deposit_system (c : Context) (hcode : c.code = runtimeCode .deposit)
    (hsys : c.caller = EvmRunner.sysAddr)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,true,out)) :
    substate.logSeries = c.substate.logSeries ∧
      ∀ addr, addr ≠ c.target → world.get? addr = c.entryWorld.get? addr := by
  have hp := SuccessfulQuote.positive_fuel c h
  have hsteps : c.fuel = (c.fuel-1)+1 := by omega
  obtain ⟨ew,es,he,hw,hs⟩ := CallSuccess.codeCall_of_success c hcode (c.fuel-1) hsteps h
  obtain ⟨hl,hf⟩ := deposit_execution (codeCall c hcode (c.fuel-1)) hsys he
  exact settle_frame c ew world es substate hw hs hl hf

/-- Common interface for the two pinned SYSTEM runtimes. -/
theorem system_frame (kind : Kind) (c : Context) (hcode : c.code = runtimeCode kind)
    (hsys : c.caller = EvmRunner.sysAddr)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,true,out)) :
    substate.logSeries = c.substate.logSeries ∧
      ∀ addr, addr ≠ c.target → world.get? addr = c.entryWorld.get? addr := by
  cases kind with
  | deposit => exact deposit_system c hcode hsys h
  | exit => exact exit_system c hcode hsys h

/-- SYSTEM cannot append a log in any actual successful complete call.
No owner, gas, fuel or permission premise is supplied. -/
theorem logs_preserved (kind : Kind) (c : Context) (hcode : c.code = runtimeCode kind)
    (hsys : c.caller = EvmRunner.sysAddr)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,true,out)) :
    substate.logSeries = c.substate.logSeries :=
  (system_frame kind c hcode hsys h).1

#print axioms exit_execution
#print axioms deposit_execution
#print axioms exit_system
#print axioms deposit_system
#print axioms system_frame
#print axioms logs_preserved

end Eip8282.Audit.Integrator.SystemFrame
