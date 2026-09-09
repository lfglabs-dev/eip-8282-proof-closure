import Eip8282.Audit.Integrator.AppendStorage
import Eip8282.Audit.Integrator.ExitRecord
import Eip8282.Audit.Integrator.CallBridge
import Eip8282.Audit.Integrator.WorldNonempty

/-!
# Authentic append storage and receipt committed by Θ

Each theorem supplies one actual committed result containing both independent
storage postconditions and the authentic anonymous log. Equality of the actual
Ξ results joins the storage and receipt witnesses. Owner preservation rules out
Θ's empty-world fallback without an assumed post-world condition.

All acceptance checks, fee-loop completion, resources, and local AppendFits
bounds remain explicit. These are sufficient-success theorems, not inversion
of arbitrary successful calls or protocol-history invariants. Other-account
preservation is relative to Θ's transferred entry world. Message-call admission
and the relation between transferred and apparent value are separate concerns.
-/

namespace Eip8282.Audit.Integrator.CommittedAppend

open EvmYul EvmYul.EVM
open Eip8282.Audit.XiTransport
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Correspondence (runtimeCode)
open Eip8282.Audit.Integrator.MessageCall
open Eip8282.Audit.Integrator.CallBridge
open Eip8282.Audit.Integrator.SystemSpec (HasOwner worldSlot)
open Eip8282.Audit.Integrator.WorldNonempty

/-- All observations concern the same world and substate returned by Θ.
`StoragePost` exposes unchanged excess/head, natural count/tail successors,
the complete record window, and every slot outside the write footprint. -/
def AppendResult (c : Context) (q : XiCall kind) (record : ByteArray) : Prop :=
  ∃ (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (substate : Substate),
    c.result = .ok (created, world, gas, substate, true, .empty) ∧
    (∃ acc, world.get? c.target = some acc) ∧
    (∀ k, worldSlot world c.target k = AppendStorage.expected q k) ∧
    AppendStorage.StoragePost q world ∧
    substate.logSeries = c.substate.logSeries.push ⟨c.target, #[], record⟩ ∧
    (∀ addr, addr ≠ c.target → world.get? addr = c.entryWorld.get? addr)

theorem deposit_append_commits (c : Context)
    (hcode : c.code = runtimeCode .deposit) (steps : Nat) (hf : c.fuel = steps + 1)
    (huser : Deposit.callerWord (codeCall c hcode steps) ≠ sysW)
    (hen : Deposit.excessWord (codeCall c hcode steps) ≠ INH)
    (hperm : c.permission = true) {n : Nat} {o i : UInt256}
    (hfee : Deposit.FeeLoopEnds (codeCall c hcode steps) n o i)
    (hsize : c.calldata.size = 184)
    (hpaid : ¬ Deposit.valueWord (codeCall c hcode steps) < Deposit.feeWord o)
    (hfloor : ¬ Deposit.amountWord (codeCall c hcode steps) < UInt256.ofNat 1000000000)
    (hstake : ¬ (Deposit.valueWord (codeCall c hcode steps) - Deposit.feeWord o) <
      UInt256.ofNat 1000000000 * Deposit.amountWord (codeCall c hcode steps))
    (hg : 87 * n + 190000 ≤ c.gas.toNat) (hsteps : 24 * n + 152 ≤ steps)
    (ho : HasOwner (entrySt (codeCall c hcode steps)))
    (hfit : AppendStorage.AppendFits (codeCall c hcode steps)) :
    AppendResult c (codeCall c hcode steps) c.calldata := by
  let q := codeCall c hcode steps
  obtain ⟨created, world, gas, substate, hr, howner, hslots, hpost⟩ :=
    AppendStorage.deposit_storage_result q huser hen hperm hfee hsize hpaid hfloor
      hstake hg hsteps ho hfit
  obtain ⟨created', world', gas', substate', hr', hlog, hframe⟩ :=
    AppendSpec.deposit_submission_receipt q huser hen hperm hfee hsize hpaid hfloor
      hstake hg hsteps
  have he : created = created' ∧ world = world' ∧ gas = gas' ∧ substate = substate' := by
    simpa only [Except.ok.injEq, ExecutionResult.success.injEq, Prod.mk.injEq, and_true]
      using hr.symm.trans hr'
  rcases he with ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨acc, hacc⟩ := howner
  exact ⟨created, world, gas, substate,
    commits_endpoint c hcode steps hf _ _ _ _ _ hr
      (beq_empty_false_of_get_some hacc), ⟨acc, hacc⟩, hslots, hpost, hlog, hframe⟩

theorem exit_append_commits (c : Context)
    (hcode : c.code = runtimeCode .exit) (steps : Nat) (hf : c.fuel = steps + 1)
    (huser : Exit.callerWord (codeCall c hcode steps) ≠ sysW)
    (hen : Exit.excessWord (codeCall c hcode steps) ≠ INH)
    (hperm : c.permission = true) {n : Nat} {o i : UInt256}
    (hfee : Exit.FeeLoopEnds (codeCall c hcode steps) n o i)
    (hsize : c.calldata.size = 48)
    (hpaid : ¬ Exit.valueWord (codeCall c hcode steps) < Exit.feeWord o)
    (hg : 87 * n + 150000 ≤ c.gas.toNat) (hsteps : 24 * n + 122 ≤ steps)
    (ho : HasOwner (entrySt (codeCall c hcode steps)))
    (hfit : AppendStorage.AppendFits (codeCall c hcode steps)) :
    AppendResult c (codeCall c hcode steps) (ExitRecord.record c.caller c.calldata) := by
  let q := codeCall c hcode steps
  obtain ⟨created, world, gas, substate, hr, howner, hslots, hpost⟩ :=
    AppendStorage.exit_storage_result q huser hen hperm hfee hsize hpaid hg hsteps ho hfit
  obtain ⟨created', world', gas', substate', hr', hlog, hframe⟩ :=
    ExitRecord.submission_receipt q huser hen hperm hfee hsize hpaid hg hsteps
  have he : created = created' ∧ world = world' ∧ gas = gas' ∧ substate = substate' := by
    simpa only [Except.ok.injEq, ExecutionResult.success.injEq, Prod.mk.injEq, and_true]
      using hr.symm.trans hr'
  rcases he with ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨acc, hacc⟩ := howner
  exact ⟨created, world, gas, substate,
    commits_endpoint c hcode steps hf _ _ _ _ _ hr
      (beq_empty_false_of_get_some hacc), ⟨acc, hacc⟩, hslots, hpost, hlog, hframe⟩

#print axioms deposit_append_commits
#print axioms exit_append_commits

end Eip8282.Audit.Integrator.CommittedAppend
