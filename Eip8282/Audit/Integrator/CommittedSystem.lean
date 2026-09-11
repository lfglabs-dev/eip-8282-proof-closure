import Eip8282.Audit.Integrator.SystemSpec
import Eip8282.Audit.Integrator.CallBridge
import Eip8282.Audit.Integrator.WorldNonempty

/-!
# SYSTEM storage postconditions committed by Θ

The call frame is built from Θ's actual transferred world. Successful SYSTEM
execution preserves an owner account, so Θ's empty-world fallback is ruled out
by proof. No assumed post-state agreement or nonempty-result premise is needed.
The returned bytes remain the actual staged buffer; FIFO identification and
protocol-derived bounds are separate obligations.
-/

namespace Eip8282.Audit.Integrator.CommittedSystem

open EvmYul EvmYul.EVM
open Eip8282.Audit.XiTransport
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Correspondence (runtimeCode)
open Eip8282.Audit.Integrator.MessageCall
open Eip8282.Audit.Integrator.CallBridge
open Eip8282.Audit.Integrator.SystemSpec
open Eip8282.Audit.Integrator.WorldNonempty

/-- The observable storage and bytes of a successful, committed message call. -/
def StorageResult (c : Context) (q : XiCall kind)
    (target drained calldataSize : UInt256) (out : ByteArray) : Prop :=
  ∃ (world : AccountMap .EVM) (created : Std.TreeSet AccountAddress compare)
    (gas : UInt256) (substate : Substate),
    c.result = .ok (created, world, gas, substate, true, out) ∧
    ∀ k, worldSlot world c.target k = expectedSlot (entrySt q) target drained calldataSize k

def depositData (q : XiCall .deposit) : ByteArray :=
  (Deposit.drainMem (entrySt q) (Deposit.headWord₀ q) (Deposit.mem₀ q)
    (Deposit.drainWord q).toNat).readWithPadding 0
    (UInt256.ofNat 184 * Deposit.drainWord q).toNat

def exitData (q : XiCall .exit) : ByteArray :=
  (Exit.drainMem (entrySt q) (Exit.headWord₀ q) (Exit.mem₀ q)
    (Exit.drainWord q).toNat).readWithPadding 0
    (UInt256.ofNat 68 * Exit.drainWord q).toNat

theorem deposit_system_commits (c : Context)
    (hcode : c.code = runtimeCode .deposit) (steps : Nat) (hf : c.fuel = steps + 1)
    (hsys : Deposit.callerWord (codeCall c hcode steps) = sysW)
    (hperm : c.permission = true) (hg : 2500000 ≤ c.gas.toNat) (hsteps : 8502 ≤ steps)
    (ho : HasOwner (entrySt (codeCall c hcode steps))) :
    let q := codeCall c hcode steps
    StorageResult c q (UInt256.ofNat 8) (Deposit.drainWord q)
      (Deposit.cdsizeWord q) (depositData q) := by
  let q := codeCall c hcode steps
  obtain ⟨world, created, gas, substate, hr, ⟨acc, hacc⟩, hs⟩ :=
    deposit_system_storage_result q hsys hperm hg hsteps ho
  exact ⟨world, created, gas, substate,
    commits_endpoint c hcode steps hf created world gas substate _ hr
      (beq_empty_false_of_get_some hacc), hs⟩

theorem exit_system_commits (c : Context)
    (hcode : c.code = runtimeCode .exit) (steps : Nat) (hf : c.fuel = steps + 1)
    (hsys : Exit.callerWord (codeCall c hcode steps) = sysW)
    (hperm : c.permission = true) (hg : 250000 ≤ c.gas.toNat) (hsteps : 802 ≤ steps)
    (ho : HasOwner (entrySt (codeCall c hcode steps))) :
    let q := codeCall c hcode steps
    StorageResult c q (UInt256.ofNat 2) (Exit.drainWord q)
      (Exit.cdsizeWord q) (exitData q) := by
  let q := codeCall c hcode steps
  obtain ⟨world, created, gas, substate, hr, ⟨acc, hacc⟩, hs⟩ :=
    exit_system_storage_result q hsys hperm hg hsteps ho
  exact ⟨world, created, gas, substate,
    commits_endpoint c hcode steps hf created world gas substate _ hr
      (beq_empty_false_of_get_some hacc), hs⟩

#print axioms deposit_system_commits
#print axioms exit_system_commits

end Eip8282.Audit.Integrator.CommittedSystem
