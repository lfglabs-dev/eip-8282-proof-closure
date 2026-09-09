import Eip8282.Audit.Integrator.CommittedSystem
import Eip8282.Audit.Integrator.TransferFrame

/-!
# SYSTEM is not blocked by inhibition when execution resources suffice

This progress clause complements arbitrary-resource safety: a SYSTEM call with
an owner, write permission and explicit sufficient gas/fuel completes successfully
for every storage image, including INHIBITOR. No enabled gate or desired result
is assumed. It does not assert protocol scheduling or resource provision.
-/
namespace Eip8282.Audit.Integrator.SystemProgress

open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Correspondence (runtimeCode)
open Eip8282.Audit.EntryReach
open MessageCall CallBridge

def Completes (c : Context) : Prop :=
  ∃ (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (substate : Substate) (out : ByteArray),
    c.result = .ok (created, world, gas, substate, true, out)

/-- Parameter-code progress property, independent of storage contents. -/
def Progress (code : ByteArray) : Prop :=
  ∀ c : Context, c.code = code → c.caller = Eip8282.Audit.EvmRunner.sysAddr →
    (∃ account, c.world.get? c.target = some account) → c.permission = true →
    2500000 ≤ c.gas.toNat → 8503 ≤ c.fuel → Completes c

theorem pinned (kind : Kind) : Progress (runtimeCode kind) := by
  intro c hcode hsys ho hp hg hfuel
  let steps := c.fuel-1
  have hf : c.fuel = steps+1 := by omega
  have hsteps : 8502 ≤ steps := by omega
  have howner := TransferFrame.codeCall_hasOwner c hcode steps ho
  have hcaller := (callerW_eq_sysW_iff (codeCall c hcode steps)).mpr hsys
  cases kind with
  | deposit =>
    obtain ⟨world, created, gas, substate, hr, _⟩ :=
      CommittedSystem.deposit_system_commits c hcode steps hf hcaller hp hg hsteps howner
    exact ⟨created, world, gas, substate, _, hr⟩
  | exit =>
    obtain ⟨world, created, gas, substate, hr, _⟩ :=
      CommittedSystem.exit_system_commits c hcode steps hf hcaller hp (by omega) (by omega) howner
    exact ⟨created, world, gas, substate, _, hr⟩

#print axioms pinned

end Eip8282.Audit.Integrator.SystemProgress
