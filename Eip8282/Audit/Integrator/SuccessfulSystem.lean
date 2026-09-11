import Eip8282.Audit.Integrator.CommittedSystem
import Eip8282.Audit.Integrator.SystemInversion
import Eip8282.Audit.Integrator.SuccessfulQuote
import Eip8282.Audit.Integrator.TransferFrame

/-!
# SYSTEM storage commitment forced by actual Θ success

Actual success derives positive interpreter fuel and the executed Ξ result.
Owner preservation excludes Θ's empty-world fallback. No sufficient gas, fuel,
permission, or post-state agreement is assumed. The owner premise refers to the
world before the actual call-value transfer.
-/
namespace Eip8282.Audit.Integrator.SuccessfulSystem

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Correspondence (runtimeCode)
open MessageCall CallBridge CallSuccess SuccessfulQuote SystemSpec CommittedSystem

/-- A SYSTEM control store retains the executing owner after pointer updates
and all actual read touches. -/
theorem owner_final {pre st' stX : EvmYul.State .EVM}
    (ho : HasOwner pre) (ht : Touched pre st') (drained : UInt256)
    (hx : Touched (headUpdate st' (slotW pre (UInt256.ofNat 2))
      (slotW pre (UInt256.ofNat 3)) drained) stX) (excess : UInt256) :
    HasOwner (controlStore stX excess) := by
  exact owner_sstore (owner_sstore
    (owner_touched hx (owner_headUpdate (owner_touched ht ho) _ _ _)) _ _) _ _

theorem exit_system (c : Context) (hcode : c.code = runtimeCode .exit)
    (hsys : c.caller = EvmRunner.sysAddr)
    (ho : ∃ account, c.world.get? c.target = some account)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,true,out)) :
    let q := codeCall c hcode (c.fuel-1)
    StorageResult c q (UInt256.ofNat 2) (Exit.drainWord q) (Exit.cdsizeWord q) (exitData q) := by
  have hf : c.fuel = (c.fuel-1)+1 := by have hp := positive_fuel c h; omega
  obtain ⟨ew,es,he,_,_⟩ := codeCall_of_success c hcode (c.fuel-1) hf h
  let q := codeCall c hcode (c.fuel-1)
  have howner := TransferFrame.codeCall_hasOwner c hcode (c.fuel-1) ho
  obtain ⟨hs,hout⟩ := SystemInversion.exit_system_storage q hsys he howner
  obtain ⟨st',stX,g,ht,hx,hpub,_⟩ := SystemInversion.exit_system_result q hsys he
  have hw : ew = (controlStore stX (Exit.newExcess q stX)).accountMap :=
    congrArg (fun p => p.2.1) hpub
  obtain ⟨account,haccount⟩ := owner_final howner ht (Exit.drainWord q) hx (Exit.newExcess q stX)
  have hne : (ew == ∅) = false := by
    rw [hw]
    exact WorldNonempty.beq_empty_false_of_get_some haccount
  have hc := commits_endpoint c hcode (c.fuel-1) hf created ew gas es out he hne
  rw [hout] at hc
  exact ⟨ew,created,gas,es,hc,hs⟩

theorem deposit_system (c : Context) (hcode : c.code = runtimeCode .deposit)
    (hsys : c.caller = EvmRunner.sysAddr)
    (ho : ∃ account, c.world.get? c.target = some account)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,true,out)) :
    let q := codeCall c hcode (c.fuel-1)
    StorageResult c q (UInt256.ofNat 8) (Deposit.drainWord q) (Deposit.cdsizeWord q) (depositData q) := by
  have hf : c.fuel = (c.fuel-1)+1 := by have hp := positive_fuel c h; omega
  obtain ⟨ew,es,he,_,_⟩ := codeCall_of_success c hcode (c.fuel-1) hf h
  let q := codeCall c hcode (c.fuel-1)
  have howner := TransferFrame.codeCall_hasOwner c hcode (c.fuel-1) ho
  obtain ⟨hs,hout⟩ := SystemInversion.deposit_system_storage q hsys he howner
  obtain ⟨st',stX,g,ht,hx,hpub,_⟩ := SystemInversion.deposit_system_result q hsys he
  have hw : ew = (controlStore stX (Deposit.newExcess q stX)).accountMap :=
    congrArg (fun p => p.2.1) hpub
  obtain ⟨account,haccount⟩ := owner_final howner ht (Deposit.drainWord q) hx (Deposit.newExcess q stX)
  have hne : (ew == ∅) = false := by
    rw [hw]
    exact WorldNonempty.beq_empty_false_of_get_some haccount
  have hc := commits_endpoint c hcode (c.fuel-1) hf created ew gas es out he hne
  rw [hout] at hc
  exact ⟨ew,created,gas,es,hc,hs⟩

#print axioms owner_final
#print axioms exit_system
#print axioms deposit_system

end Eip8282.Audit.Integrator.SuccessfulSystem
