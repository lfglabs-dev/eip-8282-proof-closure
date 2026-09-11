import Eip8282.Audit.Integrator.PrefundedInitialization
import Eip8282.Audit.Integrator.CreationStorageFrame

/-! Other-address code and storage survive the actual pinned initializer and
successful Lambda code deposit. This is a local execution producer, not a
claim that a surrounding transaction has committed. -/
namespace Eip8282.Audit.Integrator.InitializerWorldFrame
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.EntryReach
open CreationSettlement Initialization CodeStorageFrame
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private theorem installed_world (c : Context) {bytes : ByteArray}
    (hp : c.preimage = some bytes)
    {ic : Std.TreeSet AccountAddress compare} {iw : AccountMap .EVM}
    {ig : UInt256} {ia : Substate} {code : ByteArray}
    (he : c.execution (address bytes) = .ok (.success (ic,iw,ig,ia) code))
    {a : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {world : AccountMap .EVM} {gas : UInt256} {ss : Substate} {out : ByteArray}
    (hr : c.result = .ok (a,created,world,gas,ss,true,out)) :
    world = install iw (address bytes) code := by
  rw [result_eq_settle c hp,he] at hr
  cases hf : c.depositFailure (address bytes) ig code <;>
    simp only [Context.settle,hf,Bool.false_eq_true,Bool.not_false,Bool.not_true,
      ↓reduceIte,Except.ok.injEq,Prod.mk.injEq] at hr
  · exact hr.2.2.1.symm
  · simp at hr

private theorem sstore_away (st : EvmYul.State .EVM) (k v : UInt256)
    (protectedAddr : AccountAddress) (hne : st.executionEnv.codeOwner ≠ protectedAddr) :
    Frame st.accountMap (st.sstore k v).accountMap protectedAddr := by
  have he := AppendSpec.other_account_sstore st k v protectedAddr (Ne.symm hne)
  constructor
  · intro old ho
    exact ⟨old,he.trans ho,rfl⟩
  · intro slot
    unfold SystemSpec.worldSlot
    rw [he]

/-- The frame follows from the actual initializer world and actual successful
code deposit; the protected address may be the sender but not the new target. -/
theorem preserves (kind : Kind) (c : Context) (bytes : ByteArray) (steps : Nat)
    (protectedAddr : AccountAddress) (hi : c.init = initCode kind)
    (hd : PrefundedInitialization.Domain kind c bytes steps)
    (hne : address bytes ≠ protectedAddr)
    {a : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {world : AccountMap .EVM} {gas : UInt256} {ss : Substate} {out : ByteArray}
    (hr : c.result = .ok (a,created,world,gas,ss,true,out)) :
    Frame c.world world protectedAddr := by
  let init := c.initCall (address bytes) steps
  have hentry := CreationStorageFrame.entry_frame c (address bytes) protectedAddr
  cases kind with
  | deposit =>
    obtain ⟨ig,he⟩ := deposit_execution init hd.resources.1 hd.resources.2
    rw [← execution_eq_initialization c (address bytes) steps .deposit
      hd.fuel_eq hd.no_collision hi] at he
    have hw := installed_world c hd.preimage_eq he hr
    rw [hw]
    exact CodeStorageFrame.trans hentry
      (CreationStorageFrame.install_away_frame _ _ protectedAddr _ hne)
  | exit =>
    obtain ⟨ig,he⟩ := exit_execution init hd.resources.1 hd.resources.2.1 hd.resources.2.2.1
    rw [← execution_eq_initialization c (address bytes) steps .exit
      hd.fuel_eq hd.no_collision hi] at he
    have hw := installed_world c hd.preimage_eq he hr
    rw [hw]
    have hstore : Frame (c.entryWorld (address bytes)) (exitStored init).accountMap protectedAddr :=
      sstore_away (init.entry .exit).toState ⟨0⟩ INH protectedAddr hne
    exact CodeStorageFrame.trans (CodeStorageFrame.trans hentry hstore)
      (CreationStorageFrame.install_away_frame _ _ protectedAddr _ hne)

#print axioms preserves
end Eip8282.Audit.Integrator.InitializerWorldFrame
