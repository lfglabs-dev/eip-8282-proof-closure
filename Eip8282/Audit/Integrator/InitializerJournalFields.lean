import Eip8282.Audit.Integrator.PrefundedInitialization

/-! Journal fields of an actual successful initializer, including code deposit.
The self-destruct set follows the complete concrete init executions and actual
settlement guards. No predicted final substate is supplied. Parent factory,
Theta and transaction commitment remain separate consumers. -/
namespace Eip8282.Audit.Integrator.InitializerJournalFields
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open CreationSettlement (Context address)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private theorem sstore_set (s : EvmYul.State .EVM) (key value : UInt256) :
    (s.sstore key value).substate.selfDestructSet = s.substate.selfDestructSet := by
  unfold EvmYul.State.sstore
  dsimp only
  cases s.lookupAccount s.executionEnv.codeOwner <;> rfl

theorem logs (kind : Kind) (c : Context) (preimage : ByteArray) (steps : Nat)
    (hi : c.init = Initialization.initCode kind)
    (hd : PrefundedInitialization.Domain kind c preimage steps)
    {a : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {world : AccountMap .EVM} {gas : UInt256} {ss : Substate} {out : ByteArray}
    (hr : c.result = .ok (a,created,world,gas,ss,true,out)) :
    ss.logSeries = c.substate.logSeries := by
  exact (PrefundedInitialization.observed_of_success kind c preimage steps hi hd hr).2.2.2.2.2.2

theorem selfdestruct (kind : Kind) (c : Context) (preimage : ByteArray) (steps : Nat)
    (hi : c.init = Initialization.initCode kind)
    (hd : PrefundedInitialization.Domain kind c preimage steps)
    {a : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {world : AccountMap .EVM} {gas : UInt256} {ss : Substate} {out : ByteArray}
    (hr : c.result = .ok (a,created,world,gas,ss,true,out)) :
    ss.selfDestructSet = c.substate.selfDestructSet := by
  cases kind with
  | deposit =>
    obtain ⟨ig,he⟩ := Initialization.deposit_execution
      (c.initCall (address preimage) steps) hd.resources.1 hd.resources.2
    rw [← CreationSettlement.execution_eq_initialization c (address preimage) steps .deposit
      hd.fuel_eq hd.no_collision hi] at he
    obtain ⟨_,_,_,_,_,hss,_,_⟩ := CreationSettlement.installed_of_known_execution c hd.preimage_eq he hr
    rw [hss]
    rfl
  | exit =>
    obtain ⟨ig,he⟩ := Initialization.exit_execution
      (c.initCall (address preimage) steps) hd.resources.1 hd.resources.2.1 hd.resources.2.2.1
    rw [← CreationSettlement.execution_eq_initialization c (address preimage) steps .exit
      hd.fuel_eq hd.no_collision hi] at he
    obtain ⟨_,_,_,_,_,hss,_,_⟩ := CreationSettlement.installed_of_known_execution c hd.preimage_eq he hr
    rw [hss]
    unfold Initialization.exitStored
    rw [sstore_set]
    rfl

theorem completed (kind : Kind) (c : Context) (preimage : ByteArray) (steps : Nat)
    (hi : c.init = Initialization.initCode kind)
    (hd : PrefundedInitialization.Domain kind c preimage steps)
    {a : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {world : AccountMap .EVM} {gas : UInt256} {ss : Substate} {out : ByteArray}
    (hr : c.result = .ok (a,created,world,gas,ss,true,out)) :
    ss.logSeries = c.substate.logSeries ∧ ss.selfDestructSet = c.substate.selfDestructSet :=
  ⟨logs kind c preimage steps hi hd hr,selfdestruct kind c preimage steps hi hd hr⟩

#print axioms logs
#print axioms selfdestruct
#print axioms completed
end Eip8282.Audit.Integrator.InitializerJournalFields
