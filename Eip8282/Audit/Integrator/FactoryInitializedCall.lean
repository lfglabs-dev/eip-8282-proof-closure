import Eip8282.Audit.Integrator.FactoryInitializedExecution
import Eip8282.Audit.Integrator.FactoryCallEntry
import Eip8282.Audit.Integrator.FactoryReturnEncoding
import Eip8282.Audit.Integrator.WorldNonempty

/-! Actual factory message-call success from its pre-transfer world. The
constructor-derived invariant survives Θ's literal nonempty-world settlement.
Enclosing transaction settlement and canonical deployment history are separate
consumers; this result is not a protocol deployment certificate. -/
namespace Eip8282.Audit.Integrator.FactoryInitializedCall
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open NestedEvents FactoryRuntimeEntry FactoryChildResources
open ReachableCalls (Contract address)
open JournalInvariant (modelKind Invariant)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem initializes (kind : Contract) (c : MessageCall.Context) (steps : Nat)
    (old : Account .EVM)
    (ht : c.target = factoryAddress) (hc : c.code = FactoryRuntimeEntry.runtime)
    (hinstalled : c.world.get? c.target = some old)
    (hold : old.code = FactoryRuntimeEntry.runtime) (hn : old.nonce.toNat < 2^64-1)
    (hne : c.caller ≠ c.target)
    (hfunded : c.value.toNat ≤ TransferFunding.worldBalance c.world c.caller)
    (hworld : TransferFunding.worldFunds c.world < UInt256.size)
    (hv : c.apparentValue = c.value) (hp : c.permission = true) (hd : c.depth < 1024)
    (hdata : c.calldata = calldata (modelKind kind))
    (hgas : 1000000 ≤ c.gas.toNat) (hupper : c.gas.toNat ≤ 2^64)
    (hf : 13 ≤ steps) (hcf : c.fuel = steps+18)
    (hcollision : ((childArgs (modelKind kind) (FactoryCallEntry.args c) c.gas 0).context
      (steps+1)).collision (CreationSettlement.address (preimage (modelKind kind))) = false)
    (haddress : CreationSettlement.address (preimage (modelKind kind)) = address kind) :
    ∃ cr w gas ss,
      c.result = .ok (cr,w,gas,ss,true,(address kind).toByteArray) ∧ Invariant kind 0 w ∧
      ss.logSeries = c.substate.logSeries ∧ ss.selfDestructSet = c.substate.selfDestructSet ∧
      ∀ protectedAddr, factoryAddress ≠ protectedAddr → address kind ≠ protectedAddr →
        CodeStorageFrame.Frame c.world w protectedAddr := by
  obtain ⟨hcode,howner,hcalldata,hperm,hdepth,hnonce,hvalue,_⟩ :=
    FactoryCallEntry.entry_gates (modelKind kind) c old ht hc hinstalled hold hn hne
      hfunded hworld hv hp hd hdata
  obtain ⟨cr,w,gas,ss,he,hi,hlogs,hsd,hframes⟩ := FactoryInitializedExecution.initializes kind
    (FactoryCallEntry.args c) steps hcode hcalldata howner hperm hgas hupper hf
    hnonce hvalue hdepth hcollision haddress
  rw [← hcf,FactoryCallEntry.execution_eq,FactoryReturnEncoding.output_address] at he
  obtain ⟨account,haccount,_⟩ := hi.1
  refine ⟨cr,w,gas,ss,MessageCall.success_commits_world c cr w gas ss
    (address kind).toByteArray he (WorldNonempty.beq_empty_false_of_get_some haccount),hi,hlogs,hsd,?_⟩
  intro protectedAddr hfactory htarget
  exact CodeStorageFrame.trans (CodeStorageFrame.entry c protectedAddr)
    (hframes protectedAddr hfactory htarget)

#print axioms initializes
end Eip8282.Audit.Integrator.FactoryInitializedCall
