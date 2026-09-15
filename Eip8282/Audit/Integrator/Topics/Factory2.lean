import Eip8282.Audit.Integrator.Topics.Factory
import Eip8282.Audit.Integrator.FactoryInitializedExecution
import Eip8282.Audit.Integrator.Topics.Transaction
import Eip8282.Audit.Integrator.Topics.Transaction2
import Eip8282.Audit.Integrator.WorldNonempty

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## FactoryInitializedCall -/

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

end

section

/-! ## FactoryInitializedTransaction -/

/-! Committed initialization through the actual Υ factory transaction.
The post-constructor world is carried through Θ and Υ refund/payment/cleanup.
Canonical installation of the factory and the transaction's protocol admission
are explicit inputs, not consequences of its familiar address or of test RPCs. -/
namespace Eip8282.Audit.Integrator.FactoryInitializedTransaction
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open NestedEvents FactoryRuntimeEntry FactoryChildResources
open ReachableCalls (Contract address)
open JournalInvariant (modelKind Invariant)
open TransferFunding
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

/-- A successful actual deployment transaction supplies the invariant consumed
by later transaction histories. No initial protected invariant is assumed. -/
theorem initializes (kind : Contract) (c : RefundAccounting.Context) (steps : Nat)
    (sender factory : Account .EVM)
    (ha : TransactionFunding.Admission c sender)
    (hi : c.world.get? factoryAddress = some factory)
    (hc : factory.code = FactoryRuntimeEntry.runtime)
    (hn : factory.nonce.toNat < 2^64-1) (hne : c.sender ≠ factoryAddress)
    (ht : c.transaction.base.recipient = some factoryAddress)
    (hworld : worldFunds c.world < UInt256.size)
    (hdata : c.transaction.base.data = calldata (modelKind kind))
    (hgas : 1000000 ≤ c.entryGas.toNat)
    (hupper : c.transaction.base.gasLimit.toNat ≤ 2^64)
    (hf : 13 ≤ steps) (hcf : c.fuel = steps+19)
    (hcollision : ((childArgs (modelKind kind)
      (FactoryCallEntry.args (TransactionFactoryEntry.call c)) c.entryGas 0).context
      (steps+1)).collision (CreationSettlement.address (preimage (modelKind kind))) = false)
    (haddress : CreationSettlement.address (preimage (modelKind kind)) = address kind) :
    ∃ w ss used,
      c.result = .ok (w,ss,true,used) ∧ Invariant kind 0 w ∧
      ss.logSeries = #[] ∧ ss.selfDestructSet = ∅ ∧
      ∀ other budget, other ≠ kind → Invariant other budget c.world → Invariant other budget w := by
  have hentry : c.entryGas.toNat ≤ c.transaction.base.gasLimit.toNat := by
    change (UInt256.ofNat _).toNat ≤ _
    rw [Eip8282.Audit.EntryReach.toNat_ofNat_lit
      (c.transaction.base.gasLimit.toNat-intrinsicGas c.transaction)
      ((Nat.sub_le c.transaction.base.gasLimit.toNat (intrinsicGas c.transaction)).trans_lt
        c.transaction.base.gasLimit.val.isLt)]
    exact Nat.sub_le _ _
  have hcp := TransactionFactoryEntry.checkpoint_factory c sender factory ha hi hne
  have hfunded := (TransactionFactoryEntry.call_funding c sender ha).1
  have hbound := TransactionFactoryEntry.call_world_bound c sender ha hworld
  have hcallfuel : (TransactionFactoryEntry.call c).fuel = steps+18 :=
    TransactionFactoryEntry.call_fuel c (steps+18) hcf
  obtain ⟨cr,pw,remaining,ss,hcall,hinv,hlogs,hsd,hframes⟩ := FactoryInitializedCall.initializes kind
    (TransactionFactoryEntry.call c) steps factory rfl rfl hcp hc hn hne hfunded hbound
    rfl rfl (by change 0 < 1024; decide) hdata hgas (hentry.trans hupper) hf hcallfuel hcollision haddress
  have hsel := TransactionFactoryEntry.selected_code c sender factory ha hi hne hc
  have hprov := TransactionFactoryEntry.provisional_of_call c (by omega) hsel ht
    cr pw remaining ss true (address kind).toByteArray hcall
  have hlogs' : ss.logSeries = #[] := hlogs
  have hsd' : ss.selfDestructSet = ∅ := hsd
  have hnot : address kind ∉ ss.selfDestructSet := by rw [hsd']; simp
  have hframe := TransactionJournalEdges.settled_codeAt_frame c pw remaining ss hinv.1 hnot
  refine ⟨TransactionFunding.settledWorld c pw remaining ss,ss,
    RefundAccounting.netGas c.transaction.base.gasLimit remaining ss.refundBalance,
    ?_,JournalInvariant.frame hinv hframe,hlogs',hsd',?_⟩
  · rw [TransactionFunding.result_equation,hprov]
    rfl
  · intro other budget hne hiOther
    have hfactory : factoryAddress ≠ address other := by cases other <;> decide
    have htarget : address kind ≠ address other := by cases kind <;> cases other <;> simp_all +decide
    have hcpframe := TransactionJournalEdges.checkpoint_frame c ha (address other)
    have hpframe := hframes (address other) hfactory htarget
    have hprovInv := JournalInvariant.frame hiOther (CodeStorageFrame.trans hcpframe hpframe)
    exact JournalInvariant.frame hprovInv
      (TransactionJournalEdges.settled_codeAt_frame c pw remaining ss hprovInv.1 (by rw [hsd']; simp))

#print axioms initializes
end Eip8282.Audit.Integrator.FactoryInitializedTransaction

end
