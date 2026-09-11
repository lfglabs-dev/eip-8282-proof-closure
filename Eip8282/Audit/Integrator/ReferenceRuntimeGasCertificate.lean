import Eip8282.Audit.Integrator.ReferenceRuntimeTransactionPayment
import Eip8282.Audit.Integrator.ReferenceRuntimeGasBalance

/-! The same successful or reverted runtime witness now carries source
allocation, exact terminal payment and an executed-log bound in net pools with
its initial state-credit correction. This does not replace committed occurrence
selection, source nested grant binding or post-transaction refund settlement. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeGasCertificate
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings
open ReferenceRuntimeCompletion ReferenceRuntimePayment ReferenceMeterPath
open ReferenceMemoryCapacity (cost)
open ReferenceRuntimeTerminalPayment ReferenceRuntimeTransactionPayment
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def AllocatedBoundFor (p : ReferenceStorageView.Parent) (v : View)
    (cap : Nat) (trace : List Labelled) (events : List Event) (amount : Nat) : Prop :=
  ∀ txGas intrinsic : Nat,
    intrinsic+baseBound cap*trace.length+cost cap ≤ 16777216 →
    intrinsic+baseBound cap*trace.length+cost cap+97920*storageWrites trace ≤ txGas →
    ∃ final,
      run (events++[.ordinary amount]) (ReferenceTransactionPayment.initialMeter txGas intrinsic) = some final ∧
      (375*ReferenceRuntimeGasBalance.logCount trace : Int) ≤
        ReferenceMeterConservation.pools (ReferenceTransactionPayment.initialMeter txGas intrinsic)-
        ReferenceMeterConservation.pools final+ReferenceRuntimeStateBalance.totalPotential p v.storage

private theorem bounded {kind : Kind} {p : ReferenceStorageView.Parent} {initialCreated : Set AccountAddress}
    {fuel rem cap amount : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post finish finalWarm events)
    (paid : AllocatedPaymentFor cap trace events amount) : AllocatedBoundFor p v cap trace events amount := by
  intro txGas intrinsic execution total
  obtain ⟨final,hpaid⟩ := paid txGas intrinsic execution total
  exact ⟨final,hpaid,ReferenceRuntimeGasBalance.through_terminal h amount hpaid⟩

def SuccessGas (kind : Kind) (parent : ReferenceStorageView.Parent)
    (initialCreated : Set AccountAddress) (fuel cap : Nat) (pre post : EVM.State)
    (out : ByteArray) (v : View) (w : Warm) : Prop :=
  ∃ t : SuccessInversion.SuccessTrace (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre post out,
    ∃ finish finalWarm events,
      Coupled kind parent initialCreated fuel pre v w t.trace (t.rem+1) t.exit finish finalWarm events ∧
      Related parent finish t.exit ∧ WarmRelated finalWarm t.exit ∧
      finish.storage.created = initialCreated ∧
      decodeAt t.exit = (ReferenceDecodeSites.referenceDecode finish.env.code finish.pc).getD (.STOP,none) ∧
      SuccessEnd parent finish post out t.op ∧
      PaymentFor cap t.trace events (terminalCost t.op finish) ∧
      AllocatedBoundFor parent v cap t.trace events (terminalCost t.op finish)

theorem success {kind : Kind} {parent : ReferenceStorageView.Parent}
    {initialCreated : Set AccountAddress} {fuel cap : Nat} {pre post : EVM.State}
    {out : ByteArray} {v : View} {w : Warm}
    (certificate : SuccessPayment kind parent initialCreated fuel cap pre post out v w) :
    SuccessGas kind parent initialCreated fuel cap pre post out v w := by
  obtain ⟨t,finish,finalWarm,events,h,related,warm,created,decoded,terminal,paid,allocated⟩ := certificate
  exact ⟨t,finish,finalWarm,events,h,related,warm,created,decoded,terminal,paid,bounded h allocated⟩

def RevertGas (kind : Kind) (parent : ReferenceStorageView.Parent)
    (initialCreated : Set AccountAddress) (fuel cap : Nat) (pre : EVM.State)
    (gas : UInt256) (out : ByteArray) (v : View) (w : Warm) : Prop :=
  ∃ t : RuntimeRevertTrace.RevertTrace (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre gas out,
    ∃ finish finalWarm events off len rest,
      Coupled kind parent initialCreated fuel pre v w t.trace (t.rem+1) t.exit finish finalWarm events ∧
      Related parent finish t.exit ∧ WarmRelated finalWarm t.exit ∧
      finish.storage.created = initialCreated ∧
      decodeAt t.exit = (ReferenceDecodeSites.referenceDecode finish.env.code finish.pc).getD (.STOP,none) ∧
      finish.stack = off::len::rest ∧ ReferenceReturnView.Result parent finish off len rest t.post ∧
      out = (ReferenceReturnView.returnMemory finish off len).extract off.toNat (off.toNat+len.toNat) ∧
      PaymentFor cap t.trace events (terminalCost .REVERT finish) ∧
      AllocatedBoundFor parent v cap t.trace events (terminalCost .REVERT finish)

theorem revert {kind : Kind} {parent : ReferenceStorageView.Parent}
    {initialCreated : Set AccountAddress} {fuel cap : Nat} {pre : EVM.State}
    {gas : UInt256} {out : ByteArray} {v : View} {w : Warm}
    (certificate : RevertPayment kind parent initialCreated fuel cap pre gas out v w) :
    RevertGas kind parent initialCreated fuel cap pre gas out v w := by
  obtain ⟨t,finish,finalWarm,events,off,len,rest,h,related,warm,created,decoded,shape,result,output,paid,allocated⟩ := certificate
  exact ⟨t,finish,finalWarm,events,off,len,rest,h,related,warm,created,decoded,shape,result,output,paid,bounded h allocated⟩

#print axioms success
#print axioms revert
end Eip8282.Audit.Integrator.ReferenceRuntimeGasCertificate
