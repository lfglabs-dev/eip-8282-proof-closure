import Eip8282.Audit.Integrator.Topics.Reference4
import Eip8282.Audit.Integrator.ReferenceRuntimeTerminalPayment

/-! Source transaction allocation pays the event list of the same actual
completed runtime, through its terminal charge. Requirements refer to actual
finite instruction occurrences, not persistent queue length. This is sufficient
resource accounting; actual source admission/execution remain separate. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeTransactionPayment
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings
open ReferenceRuntimeCompletion ReferenceRuntimePayment ReferenceMeterPath
open ReferenceMemoryCapacity (cost cost_mono)
open ReferenceRuntimeTerminalPayment
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def AllocatedPaymentFor (cap : Nat) (trace : List Labelled) (events : List Event) (amount : Nat) : Prop :=
  ∀ txGas intrinsic : Nat,
    intrinsic+baseBound cap*trace.length+cost cap ≤ 16777216 →
    intrinsic+baseBound cap*trace.length+cost cap+97920*storageWrites trace ≤ txGas →
    ∃ final, run (events++[.ordinary amount]) (ReferenceTransactionPayment.initialMeter txGas intrinsic) = some final

private theorem through_terminal {kind : Kind} {parent : ReferenceStorageView.Parent}
    {initialCreated : Set AccountAddress} {fuel rem cap gasCost amount : Nat}
    {pre exit mid post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind parent initialCreated fuel pre v w trace rem exit finish finalWarm events)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt exit).1 exit = .ok (mid,gasCost))
    (hs : StepOk (rem-1) gasCost (decodeAt exit) mid post)
    (threshold : RuntimeMemoryFunding.energy pre < cost (cap+1))
    (amountEq : amount = cost post.activeWords.toNat-cost exit.activeWords.toNat) :
    AllocatedPaymentFor cap trace events amount := by
  have hr := h.viewed.erase
  have hatExit := (RuntimeMemoryMonotone.runs hat hr).1
  have monoPrefix := cost_mono (RuntimeMemoryMonotone.runs hat hr).2
  have monoTerminal := cost_mono (RuntimeMemoryMonotone.accepted hatExit hz hs).1
  have finalEnergy := (RuntimeMemoryFunding.accepted_energy hatExit hz hs).trans
    (RuntimeMemoryFunding.runs_energy hat hr)
  have postCost : cost post.activeWords.toNat ≤ RuntimeMemoryFunding.energy pre := by
    unfold RuntimeMemoryFunding.energy at finalEnergy ⊢
    omega
  have postCap := RuntimeMemoryFunding.capacity_of_energy postCost threshold
  have exitCap := (RuntimeMemoryMonotone.accepted hatExit hz hs).1.trans postCap
  have prefixBound := execution_bound h hat exitCap
  have costBound := cost_mono postCap
  have totalExec : sumExec (events++[.ordinary amount]) ≤ baseBound cap*trace.length+cost cap := by
    have split := (budgets_append events [.ordinary amount]).1
    change sumExec (events++[.ordinary amount]) = sumExec events+amount at split
    rw [split,amountEq]
    omega
  have totalState : sumState (events++[.ordinary amount]) = 97920*storageWrites trace := by
    have split := (budgets_append events [.ordinary amount]).2
    change sumState (events++[.ordinary amount]) = sumState events+0 at split
    rw [split,state_total h,Nat.add_zero]
  intro txGas intrinsic ex total
  apply ReferenceTransactionPayment.payment
  · omega
  · omega

/-- Full actual success witness and terminal view, paid using the source split.
The old sufficient separate-pool certificate is preserved on this same witness. -/
def SuccessPayment (kind : Kind) (parent : ReferenceStorageView.Parent)
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
        AllocatedPaymentFor cap t.trace events (terminalCost t.op finish)

theorem success {kind : Kind} {parent : ReferenceStorageView.Parent}
    {initialCreated : Set AccountAddress} {fuel cap : Nat} {pre post : EVM.State}
    {out : ByteArray} {v : View} {w : Warm}
    (certificate : SuccessCertificate kind parent initialCreated fuel cap pre post out v w)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (threshold : RuntimeMemoryFunding.energy pre < cost (cap+1)) :
    SuccessPayment kind parent initialCreated fuel cap pre post out v w := by
  obtain ⟨t,finish,finalWarm,events,h,related,warm,created,decoded,terminal,amountEq,paid⟩ := certificate
  have hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt t.exit).1 t.exit = .ok (t.mid,t.cost) := by
    rw [t.decode]; exact t.charge
  have hs : StepOk (t.rem+1-1) t.cost (decodeAt t.exit) t.mid post := by
    rw [t.decode]; simpa only [Nat.add_sub_cancel] using t.step
  exact ⟨t,finish,finalWarm,events,h,related,warm,created,decoded,terminal,paid,
    through_terminal h hat hz hs threshold amountEq⟩

/-- Cancelled internal execution still consumes resources through REVERT.
This theorem preserves its output and does not commit its writes or logs. -/
def RevertPayment (kind : Kind) (parent : ReferenceStorageView.Parent)
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
        AllocatedPaymentFor cap t.trace events (terminalCost .REVERT finish)

theorem revert {kind : Kind} {parent : ReferenceStorageView.Parent}
    {initialCreated : Set AccountAddress} {fuel cap : Nat} {pre : EVM.State}
    {gas : UInt256} {out : ByteArray} {v : View} {w : Warm}
    (certificate : RevertCertificate kind parent initialCreated fuel cap pre gas out v w)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (threshold : RuntimeMemoryFunding.energy pre < cost (cap+1)) :
    RevertPayment kind parent initialCreated fuel cap pre gas out v w := by
  obtain ⟨t,finish,finalWarm,events,off,len,rest,h,related,warm,created,decoded,shape,result,output,amountEq,paid⟩ := certificate
  have hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt t.exit).1 t.exit = .ok (t.mid,t.cost) := by
    rw [t.decode]; exact t.charge
  have hs : StepOk (t.rem+1-1) t.cost (decodeAt t.exit) t.mid t.post := by
    rw [t.decode]; simpa only [Nat.add_sub_cancel] using t.step
  exact ⟨t,finish,finalWarm,events,off,len,rest,h,related,warm,created,decoded,shape,result,output,paid,
    through_terminal h hat hz hs threshold amountEq⟩

#print axioms success
#print axioms revert
end Eip8282.Audit.Integrator.ReferenceRuntimeTransactionPayment
