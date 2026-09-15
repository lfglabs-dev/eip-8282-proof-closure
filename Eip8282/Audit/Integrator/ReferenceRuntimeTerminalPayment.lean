import Eip8282.Audit.Integrator.Topics.ReferenceRuntime
import Eip8282.Audit.Integrator.ReferenceRuntimeCompletion

/-! Complete source-formula resource certificates for the same observed
successful or reverted runtime execution. Each certificate gives sufficient
initial grants for the literal payment sequence through the terminal opcode;
it does not assert that protocol admission supplied those grants. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeTerminalPayment
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings
open ReferenceRuntimeCompletion ReferenceRuntimePayment ReferenceMeterPath
open ReferenceMemoryCapacity (cost cost_mono)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def returnCost (v : View) (off len : UInt256) : Nat :=
  cost ((ReferenceReturnView.returnMemory v off len).size/32)-cost (words v)

def terminalCost (op : Operation .EVM) (v : View) : Nat :=
  if op = .STOP then 0 else returnCost v v.stack[0]! v.stack[1]!

private theorem returned_cost {parent : ReferenceStorageView.Parent} {v : View}
    {pre post : EVM.State} {off len : UInt256} {rest : Stack UInt256}
    (related : Related parent v pre) (result : ReferenceReturnView.Result parent v off len rest post) :
    returnCost v off len = cost post.activeWords.toNat-cost pre.activeWords.toNat := by
  unfold returnCost
  rw [result.memory.size,words_related related]
  congr 2
  omega

theorem success_cost {parent : ReferenceStorageView.Parent} {v : View}
    {pre post : EVM.State} {op : Operation .EVM} {out : ByteArray}
    (related : Related parent v pre) (terminal : SuccessEnd parent v post out op) :
    terminalCost op v = cost post.activeWords.toNat-cost pre.activeWords.toNat := by
  cases terminal with
  | stopped postRelated _ =>
    have he := (words_related postRelated).symm.trans (words_related related)
    simp [terminalCost,he]
  | returned shape result _ =>
    simpa only [terminalCost,show (Operation.RETURN : Operation .EVM) ≠ .STOP by decide,
      ↓reduceIte,shape,List.getElem!_cons_zero,List.getElem!_cons_succ] using returned_cost related result

theorem revert_cost {parent : ReferenceStorageView.Parent} {v : View}
    {pre post : EVM.State} {off len : UInt256} {rest : Stack UInt256}
    (related : Related parent v pre) (shape : v.stack = off::len::rest)
    (result : ReferenceReturnView.Result parent v off len rest post) :
    terminalCost .REVERT v = cost post.activeWords.toNat-cost pre.activeWords.toNat := by
  simpa only [terminalCost,show (Operation.REVERT : Operation .EVM) ≠ .STOP by decide,
    ↓reduceIte,shape,List.getElem!_cons_zero,List.getElem!_cons_succ] using returned_cost related result

/-- The grants refer to the actual instruction trace. They do not identify
executed storage writes with committed appends or final queue length. -/
def PaymentFor (cap : Nat) (trace : List Labelled) (prefixEvents : List Event) (amount : Nat) : Prop :=
  ∀ meter : ReferenceStorageGas.Meter,
    baseBound cap*trace.length+cost cap ≤ meter.execution →
    97920*storageWrites trace ≤ meter.reservoir →
    ∃ final, run (prefixEvents++[.ordinary amount]) meter = some final ∧
      meter.execution-(baseBound cap*trace.length+cost cap) ≤ final.execution ∧
      meter.reservoir-97920*storageWrites trace ≤ final.reservoir

private theorem through_terminal {kind : Kind} {parent : ReferenceStorageView.Parent}
    {initialCreated : Set AccountAddress} {fuel rem cap gasCost amount : Nat}
    {pre exit mid post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {prefixEvents : List Event}
    (h : Coupled kind parent initialCreated fuel pre v w trace rem exit finish finalWarm prefixEvents)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt exit).1 exit = .ok (mid,gasCost))
    (hs : StepOk (rem-1) gasCost (decodeAt exit) mid post)
    (threshold : RuntimeMemoryFunding.energy pre < cost (cap+1))
    (amountEq : amount = cost post.activeWords.toNat-cost exit.activeWords.toNat) :
    PaymentFor cap trace prefixEvents amount := by
  have hr := h.viewed.erase
  have hatExit := (RuntimeMemoryMonotone.runs hat hr).1
  have monoPrefix := cost_mono (RuntimeMemoryMonotone.runs hat hr).2
  have monoTerminal := cost_mono (RuntimeMemoryMonotone.accepted hatExit hz hs).1
  have initialEnergy := RuntimeMemoryFunding.runs_energy hat hr
  have finalEnergy := (RuntimeMemoryFunding.accepted_energy hatExit hz hs).trans initialEnergy
  have postCost : cost post.activeWords.toNat ≤ RuntimeMemoryFunding.energy pre := by
    unfold RuntimeMemoryFunding.energy at finalEnergy ⊢
    omega
  have postCap := RuntimeMemoryFunding.capacity_of_energy postCost threshold
  have exitCap := (RuntimeMemoryMonotone.accepted hatExit hz hs).1.trans postCap
  have prefixBound := execution_bound h hat exitCap
  have costBound := cost_mono postCap
  have totalExec : sumExec (prefixEvents++[.ordinary amount]) ≤ baseBound cap*trace.length+cost cap := by
    have split := (budgets_append prefixEvents [.ordinary amount]).1
    change sumExec (prefixEvents++[.ordinary amount]) = sumExec prefixEvents+amount at split
    rw [split,amountEq]
    omega
  have totalState : sumState (prefixEvents++[.ordinary amount]) = 97920*storageWrites trace := by
    have split := (budgets_append prefixEvents [.ordinary amount]).2
    change sumState (prefixEvents++[.ordinary amount]) = sumState prefixEvents+0 at split
    rw [split,state_total h,Nat.add_zero]
  intro meter exec reserve
  obtain ⟨final,paid,he,hr⟩ := ReferenceMeterPath.payment (prefixEvents++[.ordinary amount]) meter
    (totalExec.trans exec) (by rw [totalState]; exact reserve)
  refine ⟨final,paid,?_,?_⟩
  · omega
  · rw [totalState] at hr; exact hr

/-- Annotate the actual success witness, preserving its full observed endpoint.
The returned resource certificate pays this same prefix and terminal charge. -/
def SuccessCertificate (kind : Kind) (parent : ReferenceStorageView.Parent)
    (initialCreated : Set AccountAddress) (fuel cap : Nat) (pre post : EVM.State)
    (out : ByteArray) (v : View) (w : Warm) : Prop :=
    ∃ t : SuccessInversion.SuccessTrace (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre post out,
      ∃ finish finalWarm prefixEvents,
        Coupled kind parent initialCreated fuel pre v w t.trace (t.rem+1) t.exit finish finalWarm prefixEvents ∧
        Related parent finish t.exit ∧ WarmRelated finalWarm t.exit ∧
        finish.storage.created = initialCreated ∧
        decodeAt t.exit = (ReferenceDecodeSites.referenceDecode finish.env.code finish.pc).getD (.STOP,none) ∧
        SuccessEnd parent finish post out t.op ∧
        terminalCost t.op finish = cost post.activeWords.toNat-cost t.exit.activeWords.toNat ∧
        PaymentFor cap t.trace prefixEvents (terminalCost t.op finish)

theorem success {kind : Kind} {parent : ReferenceStorageView.Parent}
    {initialCreated : Set AccountAddress} {fuel cap : Nat} {pre post : EVM.State}
    {out : ByteArray} {v : View} (observed : Successful (kind := kind) parent fuel pre post out v)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (w : Warm) (warm : WarmRelated w pre) (created_eq : v.storage.created = initialCreated)
    (threshold : RuntimeMemoryFunding.energy pre < cost (cap+1)) :
    SuccessCertificate kind parent initialCreated fuel cap pre post out v w := by
  obtain ⟨t,finish,viewed,related,decoded,terminal⟩ := observed
  obtain ⟨finalWarm,prefixEvents,coupled,finalWarmRel,finalCreated⟩ := from_viewed viewed hat w warm created_eq
  have he := success_cost related terminal
  have hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt t.exit).1 t.exit = .ok (t.mid,t.cost) := by
    rw [t.decode]; exact t.charge
  have hs : StepOk (t.rem+1-1) t.cost (decodeAt t.exit) t.mid post := by
    rw [t.decode]; simpa only [Nat.add_sub_cancel] using t.step
  exact ⟨t,finish,finalWarm,prefixEvents,coupled,related,finalWarmRel,finalCreated,decoded,terminal,he,
    through_terminal coupled hat hz hs threshold he⟩

/-- Internal reverted writes/logs remain observations of the cancelled frame.
The resource certificate charges REVERT's memory expansion; it does not commit
the frame's journal or identify it with the enclosing restored journal. -/
def RevertCertificate (kind : Kind) (parent : ReferenceStorageView.Parent)
    (initialCreated : Set AccountAddress) (fuel cap : Nat) (pre : EVM.State)
    (gas : UInt256) (out : ByteArray) (v : View) (w : Warm) : Prop :=
    ∃ t : RuntimeRevertTrace.RevertTrace (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre gas out,
      ∃ finish finalWarm prefixEvents off len rest,
        Coupled kind parent initialCreated fuel pre v w t.trace (t.rem+1) t.exit finish finalWarm prefixEvents ∧
        Related parent finish t.exit ∧ WarmRelated finalWarm t.exit ∧
        finish.storage.created = initialCreated ∧
        decodeAt t.exit = (ReferenceDecodeSites.referenceDecode finish.env.code finish.pc).getD (.STOP,none) ∧
        finish.stack = off::len::rest ∧ ReferenceReturnView.Result parent finish off len rest t.post ∧
        out = (ReferenceReturnView.returnMemory finish off len).extract off.toNat (off.toNat+len.toNat) ∧
        terminalCost .REVERT finish = cost t.post.activeWords.toNat-cost t.exit.activeWords.toNat ∧
        PaymentFor cap t.trace prefixEvents (terminalCost .REVERT finish)

theorem revert {kind : Kind} {parent : ReferenceStorageView.Parent}
    {initialCreated : Set AccountAddress} {fuel cap : Nat} {pre : EVM.State}
    {gas : UInt256} {out : ByteArray} {v : View}
    (observed : Reverted (kind := kind) parent fuel pre gas out v)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (w : Warm) (warm : WarmRelated w pre) (created_eq : v.storage.created = initialCreated)
    (threshold : RuntimeMemoryFunding.energy pre < cost (cap+1)) :
    RevertCertificate kind parent initialCreated fuel cap pre gas out v w := by
  obtain ⟨t,finish,off,len,rest,viewed,related,decoded,shape,result,output⟩ := observed
  obtain ⟨finalWarm,prefixEvents,coupled,finalWarmRel,finalCreated⟩ := from_viewed viewed hat w warm created_eq
  have he := revert_cost related shape result
  have hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt t.exit).1 t.exit = .ok (t.mid,t.cost) := by
    rw [t.decode]; exact t.charge
  have hs : StepOk (t.rem+1-1) t.cost (decodeAt t.exit) t.mid t.post := by
    rw [t.decode]; simpa only [Nat.add_sub_cancel] using t.step
  exact ⟨t,finish,finalWarm,prefixEvents,off,len,rest,coupled,related,finalWarmRel,finalCreated,
    decoded,shape,result,output,he,through_terminal coupled hat hz hs threshold he⟩

#print axioms success_cost
#print axioms revert_cost
#print axioms success
#print axioms revert
end Eip8282.Audit.Integrator.ReferenceRuntimeTerminalPayment
