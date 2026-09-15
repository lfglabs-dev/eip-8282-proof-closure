import Eip8282.Audit.Integrator.Topics.ReferenceRuntime
import Eip8282.Audit.Integrator.Topics.Reference
import Eip8282.Audit.Integrator.Topics.Reference4
import Eip8282.Audit.Integrator.Topics.Runtime

/-! Complete actual runtime successes and REVERTs supply their source-shaped
views and terminal observations. Memory capacities are derived from initial
gas plus memory energy, not assumed about the hidden terminal state. The
resource threshold/host bound are explicit environment inputs, not an adopted
Ethereum gas limit. User payment and enclosing source rollback remain separate. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeCompletion
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceRuntimeTrace
open RuntimeMemoryFunding (energy)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem view_decode {kind : Kind} {parent : ReferenceStorageView.Parent}
    {pre : EVM.State} {v : View}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (related : Related parent v pre) :
    decodeAt pre = (ReferenceDecodeSites.referenceDecode v.env.code v.pc).getD (.STOP,none) := by
  rw [related.env,related.pc,hat.1,ReferenceRuntimeSites.code_eq]
  exact ReferenceAllDecode.decode_matches hat

inductive SuccessEnd (parent : ReferenceStorageView.Parent) (v : View)
    (post : EVM.State) (out : ByteArray) : Operation .EVM → Prop where
  | stopped : Related parent v post → out = ByteArray.empty → SuccessEnd parent v post out .STOP
  | returned {off len : UInt256} {rest : Stack UInt256} :
      v.stack = off::len::rest → ReferenceReturnView.Result parent v off len rest post →
      out = (ReferenceReturnView.returnMemory v off len).extract off.toNat (off.toNat+len.toNat) →
      SuccessEnd parent v post out .RETURN

def Successful {kind : Kind} (parent : ReferenceStorageView.Parent) (fuel : Nat)
    (pre post : EVM.State) (out : ByteArray) (initial : View) : Prop :=
  ∃ t : SuccessInversion.SuccessTrace (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre post out,
    ∃ finish,
      Viewed kind parent fuel pre initial t.trace (t.rem+1) t.exit finish ∧
      Related parent finish t.exit ∧
      decodeAt t.exit = (ReferenceDecodeSites.referenceDecode finish.env.code finish.pc).getD (.STOP,none) ∧
      SuccessEnd parent finish post out t.op

def Reverted {kind : Kind} (parent : ReferenceStorageView.Parent) (fuel : Nat)
    (pre : EVM.State) (gas : UInt256) (out : ByteArray) (initial : View) : Prop :=
  ∃ t : RuntimeRevertTrace.RevertTrace (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre gas out,
    ∃ finish off len rest,
      Viewed kind parent fuel pre initial t.trace (t.rem+1) t.exit finish ∧
      Related parent finish t.exit ∧
      decodeAt t.exit = (ReferenceDecodeSites.referenceDecode finish.env.code finish.pc).getD (.STOP,none) ∧
      finish.stack = off::len::rest ∧ ReferenceReturnView.Result parent finish off len rest t.post ∧
      out = (ReferenceReturnView.returnMemory finish off len).extract off.toNat (off.toNat+len.toNat)

private theorem terminal_caps {kind : Kind} {fuel rem gasCost cap : Nat}
    {pre exit mid post : EVM.State} {trace : List Labelled}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hr : XRuns (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre trace rem exit)
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt exit).1 exit = .ok (mid,gasCost))
    (hs : StepOk (rem-1) gasCost (decodeAt exit) mid post)
    (threshold : energy pre < ReferenceMemoryCapacity.cost (cap+1)) :
    RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) exit ∧
      exit.activeWords.toNat ≤ cap ∧ post.activeWords.toNat ≤ cap := by
  have hatExit := (RuntimeMemoryMonotone.runs hat hr).1
  have he := RuntimeMemoryFunding.runs_energy hat hr
  have hp := (RuntimeMemoryFunding.accepted_energy hatExit hz hs).trans he
  have ec : ReferenceMemoryCapacity.cost exit.activeWords.toNat ≤ energy pre := by
    unfold energy at he
    unfold energy
    omega
  have pc : ReferenceMemoryCapacity.cost post.activeWords.toNat ≤ energy pre := by
    unfold energy at hp
    unfold energy
    omega
  exact ⟨hatExit,RuntimeMemoryFunding.capacity_of_energy ec threshold,
    RuntimeMemoryFunding.capacity_of_energy pc threshold⟩

theorem success {kind : Kind} {parent : ReferenceStorageView.Parent} {fuel cap : Nat}
    {pre post : EVM.State} {out : ByteArray}
    (actual : X fuel (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) pre = .ok (.success post out))
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (initial : View) (related : Related parent initial pre)
    (cdfit : initial.env.calldata.size < UInt256.size)
    (threshold : energy pre < ReferenceMemoryCapacity.cost (cap+1))
    (host : 32*cap < 2^System.Platform.numBits) :
    Successful (kind := kind) parent fuel pre post out initial := by
  obtain ⟨t⟩ := SuccessInversion.success_trace actual
  have hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt t.exit).1 t.exit = .ok (t.mid,t.cost) := by
    rw [t.decode]; exact t.charge
  have hs : StepOk (t.rem+1-1) t.cost (decodeAt t.exit) t.mid post := by
    rw [t.decode]; simpa only [Nat.add_sub_cancel] using t.step
  obtain ⟨hatExit,hcapExit,hcapPost⟩ := terminal_caps hat t.run.toXRuns hz hs threshold
  obtain ⟨finish,hview,hrel⟩ := from_runs t.run.toXRuns hat initial related cdfit hcapExit host
  have hdecode : decodeAt t.exit = (ReferenceDecodeSites.referenceDecode finish.env.code finish.pc).getD (.STOP,none) := by
    exact view_decode hatExit hrel
  refine ⟨t,finish,hview,hrel,hdecode,?_⟩
  have ha := RuntimeExecutionScope.opcode_allowed hatExit
  rw [t.decode] at ha
  have allowed_halt : ∀ op ∈ RuntimeOpcodeScope.allowedOps, Halting op = true →
      op = .STOP ∨ op = .RETURN ∨ op = .REVERT := by decide +kernel
  rcases allowed_halt t.op ha (halting_of_H_eq_some t.output) with hop | hop | hop
  · have hd := ReferenceDecodeShape.fixed t.exit .STOP (by rw [t.decode,hop]) rfl
    have hz' : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) .STOP t.exit = .ok (t.mid,t.cost) := by
      simpa only [hd] using hz
    have hs' : StepOk t.rem t.cost (.STOP,none) t.mid post := by simpa only [hd,Nat.add_sub_cancel] using hs
    cases hf : t.rem with
    | zero => rw [hf] at hs'; cases hs'
    | succ f =>
      rw [hf] at hs'
      obtain ⟨hr,ho⟩ := ReferenceStopView.terminal hz' hs' hrel
      have outEmpty : out = ByteArray.empty := by
        have hh := t.output
        rw [hop,ho] at hh
        exact (Option.some.inj hh).symm
      rw [hop]
      exact .stopped hr outEmpty
  · have hd := ReferenceDecodeShape.fixed t.exit .RETURN (by rw [t.decode,hop]) rfl
    have hz' : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) .RETURN t.exit = .ok (t.mid,t.cost) := by
      simpa only [hd] using hz
    have hs' : StepOk t.rem t.cost (.RETURN,none) t.mid post := by simpa only [hd,Nat.add_sub_cancel] using hs
    have hh : H post.toMachineState .RETURN = some out := by simpa only [hop] using t.output
    cases hf : t.rem with
    | zero => rw [hf] at hs'; cases hs'
    | succ f =>
      rw [hf] at hs'
      obtain ⟨off,len,rest,_,hshape,hr,hout⟩ := ReferenceReturnView.halted hz' hs' hrel hcapPost host hh
      rw [hop]
      exact .returned hshape hr (hout.trans (ReferenceReturnSlice.output_eq_extract hrel off len))
  · exact False.elim (t.not_revert hop)

theorem revert {kind : Kind} {parent : ReferenceStorageView.Parent} {fuel cap : Nat}
    {pre : EVM.State} {gas : UInt256} {out : ByteArray}
    (actual : X fuel (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) pre = .ok (.revert gas out))
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (initial : View) (related : Related parent initial pre)
    (cdfit : initial.env.calldata.size < UInt256.size)
    (threshold : energy pre < ReferenceMemoryCapacity.cost (cap+1))
    (host : 32*cap < 2^System.Platform.numBits) :
    Reverted (kind := kind) parent fuel pre gas out initial := by
  obtain ⟨t⟩ := RuntimeRevertTrace.revert_trace actual
  have hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt t.exit).1 t.exit = .ok (t.mid,t.cost) := by
    rw [t.decode]; exact t.charge
  have hs : StepOk (t.rem+1-1) t.cost (decodeAt t.exit) t.mid t.post := by
    rw [t.decode]; simpa only [Nat.add_sub_cancel] using t.step
  obtain ⟨hatExit,hcapExit,hcapPost⟩ := terminal_caps hat t.run hz hs threshold
  obtain ⟨finish,hview,hrel⟩ := from_runs t.run hat initial related cdfit hcapExit host
  have hdecode : decodeAt t.exit = (ReferenceDecodeSites.referenceDecode finish.env.code finish.pc).getD (.STOP,none) := by
    exact view_decode hatExit hrel
  have hstep := t.step
  cases hf : t.rem with
  | zero => rw [hf] at hstep; cases hstep
  | succ f =>
    rw [hf] at hstep
    obtain ⟨off,len,rest,_,hshape,hr,_,hout⟩ :=
      ReferenceRevertView.halted t.charge hstep hrel hcapPost host t.output
    exact ⟨t,finish,off,len,rest,hview,hrel,hdecode,hshape,hr,hout⟩

#print axioms success
#print axioms revert
end Eip8282.Audit.Integrator.ReferenceRuntimeCompletion
