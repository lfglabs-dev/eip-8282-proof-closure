import Eip8282.Audit.Integrator.CodeStorageFrame
import Eip8282.Audit.Integrator.RuntimeCodePreservation
import Eip8282.Audit.Integrator.ConcreteHistory
import Eip8282.Audit.Integrator.InitializerProgress

/-!
# Invariant transport for actual protected calls and journal restoration

The world projection combines installed code with the proved queue/control
invariants. Its transition producers use actual opcode/Theta receipts; rollback
retains a monotone execution budget. This algebra does not itself extract a
complete protocol call history or prove exclusion from transaction deletion
sets. Those producers must retain exact trace/checkpoint and budget linkage.
-/
namespace Eip8282.Audit.Integrator.JournalInvariant
open EvmYul EvmYul.EVM
open ReachableCalls (Contract Transition address runtime)
open SystemSpec
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

def modelKind : Contract → Eip8282.Audit.Model.Kind
  | .deposit => .deposit
  | .exit => .exit

def CodeAt (kind : Contract) (world : AccountMap .EVM) : Prop :=
  ∃ account, world.get? (address kind) = some account ∧ account.code = runtime kind

def Invariant (kind : Contract) (budget : Nat) (world : AccountMap .EVM) : Prop :=
  CodeAt kind world ∧ ConcreteHistory.Invariant kind budget world

/-- Restoring an earlier world does not refund already executed append work. -/
theorem mono {kind : Contract} {world : AccountMap .EVM} {before after : Nat}
    (h : Invariant kind before world) (hle : before ≤ after) : Invariant kind after world := by
  refine ⟨h.1,?_⟩
  obtain ⟨_,hi⟩ := h
  cases kind with
  | deposit =>
    obtain ⟨hb,hs,queue,hq⟩ := hi
    exact ⟨AccountedState.mono hb hle,hs,queue,hq⟩
  | exit =>
    obtain ⟨hb,hs,queue,hq,hw⟩ := hi
    exact ⟨AccountedState.mono hb hle,hs,queue,hq,hw⟩

theorem code_frame {kind : Contract} {before after : AccountMap .EVM}
    (hc : CodeAt kind before) (hf : CodeStorageFrame.Frame before after (address kind)) :
    CodeAt kind after := by
  obtain ⟨old,ho,hcode⟩ := hc
  obtain ⟨current,hc,hcc⟩ := hf.existing old ho
  exact ⟨current,hc,hcc.trans hcode⟩

/-- Extensional persistent-slot equality transports the physical queue as well
as the scalar controls; no abstract queue postcondition is supplied. -/
theorem frame {kind : Contract} {before after : AccountMap .EVM} {budget : Nat}
    (hi : Invariant kind budget before)
    (hf : CodeStorageFrame.Frame before after (address kind)) :
    Invariant kind budget after := by
  refine ⟨code_frame hi.1 hf,?_⟩
  have hs : worldSlot after (address kind) = worldSlot before (address kind) := funext hf.storage
  cases kind <;> simp only [ConcreteHistory.Invariant, hs] <;> exact hi.2

/-- The exact value-transfer entry is a frame even when caller=target. -/
theorem entry (c : MessageCall.Context) {kind : Contract} {budget : Nat}
    (hi : Invariant kind budget c.world) : Invariant kind budget c.entryWorld :=
  frame hi (CodeStorageFrame.entry c (address kind))

/-- Storage and code are composed on the very same actual protected Θ receipt.
The independent calldata/funding and global execution-budget inputs remain
visible until the full-history producer instantiates them. -/
theorem protected_call {kind : Contract} {before after : AccountMap .EVM}
    (t : Transition kind before after) (ha : ConcreteHistory.Allowed t.call)
    {budget : Nat} (hb : budget < 2^128) (hi : Invariant kind budget before) :
    Invariant kind (budget + ConcreteHistory.weight t.call t.success) after := by
  refine ⟨?_,ConcreteHistory.transition_preserves t ha budget hb hi.2⟩
  obtain ⟨old,ho,hcode⟩ := hi.1
  have hold : t.call.world.get? t.call.target = some old := by
    rw [t.pre,t.pinned.target]
    exact ho
  have hp : t.call.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
    cases kind <;> exact t.pinned.code
  obtain ⟨current,hc,hcc⟩ := RuntimeCodePreservation.theta_existing_code t.call hp hold t.executed
  rw [t.pinned.target] at hc
  exact ⟨current,hc,hcc.trans hcode⟩

/-- A returned failure restores the actual world checkpoint. `spent` is a
monotone accounting extension, not a claimed extraction of its elapsed work. -/
theorem failed_call (c : MessageCall.Context) {kind : Contract} {budget : Nat}
    (hi : Invariant kind budget c.world) (spent : Nat)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hr : c.result = .ok (created,world,gas,substate,false,out)) :
    Invariant kind (budget+spent) world := by
  obtain ⟨hw,_,_⟩ := MessageCall.failure_restores_journal c created world gas substate out hr
  rw [hw]
  exact mono hi (Nat.le_add_right _ _)

/-- The exact successful initializer's observations supply the full initial
world projection at the canonical address. Address identity is an explicit
binding; it is not inferred from a parameter name. -/
theorem of_initialized (kind : Contract) (c : CreationSettlement.Context) (preimage : ByteArray)
    {a : AccountAddress} {world : AccountMap .EVM} {substate : Substate}
    (hc : a = address kind)
    (h : DirectInitialization.Observed (modelKind kind) c preimage a world substate) :
    Invariant kind 0 world := by
  obtain ⟨_,hcode,_,hb,hs,hq,_⟩ := h
  rw [hc] at hcode hb hs hq
  cases kind with
  | deposit => exact ⟨hcode,hb,hs,[],hq⟩
  | exit => exact ⟨hcode,hb,hs,[],hq,QueueInvariant.source_width_empty⟩

/-- Actual code-deposit success and the initial journal invariant are composed.
The current initializer Domain still includes absent-target/resource inputs;
canonical deployment/admission and admissible prefunding generalization remain
separate obligations, rather than assumptions hidden in this conclusion. -/
theorem initializes (kind : Contract) (c : CreationSettlement.Context)
    (preimage : ByteArray) (steps : Nat)
    (hi : c.init = Initialization.initCode (modelKind kind))
    (hd : DirectInitialization.Domain (modelKind kind) c preimage steps)
    (hg : InitializerProgress.creationGas (modelKind kind) ≤ c.gas.toNat)
    (hc : CreationSettlement.address preimage = address kind) :
    ∃ created world gas substate,
      c.result = .ok (CreationSettlement.address preimage,created,world,gas,substate,true,ByteArray.empty) ∧
      Invariant kind 0 world := by
  obtain ⟨created,world,gas,substate,hr,ho⟩ :=
    InitializerProgress.initializes_success (modelKind kind) c preimage steps hi hd hg
  exact ⟨created,world,gas,substate,hr,of_initialized kind c preimage hc ho⟩

#print axioms mono
#print axioms frame
#print axioms protected_call
#print axioms failed_call
#print axioms of_initialized
#print axioms initializes
end Eip8282.Audit.Integrator.JournalInvariant
