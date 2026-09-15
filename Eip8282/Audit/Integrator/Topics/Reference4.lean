import Eip8282.Audit.Integrator.Topics.Reference
import Eip8282.Audit.Integrator.Topics.ReferenceCall2
import Eip8282.Audit.Integrator.Topics.ReferenceMeter2
import Eip8282.Audit.Integrator.ReferenceOrdinaryGas
import Eip8282.Audit.Integrator.ReferenceReturnSlice
import Eip8282.Audit.Integrator.Topics.ReferenceRuntime3
import Eip8282.Audit.Integrator.Topics.ReferenceSystem
import Eip8282.Audit.Integrator.RuntimeMemoryCharges
import Eip8282.Audit.Integrator.SystemMeterResources

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceActionMetadata -/

/-! Source transaction metadata carried by literal input-computed actions.
Pure actions retain the entire storage view. Storage reads/writes change only
read/write overlays, so every SYSTEM action preserves the source created set.
No equality with pinned createdAccounts or warm/BAL sets is inferred. -/
namespace Eip8282.Audit.Integrator.ReferenceActionMetadata
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferencePureAction ReferenceSystemAction
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private theorem family_storage (kind : Kind) (p : Pure) (arg : Option (UInt256 × Nat))
    (v next : View) (h : familyAction kind p arg v = some next) :
    next.storage = v.storage := by
  unfold familyAction at h
  repeat' first | split at h | (cases h <;> rfl)

/-- Every successful partial pure action changes only PC and stack. -/
theorem pure_storage {kind : Kind} {instr : Instruction} {v next : View}
    (h : ReferencePureAction.action kind instr v = some next) :
    next.storage = v.storage := by
  unfold ReferencePureAction.action at h
  cases hc : classify instr.1 with
  | none => simp only [hc,Option.bind_none] at h; cases h
  | some p =>
    simp only [hc,Option.bind_some] at h
    exact family_storage kind p instr.2 v next h

/-- In particular pure instructions neither add nor discard BAL reads. -/
theorem pure_reads {kind : Kind} {instr : Instruction} {v next : View}
    (h : ReferencePureAction.action kind instr v = some next) :
    next.storage.reads = v.storage.reads := congrArg ReferenceStorageView.Tx.reads (pure_storage h)

/-- Created metadata comes from the initial source transaction and remains
unchanged along all literal SYSTEM actions, including SLOAD and SSTORE. -/
theorem created {kind : Kind} {parent : ReferenceStorageView.Parent}
    {instr : Instruction} {v next : View} (h : Action kind parent instr v next) :
    next.storage.created = v.storage.created := by
  cases h with
  | pure hp => exact congrArg ReferenceStorageView.Tx.created (pure_storage hp)
  | load => rfl
  | store => rfl
  | word => rfl
  | byte => rfl

#print axioms pure_storage
#print axioms pure_reads
#print axioms created
end Eip8282.Audit.Integrator.ReferenceActionMetadata

end

section

/-! ## ReferenceCopyLogGas -/

/-! Literal source execution components for runtime COPY and LOG0.
EL0cc100eb190b64b23baba72dac0165652eaec252, durable archives
 audit/receipts/direct-reference-memory-control-sources-20260910.json and
 audit/receipts/direct-reference-checked-types-sources-20260910.json:
environment.py SHA8c57bd699b99ff8b4d8e41e6a9c89cd1a03dda8160bf1d6dffe091932ec03657;
gas.py SHA41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c;
log.py SHAf62f6cb589811e3a58c3a4644fcf7b979a506df1f09213e2a96e7988a4574874.
COPY uses base3 plus3*(ceil32(size)//32); LOG0 uses375+8*size.
LOG0 charges and expands before its source static guard. These are successful
source-formula prices, not source gas/exception-order or Python execution parity.
-/
namespace Eip8282.Audit.Integrator.ReferenceCopyLogGas
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000

def sourceCeil32 (n : Nat) : Nat := if n%32 = 0 then n else n+32-n%32

theorem ceil_words (n : Nat) : sourceCeil32 n / 32 = (n+31)/32 := by
  unfold sourceCeil32
  split <;> omega

def copyCost (len : Nat) : Nat := 3+3*((len+31)/32)
def logCost (len : Nat) : Nat := 375+8*len

theorem copy_source (len : Nat) : copyCost len = 3+3*(sourceCeil32 len/32) := by
  rw [ceil_words]
  rfl

/-- get! totalizes this table; actual admission recovers real operands below.
Source offsets never enter the per-word copy execution price. -/
def ordinaryCost (op : Operation .EVM) (warm : Bool) (stack : Stack UInt256) : Option Nat :=
  if op = .CALLDATACOPY then some (copyCost stack[2]!.toNat)
  else if op = .LOG0 then some (logCost stack[1]!.toNat)
  else ReferenceOrdinaryGas.ordinaryCost op warm

theorem defined {op : Operation .EVM} (warm : Bool) (stack : Stack UInt256)
    (allowed : op ∈ RuntimeOpcodeScope.allowedOps) (notStore : op ≠ .SSTORE) :
    ∃ n, ordinaryCost op warm stack = some n := by
  by_cases hc : op = .CALLDATACOPY
  · subst op; exact ⟨_,rfl⟩
  · by_cases hl : op = .LOG0
    · subst op; exact ⟨_,rfl⟩
    · obtain ⟨n,hn,_⟩ := ReferenceOrdinaryGas.defined_bound warm ⟨allowed,hl,hc⟩ notStore
      exact ⟨n,by simp only [ordinaryCost,if_neg hc,if_neg hl]; exact hn⟩

theorem accepted_copy {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    (hz : Z vj .CALLDATACOPY pre = .ok (mid,cost)) (warm : Bool) :
    ∃ rest dest source len, pre.stack.pop3 = some (rest,dest,source,len) ∧
      pre.stack = dest::source::len::rest ∧
      ordinaryCost .CALLDATACOPY warm pre.stack = some (copyCost len.toNat) := by
  obtain ⟨rest,dest,source,len,shape,pop⟩ := ReferenceAcceptedStack.pop3 hz (by decide)
  exact ⟨rest,dest,source,len,pop,shape,by rw [shape]; rfl⟩

theorem accepted_log {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    (hz : Z vj .LOG0 pre = .ok (mid,cost)) (warm : Bool) :
    ∃ rest off len, pre.stack.pop2 = some (rest,off,len) ∧ pre.stack = off::len::rest ∧
      ordinaryCost .LOG0 warm pre.stack = some (logCost len.toNat) := by
  obtain ⟨rest,off,len,shape,pop⟩ := ReferenceAcceptedStack.pop2 hz (by decide)
  exact ⟨rest,off,len,pop,shape,by rw [shape]; rfl⟩

theorem related_cost {parent : ReferenceStorageView.Parent} {v : View} {pre : EVM.State}
    (related : Related parent v pre) (op : Operation .EVM) (warm : Bool) :
    ordinaryCost op warm v.stack = ordinaryCost op warm pre.stack := by rw [related.stack]

def eventCost (op : Operation .EVM) (warm : Bool) (v next : View) : Option Nat :=
  (ordinaryCost op warm v.stack).map (fun n => n+
    (ReferenceMemoryCapacity.cost (words next)-ReferenceMemoryCapacity.cost (words v)))

/-- Same actual endpoints transport the memory component; it is added once. -/
theorem related_event {parent : ReferenceStorageView.Parent} {v next : View} {pre post : EVM.State}
    (related : Related parent v pre) (nextRelated : Related parent next post)
    (op : Operation .EVM) (warm : Bool) :
    eventCost op warm v next = (ordinaryCost op warm pre.stack).map
      (fun n => n+SystemMeterResources.delta pre post) := by
  unfold eventCost SystemMeterResources.delta
  rw [related.stack,words_related related,words_related nextRelated]

theorem charge {op : Operation .EVM} {warm : Bool} {v next : View} {amount : Nat}
    (_computed : eventCost op warm v next = some amount) (meter : ReferenceStorageGas.Meter)
    (funded : amount ≤ meter.execution) :
    ∃ final, ReferenceStorageGas.chargeExecution meter amount = some final ∧
      final.execution = meter.execution-amount ∧ final.reservoir = meter.reservoir := by
  unfold ReferenceStorageGas.chargeExecution
  rw [if_pos funded]
  exact ⟨_,rfl,rfl,rfl⟩

#print axioms ceil_words
#print axioms copy_source
#print axioms defined
#print axioms accepted_copy
#print axioms accepted_log
#print axioms related_cost
#print axioms related_event
#print axioms charge
end Eip8282.Audit.Integrator.ReferenceCopyLogGas

end

section

/-! ## ReferenceLogView -/

/-! Actual accepted LOG0 and its literal source-shaped effect. Pinned EL0cc
instructions/log.py pops, charges, extends memory, checks static mode, appends
one log and advances PC. This successful-step adapter derives permission from
actual admission; it does not equate exceptional intermediate ordering or use
the SYSTEM payment theorem (whose actual traces contain no LOG0). -/
namespace Eip8282.Audit.Integrator.ReferenceLogView
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def entry (v : View) (off len : UInt256) : LogEntry :=
  ⟨v.env.codeOwner,#[],ReferenceReturnView.output v off len⟩

def logAction (v : View) (off len : UInt256) (rest : Stack UInt256) : View :=
  {v with
    pc := v.pc+1
    stack := rest
    memory := ReferenceReturnView.returnMemory v off len
    logs := v.logs++[entry v off len]}

private theorem permission {vj : Array UInt256} {pre mid : EVM.State} {gasCost : Nat}
    (hz : Z vj .LOG0 pre = .ok (mid,gasCost)) : pre.executionEnv.perm = true := by
  simp only [Z,Bind.bind,Except.bind,pure,Except.pure] at hz
  iterate 8 replace hz := elim_guard hz
  have hn := elim_guard_not hz
  cases hp : pre.executionEnv.perm <;> simp [hp,W] at hn ⊢

private theorem expanded {parent : ReferenceStorageView.Parent} {v : View}
    {pre post : EVM.State} {off len : UInt256} (related : Related parent v pre)
    (hmem : post.memory = pre.memory)
    (hex : post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat len.toNat) :
    ReferenceMemoryOperations.Related post.toMachineState (ReferenceReturnView.returnMemory v off len) := by
  have hb := (ReferenceMemoryCapacity.expansion_bounds pre.activeWords.toNat off.toNat len.toNat).1
  have hsize : v.memory.size ≤ 32*MachineState.M (words v) off.toNat len.toNat := by
    rw [related.memory.size,words_related related]
    omega
  have hext := ReferenceMemoryOperations.extend_same v.memory
    (32*MachineState.M (words v) off.toNat len.toNat) hsize
  refine ⟨?_,?_,?_⟩
  · change post.memory.size ≤ 32*post.activeWords.toNat
    rw [hmem,hex]
    have hc := related.memory.coherent
    change pre.memory.size ≤ 32*pre.activeWords.toNat at hc
    omega
  · rw [ReferenceReturnView.returnMemory,ReferenceMemoryOperations.extend,ReferenceMemoryView.buffer_size,
      words_related related,hex]
  · rw [hmem]
    intro i
    exact (related.memory.bytes i).trans (hext i)

theorem data_slice {parent : ReferenceStorageView.Parent} {v : View} {pre : EVM.State}
    (related : Related parent v pre) (off len : UInt256) :
    (entry v off len).data = (ReferenceReturnView.returnMemory v off len).extract
      off.toNat (off.toNat+len.toNat) :=
  ReferenceReturnSlice.output_eq_extract related off len

theorem accepted {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel gasCost cap : Nat}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (decoded : decodeAt pre = (.LOG0,none))
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (decodeAt pre) mid post)
    (related : Related parent v pre)
    (capacity : post.activeWords.toNat ≤ cap) (host : 32*cap < 2^System.Platform.numBits) :
    ∃ off len rest, pre.stack.pop2 = some (rest,off,len) ∧ v.stack = off::len::rest ∧
      v.env.perm = true ∧ Related parent (logAction v off len rest) post := by
  have hex := RuntimeMemoryCharges.accepted_expansion hat hz hs
  rw [decoded] at hz hs hex
  obtain ⟨rest,off,len,hshape,hpop⟩ := ReferenceAcceptedStack.pop2 hz (by decide)
  have hp : v.env.perm = true := by rw [related.env]; exact permission hz
  change post.activeWords.toNat = MachineState.M pre.activeWords.toNat
    pre.stack[0]!.toNat pre.stack[1]!.toNat at hex
  rw [hshape] at hex
  change post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat len.toNat at hex
  have hlen : len.toNat < 2^System.Platform.numBits := by
    by_cases hzlen : len.toNat = 0
    · have hh : 0 < 2^System.Platform.numBits := by positivity
      omega
    · have hb := (ReferenceMemoryCapacity.expansion_bounds pre.activeWords.toNat off.toNat len.toNat).2 (by omega)
      rw [← hex] at hb
      omega
  have h64 : len.toNat < 2^64 := by
    rcases System.Platform.numBits_eq with hn | hn <;> rw [hn] at hlen <;> omega
  have hbytes : pre.memory.readWithPadding off.toNat len.toNat = ReferenceReturnView.output v off len := by
    rw [ReferenceMemoryView.read_eq_buffer _ _ _ h64 hlen]
    exact ReferenceMemoryView.buffer_congr _ _ related.memory.bytes _ _
  have fit : pre.pc.toNat+1 < UInt256.size := by
    have := ReferenceRuntimeSites.pc_fit hat
    omega
  obtain rfl := Z_ok_state hz
  change EVM.step (fuel+1) gasCost (some (.LOG0,none)) (zMid pre .LOG0) = .ok post at hs
  rw [OrdinaryGas.dispatch (by decide)] at hs
  have known := step_LOG0 (s := stepPre gasCost (zMid pre .LOG0)) hshape
  have same := Except.ok.inj (hs.symm.trans known)
  subst post
  refine ⟨off,len,rest,hpop,related.stack.trans hshape,hp,?_⟩
  refine ⟨related.env,?_,rfl,expanded related rfl hex,related.storage,?_,related.owner⟩
  · change v.pc+1 = (pre.pc+UInt256.ofNat 1).toNat
    rw [related.pc,toNat_add_of_lt _ _ fit]
    rfl
  · change v.logs++[entry v off len] = ProtectedLogFrame.project pre.executionEnv.codeOwner
      {pre.substate with
        logSeries := pre.substate.logSeries.push ⟨pre.executionEnv.codeOwner,#[],pre.memory.readWithPadding off.toNat len.toNat⟩}
    rw [ProtectedLogFrame.push_self pre.executionEnv.codeOwner pre.substate
      ⟨pre.executionEnv.codeOwner,#[],pre.memory.readWithPadding off.toNat len.toNat⟩ rfl,
      ← related.logs,hbytes]
    rw [entry,related.env]

#print axioms data_slice
#print axioms accepted
end Eip8282.Audit.Integrator.ReferenceLogView

end

section

/-! ## ReferenceCopyLogReverse -/

/-! Reverse raw COPY/LOG0 effects from actual input operands, with a host bound
on computed memory expansion. No successful old step or post-state is assumed.
Source charging order and failed/static executions require separate extraction. -/
namespace Eip8282.Audit.Integrator.ReferenceCopyLogReverse
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceLogView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private theorem expanded {parent : ReferenceStorageView.Parent} {v : View}
    {pre post : EVM.State} {off len : UInt256} (related : Related parent v pre)
    (hmem : post.memory = pre.memory)
    (hex : post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat len.toNat) :
    ReferenceMemoryOperations.Related post.toMachineState (ReferenceReturnView.returnMemory v off len) := by
  have hb := (ReferenceMemoryCapacity.expansion_bounds pre.activeWords.toNat off.toNat len.toNat).1
  have hsize : v.memory.size ≤ 32*MachineState.M (words v) off.toNat len.toNat := by
    rw [related.memory.size,words_related related]
    omega
  have hext := ReferenceMemoryOperations.extend_same v.memory
    (32*MachineState.M (words v) off.toNat len.toNat) hsize
  refine ⟨?_,?_,?_⟩
  · change post.memory.size ≤ 32*post.activeWords.toNat
    rw [hmem,hex]
    have hc := related.memory.coherent
    change pre.memory.size ≤ 32*pre.activeWords.toNat at hc
    omega
  · rw [ReferenceReturnView.returnMemory,ReferenceMemoryOperations.extend,ReferenceMemoryView.buffer_size,
      words_related related,hex]
  · rw [hmem]
    intro i
    exact (related.memory.bytes i).trans (hext i)

theorem copy {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre : EVM.State} {dest source len : UInt256} {rest : Stack UInt256}
    (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (shape : v.stack = dest::source::len::rest)
    (host : 32*MachineState.M (words v) dest.toNat len.toNat < 2^System.Platform.numBits) :
    ∃ post, EvmYul.step (τ := .EVM) .CALLDATACOPY none pre = .ok post ∧
      Related parent (ReferenceCalldataCopy.copyAction v dest source len rest) post := by
  have stack : pre.stack = dest::source::len::rest := related.stack.symm.trans shape
  let post := ({pre with toSharedState := pre.toSharedState.calldatacopy dest source len} : EVM.State).replaceStackAndIncrPC rest
  have fit : pre.pc.toNat+1 < UInt256.size := by
    have := ReferenceRuntimeSites.pc_fit site
    omega
  have hhost : 32*MachineState.M pre.activeWords.toNat dest.toNat len.toNat < 2^System.Platform.numBits := by
    simpa only [words_related related] using host
  have hm := ReferenceCopyMemory.copy_related pre.toMachineState v.memory pre.executionEnv.calldata
    dest source len related.memory _ (Nat.le_refl _) hhost
  refine ⟨post,step_CALLDATACOPY stack,related.env,?_,rfl,?_,related.storage,related.logs,related.owner⟩
  · change v.pc+1 = (pre.pc+UInt256.ofNat 1).toNat
    rw [related.pc,toNat_add_of_lt _ _ fit]
    rfl
  · change ReferenceMemoryOperations.Related _ (ReferenceCopyMemory.copyMemory v.memory v.env.calldata
      dest.toNat source.toNat len.toNat (32*MachineState.M (words v) dest.toNat len.toNat))
    rw [related.env,words_related related]
    exact hm

theorem log {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre : EVM.State} {off len : UInt256} {rest : Stack UInt256}
    (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (shape : v.stack = off::len::rest)
    (host : 32*MachineState.M (words v) off.toNat len.toNat < 2^System.Platform.numBits) :
    ∃ post, EvmYul.step (τ := .EVM) .LOG0 none pre = .ok post ∧
      Related parent (logAction v off len rest) post := by
  have stack : pre.stack = off::len::rest := related.stack.symm.trans shape
  let post := ({pre with toSharedState := SharedState.logOp off len #[] pre.toSharedState} : EVM.State).replaceStackAndIncrPC rest
  have raw := step_LOG0 stack
  have hex : post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat len.toNat :=
    toNat_ofNat_lit _ (RuntimeMemoryMonotone.expansion_fit pre.activeWords off len)
  have hhost : 32*MachineState.M pre.activeWords.toNat off.toNat len.toNat < 2^System.Platform.numBits := by
    simpa only [words_related related] using host
  have hlen : len.toNat < 2^System.Platform.numBits := by
    by_cases hzlen : len.toNat = 0
    · have hh : 0 < 2^System.Platform.numBits := by positivity
      omega
    · have hb := (ReferenceMemoryCapacity.expansion_bounds pre.activeWords.toNat off.toNat len.toNat).2 (by omega)
      omega
  have h64 : len.toNat < 2^64 := by
    rcases System.Platform.numBits_eq with hn | hn <;> rw [hn] at hlen <;> omega
  have hbytes : pre.memory.readWithPadding off.toNat len.toNat = ReferenceReturnView.output v off len := by
    rw [ReferenceMemoryView.read_eq_buffer _ _ _ h64 hlen]
    exact ReferenceMemoryView.buffer_congr _ _ related.memory.bytes _ _
  have fit : pre.pc.toNat+1 < UInt256.size := by
    have := ReferenceRuntimeSites.pc_fit site
    omega
  refine ⟨post,raw,related.env,?_,rfl,expanded related rfl hex,related.storage,?_,related.owner⟩
  · change v.pc+1 = (pre.pc+UInt256.ofNat 1).toNat
    rw [related.pc,toNat_add_of_lt _ _ fit]
    rfl
  · change v.logs++[entry v off len] = ProtectedLogFrame.project pre.executionEnv.codeOwner
      {pre.substate with
        logSeries := pre.substate.logSeries.push ⟨pre.executionEnv.codeOwner,#[],pre.memory.readWithPadding off.toNat len.toNat⟩}
    rw [ProtectedLogFrame.push_self pre.executionEnv.codeOwner pre.substate
      ⟨pre.executionEnv.codeOwner,#[],pre.memory.readWithPadding off.toNat len.toNat⟩ rfl,
      ← related.logs,hbytes]
    rw [entry,related.env]

#print axioms copy
#print axioms log
end Eip8282.Audit.Integrator.ReferenceCopyLogReverse

end

section

/-! ## ReferenceRevertView -/

/-! Actual internal REVERT terminal view. The pinned Amsterdam system.py
revert body expands memory and returns its slice before raising Revert.
Source: audit/receipts/direct-reference-memory-control-sources-20260910.json,
EL0cc100eb190b64b23baba72dac0165652eaec252 system.py SHA256
37c888c4f1dfed62f1947ceb457db349be6978da5519234a5b6604f2e6036890.
This successful primitive-step observation does not assert that the enclosing
Theta commits this world or logs; wrapper rollback is a separate theorem.
Source gas/failure ordering and executable Python interpretation remain separate.
-/
namespace Eip8282.Audit.Integrator.ReferenceRevertView
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open ReferenceRuntimeView ReferenceReturnView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1800000

private theorem expanded_memory {parent : ReferenceStorageView.Parent} {v : View}
    {pre post : EVM.State} {off len : UInt256} (related : Related parent v pre)
    (hmem : post.memory = pre.memory)
    (hex : post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat len.toNat) :
    ReferenceMemoryOperations.Related post.toMachineState (returnMemory v off len) := by
  have hmono := (ReferenceMemoryCapacity.expansion_bounds pre.activeWords.toNat off.toNat len.toNat).1
  have hsize : v.memory.size ≤ 32*MachineState.M (words v) off.toNat len.toNat := by
    rw [related.memory.size,words_related related]
    omega
  have hext := ReferenceMemoryOperations.extend_same v.memory
    (32*MachineState.M (words v) off.toNat len.toNat) hsize
  refine ⟨?_,?_,?_⟩
  · change post.memory.size ≤ 32*post.activeWords.toNat
    rw [hmem,hex]
    have hc := related.memory.coherent
    change pre.memory.size ≤ 32*pre.activeWords.toNat at hc
    omega
  · rw [returnMemory,ReferenceMemoryOperations.extend,ReferenceMemoryView.buffer_size,
      words_related related,hex]
  · rw [hmem]
    intro i
    exact (related.memory.bytes i).trans (hext i)

/-- Actual admission supplies operands; final capacity supplies host bounds.
No runtime-site or source-offset restriction is needed. -/
theorem terminal {parent : ReferenceStorageView.Parent} {v : View}
    {vj : Array UInt256} {pre mid post : EVM.State} {fuel gasCost cap : Nat}
    (hz : Z vj .REVERT pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (.REVERT,none) mid post)
    (related : Related parent v pre)
    (capacity : post.activeWords.toNat ≤ cap)
    (host : 32*cap < 2^System.Platform.numBits) :
    ∃ off len rest, pre.stack.pop2 = some (rest,off,len) ∧
      v.stack = off::len::rest ∧ Result parent v off len rest post := by
  obtain ⟨rest,off,len,hshape,hpop⟩ := ReferenceAcceptedStack.pop2 hz (by decide)
  obtain rfl := Z_ok_state hz
  have raw : EvmYul.step (τ := .EVM) .REVERT none
      (stepPre gasCost (zMid pre .REVERT)) = .ok post := by
    change EVM.step (fuel+1) gasCost (some (.REVERT,none)) _ = .ok post at hs
    rw [OrdinaryGas.dispatch (by decide)] at hs
    exact hs
  have hex := RuntimeMemoryCharges.raw_expansion (by decide : Operation.REVERT ∈ RuntimeOpcodeScope.allowedOps) raw
  change post.activeWords.toNat = MachineState.M pre.activeWords.toNat
    pre.stack[0]!.toNat pre.stack[1]!.toNat at hex
  rw [hshape] at hex
  change post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat len.toNat at hex
  have hlen : len.toNat < 2^System.Platform.numBits := by
    by_cases hzlen : len.toNat = 0
    · have hp : 0 < 2^System.Platform.numBits := by positivity
      omega
    · have hb := (ReferenceMemoryCapacity.expansion_bounds
        pre.activeWords.toNat off.toNat len.toNat).2 (by omega)
      rw [← hex] at hb
      omega
  have h64 : len.toNat < 2^64 := by
    rcases System.Platform.numBits_eq with hn | hn <;> rw [hn] at hlen <;> omega
  have hout : pre.memory.readWithPadding off.toNat len.toNat = output v off len := by
    rw [ReferenceMemoryView.read_eq_buffer _ _ _ h64 hlen]
    exact ReferenceMemoryView.buffer_congr _ _ related.memory.bytes _ _
  have known := Eip8282.Audit.SymExec.step_REVERT
    (s := stepPre gasCost (zMid pre .REVERT)) hshape
  have same := Except.ok.inj (raw.symm.trans known)
  subst post
  refine ⟨off,len,rest,hpop,related.stack.trans hshape,?_⟩
  exact ⟨hout,rfl,related.env,related.storage,related.owner,related.logs,
    expanded_memory related rfl hex⟩

/-- Actual H identifies this internal terminal's output, including the exact
unpadded slice of the computed source memory. This is not a commit theorem. -/
theorem halted {parent : ReferenceStorageView.Parent} {v : View}
    {vj : Array UInt256} {pre mid post : EVM.State} {fuel gasCost cap : Nat} {out : ByteArray}
    (hz : Z vj .REVERT pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (.REVERT,none) mid post)
    (related : Related parent v pre)
    (capacity : post.activeWords.toNat ≤ cap)
    (host : 32*cap < 2^System.Platform.numBits)
    (hh : H post.toMachineState .REVERT = some out) :
    ∃ off len rest, pre.stack.pop2 = some (rest,off,len) ∧
      v.stack = off::len::rest ∧ Result parent v off len rest post ∧
      out = output v off len ∧ out = (returnMemory v off len).extract off.toNat (off.toNat+len.toNat) := by
  obtain ⟨off,len,rest,hpop,hshape,hr⟩ := terminal hz hs related capacity host
  have ho : post.H_return = out := Option.some.inj hh
  have he := ho.symm.trans hr.returned
  exact ⟨off,len,rest,hpop,hshape,hr,he,
    he.trans (ReferenceReturnSlice.output_eq_extract related off len)⟩

#print axioms terminal
#print axioms halted
end Eip8282.Audit.Integrator.ReferenceRevertView

end

section

/-! ## ReferenceSharedPayment -/

/-! Initial budgets for the literal source meter with reservoir-first state
charges and execution spill. No separate state reservoir is required: execution
must cover the execution budget, and the two pools together must cover both
budgets. Credits are observed only when their instruction executes. This is a
source-meter theorem, not an admitted transaction or Python execution theorem. -/
namespace Eip8282.Audit.Integrator.ReferenceSharedPayment
open EvmYul ReferenceStorageGas ReferenceMeterPath
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem state_success (m : Meter) (amount futureExec futureState : Nat)
    (he : futureExec ≤ m.execution)
    (ht : amount+futureExec+futureState ≤ m.execution+m.reservoir) :
    ∃ post, chargeState m amount = some post ∧
      futureExec ≤ post.execution ∧ futureExec+futureState ≤ post.execution+post.reservoir := by
  unfold chargeState
  split
  · exact ⟨_,rfl,he,by dsimp; omega⟩
  · rw [if_pos (by omega)]
    exact ⟨_,rfl,by dsimp; omega,by dsimp; omega⟩

/-- The caller reserves the remaining execution work before this instruction.
If state payment spills, the remaining reservoir is zero and total funds protect
that same execution reserve. No future refund is borrowed. -/
theorem pay_success (event : Event) (m : Meter) (futureExec futureState : Nat)
    (he : executionBudget event+futureExec ≤ m.execution)
    (ht : executionBudget event+stateBudget event+futureExec+futureState ≤ m.execution+m.reservoir) :
    ∃ post, pay event m = some post ∧
      futureExec ≤ post.execution ∧ futureExec+futureState ≤ post.execution+post.reservoir := by
  cases event with
  | ordinary amount =>
    change amount+futureExec ≤ m.execution at he
    change amount+0+futureExec+futureState ≤ m.execution+m.reservoir at ht
    refine ⟨{m with execution := m.execution-amount},?_,?_,?_⟩
    · exact if_pos (by omega)
    · dsimp; omega
    · dsimp; omega
  | store warm original current new =>
    change 12100+futureExec ≤ m.execution at he
    change 12100+97920+futureExec+futureState ≤ m.execution+m.reservoir at ht
    obtain ⟨be,bs,sentry⟩ := charge_bounds warm original current new
    unfold pay storageCharge
    simp only [Bool.false_eq_true,↓reduceIte,sentry]
    rw [if_pos (by omega)]
    unfold creditState chargeExecution
    rw [if_pos (by dsimp; omega)]
    simp only [Option.bind_some]
    apply state_success
    · dsimp; omega
    · dsimp; omega

/-- Arbitrarily long finite event lists, funded at entry with actual split pools.
State charges may spill into execution gas; no artificial positive-reservoir
premise or iteration bound is introduced. -/
theorem payment (events : List Event) (m : Meter)
    (he : sumExec events ≤ m.execution)
    (ht : sumExec events+sumState events ≤ m.execution+m.reservoir) :
    ∃ post, run events m = some post := by
  induction events generalizing m with
  | nil => exact ⟨m,rfl⟩
  | cons event events ih =>
    have ex : sumExec (event::events) = executionBudget event+sumExec events := rfl
    have st : sumState (event::events) = stateBudget event+sumState events := rfl
    obtain ⟨middle,paid,me,mt⟩ := pay_success event m (sumExec events) (sumState events)
      (by omega) (by omega)
    obtain ⟨post,tail⟩ := ih middle me mt
    exact ⟨post,by simp only [run,paid,Option.bind_some,tail]⟩

#print axioms pay_success
#print axioms payment
end Eip8282.Audit.Integrator.ReferenceSharedPayment

end

section

/-! ## ReferenceTransactionGas -/

/-! Literal Nat transcription of Amsterdam allocation and settlement.
EL0cc100eb190b64b23baba72dac0165652eaec252 vm/gas.py:1116-1150,1177-1250,
SHA41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c,
full body audit/receipts/direct-reference-admission-sources-20260910.json.
Explicit source guards justify checked subtraction. This proves arithmetic of
these definitions, not Python execution or that a validator/frame supplied
the inputs. In particular source execution and state pools are not oldYul gas.
-/
namespace Eip8282.Audit.Integrator.ReferenceTransactionGas
open EvmYul
set_option autoImplicit false

structure Allocation where
  execution : Nat
  reservoir : Nat

def allocate (txGas intrinsic : Nat) : Allocation :=
  let evmGas := txGas-intrinsic
  let executionBudget := 16777216-intrinsic
  let execution := min executionBudget evmGas
  {execution := execution, reservoir := evmGas-execution}

/-- Every checked subtraction in allocation is funded by the two admission
checks; remaining-pool conservation is a conclusion. -/
theorem allocation (txGas intrinsic : Nat)
    (affords : intrinsic ≤ txGas) (maximum : intrinsic ≤ 16777216) :
    (allocate txGas intrinsic).execution+(allocate txGas intrinsic).reservoir = txGas-intrinsic ∧
    intrinsic+(allocate txGas intrinsic).execution+(allocate txGas intrinsic).reservoir = txGas ∧
    (allocate txGas intrinsic).execution ≤ 16777216-intrinsic ∧
    (allocate txGas intrinsic).execution ≤ txGas-intrinsic ∧
    intrinsic+(allocate txGas intrinsic).execution ≤ 16777216 := by
  simp only [allocate]
  omega

structure Settlement where
  gasUsed : Nat
  gasLeft : Nat
  executionUsed : Nat
  stateUsed : Nat

/-- Uint(max(0,netState)) has value Int.toNat netState. -/
def settledState (netState : Int) : Nat := (max 0 netState).toNat

def settle (txGas calldataFloor gasLeft stateLeft : Nat) (refund : UInt256) (netState : Int) : Settlement :=
  let beforeRefund := txGas-gasLeft-stateLeft
  let gasRefund := min (beforeRefund/5) refund.toNat
  let afterRefund := beforeRefund-gasRefund
  let gasUsed := max afterRefund calldataFloor
  let stateUsed := settledState netState
  let executionUsed := max (beforeRefund-stateUsed) calldataFloor
  {gasUsed := gasUsed, gasLeft := txGas-gasUsed,
   executionUsed := executionUsed, stateUsed := stateUsed}

/-- The source sender-facing charge never drops below its calldata floor. -/
theorem floor_paid (txGas calldataFloor gasLeft stateLeft : Nat) (refund : UInt256) (netState : Int) :
    calldataFloor ≤ (settle txGas calldataFloor gasLeft stateLeft refund netState).gasUsed := by
  exact Nat.le_max_right _ _

/-- Source checked subtraction guards, final sender conservation and bounds.
Returned pools and net state usage are frame inputs, not assumed conclusions
about this allocation or a claimed source interpreter execution. -/
theorem settlement (txGas calldataFloor gasLeft stateLeft : Nat) (refund : UInt256) (netState : Int)
    (returned : gasLeft+stateLeft ≤ txGas) (floorFits : calldataFloor ≤ txGas)
    (stateFits : settledState netState ≤ txGas-gasLeft-stateLeft) :
    gasLeft ≤ txGas ∧ stateLeft ≤ txGas-gasLeft ∧
    min ((txGas-gasLeft-stateLeft)/5) refund.toNat ≤ txGas-gasLeft-stateLeft ∧
    settledState netState ≤ txGas-gasLeft-stateLeft ∧
    (settle txGas calldataFloor gasLeft stateLeft refund netState).gasUsed ≤ txGas ∧
    (settle txGas calldataFloor gasLeft stateLeft refund netState).gasUsed+
      (settle txGas calldataFloor gasLeft stateLeft refund netState).gasLeft = txGas ∧
    calldataFloor ≤ (settle txGas calldataFloor gasLeft stateLeft refund netState).executionUsed := by
  simp only [settle]
  omega

#print axioms allocation
#print axioms floor_paid
#print axioms settlement
end Eip8282.Audit.Integrator.ReferenceTransactionGas

end

section

/-! ## ReferenceTransactionPayment -/

/-! Concrete source allocation consumes the same event list's two budgets.
The inequalities are sufficient resource requirements, not consequences of
transaction validity alone. In particular a valid transaction may run out of
gas. State payment can spill, including when the initial reservoir is zero. -/
namespace Eip8282.Audit.Integrator.ReferenceTransactionPayment
open EvmYul ReferenceStorageGas ReferenceMeterPath ReferenceTransactionGas
set_option autoImplicit false

def initialMeter (txGas intrinsic : Nat) : Meter :=
  {execution := (allocate txGas intrinsic).execution,
   reservoir := (allocate txGas intrinsic).reservoir,
   spill := 0, refund := 0}

theorem payment (events : List Event) (txGas intrinsic : Nat)
    (executionFits : intrinsic+sumExec events ≤ 16777216)
    (totalFits : intrinsic+sumExec events+sumState events ≤ txGas) :
    ∃ post, run events (initialMeter txGas intrinsic) = some post := by
  have alloc := allocation txGas intrinsic (by omega) (by omega)
  apply ReferenceSharedPayment.payment
  · change sumExec events ≤ min (16777216-intrinsic) (txGas-intrinsic)
    omega
  · change sumExec events+sumState events ≤ (allocate txGas intrinsic).execution+(allocate txGas intrinsic).reservoir
    omega

/-- A zero reservoir is supported by the same literal allocation and payment,
without changing either source rule or inventing additional state gas. -/
theorem below_cap (events : List Event) (txGas intrinsic : Nat)
    (cap : txGas ≤ 16777216)
    (totalFits : intrinsic+sumExec events+sumState events ≤ txGas) :
    (initialMeter txGas intrinsic).reservoir = 0 ∧
    ∃ post, run events (initialMeter txGas intrinsic) = some post := by
  constructor
  · simp only [initialMeter,allocate]
    omega
  · exact payment events txGas intrinsic (by omega) totalFits

#print axioms payment
#print axioms below_cap
end Eip8282.Audit.Integrator.ReferenceTransactionPayment

end
