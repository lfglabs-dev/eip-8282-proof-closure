import Eip8282.Audit.Integrator.ReferenceOrdinaryGas
import Eip8282.Audit.Integrator.ReferenceRuntimeView
import Eip8282.Audit.Integrator.ReferenceAcceptedStack
import Eip8282.Audit.Integrator.SystemMeterResources

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
