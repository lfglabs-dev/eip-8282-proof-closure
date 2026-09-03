import Eip8282.Audit.SymExec
import Eip8282.Audit.UniversalBoundary

/-!
# The machine of a `Ξ` call, with the fields a run changes made explicit

`Eip8282.Audit.XiTransport.XiCall.entry` is the machine `Ξ` hands to `X`. Every
state a run of the pinned runtimes passes through is that machine with a new
program counter, stack, gas, instruction count, storage-access state, memory and
active-word count — and nothing else: the two runtimes never touch the return
data before their halt, never call, and never change the environment.

`at_` names such a state. The block lemmas of `Eip8282.Audit.EntryReach.Blocks`
are `rfl` equations between two `at_` states, and the path theorems compose
them. The word readers below are the values the pinned code reads off the
environment and the storage, as `SymExec.pureStep` computes them.
-/

namespace Eip8282.Audit.EntryReach

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Model (Kind)

/-- The machine of `c` at offset `pc` with stack `stk`, holding state `st`, memory
`mem`, `aw` active words, `g` gas and `e` executed instructions. -/
def at_ {kind : Kind} (c : XiCall kind) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (pc : Nat) (stk : Stack UInt256) (e : Nat) : EVM.State :=
  { c.entry with toState := st, memory := mem, activeWords := aw, gasAvailable := g,
                 pc := UInt256.ofNat pc, stack := stk, execLength := e }

/-- `Ξ`'s entry machine is `at_` at offset zero with an empty stack. -/
theorem entry_eq_at {kind : Kind} (c : XiCall kind) :
    c.entry = at_ c c.entry.toState c.entry.memory c.entry.activeWords c.gas 0 [] 0 := rfl

@[simp] theorem pc_at {kind : Kind} (c : XiCall kind) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (pc : Nat) (stk : Stack UInt256) (e : Nat) :
    (at_ c st mem aw g pc stk e).pc = UInt256.ofNat pc := rfl

@[simp] theorem stack_at {kind : Kind} (c : XiCall kind) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (pc : Nat) (stk : Stack UInt256) (e : Nat) :
    (at_ c st mem aw g pc stk e).stack = stk := rfl

@[simp] theorem gas_at {kind : Kind} (c : XiCall kind) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (pc : Nat) (stk : Stack UInt256) (e : Nat) :
    (at_ c st mem aw g pc stk e).gasAvailable = g := rfl

@[simp] theorem toState_at {kind : Kind} (c : XiCall kind) (st : EvmYul.State .EVM)
    (mem : ByteArray) (aw g : UInt256) (pc : Nat) (stk : Stack UInt256) (e : Nat) :
    (at_ c st mem aw g pc stk e).toState = st := rfl

@[simp] theorem executionEnv_at {kind : Kind} (c : XiCall kind) (st : EvmYul.State .EVM)
    (mem : ByteArray) (aw g : UInt256) (pc : Nat) (stk : Stack UInt256) (e : Nat) :
    (at_ c st mem aw g pc stk e).executionEnv = st.executionEnv := rfl

@[simp] theorem memory_at {kind : Kind} (c : XiCall kind) (st : EvmYul.State .EVM)
    (mem : ByteArray) (aw g : UInt256) (pc : Nat) (stk : Stack UInt256) (e : Nat) :
    (at_ c st mem aw g pc stk e).memory = mem := rfl

@[simp] theorem activeWords_at {kind : Kind} (c : XiCall kind) (st : EvmYul.State .EVM)
    (mem : ByteArray) (aw g : UInt256) (pc : Nat) (stk : Stack UInt256) (e : Nat) :
    (at_ c st mem aw g pc stk e).activeWords = aw := rfl

/-- Re-attaching gas and the instruction count to an `at_` state. -/
theorem withGE_at {kind : Kind} (c : XiCall kind) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (pc : Nat) (stk : Stack UInt256) (e : Nat) (g' : UInt256) (e' : Nat) :
    withGE (at_ c st mem aw g pc stk e) g' e' = at_ c st mem aw g' pc stk e' := rfl

/-! ## The words the pinned code reads -/

/-- `CALLER`: the immediate caller, `Iₛ`, as a word. -/
def callerW (st : EvmYul.State .EVM) : UInt256 := UInt256.ofNat st.executionEnv.source.val

/-- `CALLVALUE`: `Iᵥ`. -/
def valueW (st : EvmYul.State .EVM) : UInt256 := st.executionEnv.weiValue

/-- `CALLDATASIZE`: `|I_d|`. -/
def cdsizeW (st : EvmYul.State .EVM) : UInt256 := UInt256.ofNat st.executionEnv.calldata.size

/-- `CALLDATALOAD off`: the zero-padded 32-byte word of calldata at `off`. -/
def cdW (st : EvmYul.State .EVM) (off : UInt256) : UInt256 := st.calldataload off

/-- `SLOAD k`: the executing account's storage word at `k`. -/
def slotW (st : EvmYul.State .EVM) (k : UInt256) : UInt256 := (st.sload k).2

/-- The state after `SLOAD k`: only the accessed-keys set changes. -/
def touch (st : EvmYul.State .EVM) (k : UInt256) : EvmYul.State .EVM := (st.sload k).1

@[simp] theorem executionEnv_touch (st : EvmYul.State .EVM) (k : UInt256) :
    (touch st k).executionEnv = st.executionEnv := rfl

@[simp] theorem accountMap_touch (st : EvmYul.State .EVM) (k : UInt256) :
    (touch st k).accountMap = st.accountMap := rfl

@[simp] theorem logSeries_touch (st : EvmYul.State .EVM) (k : UInt256) :
    (touch st k).substate.logSeries = st.substate.logSeries := rfl

@[simp] theorem σ₀_touch (st : EvmYul.State .EVM) (k : UInt256) :
    (touch st k).σ₀ = st.σ₀ := rfl

/-- Reading a slot after touching another: the value is unaffected. -/
@[simp] theorem slotW_touch (st : EvmYul.State .EVM) (k k' : UInt256) :
    slotW (touch st k) k' = slotW st k' := rfl

@[simp] theorem callerW_touch (st : EvmYul.State .EVM) (k : UInt256) :
    callerW (touch st k) = callerW st := rfl
@[simp] theorem valueW_touch (st : EvmYul.State .EVM) (k : UInt256) :
    valueW (touch st k) = valueW st := rfl
@[simp] theorem cdsizeW_touch (st : EvmYul.State .EVM) (k : UInt256) :
    cdsizeW (touch st k) = cdsizeW st := rfl
@[simp] theorem cdW_touch (st : EvmYul.State .EVM) (k off : UInt256) :
    cdW (touch st k) off = cdW st off := rfl

end Eip8282.Audit.EntryReach
