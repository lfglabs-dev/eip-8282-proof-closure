import Eip8282.Audit.Execution.State
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





















/-! ## The words the pinned code reads -/




























end Eip8282.Audit.EntryReach
