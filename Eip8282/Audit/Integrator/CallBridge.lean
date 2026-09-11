import Eip8282.Audit.Integrator.MessageCall
import Eip8282.Audit.XiTransport

/-!
# Bind pinned code execution to the enclosing message call

The code frame below uses the world after Θ's actual value transfer, not an
unrelated storage image. Fuel has two wrappers: Θ consumes one level, then Ξ
consumes one before X. The bridge records that offset explicitly.

These transport lemmas can consume the concrete endpoint theorems without a
model-agreement assumption. Funding, installed-code identity and protocol
authorization still belong to the caller; this module does not derive them.
-/

namespace Eip8282.Audit.Integrator.CallBridge

open EvmYul EvmYul.EVM
open Eip8282.Audit.XiTransport
open Eip8282.Audit.Correspondence (runtimeCode)
open Eip8282.Audit.Integrator.MessageCall
open Eip8282.Audit.Model (Kind)

/-- A pinned Ξ frame built from the actual inputs and transferred world of Θ. -/
def codeCall (c : Context) {kind : Kind} (hcode : c.code = runtimeCode kind)
    (steps : Nat) : XiCall kind :=
  { fuel := steps, createdAccounts := c.created, genesisBlockHeader := c.genesis,
    blocks := c.blocks, σ := c.entryWorld, σ₀ := c.originalWorld, gas := c.gas,
    substate := c.substate, env := c.environment, code_pinned := hcode }

theorem execution_eq_codeCall (c : Context) {kind : Kind}
    (hcode : c.code = runtimeCode kind) (steps : Nat) (hf : c.fuel = steps + 1) :
    c.execution = (codeCall c hcode steps).result := by
  unfold Context.execution XiCall.result codeCall
  rw [hf]

/-- Exact composition, keeping even the upstream empty-world fallback visible. -/
theorem result_eq_codeCall_settlement (c : Context) {kind : Kind}
    (hcode : c.code = runtimeCode kind) (steps : Nat) (hf : c.fuel = steps + 1) :
    c.result = c.settle (codeCall c hcode steps).result := by
  rw [result_eq_settle, execution_eq_codeCall c hcode steps hf]

/-- A concrete successful endpoint is the committed message-call result when
its published world survives the upstream empty-world test. -/
theorem commits_endpoint (c : Context) {kind : Kind}
    (hcode : c.code = runtimeCode kind) (steps : Nat) (hf : c.fuel = steps + 1)
    (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (substate : Substate) (out : ByteArray)
    (hr : (codeCall c hcode steps).result =
      .ok (.success (created, world, gas, substate) out))
    (hne : (world == ∅) = false) :
    c.result = .ok (created, world, gas, substate, true, out) := by
  exact success_commits_world c created world gas substate out
    ((execution_eq_codeCall c hcode steps hf).trans hr) hne

/-- A concrete rejected endpoint restores the complete pre-transfer journal. -/
theorem rolls_back_endpoint (c : Context) {kind : Kind}
    (hcode : c.code = runtimeCode kind) (steps : Nat) (hf : c.fuel = steps + 1)
    (gas : UInt256) (out : ByteArray)
    (hr : (codeCall c hcode steps).result = .ok (.revert gas out)) :
    c.result = .ok (c.created, c.world, gas, c.substate, false, out) := by
  exact revert_restores_world c gas out
    ((execution_eq_codeCall c hcode steps hf).trans hr)

#print axioms execution_eq_codeCall
#print axioms commits_endpoint
#print axioms rolls_back_endpoint

end Eip8282.Audit.Integrator.CallBridge
