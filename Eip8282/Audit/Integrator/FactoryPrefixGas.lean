import Eip8282.Audit.Integrator.FactoryChildResources
import Eip8282.Audit.Integrator.ReturnedGas

/-! Gas upper bounds for the same actual prefix witness used by initialization.
The generic bound follows actual accepted steps, including recursive outcomes,
and does not require a predicted instruction trace or a no-wrap premise. -/
namespace Eip8282.Audit.Integrator.FactoryPrefixGas
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.SymExec
open NestedEvents FactoryRuntimeEntry FactoryChildResources
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem step_gas_nonincrease {vj : Array UInt256} {fuel cost : Nat}
    {pre post : EVM.State} (h : XStepAt vj fuel cost pre post) :
    post.gasAvailable.toNat ≤ pre.gasAvailable.toNat := by
  obtain ⟨mid,hz,hs,_⟩ := h
  exact ReturnedGas.step_remaining fuel hz hs

theorem runs_gas_nonincrease {vj : Array UInt256} {fuel rem : Nat}
    {pre post : EVM.State} {trace : List Labelled}
    (h : XRuns vj fuel pre trace rem post) :
    post.gasAvailable.toNat ≤ pre.gasAvailable.toNat := by
  induction h with
  | refl => exact Nat.le_refl _
  | cons hs _ ih => exact ih.trans (step_gas_nonincrease hs)

theorem reaches_gas_nonincrease {vj : Array UInt256} {k : Nat}
    {pre post : EVM.State} (h : Reaches vj k pre post) :
    post.gasAvailable.toNat ≤ pre.gasAvailable.toNat := by
  obtain ⟨trace,hr⟩ := h 0
  exact runs_gas_nonincrease hr

/-- This applies to the supplied witness, including the witness retained by
FactoryChildResources.entry_resources. -/
theorem atCreate_gas_le {kind : Kind} {a : XiArgs} {gas : UInt256} {e : Nat}
    (h : Reaches a.jumps 13 a.entry (atCreate kind a gas e)) : gas.toNat ≤ a.gas.toNat :=
  reaches_gas_nonincrease h

/-- Both gas bounds describe the same concrete post-prefix state. -/
theorem prefix_bounds (kind : Kind) (a : XiArgs)
    (hcode : a.env.code = FactoryRuntimeEntry.runtime)
    (hdata : a.env.calldata = calldata kind) (hgas : 200 ≤ a.gas.toNat) :
    ∃ gas e, a.gas.toNat-157 ≤ gas.toNat ∧ gas.toNat ≤ a.gas.toNat ∧
      Reaches a.jumps 13 a.entry (atCreate kind a gas e) := by
  obtain ⟨gas,e,hlo,hr⟩ := reaches_create2 kind a hcode hdata hgas
  exact ⟨gas,e,hlo,atCreate_gas_le hr,hr⟩

#print axioms step_gas_nonincrease
#print axioms runs_gas_nonincrease
#print axioms reaches_gas_nonincrease
#print axioms atCreate_gas_le
#print axioms prefix_bounds
end Eip8282.Audit.Integrator.FactoryPrefixGas
