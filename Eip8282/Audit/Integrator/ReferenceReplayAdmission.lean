import Eip8282.Audit.Integrator.ReferenceActionStackBounds
import Eip8282.Audit.Integrator.ReferenceActionControlAdmission

/-! Construct actual old Z admission from source-shaped action guards and a
synthetic sufficient budget. The budget is explicit and must be derived from
source work; this theorem never equates source and old gas meters. -/
namespace Eip8282.Audit.Integrator.ReferenceReplayAdmission
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceRuntimeAction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

/-- Protected opcode prices do not read the synthetic gas/step counters. -/
theorem base_charged (pre : EVM.State) (op : Operation .EVM)
    (allowed : op ∈ RuntimeOpcodeScope.allowedOps) :
    C' (zMid pre op) op = C' pre op := by
  simp only [RuntimeOpcodeScope.allowedOps,List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem base_replay (pre : EVM.State) (op : Operation .EVM) (cost : Nat)
    (allowed : op ∈ RuntimeOpcodeScope.allowedOps) :
    C' (stepPre cost (zMid pre op)) op = C' pre op := by
  simp only [RuntimeOpcodeScope.allowedOps,List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- All non-gas guards are produced from the same running action and source
stack bound. The reserve also discharges the actual SSTORE sentry after memory
has been charged, in the order used by Z. -/
theorem z {kind : Kind} {parent : ReferenceStorageView.Parent} {v next : View} {pre : EVM.State}
    (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (effect : Action kind parent (decodeAt pre) v next)
    (postbounded : next.stack.length ≤ 1024)
    (budget : C' pre (decodeAt pre).1+memoryExpansionCost pre (decodeAt pre).1+2301 ≤ pre.gasAvailable.toNat) :
    Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre =
      .ok (zMid pre (decodeAt pre).1,C' pre (decodeAt pre).1) := by
  have allowed := RuntimeExecutionScope.opcode_allowed site
  have bounds := ReferenceActionStackBounds.admission effect postbounded
  rw [related.stack] at bounds
  have jumps := ReferenceActionControlAdmission.jump_guards related effect
  have others := ReferenceActionControlAdmission.other_guards site
  have hm : memoryExpansionCost pre (decodeAt pre).1 ≤ pre.gasAvailable.toNat := by omega
  have hg : (charged pre (decodeAt pre).1).gasAvailable.toNat =
      pre.gasAvailable.toNat-memoryExpansionCost pre (decodeAt pre).1 := toNat_sub_ofNat hm
  have hb := base_charged pre (decodeAt pre).1 allowed
  have result := Z_of_facts (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre
    hm (by change C' (zMid pre (decodeAt pre).1) _ ≤ _; rw [hb,hg]; omega)
    others.1 others.2.1 bounds.1 bounds.2 jumps.1 jumps.2 others.2.2.1
    (ReferenceActionControlAdmission.static_guard related effect)
    (fun _ => by change 2300 < _; rw [hg]; omega) others.2.2.2
  change Z _ _ pre = .ok (zMid pre (decodeAt pre).1,C' (zMid pre (decodeAt pre).1) (decodeAt pre).1) at result
  rw [hb] at result
  exact result

#print axioms base_charged
#print axioms base_replay
#print axioms z
end Eip8282.Audit.Integrator.ReferenceReplayAdmission
