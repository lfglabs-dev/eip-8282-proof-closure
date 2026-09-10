import Eip8282.Audit.Integrator.ReferenceAppendPrice

/-! A coarse synthetic execution budget for protected effect replay. This
compares old opcode prices with literal source execution prices, without
identifying the two gas meters or their original-storage/warmth histories.
Memory expansion and source stack/decoder admission are separate obligations.
The factor is a proof budget, never a change to the runtime's actual tariff. -/
namespace Eip8282.Audit.Integrator.ReferenceReplayCost
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings ReferenceMeterPath
open ReferenceExecutionLedger
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem ordinary_ratio {op : Operation .EVM} {n : Nat} (pre : EVM.State) (warm : Bool)
    (allowed : op ∈ RuntimeOpcodeScope.allowedOps)
    (price : ReferenceOrdinaryGas.ordinaryCost op warm = some n) : C' pre op ≤ 221*n := by
  simp only [RuntimeOpcodeScope.allowedOps,List.mem_cons,List.not_mem_nil,or_false] at allowed
  rcases allowed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (simp_all [ReferenceOrdinaryGas.ordinaryCost]; done)
    | (simp_all +decide [C',ReferenceOrdinaryGas.ordinaryCost,GasConstants.Gzero,GasConstants.Gbase,
        GasConstants.Gverylow,GasConstants.Glow,GasConstants.Gmid,GasConstants.Ghigh,GasConstants.Gjumpdest,
        Csload,GasConstants.Gcoldsload,GasConstants.Gwarmaccess]
       try split_ifs at *
       all_goals omega)

/-- The same stack supplies COPY and LOG lengths. SSTORE uses the universal
old22100 upper bound and the actual source class's100 lower bound; no equality
of original-state or warm sets is needed for this deliberately coarse ratio. -/
theorem opcode_ratio {op : Operation .EVM} {p : Parent} {v next : View} {w : Warm} {event : Event}
    (pre : EVM.State) (stack : pre.stack = v.stack) (allowed : op ∈ RuntimeOpcodeScope.allowedOps)
    (price : Price p v w next op event) : C' pre op ≤ 221*eventWork event := by
  by_cases hs : op = .SSTORE
  · subst op
    simp only [Price,↓reduceIte] at price
    rw [price.2]
    have upper := Csstore_le pre
    have lower : 100 ≤ (ReferenceStorageGas.classify (sourceReading p v w).warm
        (sourceReading p v w).original (sourceReading p v w).current (sourceReading p v w).new).execution := by
      simp only [ReferenceStorageGas.classify]
      split <;> omega
    change Csstore pre ≤ _
    simp only [GasConstants.Gcoldsload,GasConstants.Gsset] at upper
    simp only [eventWork]
    omega
  · simp only [Price,if_neg hs] at price
    obtain ⟨n,computed,rfl⟩ := price
    have base : C' pre op ≤ 221*n := by
      by_cases hc : op = .CALLDATACOPY
      · subst op
        have hn : ReferenceCopyLogGas.copyCost v.stack[2]!.toNat = n := Option.some.inj computed
        have hold : C' pre .CALLDATACOPY = ReferenceCopyLogGas.copyCost v.stack[2]!.toNat := by
          simp +decide [C',ReferenceCopyLogGas.copyCost,stack,GasConstants.Gverylow,GasConstants.Gcopy]
        omega
      · by_cases hl : op = .LOG0
        · subst op
          have hn : ReferenceCopyLogGas.logCost v.stack[1]!.toNat = n := Option.some.inj computed
          have hold : C' pre .LOG0 = ReferenceCopyLogGas.logCost v.stack[1]!.toNat := by
            simp [C',ReferenceCopyLogGas.logCost,stack,GasConstants.Glog,GasConstants.Glogdata]
          omega
        · simp only [ReferenceCopyLogGas.ordinaryCost,if_neg hc,if_neg hl] at computed
          exact ordinary_ratio pre _ allowed computed
    simp only [eventWork]
    omega

#print axioms opcode_ratio
end Eip8282.Audit.Integrator.ReferenceReplayCost
