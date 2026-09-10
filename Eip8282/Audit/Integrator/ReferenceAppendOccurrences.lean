import Eip8282.Audit.Integrator.AppendGasPath

/-! Ordered selected instruction occurrences in actual successful append suffixes.
Unmarked segments retain the original actual XRuns. Marked singletons retain
their actual pre-state, decode, and LOG0 length operand. This proves necessity
for the pinned evaluator at arbitrary fuel/gas, not source execution or a
desired endpoint/count assumption. Whole-entry and source Coupled alignment
are separate consumers. Tail SSTORE is deliberately selected after LOG0. -/
namespace Eip8282.Audit.Integrator.ReferenceAppendOccurrences
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall)
open SuccessInversion ActualAppendGas AppendGasPath
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

inductive Marker where
  | store
  | log (length : UInt256)
  deriving DecidableEq, Repr

def Matches : Marker → EVM.State → Prop
  | .store, pre => decodeAt pre = (.SSTORE,none)
  | .log len, pre => decodeAt pre = (.LOG0,none) ∧ ∃ off rest, pre.stack = off::len::rest

/-- Selected single steps cannot overlap: trans joins actual endpoint/fuel
indices and every marked singleton consumes one unit of evaluator fuel. -/
inductive Marked (vj : Array UInt256) : Nat → EVM.State → Nat → EVM.State → List Marker → Prop where
  | skip {fuel rest : Nat} {pre post : EVM.State}
      (run : Segment vj fuel pre rest post) : Marked vj fuel pre rest post []
  | single {fuel cost : Nat} {pre post : EVM.State} {marker : Marker}
      (step : XStepAt vj fuel cost pre post) (markProof : Matches marker pre) :
      Marked vj (fuel+1) pre fuel post [marker]
  | trans {f g r : Nat} {pre mid post : EVM.State} {left right : List Marker}
      (first : Marked vj f pre g mid left) (second : Marked vj g mid r post right) :
      Marked vj f pre r post (left++right)

theorem Marked.erase {vj : Array UInt256} {fuel rest : Nat} {pre post : EVM.State}
    {markers : List Marker} (h : Marked vj fuel pre rest post markers) : Segment vj fuel pre rest post := by
  induction h with
  | skip run => exact run
  | @single fuel cost pre post marker step markProof =>
    apply Segment.single ?_ step
    cases marker with
    | store => rw [markProof]; decide
    | log len => rw [markProof.1]; decide
  | trans first second ih1 ih2 => exact ih1.trans ih2

theorem Marked.selected_le {vj : Array UInt256} {fuel rest : Nat} {pre post : EVM.State}
    {markers : List Marker} (h : Marked vj fuel pre rest post markers) : markers.length+rest ≤ fuel := by
  induction h with
  | skip run => obtain ⟨trace,hr,_⟩ := run; simpa using hr.rem_le
  | single => simp; omega
  | trans first second ih1 ih2 => simp only [List.length_append]; omega

def exitMarkers : List Marker := [.store,.store,.store,.store,.log (UInt256.ofNat 68),.store]
def depositMarkers : List Marker :=
  [.store,.store,.store,.store,.store,.store,.store,.log (UInt256.ofNat 184),.store]

/-- Companion of the existing actual SSTORE inversion, retaining its single step. -/
theorem store_one {kind : Eip8282.Audit.Model.Kind} {c : XiCall kind}
    {fuel pc : Nat} {vj : Array UInt256} {code : ByteArray}
    {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {key value : UInt256} {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (hop : opcodeAt code pc = some (.SSTORE,none)) (hc : st.executionEnv.code = code)
    (h : X fuel vj (at_ c st mem aw g pc (key::value::stk) e) = .ok (.success final out)) :
    ∃ rest gas count, X rest vj (at_ c (st.sstore key value) mem aw gas (pc+1) stk count) =
      .ok (.success final out) ∧
      Marked vj fuel (at_ c st mem aw g pc (key::value::stk) e) rest
        (at_ c (st.sstore key value) mem aw gas (pc+1) stk count) [.store] := by
  have hd := decodeAt_of_code_pc (st := at_ c st mem aw g pc (key::value::stk) e) hc rfl hop
  obtain ⟨rest, gas, count, cost, hf, hp, hx⟩ := effect_one (by decide : Operation.SSTORE ∈ allOps) (by decide)
    hd (step_SSTORE rfl) h
  rw [toState_replace_at,withGE_at] at hx hp
  refine ⟨rest,gas,count,hx,?_⟩
  rw [hf]
  exact .single hp hd

/-- Actual completed exit suffix selects every required store and its exact log. -/
theorem exit_suffix (c : XiCall .exit)
    {fuel : Nat} {aw g : UInt256} {e : Nat} {final : EVM.State} {out : ByteArray}
    (h : X fuel exitJumpdests
      (at_ c (Exit.st₂ c) (Exit.mem₀ c) aw g 165 [] e) = .ok (.success final out)) :
    ∃ rest finish, Marked exitJumpdests fuel
      (at_ c (Exit.st₂ c) (Exit.mem₀ c) aw g 165 [] e) rest finish exitMarkers ∧
      decodeAt finish = (.STOP,none) ∧ X rest exitJumpdests finish = .ok (.success final out) := by
  obtain ⟨f1, g1, e1, _, hx1, hp1⟩ := traced_symBlock (h := h) exit_b165 exit_b165_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b165_shape c (Exit.st₂ c) _ _ _ _ [])
  rw [withGE_at] at hx1 hp1
  simp only [slotW_touch] at hx1 hp1
  obtain ⟨f2, g2, e2, hx2, hp2⟩ := store_one exit_s173 (Exit.hcode_of_env c (by append_env)) hx1
  obtain ⟨f3, g3, e3, _, hx3, hp3⟩ := traced_symBlock (h := hx2) exit_b174 exit_b174_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b174_shape c (Exit.countStore c) _ _ _ _ [])
  rw [withGE_at] at hx3 hp3
  simp only [callerW_touch, callerW_sstore] at hx3 hp3
  obtain ⟨f4, g4, e4, hx4, hp4⟩ := store_one exit_s186 (Exit.hcode_of_env c (by append_env)) hx3
  obtain ⟨f5, g5, e5, _, hx5, hp5⟩ := traced_symBlock (h := hx4) exit_b187 exit_b187_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b187_shape c _ _ _ _ _ (Exit.slotBase c) [Exit.tailWord c])
  rw [withGE_at] at hx5 hp5
  simp only [cdW_touch, cdW_sstore] at hx5 hp5
  obtain ⟨f6, g6, e6, hx6, hp6⟩ := store_one exit_s193 (Exit.hcode_of_env c (by append_env)) hx5
  obtain ⟨f7, g7, e7, _, hx7, hp7⟩ := traced_symBlock (h := hx6) exit_b194 exit_b194_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b194_shape c _ _ _ _ _ _ [Exit.tailWord c])
  rw [withGE_at] at hx7 hp7
  simp only [cdW_touch, cdW_sstore] at hx7 hp7
  obtain ⟨f8, g8, e8, hx8, hp8⟩ := store_one exit_s201 (Exit.hcode_of_env c (by append_env)) hx7
  obtain ⟨f9, g9, e9, _, hx9, hp9⟩ := traced_symBlock (h := hx8) exit_b202 exit_b202_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b202_shape c (Exit.itemStored c) _ _ _ _ [Exit.tailWord c])
  rw [withGE_at] at hx9 hp9
  simp only [callerW_touch, callerW_sstore] at hx9 hp9
  obtain ⟨f10, g10, e10, hx10, hp10⟩ := traced_mstore_success exit_s207 (Exit.hcode_of_env c (by append_env)) hx9
  obtain ⟨f11, g11, e11, _, hx11, hp11⟩ := traced_symBlock (h := hx10) exit_b208 exit_b208_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b208_shape c (Exit.itemStored c) _ _ _ _ [Exit.tailWord c])
  rw [withGE_at] at hx11 hp11
  obtain ⟨f12, g12, e12, hx12, hp12⟩ := traced_copy_success exit_s213 (Exit.hcode_of_env c (by append_env)) hx11
  obtain ⟨f13, g13, e13, _, hx13, hp13⟩ := traced_symBlock (h := hx12) exit_b214 exit_b214_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b214_shape c (Exit.itemStored c) _ _ _ _ [Exit.tailWord c])
  rw [withGE_at] at hx13 hp13
  obtain ⟨f14, g14, e14, cost14, hf14, hstep14, hx14⟩ := log_one exit_s217 (Exit.hcode_of_env c (by append_env)) hx13
  obtain ⟨f15, g15, e15, _, hx15, hp15⟩ := traced_symBlock (h := hx14) exit_b218 exit_b218_ok
    (Exit.hcode_of_env c (by append_env)) rfl (exit_b218_shape c _ _ _ _ _ (Exit.tailWord c) [])
  rw [withGE_at] at hx15 hp15
  obtain ⟨f16, g16, e16, hx16, hp16⟩ := store_one exit_s223 (Exit.hcode_of_env c (by append_env)) hx15
  have markedLog : Marked exitJumpdests (f14+1) _ f14 _ [.log (UInt256.ofNat 68)] :=
    .single hstep14 ⟨decodeAt_of_code_pc (Exit.hcode_of_env c (by append_env)) rfl exit_s217,⟨_,_,rfl⟩⟩
  rw [hf14] at hp13
  have selected := (Marked.skip hp1).trans (hp2.trans ((Marked.skip hp3).trans (hp4.trans ((Marked.skip hp5).trans (hp6.trans ((Marked.skip hp7).trans (hp8.trans ((Marked.skip hp9).trans ((Marked.skip hp10).trans ((Marked.skip hp11).trans ((Marked.skip hp12).trans ((Marked.skip hp13).trans (markedLog.trans ((Marked.skip hp15).trans (hp16)))))))))))))))
  refine ⟨f16,_,?_,?_,hx16⟩
  · simpa only [exitMarkers,List.cons_append,List.nil_append] using selected
  · exact decodeAt_of_code_pc (Exit.hcode_of_env c (by append_env)) rfl exit_s224

/-- Actual completed deposit suffix selects every required store and its exact log. -/
theorem deposit_suffix (c : XiCall .deposit)
    {fuel : Nat} {aw g : UInt256} {e : Nat} {final : EVM.State} {out : ByteArray}
    (h : X fuel depositJumpdests
      (at_ c (Deposit.st₂ c) (Deposit.mem₀ c) aw g 205 [] e) = .ok (.success final out)) :
    ∃ rest finish, Marked depositJumpdests fuel
      (at_ c (Deposit.st₂ c) (Deposit.mem₀ c) aw g 205 [] e) rest finish depositMarkers ∧
      decodeAt finish = (.STOP,none) ∧ X rest depositJumpdests finish = .ok (.success final out) := by
  obtain ⟨f1, g1, e1, _, hx1, hp1⟩ := traced_symBlock (h := h) deposit_b205 deposit_b205_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b205_shape c (Deposit.st₂ c) _ _ _ _ [])
  rw [withGE_at] at hx1 hp1
  simp only [slotW_touch] at hx1 hp1
  obtain ⟨f2, g2, e2, hx2, hp2⟩ := store_one deposit_s213 (Deposit.hcode_of_env c (by append_env)) hx1
  obtain ⟨f3, g3, e3, _, hx3, hp3⟩ := traced_symBlock (h := hx2) deposit_b214 deposit_b214_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b214_shape c (Deposit.countStore c) _ _ _ _ [])
  rw [withGE_at] at hx3 hp3
  simp only [cdW_touch, cdW_sstore] at hx3 hp3
  obtain ⟨f4, g4, e4, hx4, hp4⟩ := store_one deposit_s227 (Deposit.hcode_of_env c (by append_env)) hx3
  obtain ⟨f5, g5, e5, _, hx5, hp5⟩ := traced_symBlock (h := hx4) deposit_b228 deposit_b228_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b228_shape c _ _ _ _ _ (Deposit.slotBase c) [Deposit.tailWord c])
  rw [withGE_at] at hx5 hp5
  simp only [cdW_touch, cdW_sstore] at hx5 hp5
  obtain ⟨f6, g6, e6, hx6, hp6⟩ := store_one deposit_s235 (Deposit.hcode_of_env c (by append_env)) hx5
  obtain ⟨f7, g7, e7, _, hx7, hp7⟩ := traced_symBlock (h := hx6) deposit_b236 deposit_b236_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b236_shape c _ _ _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx7 hp7
  simp only [cdW_touch, cdW_sstore] at hx7 hp7
  obtain ⟨f8, g8, e8, hx8, hp8⟩ := store_one deposit_s243 (Deposit.hcode_of_env c (by append_env)) hx7
  obtain ⟨f9, g9, e9, _, hx9, hp9⟩ := traced_symBlock (h := hx8) deposit_b244 deposit_b244_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b244_shape c _ _ _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx9 hp9
  simp only [cdW_touch, cdW_sstore] at hx9 hp9
  obtain ⟨f10, g10, e10, hx10, hp10⟩ := store_one deposit_s251 (Deposit.hcode_of_env c (by append_env)) hx9
  obtain ⟨f11, g11, e11, _, hx11, hp11⟩ := traced_symBlock (h := hx10) deposit_b252 deposit_b252_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b252_shape c _ _ _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx11 hp11
  simp only [cdW_touch, cdW_sstore] at hx11 hp11
  obtain ⟨f12, g12, e12, hx12, hp12⟩ := store_one deposit_s259 (Deposit.hcode_of_env c (by append_env)) hx11
  obtain ⟨f13, g13, e13, _, hx13, hp13⟩ := traced_symBlock (h := hx12) deposit_b260 deposit_b260_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b260_shape c _ _ _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx13 hp13
  simp only [cdW_touch, cdW_sstore] at hx13 hp13
  obtain ⟨f14, g14, e14, hx14, hp14⟩ := store_one deposit_s267 (Deposit.hcode_of_env c (by append_env)) hx13
  obtain ⟨f15, g15, e15, _, hx15, hp15⟩ := traced_symBlock (h := hx14) deposit_b268 deposit_b268_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b268_shape c (Deposit.itemStored c) _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx15 hp15
  obtain ⟨f16, g16, e16, hx16, hp16⟩ := traced_copy_success deposit_s272 (Deposit.hcode_of_env c (by append_env)) hx15
  obtain ⟨f17, g17, e17, _, hx17, hp17⟩ := traced_symBlock (h := hx16) deposit_b273 deposit_b273_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b273_shape c (Deposit.itemStored c) _ _ _ _ [Deposit.tailWord c])
  rw [withGE_at] at hx17 hp17
  obtain ⟨f18, g18, e18, cost18, hf18, hstep18, hx18⟩ := log_one deposit_s276 (Deposit.hcode_of_env c (by append_env)) hx17
  obtain ⟨f19, g19, e19, _, hx19, hp19⟩ := traced_symBlock (h := hx18) deposit_b277 deposit_b277_ok
    (Deposit.hcode_of_env c (by append_env)) rfl (deposit_b277_shape c _ _ _ _ _ (Deposit.tailWord c) [])
  rw [withGE_at] at hx19 hp19
  obtain ⟨f20, g20, e20, hx20, hp20⟩ := store_one deposit_s282 (Deposit.hcode_of_env c (by append_env)) hx19
  have markedLog : Marked depositJumpdests (f18+1) _ f18 _ [.log (UInt256.ofNat 184)] :=
    .single hstep18 ⟨decodeAt_of_code_pc (Deposit.hcode_of_env c (by append_env)) rfl deposit_s276,⟨_,_,rfl⟩⟩
  rw [hf18] at hp17
  have selected := (Marked.skip hp1).trans (hp2.trans ((Marked.skip hp3).trans (hp4.trans ((Marked.skip hp5).trans (hp6.trans ((Marked.skip hp7).trans (hp8.trans ((Marked.skip hp9).trans (hp10.trans ((Marked.skip hp11).trans (hp12.trans ((Marked.skip hp13).trans (hp14.trans ((Marked.skip hp15).trans ((Marked.skip hp16).trans ((Marked.skip hp17).trans (markedLog.trans ((Marked.skip hp19).trans (hp20)))))))))))))))))))
  refine ⟨f20,_,?_,?_,hx20⟩
  · simpa only [depositMarkers,List.cons_append,List.nil_append] using selected
  · exact decodeAt_of_code_pc (Deposit.hcode_of_env c (by append_env)) rfl deposit_s283

#print axioms Marked.erase
#print axioms Marked.selected_le
#print axioms store_one
#print axioms exit_suffix
#print axioms deposit_suffix
end Eip8282.Audit.Integrator.ReferenceAppendOccurrences
