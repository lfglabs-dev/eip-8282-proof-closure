import Eip8282.Audit.Integrator.DirectInitialization

/-!
# Successful actual initialization with code-deposit resources

The existing initializer paths erase their remaining-gas bounds. The small
symbolic paths below retain those bounds and compose the actual Lambda
settlement. No successful-result premise, canonical deployment identity or
protocol-history assumption supplies the result. Gas bounds are conservative
pinned-evaluator resources, not minimum deployment-transaction gas estimates.
-/
namespace Eip8282.Audit.Integrator.InitializerProgress

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall entryState)
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.Model (Kind)
open SystemSpec (HasOwner worldSlot slot_sstore owner_sstore)
open Initialization

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

def executionEnvelope : Kind → Nat | .deposit => 1000 | .exit => 25000
def executionSteps : Kind → Nat | .deposit => 8 | .exit => 11

private def template (c : InitCall) : XiCall .deposit :=
  { fuel := c.fuel, createdAccounts := c.createdAccounts,
    genesisBlockHeader := c.genesisBlockHeader, blocks := c.blocks,
    σ := c.world, σ₀ := c.originalWorld, gas := c.gas, substate := c.substate,
    env := { c.env with code := depositRuntime }, code_pinned := rfl }

private theorem Z_CODECOPY {vj : Array UInt256} {s : EVM.State}
    (hlen : 3 ≤ s.stack.length) (hover : s.stack.length - 3 ≤ 1024)
    (hg : memoryExpansionCost s .CODECOPY + C' (charged s .CODECOPY) .CODECOPY ≤
      s.gasAvailable.toNat) :
    Z vj .CODECOPY s = .ok (charged s .CODECOPY, C' (charged s .CODECOPY) .CODECOPY) := by
  apply Z_of_facts vj .CODECOPY s (d := 3) (a := 0) (by omega)
    (by change _ ≤ (s.gasAvailable - UInt256.ofNat _).toNat
        rw [toNat_sub_ofNat (by omega)]; omega) rfl rfl hlen (by omega)
  · intro h; cases h
  · intro h; cases h
  · decide
  · intro _; simp +decide [W]
  · intro h; cases h
  · decide

private theorem step_CODECOPY {s : EVM.State} {dst src len : UInt256} {r : Stack UInt256}
    (hs : s.stack = dst :: src :: len :: r) :
    EvmYul.step (τ := .EVM) .CODECOPY none s =
      .ok (({ s with toSharedState := s.toSharedState.codeCopy dst src len } : EVM.State).replaceStackAndIncrPC r) := by
  obtain ⟨sh, pc, stk, ex⟩ := s
  simp only at hs
  subst hs
  rfl

private theorem xStepAt_CODECOPY {vj : Array UInt256} {s : EVM.State} {f : Nat}
    {dst src len : UInt256} {r : Stack UInt256}
    (hd : decodeAt s = (.CODECOPY, none)) (hs : s.stack = dst :: src :: len :: r)
    (hz : Z vj .CODECOPY s = .ok (charged s .CODECOPY, C' (charged s .CODECOPY) .CODECOPY)) :
    XStepAt vj (f + 1) (C' (charged s .CODECOPY) .CODECOPY) s
      (withGE (({ s with toSharedState := s.toSharedState.codeCopy dst src len } : EVM.State).replaceStackAndIncrPC r)
        (s.gasAvailable - UInt256.ofNat (memoryExpansionCost s .CODECOPY) -
          UInt256.ofNat (C' (charged s .CODECOPY) .CODECOPY)) (s.execLength + 1)) := by
  refine ⟨charged s .CODECOPY, ?_, ?_, ?_⟩
  · rw [hd]; exact hz
  · rw [hd]
    obtain ⟨sh, pc, stk, ex⟩ := s
    simp only at hs
    subst hs
    rfl
  · rw [hd]; rfl

private def copyMem (st : EvmYul.State .EVM) (mem : ByteArray) (dst src len : UInt256) :=
  st.executionEnv.code.write src.toNat mem dst.toNat len.toNat

private theorem reach_codecopy {kind : Kind} {vj : Array UInt256} {code : ByteArray}
    {c : XiCall kind} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc : Nat} {dst src len : UInt256} {r : Stack UInt256} {e : Nat} {B : Nat}
    (hsite : opcodeAt code pc = some (.CODECOPY, none)) (hcode : st.executionEnv.code = code)
    (haw : aw.toNat ≤ B) (hspan : (dst.toNat + len.toNat + 31) / 32 ≤ B) (hB : B < UInt256.size)
    {M : Nat}
    (hM : memBound B + GasConstants.Gverylow + GasConstants.Gcopy * ((len.toNat + 31) / 32) = M)
    (hgas : M ≤ g.toNat) (hlen : r.length ≤ 1024) :
    ∃ g' e', g.toNat - M ≤ g'.toNat ∧
      Reaches vj 1 (at_ c st mem aw g pc (dst :: src :: len :: r) e)
        (at_ c st (copyMem st mem dst src len) (mAfter aw dst.toNat len.toNat) g' (pc + 1) r e') := by
  subst hM
  set s := at_ c st mem aw g pc (dst :: src :: len :: r) e with hs
  have hμ : (memoryExpansionCost.μᵢ' s .CODECOPY).toNat ≤ B := by
    show (mAfter aw dst.toNat len.toNat).toNat ≤ B
    exact toNat_mAfter_le haw hspan hB
  have hmc := memcost_le_of_M_le hμ
  have hC : C' (charged s .CODECOPY) .CODECOPY
      = GasConstants.Gverylow + GasConstants.Gcopy * ((len.toNat + 31) / 32) := by simp +decide [C', hs]
  have hZ : Z vj .CODECOPY s
      = .ok (charged s .CODECOPY, C' (charged s .CODECOPY) .CODECOPY) :=
    Z_CODECOPY (by simp [hs]) (by simpa [hs] using hlen)
      (by rw [hC]
          show memoryExpansionCost s .CODECOPY
            + (GasConstants.Gverylow + GasConstants.Gcopy * ((len.toNat + 31) / 32)) ≤ g.toNat
          omega)
  refine ⟨g - UInt256.ofNat (memoryExpansionCost s .CODECOPY)
      - UInt256.ofNat (C' (charged s .CODECOPY) .CODECOPY),
    e + 1, ?_, ?_⟩
  · rw [hC, toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega), toNat_sub_ofNat (by omega)]
    omega
  · exact Reaches.of_stepAt fun f => by
      have h := xStepAt_CODECOPY (vj := vj) (f := f)
        (decodeAt_of_code_pc (st := s) (by simpa [hs] using hcode) rfl hsite) rfl hZ
      have heq : withGE (({ s with toSharedState := s.toSharedState.codeCopy dst src len } :
            EVM.State).replaceStackAndIncrPC r)
          (g - UInt256.ofNat (memoryExpansionCost s .CODECOPY)
            - UInt256.ofNat (C' (charged s .CODECOPY) .CODECOPY)) (e + 1)
          = at_ c st (copyMem st mem dst src len) (mAfter aw dst.toNat len.toNat)
              (g - UInt256.ofNat (memoryExpansionCost s .CODECOPY)
                - UInt256.ofNat (C' (charged s .CODECOPY) .CODECOPY))
              (pc + 1) r (e + 1) :=
        withGE_shared_replace_at c st mem aw g pc (dst :: src :: len :: r) r e _ _ _ rfl rfl
      exact Eq.mp (congrArg (XStepAt vj (f + 1) _ s) heq) h


private def copyBlock (kind : Kind) : List Site :=
  [(startCopy kind, (.PUSH2, some (UInt256.ofNat (runtimeLen kind), 2))),
   (startCopy kind + 3, (.DUP1, none)),
   (startCopy kind + 4, (.PUSH1, some (UInt256.ofNat (preamble kind), 1))),
   (startCopy kind + 6, (.PUSH0, none))]

private theorem copyBlock_ok (kind : Kind) : sitesOk (initCode kind) (copyBlock kind) = true := by
  cases kind <;> decide +kernel

private theorem copyBlock_shape (c : InitCall) (kind : Kind) (st : EvmYul.State .EVM)
    (g : UInt256) (e : Nat) :
    symBlock [] ((copyBlock kind).map Prod.snd)
      (at_ (template c) st .empty ⟨0⟩ g (startCopy kind) [] e) =
      some (at_ (template c) st .empty ⟨0⟩ g (startCopy kind + 7)
        [⟨0⟩, UInt256.ofNat (preamble kind), UInt256.ofNat (runtimeLen kind),
          UInt256.ofNat (runtimeLen kind)] e) := by
  cases kind <;> rfl

private def retBlock (kind : Kind) : List Site :=
  [(startCopy kind + 8, (.PUSH0, none))]

private theorem retBlock_ok (kind : Kind) : sitesOk (initCode kind) (retBlock kind) = true := by
  cases kind <;> decide +kernel

private theorem retBlock_shape (c : InitCall) (kind : Kind) (st : EvmYul.State .EVM)
    (mem : ByteArray) (aw g : UInt256) (e : Nat) :
    symBlock [] ((retBlock kind).map Prod.snd)
      (at_ (template c) st mem aw g (startCopy kind + 8) [UInt256.ofNat (runtimeLen kind)] e) =
      some (at_ (template c) st mem aw g (startCopy kind + 9)
        [⟨0⟩, UInt256.ofNat (runtimeLen kind)] e) := by
  cases kind <;> rfl

private theorem write_empty_slice (src : ByteArray) (off len : Nat)
    (hl : 0 < len) (hb : off + len ≤ src.size) :
    src.write off .empty 0 len = src.extract off (off + len) := by
  unfold ByteArray.write
  rw [if_neg (by omega), if_neg (by omega)]
  have hm : min len (src.size - off) = len := by omega
  simp only [hm, ByteArray.size_empty, Nat.zero_add, Nat.zero_min, Nat.zero_sub]
  have hz : ffi.ByteArray.zeroes (⟨((0 : Nat) : BitVec System.Platform.numBits)⟩ : USize) = .empty := rfl
  rw [hz]
  simp only [ByteArray.append_empty]
  unfold ByteArray.extract
  rw [Nat.add_sub_cancel_left]
  rfl

private theorem runtime_size (kind : Kind) : (runtime kind).size = runtimeLen kind := by
  cases kind <;> rfl

private theorem copied_runtime (kind : Kind) :
    (initCode kind).write (preamble kind) .empty 0 (runtimeLen kind) = runtime kind := by
  rw [write_empty_slice _ _ _ (by cases kind <;> decide) (by cases kind <;> decide)]
  apply ByteArray.ext
  apply Array.ext'
  simp only [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  cases kind <;> rfl

private theorem returned_runtime (kind : Kind) :
    (runtime kind).readWithPadding 0 (runtimeLen kind) = runtime kind := by
  rw [ByteArray.readWithPadding_eq_extract _ 0 _ (by cases kind <;> decide)
    (by cases kind <;> decide) (by rw [runtime_size]; omega)]
  apply ByteArray.ext
  simp only [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by rw [ByteArray.size_data, runtime_size]; omega)

private theorem copy_return_path (c : InitCall) (kind : Kind) (st : EvmYul.State .EVM)
    (g : UInt256) (e : Nat) (hcode : st.executionEnv.code = initCode kind)
    (hg : 1000 ≤ g.toNat) :
    ∃ g' e',
      Reaches (D_J (initCode kind) ⟨0⟩) 6
        (at_ (template c) st .empty ⟨0⟩ g (startCopy kind) [] e)
        (at_ (template c) st (runtime kind)
          (mAfter ⟨0⟩ 0 (runtimeLen kind)) g' (startCopy kind + 9)
          [⟨0⟩, UInt256.ofNat (runtimeLen kind)] e') ∧
      Halt (D_J (initCode kind) ⟨0⟩)
        (at_ (template c) st (runtime kind)
          (mAfter ⟨0⟩ 0 (runtimeLen kind)) g' (startCopy kind + 9)
          [⟨0⟩, UInt256.ofNat (runtimeLen kind)] e') .RETURN (runtime kind) ∧
      g.toNat - 136 ≤ g'.toNat ∧
      memoryExpansionCost (at_ (template c) st (runtime kind)
        (mAfter ⟨0⟩ 0 (runtimeLen kind)) g' (startCopy kind + 9)
        [⟨0⟩, UInt256.ofNat (runtimeLen kind)] e') .RETURN ≤ 60 := by
  have hvj : ∀ n ∈ ([] : List Nat), (D_J (initCode kind) ⟨0⟩).contains (UInt256.ofNat n) = true := by simp
  obtain ⟨g1, e1, hg1, h1⟩ := block_step hvj (copyBlock kind) (copyBlock_ok kind)
    (show blockBound (copyBlock kind) = 11 by cases kind <;> rfl)
    (show (copyBlock kind).length = 4 by rfl)
    (copyBlock_shape c kind st g e) hcode rfl (by omega) (by decide)
  have hlen : (UInt256.ofNat (runtimeLen kind)).toNat = runtimeLen kind := by cases kind <;> rfl
  have hcost : memBound 20 + GasConstants.Gverylow +
      GasConstants.Gcopy * ((runtimeLen kind + 31) / 32) ≤ 123 := by cases kind <;> decide
  obtain ⟨g2, e2, hg2, h2⟩ := reach_codecopy (vj := D_J (initCode kind) ⟨0⟩)
    (c := template c) (st := st) (mem := .empty) (aw := ⟨0⟩) (g := g1)
    (pc := startCopy kind + 7) (dst := ⟨0⟩) (src := UInt256.ofNat (preamble kind))
    (len := UInt256.ofNat (runtimeLen kind)) (r := [UInt256.ofNat (runtimeLen kind)]) (e := e1)
    (B := 20) (by cases kind <;> decide +kernel) hcode (by decide)
    (by cases kind <;> decide) (by decide) rfl (by rw [hlen]; gas_omega) (by simp)
  have hmem : copyMem st .empty ⟨0⟩ (UInt256.ofNat (preamble kind))
      (UInt256.ofNat (runtimeLen kind)) = runtime kind := by
    unfold copyMem
    rw [hcode]
    have hp : (UInt256.ofNat (preamble kind)).toNat = preamble kind := by cases kind <;> rfl
    rw [hp, hlen]
    exact copied_runtime kind
  rw [hmem, hlen] at h2
  rw [hlen] at hg2
  obtain ⟨g3, e3, hg3, h3⟩ := block_step hvj (retBlock kind) (retBlock_ok kind)
    (show blockBound (retBlock kind) = 2 by rfl)
    (show (retBlock kind).length = 1 by rfl)
    (retBlock_shape c kind st (runtime kind) (mAfter ⟨0⟩ 0 (runtimeLen kind)) g2 e2)
    hcode rfl (by gas_omega) (by simp)
  refine ⟨g3, e3, h1.trans h2 |>.trans h3, ?_, by gas_omega, ?_⟩
  ·
    have hh := halt_RETURN (vj := D_J (initCode kind) ⟨0⟩) (c := template c)
      (st := st) (mem := runtime kind) (aw := mAfter ⟨0⟩ 0 (runtimeLen kind))
      (g := g3) (pc := startCopy kind + 9) (off := ⟨0⟩)
      (len := UInt256.ofNat (runtimeLen kind)) (r := []) (e := e3) (B := 20)
      (by cases kind <;> decide +kernel) hcode
      (by cases kind <;> decide) (by cases kind <;> decide) (by decide)
      (show memBound 20 = 60 by rfl) (by gas_omega) (by decide)
    rw [hlen] at hh
    rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, returned_runtime] at hh
    exact hh
  · apply memcost_le_of_M_le (B := 20)
    show (mAfter (mAfter ⟨0⟩ 0 (runtimeLen kind)) 0
      (UInt256.ofNat (runtimeLen kind)).toNat).toNat ≤ 20
    apply toNat_mAfter_le
    · cases kind <;> decide
    · cases kind <;> decide
    · decide


private theorem result_of_return_path (c : InitCall) (kind : Kind)
    {k : Nat} {x : EVM.State} {off len : UInt256} {r : Stack UInt256} {out : ByteArray}
    (hpath : Reaches (D_J (initCode kind) ⟨0⟩) k (c.entry kind) x)
    (hhalt : Halt (D_J (initCode kind) ⟨0⟩) x .RETURN out)
    (hstack : x.stack = off :: len :: r) (hf : k + 2 ≤ c.fuel)
    (hmc : memoryExpansionCost x .RETURN ≤ 60) (hg : 60 ≤ x.gasAvailable.toNat) :
    ∃ gas, c.result kind = .ok (.success
      (x.createdAccounts, x.accountMap, gas, x.substate) out) ∧
      x.gasAvailable.toNat - 60 ≤ gas.toNat := by
  obtain ⟨tr, hrun⟩ := hpath (c.fuel - k - 1)
  rw [show c.fuel - k - 1 + 1 + k = c.fuel by omega] at hrun
  have hrun' := Eip8282.Audit.XiTransport.runUntil_of_xRuns hrun
    (RunUntil.stop (by rw [hhalt.decode]; exact stopOrHalting_of_halting EntryReach.halting_RETURN))
  obtain ⟨post, hstep, hH⟩ := hhalt.step (c.fuel - k - 2)
  have hc := stepOk_halt (f := c.fuel - k - 2) (by decide : .RETURN ∈ allOps)
    (Eip8282.Audit.SymExec.step_RETURN hstack)
  have heq := Step.deterministic_ok hstep hc
  subst post
  rw [show c.fuel - k - 2 + 1 = c.fuel - k - 1 by omega] at hstep
  have hx := hrun'.X_success hhalt.decode hhalt.charge hstep hH
    (by decide : (Operation.RETURN : Operation .EVM) ≠ .REVERT)
  refine ⟨x.gasAvailable - UInt256.ofNat (memoryExpansionCost x .RETURN) -
    UInt256.ofNat (C' (charged x .RETURN) .RETURN), ?_, ?_⟩
  · unfold InitCall.result Ξ
    change (do
      let r ← X c.fuel (D_J (initCode kind) ⟨0⟩) (c.entry kind)
      match r with
      | .success st o => Except.ok (ExecutionResult.success
          (st.createdAccounts, st.accountMap, st.gasAvailable, st.substate) o)
      | .revert g o => Except.ok (ExecutionResult.revert g o)) = _
    rw [hx]
    rfl
  · rw [C'_RETURN]
    rw [toNat_sub_ofNat (Nat.zero_le _)]
    simp only [Nat.sub_zero]
    rw [toNat_sub_ofNat (by omega)]
    omega


/-- Arbitrary-world deposit initialization executes the entire pinned init
image, returns precisely the pinned runtime, and preserves world and substate. -/
theorem deposit_execution_budget (c : InitCall) (hg : 1000 ≤ c.gas.toNat) (hf : 8 ≤ c.fuel) :
    ∃ gas, c.result .deposit = .ok (.success
      (c.createdAccounts, c.world, gas, c.substate) depositRuntime) ∧
      c.gas.toNat - 1000 ≤ gas.toNat := by
  obtain ⟨g, e, hp, hh, hgb, hmc⟩ := copy_return_path c .deposit (c.entry .deposit).toState
    c.gas 0 rfl hg
  obtain ⟨gas, hr, hgas⟩ := result_of_return_path c .deposit hp hh rfl hf hmc
    (by change 60 ≤ g.toNat; omega)
  exact ⟨gas, hr, by change g.toNat - 60 ≤ gas.toNat at hgas; omega⟩

private def exitOpening : List Site :=
  [(0, (.PUSH32, some (INH, 32))), (33, (.PUSH0, none))]

private theorem exitOpening_ok : sitesOk exitInit exitOpening = true := by decide +kernel

private theorem exitOpening_shape (c : InitCall) :
    symBlock [] (exitOpening.map Prod.snd) (c.entry .exit) =
      some (at_ (template c) (c.entry .exit).toState .empty ⟨0⟩ c.gas 34 [⟨0⟩, INH] 0) := rfl

/-- Arbitrary-world exit initialization executes its store and returns the
complete pinned runtime. Gas covers the cold SSTORE bound and the copy/return. -/
theorem exit_execution_budget (c : InitCall) (hperm : c.env.perm = true)
    (hg : 25000 ≤ c.gas.toNat) (hf : 11 ≤ c.fuel) :
    ∃ gas, c.result .exit = .ok (.success
      ((exitStored c).createdAccounts, (exitStored c).accountMap, gas,
        (exitStored c).substate) exitRuntime) ∧
      c.gas.toNat - 25000 ≤ gas.toNat := by
  have hvj : ∀ n ∈ ([] : List Nat), (D_J exitInit ⟨0⟩).contains (UInt256.ofNat n) = true := by simp
  obtain ⟨g1, e1, hg1, h1⟩ := block_step hvj exitOpening exitOpening_ok
    (show blockBound exitOpening = 5 by rfl) (show exitOpening.length = 2 by rfl)
    (show symBlock [] (exitOpening.map Prod.snd)
      (at_ (template c) (c.entry .exit).toState .empty ⟨0⟩ c.gas 0 [] 0) =
      some (at_ (template c) (c.entry .exit).toState .empty ⟨0⟩ c.gas 34 [⟨0⟩, INH] 0)
      from exitOpening_shape c)
    rfl rfl (by omega) (by decide)
  obtain ⟨g2, e2, hg2, h2⟩ := reach_sstore (vj := D_J exitInit ⟨0⟩)
    (c := template c) (st := (c.entry .exit).toState) (mem := .empty) (aw := ⟨0⟩)
    (g := g1) (pc := 34) (k := ⟨0⟩) (v := INH) (r := []) (e := e1)
    (by decide +kernel : opcodeAt exitInit 34 = some (.SSTORE, none)) rfl
    hperm (by gas_omega) (by decide)
  obtain ⟨g3, e3, h3, hh, hg3, hmc⟩ := copy_return_path c .exit (exitStored c) g2 e2
    (by unfold exitStored; rw [executionEnv_sstore]; rfl) (by gas_omega)
  obtain ⟨gas, hr, hgas⟩ := result_of_return_path c .exit (h1.trans h2 |>.trans h3) hh rfl hf hmc
    (by change 60 ≤ g3.toNat; gas_omega)
  exact ⟨gas, hr, by change g3.toNat - 60 ≤ gas.toNat at hgas; gas_omega⟩


/-- Execution envelope plus the exact 200-gas-per-byte code-deposit charge. -/
def creationGas : Kind → Nat | .deposit => 126600 | .exit => 116600

/-- An absent destination and sufficient remaining gas pass every actual
code-deposit guard for the pinned runtime. -/
theorem deposit_guards (kind : Kind) (c : CreationSettlement.Context)
    (a : AccountAddress) (gas : UInt256)
    (ha : c.world.get? a = none)
    (hg : 200 * runtimeLen kind ≤ gas.toNat) :
    c.depositFailure a gas (runtime kind) = false := by
  unfold CreationSettlement.Context.depositFailure
  rw [ha, runtime_size]
  have hf : ¬ gas.toNat < GasConstants.Gcodedeposit * runtimeLen kind := by
    change ¬ gas.toNat < 200 * runtimeLen kind
    omega
  have hs : ¬ runtimeLen kind > 24576 := by cases kind <;> decide
  have hp : (runtime kind)[0]? ≠ some 0xef := by cases kind <;> decide +kernel
  simp [hf, hs, hp]

/-- Both init paths expose their actual returned world and log series together
with a lower remaining-gas bound. The exit owner's presence is needed only for
the independent storage interpretation. -/
theorem execution_budget (kind : Kind) (c : Initialization.InitCall)
    (hg : executionEnvelope kind ≤ c.gas.toNat)
    (hf : executionSteps kind ≤ c.fuel)
    (hp : kind = .exit → c.env.perm = true)
    (ho : kind = .exit → HasOwner (c.entry .exit).toState) :
    ∃ created world gas substate,
      c.result kind = .ok (.success (created, world, gas, substate) (runtime kind)) ∧
      c.gas.toNat - executionEnvelope kind ≤ gas.toNat ∧
      Initialization.StoragePost kind c world ∧
      substate.logSeries = c.substate.logSeries := by
  cases kind with
  | deposit =>
    obtain ⟨gas, hr, hb⟩ := deposit_execution_budget c hg hf
    refine ⟨_, _, gas, _, hr, hb, ?_, rfl⟩
    intro q
    simp only [reduceCtorEq, false_and, ↓reduceIte]
  | exit =>
    obtain ⟨gas, hr, hb⟩ := exit_execution_budget c (hp rfl) hg hf
    obtain ⟨cr, w, g, ss, he, _, hs, hl, _⟩ := Initialization.exit_initializes c (hp rfl) hg hf (ho rfl)
    have eq : (exitStored c).createdAccounts = cr ∧ (exitStored c).accountMap = w ∧
        gas = g ∧ (exitStored c).substate = ss := by
      simpa only [Except.ok.injEq, ExecutionResult.success.injEq, Prod.mk.injEq, and_true]
        using hr.symm.trans he
    rcases eq with ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨_, _, _, _, he, hb, hs, hl⟩

/-- Actual successful Lambda installation under independent stronger resources.
Canonical address identity, deployment transaction admission and preservation
through pre-activation calls remain separate protocol obligations. -/
theorem initializes_success (kind : Kind)
    (c : CreationSettlement.Context) (preimage : ByteArray) (steps : Nat)
    (hi : c.init = Initialization.initCode kind)
    (hd : DirectInitialization.Domain kind c preimage steps)
    (hg : creationGas kind ≤ c.gas.toNat) :
    ∃ created world gas substate,
      c.result = .ok (CreationSettlement.address preimage,
        created, world, gas, substate, true, ByteArray.empty) ∧
      DirectInitialization.Observed kind c preimage
        (CreationSettlement.address preimage) world substate := by
  let init := c.initCall (CreationSettlement.address preimage) steps
  have hgas : executionEnvelope kind ≤ init.gas.toNat := by
    change executionEnvelope kind ≤ c.gas.toNat
    cases kind <;> simp only [creationGas, executionEnvelope] at hg ⊢ <;> omega
  have hf : executionSteps kind ≤ init.fuel := by
    cases kind with
    | deposit => exact hd.resources.2
    | exit => exact hd.resources.2.2.1
  have hp : kind = .exit → init.env.perm = true := by
    intro he
    subst kind
    exact hd.resources.1
  have ho : kind = .exit → HasOwner (init.entry .exit).toState := by
    intro he
    subst kind
    exact CreationSettlement.entry_hasOwner c _ steps .exit hd.resources.2.2.2
  obtain ⟨ic, iw, ig, ia, hr, hb, _, _⟩ := execution_budget kind init hgas hf hp ho
  have he : c.execution (CreationSettlement.address preimage) =
      .ok (.success (ic, iw, ig, ia) (runtime kind)) := by
    rw [CreationSettlement.execution_eq_initialization c _ steps kind hd.fuel_eq hd.no_collision hi]
    exact hr
  have hremaining : 200 * runtimeLen kind ≤ ig.toNat := by
    change c.gas.toNat - executionEnvelope kind ≤ ig.toNat at hb
    cases kind <;> simp only [creationGas, runtimeLen, executionEnvelope] at hg hb ⊢ <;> omega
  have hguards := deposit_guards kind c _ ig hd.absent hremaining
  have result := CreationSettlement.installs_of_execution c hd.preimage_eq he hguards
  exact ⟨_, _, _, _, result,
    DirectInitialization.pinned kind c preimage steps hi hd _ _ _ _ _ _ result⟩

#print axioms deposit_execution_budget
#print axioms exit_execution_budget
#print axioms deposit_guards
#print axioms execution_budget
#print axioms initializes_success

end Eip8282.Audit.Integrator.InitializerProgress
