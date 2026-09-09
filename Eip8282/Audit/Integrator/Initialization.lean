import Eip8282.Audit.Integrator.SystemSpec
import Eip8282.Audit.Integrator.AppendSpec

/-!
# Universal execution of the pinned initialization programs

These results concern actual Ξ execution of init code. Returning a runtime is
not the CREATE code-deposit step or a genesis allocation proof. Initial zero
storage is an explicit input condition, never a desired post-world definition.
-/

namespace Eip8282.Audit.Integrator.Initialization

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall entryState)
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.Model (Kind)
open SystemSpec (HasOwner worldSlot slot_sstore owner_sstore)

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

def initCode : Kind → ByteArray | .deposit => depositInit | .exit => exitInit
def runtime : Kind → ByteArray | .deposit => depositRuntime | .exit => exitRuntime
def runtimeLen : Kind → Nat | .deposit => 628 | .exit => 458
def preamble : Kind → Nat | .deposit => 10 | .exit => 45
def startCopy : Kind → Nat | .deposit => 0 | .exit => 35

/-- Full Ξ inputs, unrestricted except for resource and permission conditions
on the theorems. The init bytes are selected by `kind` in `result`. -/
structure InitCall where
  fuel : Nat
  createdAccounts : Std.TreeSet AccountAddress compare
  genesisBlockHeader : BlockHeader
  blocks : ProcessedBlocks
  world : AccountMap .EVM
  originalWorld : AccountMap .EVM
  gas : UInt256
  substate : Substate
  env : ExecutionEnv .EVM

def InitCall.environment (c : InitCall) (kind : Kind) : ExecutionEnv .EVM :=
  { c.env with code := initCode kind }

def InitCall.entry (c : InitCall) (kind : Kind) : EVM.State :=
  entryState c.createdAccounts c.genesisBlockHeader c.blocks c.world c.originalWorld
    c.gas c.substate (c.environment kind)

def InitCall.result (c : InitCall) (kind : Kind) :=
  Ξ (c.fuel + 1) c.createdAccounts c.genesisBlockHeader c.blocks c.world c.originalWorld
    c.gas c.substate (c.environment kind)

/-- Private record template used only by the existing `at_` machine constructor.
Its runtime pin is not used as an execution assumption: `at_` replaces the whole
State, including its environment, with the actual init state. -/
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
          [⟨0⟩, UInt256.ofNat (runtimeLen kind)] e') .RETURN (runtime kind) := by
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
  refine ⟨g3, e3, h1.trans h2 |>.trans h3, ?_⟩
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

private theorem result_of_return_path (c : InitCall) (kind : Kind)
    {k : Nat} {x : EVM.State} {off len : UInt256} {r : Stack UInt256} {out : ByteArray}
    (hpath : Reaches (D_J (initCode kind) ⟨0⟩) k (c.entry kind) x)
    (hhalt : Halt (D_J (initCode kind) ⟨0⟩) x .RETURN out)
    (hstack : x.stack = off :: len :: r) (hf : k + 2 ≤ c.fuel) :
    ∃ gas, c.result kind = .ok (.success
      (x.createdAccounts, x.accountMap, gas, x.substate) out) := by
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
    UInt256.ofNat (C' (charged x .RETURN) .RETURN), ?_⟩
  unfold InitCall.result Ξ
  change (do
    let r ← X c.fuel (D_J (initCode kind) ⟨0⟩) (c.entry kind)
    match r with
    | .success st o => Except.ok (ExecutionResult.success
        (st.createdAccounts, st.accountMap, st.gasAvailable, st.substate) o)
    | .revert g o => Except.ok (ExecutionResult.revert g o)) = _
  rw [hx]
  rfl

/-- Arbitrary-world deposit initialization executes the entire pinned init
image, returns precisely the pinned runtime, and preserves world and substate. -/
theorem deposit_execution (c : InitCall) (hg : 1000 ≤ c.gas.toNat) (hf : 8 ≤ c.fuel) :
    ∃ gas, c.result .deposit = .ok (.success
      (c.createdAccounts, c.world, gas, c.substate) depositRuntime) := by
  obtain ⟨g, e, hp, hh⟩ := copy_return_path c .deposit (c.entry .deposit).toState
    c.gas 0 rfl hg
  exact result_of_return_path c .deposit hp hh rfl hf

private def exitOpening : List Site :=
  [(0, (.PUSH32, some (INH, 32))), (33, (.PUSH0, none))]

private theorem exitOpening_ok : sitesOk exitInit exitOpening = true := by decide +kernel

private theorem exitOpening_shape (c : InitCall) :
    symBlock [] (exitOpening.map Prod.snd) (c.entry .exit) =
      some (at_ (template c) (c.entry .exit).toState .empty ⟨0⟩ c.gas 34 [⟨0⟩, INH] 0) := rfl

/-- The actual state produced by the constructor's single SSTORE. This helper
is used only to exhibit the operational endpoint; `exit_initializes` below
exports its independent all-slot storage interpretation. -/
def exitStored (c : InitCall) : EvmYul.State .EVM :=
  (c.entry .exit).toState.sstore ⟨0⟩ INH

/-- Arbitrary-world exit initialization executes its store and returns the
complete pinned runtime. Gas covers the cold SSTORE bound and the copy/return. -/
theorem exit_execution (c : InitCall) (hperm : c.env.perm = true)
    (hg : 25000 ≤ c.gas.toNat) (hf : 11 ≤ c.fuel) :
    ∃ gas, c.result .exit = .ok (.success
      ((exitStored c).createdAccounts, (exitStored c).accountMap, gas,
        (exitStored c).substate) exitRuntime) := by
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
  obtain ⟨g3, e3, h3, hh⟩ := copy_return_path c .exit (exitStored c) g2 e2
    (by unfold exitStored; rw [executionEnv_sstore]; rfl) (by gas_omega)
  exact result_of_return_path c .exit (h1.trans h2 |>.trans h3) hh rfl hf

/-- All storage slots after initialization, independently of the concrete
SSTORE expression. Deposit changes none; exit changes only slot zero. -/
def StoragePost (kind : Kind) (c : InitCall) (world : AccountMap .EVM) : Prop :=
  ∀ q, worldSlot world c.env.codeOwner q =
    if kind = .exit ∧ q = ⟨0⟩ then INH else worldSlot c.world c.env.codeOwner q

/-- Universal deposit constructor result and storage frame. No initial owner
or zero-storage hypothesis is needed to prove that the constructor writes none. -/
theorem deposit_initializes (c : InitCall) (hg : 1000 ≤ c.gas.toNat) (hf : 8 ≤ c.fuel) :
    ∃ created world gas substate,
      c.result .deposit = .ok (.success (created, world, gas, substate) depositRuntime) ∧
      StoragePost .deposit c world ∧ substate.logSeries = c.substate.logSeries := by
  obtain ⟨gas, hr⟩ := deposit_execution c hg hf
  refine ⟨_, _, gas, _, hr, ?_, rfl⟩
  intro q
  simp only [reduceCtorEq, false_and, ↓reduceIte]

/-- Universal exit constructor result: its owner survives, precisely slot zero
becomes INHIBITOR, every other slot and other account stays unchanged, no log. -/
theorem exit_initializes (c : InitCall) (hperm : c.env.perm = true)
    (hg : 25000 ≤ c.gas.toNat) (hf : 11 ≤ c.fuel)
    (ho : HasOwner (c.entry .exit).toState) :
    ∃ created world gas substate,
      c.result .exit = .ok (.success (created, world, gas, substate) exitRuntime) ∧
      (∃ acc, world.get? c.env.codeOwner = some acc) ∧
      StoragePost .exit c world ∧ substate.logSeries = c.substate.logSeries ∧
      (∀ addr, addr ≠ c.env.codeOwner → world.get? addr = c.world.get? addr) := by
  obtain ⟨gas, hr⟩ := exit_execution c hperm hg hf
  have he : (exitStored c).executionEnv.codeOwner = c.env.codeOwner := by
    unfold exitStored
    rw [executionEnv_sstore]
    rfl
  have howner := owner_sstore ho ⟨0⟩ INH
  refine ⟨_, _, gas, _, hr, ?_, ?_, ?_, ?_⟩
  · change HasOwner (exitStored c) at howner
    simpa only [HasOwner, he] using howner
  · intro q
    rw [← he, SystemSpec.worldSlot_state]
    unfold exitStored
    rw [slot_sstore ho]
    simp only [executionEnv_sstore, true_and, eq_self]
    change (if q = ⟨0⟩ then INH else slotW (c.entry .exit).toState q) =
      (if q = ⟨0⟩ then INH else worldSlot c.world c.env.codeOwner q)
    rw [show worldSlot c.world c.env.codeOwner q = slotW (c.entry .exit).toState q
      from SystemSpec.worldSlot_state (c.entry .exit).toState q]
  · exact AppendSpec.logs_sstore _ _ _
  · intro addr hn
    exact AppendSpec.other_account_sstore _ _ _ addr hn

/-- Only the four initial controls are constrained; other initial storage is
irrelevant to the constructor's control values. This is an input condition. -/
def ZeroControls (c : InitCall) : Prop :=
  ∀ q : UInt256, q.toNat < 4 → worldSlot c.world c.env.codeOwner q = ⟨0⟩

theorem deposit_enabled (c : InitCall) (hg : 1000 ≤ c.gas.toNat) (hf : 8 ≤ c.fuel)
    (hz : ZeroControls c) :
    ∃ created world gas substate,
      c.result .deposit = .ok (.success (created, world, gas, substate) depositRuntime) ∧
      (∀ q : UInt256, q.toNat < 4 → worldSlot world c.env.codeOwner q = ⟨0⟩) ∧
      worldSlot world c.env.codeOwner ⟨0⟩ ≠ INH := by
  obtain ⟨gas, hr⟩ := deposit_execution c hg hf
  exact ⟨_, _, gas, _, hr, hz, by rw [hz ⟨0⟩ (by decide)]; decide⟩

theorem exit_inhibited (c : InitCall) (hperm : c.env.perm = true)
    (hg : 25000 ≤ c.gas.toNat) (hf : 11 ≤ c.fuel)
    (ho : HasOwner (c.entry .exit).toState) (hz : ZeroControls c) :
    ∃ created world gas substate,
      c.result .exit = .ok (.success (created, world, gas, substate) exitRuntime) ∧
      worldSlot world c.env.codeOwner ⟨0⟩ = INH ∧
      (∀ q : UInt256, 0 < q.toNat → q.toNat < 4 →
        worldSlot world c.env.codeOwner q = ⟨0⟩) := by
  obtain ⟨created, world, gas, substate, hr, _, hs, _, _⟩ := exit_initializes c hperm hg hf ho
  refine ⟨_, _, _, _, hr, ?_, ?_⟩
  · rw [hs]; simp
  · intro q hpos hlt
    have hn : q ≠ ⟨0⟩ := by intro he; subst q; exact Nat.lt_irrefl _ hpos
    rw [hs, if_neg (by simp [hn]), hz q hlt]

#print axioms deposit_initializes
#print axioms exit_initializes
#print axioms deposit_enabled
#print axioms exit_inhibited

end Eip8282.Audit.Integrator.Initialization
