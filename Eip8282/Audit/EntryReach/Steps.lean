import Eip8282.Audit.EntryReach.Machine

/-!
# One step of a path, on named machines

`Eip8282.Audit.SymExec` states its lemmas on an arbitrary `EVM.State`. A path
through a pinned runtime is a chain of `at_` machines, so this module restates
each kind of step — a listed block, a `JUMPI` either way, a storage write, a
memory write, a log, and the three halts — as a `Reaches` between two `at_`
machines, with the gas left over as an existential bounded below.

Every lemma here is a corollary of the corresponding `SymExec` lemma plus a
`rfl`-level record identity; none adds a hypothesis about the model.
-/

namespace Eip8282.Audit.EntryReach

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec
open Eip8282.Audit.Jumpdests (opcodeAt)
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Model (Kind)

/-! ## Record identities -/

theorem ofNat_add_one' (n : Nat) : UInt256.ofNat n + ⟨1⟩ = UInt256.ofNat (n + 1) :=
  ofNat_add_ofNat n 1

/-- `replaceStackAndIncrPC` on a named machine is the named machine one byte on. -/
theorem replace_at {kind : Kind} (c : XiCall kind) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (pc : Nat) (stk stk' : Stack UInt256) (e : Nat) :
    (at_ c st mem aw g pc stk e).replaceStackAndIncrPC stk' = at_ c st mem aw g (pc + 1) stk' e := by
  show ({ c.entry with toState := st, memory := mem, activeWords := aw, gasAvailable := g,
                       pc := UInt256.ofNat pc + UInt256.ofNat 1, stack := stk',
                       execLength := e } : EVM.State) = _
  rw [ofNat_add_ofNat]
  rfl

theorem toState_replace_at {kind : Kind} (c : XiCall kind) (st st' : EvmYul.State .EVM)
    (mem : ByteArray) (aw g : UInt256) (pc : Nat) (stk stk' : Stack UInt256) (e : Nat) :
    ({ at_ c st mem aw g pc stk e with toState := st' } : EVM.State).replaceStackAndIncrPC stk'
      = at_ c st' mem aw g (pc + 1) stk' e := by
  show (at_ c st' mem aw g pc stk e).replaceStackAndIncrPC stk' = _
  exact replace_at c st' mem aw g pc stk stk' e

/-- A `JUMPI` that falls through. -/
theorem jumpi_fallthrough_at {kind : Kind} (c : XiCall kind) (st : EvmYul.State .EVM)
    (mem : ByteArray) (aw g : UInt256) (pc : Nat) (stk r : Stack UInt256) (e : Nat) :
    ({ at_ c st mem aw g pc stk e with pc := (at_ c st mem aw g pc stk e).pc + ⟨1⟩, stack := r } :
      EVM.State) = at_ c st mem aw g (pc + 1) r e := by
  show ({ c.entry with toState := st, memory := mem, activeWords := aw, gasAvailable := g,
                       pc := UInt256.ofNat pc + ⟨1⟩, stack := r, execLength := e } : EVM.State) = _
  rw [ofNat_add_one']
  rfl

/-- A `JUMPI` that is taken, to a literal destination. -/
theorem jumpi_taken_at {kind : Kind} (c : XiCall kind) (st : EvmYul.State .EVM)
    (mem : ByteArray) (aw g : UInt256) (pc d : Nat) (stk r : Stack UInt256) (e : Nat) :
    ({ at_ c st mem aw g pc stk e with pc := UInt256.ofNat d, stack := r } : EVM.State)
      = at_ c st mem aw g d r e := rfl

/-- A machine-state update followed by `replaceStackAndIncrPC`, with gas and
count re-attached: the named machine one byte on, carrying the new memory and
active words. The return data and `H_return` must be untouched, which every
non-halting instruction guarantees. -/
theorem withGE_machine_replace_at {kind : Kind} (c : XiCall kind) (st : EvmYul.State .EVM)
    (mem : ByteArray) (aw g : UInt256) (pc : Nat) (stk stk' : Stack UInt256) (e : Nat)
    (μ' : MachineState) (g' : UInt256) (e' : Nat)
    (hret : μ'.returnData = c.entry.returnData) (hH : μ'.H_return = c.entry.H_return) :
    withGE (({ at_ c st mem aw g pc stk e with toMachineState := μ' } : EVM.State).replaceStackAndIncrPC stk')
        g' e'
      = at_ c st μ'.memory μ'.activeWords g' (pc + 1) stk' e' := by
  obtain ⟨gμ, awμ, memμ, rdμ, hrμ⟩ := μ'
  simp only at hret hH
  subst hret hH
  show ({ c.entry with toState := st, memory := memμ, activeWords := awμ, gasAvailable := g',
                       pc := UInt256.ofNat pc + UInt256.ofNat 1, stack := stk',
                       execLength := e' } : EVM.State) = _
  rw [ofNat_add_ofNat]
  rfl

/-- The same for a shared-state update (state and machine state together). -/
theorem withGE_shared_replace_at {kind : Kind} (c : XiCall kind) (st : EvmYul.State .EVM)
    (mem : ByteArray) (aw g : UInt256) (pc : Nat) (stk stk' : Stack UInt256) (e : Nat)
    (sh' : SharedState .EVM) (g' : UInt256) (e' : Nat)
    (hret : sh'.returnData = c.entry.returnData) (hH : sh'.H_return = c.entry.H_return) :
    withGE (({ at_ c st mem aw g pc stk e with toSharedState := sh' } : EVM.State).replaceStackAndIncrPC stk')
        g' e'
      = at_ c sh'.toState sh'.memory sh'.activeWords g' (pc + 1) stk' e' := by
  obtain ⟨st', ⟨gμ, awμ, memμ, rdμ, hrμ⟩⟩ := sh'
  simp only at hret hH
  subst hret hH
  show ({ c.entry with toState := st', memory := memμ, activeWords := awμ, gasAvailable := g',
                       pc := UInt256.ofNat pc + UInt256.ofNat 1, stack := stk',
                       execLength := e' } : EVM.State) = _
  rw [ofNat_add_ofNat]
  rfl

/-! ## The memory and log writers, as functions of the machine components -/

/-- Memory after `MSTORE off v`. -/
def mstoreMem (mem : ByteArray) (off v : UInt256) : ByteArray :=
  v.toByteArray.write 0 mem off.toNat 32

/-- Memory after `MSTORE8 off v`. -/
def mstore8Mem (mem : ByteArray) (off v : UInt256) : ByteArray :=
  (ByteArray.mk #[UInt8.ofNat v.toNat]).write 0 mem off.toNat 1

/-- Memory after `CALLDATACOPY dst src len`. -/
def cdcopyMem (st : EvmYul.State .EVM) (mem : ByteArray) (dst src len : UInt256) : ByteArray :=
  st.executionEnv.calldata.write src.toNat mem dst.toNat len.toNat

/-- Active words after touching `len` bytes at `off`. -/
def mAfter (aw : UInt256) (off len : Nat) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat off len)

/-- The state after `LOG0` of `data`: one anonymous entry from the executing
account appended to the log series. -/
def logged (st : EvmYul.State .EVM) (data : ByteArray) : EvmYul.State .EVM :=
  { st with substate := { st.substate with
      logSeries := st.substate.logSeries.push ⟨st.executionEnv.codeOwner, #[], data⟩ } }

@[simp] theorem executionEnv_logged (st : EvmYul.State .EVM) (data : ByteArray) :
    (logged st data).executionEnv = st.executionEnv := rfl
@[simp] theorem accountMap_logged (st : EvmYul.State .EVM) (data : ByteArray) :
    (logged st data).accountMap = st.accountMap := rfl

/-! ## Listed blocks -/

/-- **A listed block between two named machines.** The shape equation is `rfl`
at every call site (`Eip8282.Audit.EntryReach.Blocks`); what this adds is the
run and the gas. -/
theorem reach_block {kind : Kind} {vj : Array UInt256} {vjNats : List Nat}
    (hvj : ∀ n ∈ vjNats, vj.contains (UInt256.ofNat n) = true)
    {code : ByteArray} (sites : List Site) (hsites : sitesOk code sites = true)
    {c : XiCall kind} {st st' : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc pc' : Nat} {stk stk' : Stack UInt256} {e : Nat}
    (hcode : st.executionEnv.code = code) (hpc : pc = headPc sites)
    (hgas : blockBound sites ≤ g.toNat) (hlen : stk.length + sites.length ≤ 1024)
    (hshape : symBlock vjNats (sites.map Prod.snd) (at_ c st mem aw g pc stk e)
      = some (at_ c st' mem aw g pc' stk' e)) :
    ∃ g' e', g.toNat - blockBound sites ≤ g'.toNat ∧
      Reaches vj sites.length (at_ c st mem aw g pc stk e) (at_ c st' mem aw g' pc' stk' e') := by
  obtain ⟨g', e', hb, hr⟩ := Reaches.of_symBlock hvj sites hsites
    (s := at_ c st mem aw g pc stk e) (by simpa using hcode) (by rw [hpc]; rfl) hgas hlen hshape
  rw [withGE_at] at hr
  exact ⟨g', e', hb, hr⟩

/-! ## `JUMPI` -/

theorem reach_jumpi_taken {kind : Kind} {vj : Array UInt256} {code : ByteArray}
    {c : XiCall kind} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc d : Nat} {cond : UInt256} {r : Stack UInt256} {e : Nat}
    (hsite : opcodeAt code pc = some (.JUMPI, none)) (hcode : st.executionEnv.code = code)
    (hc : cond ≠ ⟨0⟩) (hdest : vj.contains (UInt256.ofNat d) = true)
    (hgas : 10 ≤ g.toNat) (hlen : r.length ≤ 1024) :
    ∃ g' e', g.toNat - 10 ≤ g'.toNat ∧
      Reaches vj 1 (at_ c st mem aw g pc (UInt256.ofNat d :: cond :: r) e)
        (at_ c st mem aw g' d r e') := by
  refine ⟨g - UInt256.ofNat GasConstants.Ghigh, e + 1, ?_, ?_⟩
  · show g.toNat - 10 ≤ (g - UInt256.ofNat 10).toNat
    rw [toNat_sub_ofNat hgas]
  · exact Reaches.of_stepAt fun f => by
      have h := xStepAt_JUMPI_taken (vj := vj) (f := f)
        (decodeAt_of_code_pc (st := at_ c st mem aw g pc (UInt256.ofNat d :: cond :: r) e)
          (by simpa using hcode) rfl hsite)
        rfl hc hdest (by simpa [GasConstants.Ghigh] using hgas) hlen
      rw [jumpi_taken_at, withGE_at] at h
      exact h

theorem reach_jumpi_fallthrough {kind : Kind} {vj : Array UInt256} {code : ByteArray}
    {c : XiCall kind} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc : Nat} {d cond : UInt256} {r : Stack UInt256} {e : Nat}
    (hsite : opcodeAt code pc = some (.JUMPI, none)) (hcode : st.executionEnv.code = code)
    (hc : cond = ⟨0⟩) (hgas : 10 ≤ g.toNat) (hlen : r.length ≤ 1024) :
    ∃ g' e', g.toNat - 10 ≤ g'.toNat ∧
      Reaches vj 1 (at_ c st mem aw g pc (d :: cond :: r) e) (at_ c st mem aw g' (pc + 1) r e') := by
  refine ⟨g - UInt256.ofNat GasConstants.Ghigh, e + 1, ?_, ?_⟩
  · show g.toNat - 10 ≤ (g - UInt256.ofNat 10).toNat
    rw [toNat_sub_ofNat hgas]
  · exact Reaches.of_stepAt fun f => by
      have h := xStepAt_JUMPI_untaken (vj := vj) (f := f)
        (decodeAt_of_code_pc (st := at_ c st mem aw g pc (d :: cond :: r) e)
          (by simpa using hcode) rfl hsite)
        rfl hc (by simpa [GasConstants.Ghigh] using hgas) hlen
      rw [jumpi_fallthrough_at, withGE_at] at h
      exact h

/-! ## `SSTORE` -/

theorem reach_sstore {kind : Kind} {vj : Array UInt256} {code : ByteArray}
    {c : XiCall kind} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc : Nat} {k v : UInt256} {r : Stack UInt256} {e : Nat}
    (hsite : opcodeAt code pc = some (.SSTORE, none)) (hcode : st.executionEnv.code = code)
    (hperm : st.executionEnv.perm = true)
    (hgas : 22100 ≤ g.toNat) (hlen : r.length ≤ 1024) :
    ∃ g' e', g.toNat - 22100 ≤ g'.toNat ∧
      Reaches vj 1 (at_ c st mem aw g pc (k :: v :: r) e)
        (at_ c (st.sstore k v) mem aw g' (pc + 1) r e') := by
  have hle := Csstore_le (at_ c st mem aw g pc (k :: v :: r) e)
  simp only [GasConstants.Gcoldsload, GasConstants.Gsset] at hle
  refine ⟨g - UInt256.ofNat (Csstore (at_ c st mem aw g pc (k :: v :: r) e)), e + 1, ?_, ?_⟩
  · rw [toNat_sub_ofNat (by omega)]; omega
  · exact Reaches.of_stepAt fun f => by
      have h := xStepAt_SSTORE (vj := vj) (f := f)
        (decodeAt_of_code_pc (st := at_ c st mem aw g pc (k :: v :: r) e)
          (by simpa using hcode) rfl hsite)
        rfl (by simpa using hperm) (by simpa [GasConstants.Gcoldsload, GasConstants.Gsset] using hgas) hlen
      rw [toState_replace_at, withGE_at] at h
      exact h

/-! ## The memory writers

Each takes the memory-expansion charge symbolically, bounded by the caller. -/

/-- The quadratic memory cost of `B` words. -/
def memBound (B : Nat) : Nat := GasConstants.Gmemory * B + B * B / 512

theorem Cₘ_eq (a : UInt256) :
    Cₘ a = GasConstants.Gmemory * a.toNat + a.toNat * a.toNat / 512 := rfl

/-- Any memory expansion whose new word count is at most `B` costs at most
`memBound B`. -/
theorem memcost_le_of_M_le {s : EVM.State} {w : Operation .EVM} {B : Nat}
    (hμ : (memoryExpansionCost.μᵢ' s w).toNat ≤ B) :
    memoryExpansionCost s w ≤ memBound B := by
  unfold memoryExpansionCost memBound
  rw [Cₘ_eq, Cₘ_eq]
  have h2 : (memoryExpansionCost.μᵢ' s w).toNat * (memoryExpansionCost.μᵢ' s w).toNat / 512
      ≤ B * B / 512 := Nat.div_le_div_right (Nat.mul_le_mul hμ hμ)
  simp only [GasConstants.Gmemory]
  omega

theorem M_le {aw off len B : Nat} (haw : aw ≤ B) (hspan : (off + len + 31) / 32 ≤ B) :
    MachineState.M aw off len ≤ B := by
  unfold MachineState.M
  split
  · exact haw
  · exact Nat.max_le.mpr ⟨haw, hspan⟩

theorem toNat_mAfter_le {aw : UInt256} {off len B : Nat} (haw : aw.toNat ≤ B)
    (hspan : (off + len + 31) / 32 ≤ B) (hB : B < UInt256.size) :
    (mAfter aw off len).toNat ≤ B := by
  unfold mAfter
  rw [toNat_ofNat_of_lt (Nat.lt_of_le_of_lt (M_le haw hspan) hB)]
  exact M_le haw hspan

theorem reach_mstore {kind : Kind} {vj : Array UInt256} {code : ByteArray}
    {c : XiCall kind} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc : Nat} {off v : UInt256} {r : Stack UInt256} {e : Nat} {B : Nat}
    (hsite : opcodeAt code pc = some (.MSTORE, none)) (hcode : st.executionEnv.code = code)
    (haw : aw.toNat ≤ B) (hspan : (off.toNat + 32 + 31) / 32 ≤ B) (hB : B < UInt256.size)
    {M : Nat} (hM : memBound B + GasConstants.Gverylow = M)
    (hgas : M ≤ g.toNat) (hlen : r.length ≤ 1024) :
    ∃ g' e', g.toNat - M ≤ g'.toNat ∧
      Reaches vj 1 (at_ c st mem aw g pc (off :: v :: r) e)
        (at_ c st (mstoreMem mem off v) (mAfter aw off.toNat 32) g' (pc + 1) r e') := by
  subst hM
  set s := at_ c st mem aw g pc (off :: v :: r) e with hs
  have hμ : (memoryExpansionCost.μᵢ' s .MSTORE).toNat ≤ B := by
    show (mAfter aw off.toNat 32).toNat ≤ B
    exact toNat_mAfter_le haw hspan hB
  have hmc := memcost_le_of_M_le hμ
  have hC : C' (charged s .MSTORE) .MSTORE = GasConstants.Gverylow := C'_MSTORE _
  have hZ : Z vj .MSTORE s = .ok (charged s .MSTORE, C' (charged s .MSTORE) .MSTORE) :=
    Z_memop (Or.inl rfl) rfl rfl (by simp [hs]) (by simpa [hs] using hlen)
      (by rw [hC]; show memoryExpansionCost s .MSTORE + GasConstants.Gverylow ≤ g.toNat; omega)
      (fun h => absurd h (by decide))
  refine ⟨g - UInt256.ofNat (memoryExpansionCost s .MSTORE) - UInt256.ofNat GasConstants.Gverylow,
    e + 1, ?_, ?_⟩
  · rw [toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega), toNat_sub_ofNat (by omega)]
    omega
  · exact Reaches.of_stepAt fun f => by
      have h := xStepAt_of_step (vj := vj) (f := f) (by decide) (by decide)
        (decodeAt_of_code_pc (st := s) (by simpa [hs] using hcode) rfl hsite) hZ
        (step_MSTORE (s := s) rfl)
      rw [hC] at h
      have heq : withGE (({ s with toMachineState := s.toMachineState.mstore off v } : EVM.State).replaceStackAndIncrPC r)
          (g - UInt256.ofNat (memoryExpansionCost s .MSTORE) - UInt256.ofNat GasConstants.Gverylow) (e + 1)
          = at_ c st (mstoreMem mem off v) (mAfter aw off.toNat 32)
              (g - UInt256.ofNat (memoryExpansionCost s .MSTORE) - UInt256.ofNat GasConstants.Gverylow)
              (pc + 1) r (e + 1) :=
        withGE_machine_replace_at c st mem aw g pc (off :: v :: r) r e _ _ _ rfl rfl
      exact Eq.mp (congrArg (XStepAt vj (f + 1) GasConstants.Gverylow s) heq) h

theorem reach_mstore8 {kind : Kind} {vj : Array UInt256} {code : ByteArray}
    {c : XiCall kind} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc : Nat} {off v : UInt256} {r : Stack UInt256} {e : Nat} {B : Nat}
    (hsite : opcodeAt code pc = some (.MSTORE8, none)) (hcode : st.executionEnv.code = code)
    (haw : aw.toNat ≤ B) (hspan : (off.toNat + 1 + 31) / 32 ≤ B) (hB : B < UInt256.size)
    {M : Nat} (hM : memBound B + GasConstants.Gverylow = M)
    (hgas : M ≤ g.toNat) (hlen : r.length ≤ 1024) :
    ∃ g' e', g.toNat - M ≤ g'.toNat ∧
      Reaches vj 1 (at_ c st mem aw g pc (off :: v :: r) e)
        (at_ c st (mstore8Mem mem off v) (mAfter aw off.toNat 1) g' (pc + 1) r e') := by
  subst hM
  set s := at_ c st mem aw g pc (off :: v :: r) e with hs
  have hμ : (memoryExpansionCost.μᵢ' s .MSTORE8).toNat ≤ B := by
    show (mAfter aw off.toNat 1).toNat ≤ B
    exact toNat_mAfter_le haw hspan hB
  have hmc := memcost_le_of_M_le hμ
  have hC : C' (charged s .MSTORE8) .MSTORE8 = GasConstants.Gverylow := C'_MSTORE8 _
  have hZ : Z vj .MSTORE8 s = .ok (charged s .MSTORE8, C' (charged s .MSTORE8) .MSTORE8) :=
    Z_memop (Or.inr (Or.inl rfl)) rfl rfl (by simp [hs]) (by simpa [hs] using hlen)
      (by rw [hC]; show memoryExpansionCost s .MSTORE8 + GasConstants.Gverylow ≤ g.toNat; omega)
      (fun h => absurd h (by decide))
  refine ⟨g - UInt256.ofNat (memoryExpansionCost s .MSTORE8) - UInt256.ofNat GasConstants.Gverylow,
    e + 1, ?_, ?_⟩
  · rw [toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega), toNat_sub_ofNat (by omega)]
    omega
  · exact Reaches.of_stepAt fun f => by
      have h := xStepAt_of_step (vj := vj) (f := f) (by decide) (by decide)
        (decodeAt_of_code_pc (st := s) (by simpa [hs] using hcode) rfl hsite) hZ
        (step_MSTORE8 (s := s) rfl)
      rw [hC] at h
      have heq : withGE (({ s with toMachineState := s.toMachineState.mstore8 off v } : EVM.State).replaceStackAndIncrPC r)
          (g - UInt256.ofNat (memoryExpansionCost s .MSTORE8) - UInt256.ofNat GasConstants.Gverylow) (e + 1)
          = at_ c st (mstore8Mem mem off v) (mAfter aw off.toNat 1)
              (g - UInt256.ofNat (memoryExpansionCost s .MSTORE8) - UInt256.ofNat GasConstants.Gverylow)
              (pc + 1) r (e + 1) :=
        withGE_machine_replace_at c st mem aw g pc (off :: v :: r) r e _ _ _ rfl rfl
      exact Eq.mp (congrArg (XStepAt vj (f + 1) GasConstants.Gverylow s) heq) h

theorem reach_calldatacopy {kind : Kind} {vj : Array UInt256} {code : ByteArray}
    {c : XiCall kind} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc : Nat} {dst src len : UInt256} {r : Stack UInt256} {e : Nat} {B : Nat}
    (hsite : opcodeAt code pc = some (.CALLDATACOPY, none)) (hcode : st.executionEnv.code = code)
    (haw : aw.toNat ≤ B) (hspan : (dst.toNat + len.toNat + 31) / 32 ≤ B) (hB : B < UInt256.size)
    {M : Nat}
    (hM : memBound B + GasConstants.Gverylow + GasConstants.Gcopy * ((len.toNat + 31) / 32) = M)
    (hgas : M ≤ g.toNat) (hlen : r.length ≤ 1024) :
    ∃ g' e', g.toNat - M ≤ g'.toNat ∧
      Reaches vj 1 (at_ c st mem aw g pc (dst :: src :: len :: r) e)
        (at_ c st (cdcopyMem st mem dst src len) (mAfter aw dst.toNat len.toNat) g' (pc + 1) r e') := by
  subst hM
  set s := at_ c st mem aw g pc (dst :: src :: len :: r) e with hs
  have hμ : (memoryExpansionCost.μᵢ' s .CALLDATACOPY).toNat ≤ B := by
    show (mAfter aw dst.toNat len.toNat).toNat ≤ B
    exact toNat_mAfter_le haw hspan hB
  have hmc := memcost_le_of_M_le hμ
  have hC : C' (charged s .CALLDATACOPY) .CALLDATACOPY
      = GasConstants.Gverylow + GasConstants.Gcopy * ((len.toNat + 31) / 32) := C'_CALLDATACOPY _
  have hZ : Z vj .CALLDATACOPY s
      = .ok (charged s .CALLDATACOPY, C' (charged s .CALLDATACOPY) .CALLDATACOPY) :=
    Z_memop (Or.inr (Or.inr (Or.inl rfl))) rfl rfl (by simp [hs]) (by simpa [hs] using hlen)
      (by rw [hC]
          show memoryExpansionCost s .CALLDATACOPY
            + (GasConstants.Gverylow + GasConstants.Gcopy * ((len.toNat + 31) / 32)) ≤ g.toNat
          omega)
      (fun h => absurd h (by decide))
  refine ⟨g - UInt256.ofNat (memoryExpansionCost s .CALLDATACOPY)
      - UInt256.ofNat (C' (charged s .CALLDATACOPY) .CALLDATACOPY),
    e + 1, ?_, ?_⟩
  · rw [hC, toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega), toNat_sub_ofNat (by omega)]
    omega
  · exact Reaches.of_stepAt fun f => by
      have h := xStepAt_of_step (vj := vj) (f := f) (by decide) (by decide)
        (decodeAt_of_code_pc (st := s) (by simpa [hs] using hcode) rfl hsite) hZ
        (step_CALLDATACOPY (s := s) rfl)
      have heq : withGE (({ s with toSharedState := s.toSharedState.calldatacopy dst src len } :
            EVM.State).replaceStackAndIncrPC r)
          (g - UInt256.ofNat (memoryExpansionCost s .CALLDATACOPY)
            - UInt256.ofNat (C' (charged s .CALLDATACOPY) .CALLDATACOPY)) (e + 1)
          = at_ c st (cdcopyMem st mem dst src len) (mAfter aw dst.toNat len.toNat)
              (g - UInt256.ofNat (memoryExpansionCost s .CALLDATACOPY)
                - UInt256.ofNat (C' (charged s .CALLDATACOPY) .CALLDATACOPY))
              (pc + 1) r (e + 1) :=
        withGE_shared_replace_at c st mem aw g pc (dst :: src :: len :: r) r e _ _ _ rfl rfl
      exact Eq.mp (congrArg (XStepAt vj (f + 1) _ s) heq) h

theorem reach_log0 {kind : Kind} {vj : Array UInt256} {code : ByteArray}
    {c : XiCall kind} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc : Nat} {off len : UInt256} {r : Stack UInt256} {e : Nat} {B : Nat}
    (hsite : opcodeAt code pc = some (.LOG0, none)) (hcode : st.executionEnv.code = code)
    (hperm : st.executionEnv.perm = true)
    (haw : aw.toNat ≤ B) (hspan : (off.toNat + len.toNat + 31) / 32 ≤ B) (hB : B < UInt256.size)
    {M : Nat} (hM : memBound B + GasConstants.Glog + GasConstants.Glogdata * len.toNat = M)
    (hgas : M ≤ g.toNat) (hlen : r.length ≤ 1024) :
    ∃ g' e', g.toNat - M ≤ g'.toNat ∧
      Reaches vj 1 (at_ c st mem aw g pc (off :: len :: r) e)
        (at_ c (logged st (mem.readWithPadding off.toNat len.toNat)) mem
          (mAfter aw off.toNat len.toNat) g' (pc + 1) r e') := by
  subst hM
  set s := at_ c st mem aw g pc (off :: len :: r) e with hs
  have hμ : (memoryExpansionCost.μᵢ' s .LOG0).toNat ≤ B := by
    show (mAfter aw off.toNat len.toNat).toNat ≤ B
    exact toNat_mAfter_le haw hspan hB
  have hmc := memcost_le_of_M_le hμ
  have hC : C' (charged s .LOG0) .LOG0 = GasConstants.Glog + GasConstants.Glogdata * len.toNat :=
    C'_LOG0 _
  have hZ : Z vj .LOG0 s = .ok (charged s .LOG0, C' (charged s .LOG0) .LOG0) :=
    Z_memop (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) rfl rfl (by simp [hs]) (by simpa [hs] using hlen)
      (by rw [hC]
          show memoryExpansionCost s .LOG0
            + (GasConstants.Glog + GasConstants.Glogdata * len.toNat) ≤ g.toNat
          omega)
      (fun _ => by simpa [hs] using hperm)
  refine ⟨g - UInt256.ofNat (memoryExpansionCost s .LOG0) - UInt256.ofNat (C' (charged s .LOG0) .LOG0),
    e + 1, ?_, ?_⟩
  · rw [hC, toNat_sub_ofNat (by rw [toNat_sub_ofNat (by omega)]; omega), toNat_sub_ofNat (by omega)]
    omega
  · exact Reaches.of_stepAt fun f => by
      have h := xStepAt_of_step (vj := vj) (f := f) (by decide) (by decide)
        (decodeAt_of_code_pc (st := s) (by simpa [hs] using hcode) rfl hsite) hZ
        (step_LOG0 (s := s) rfl)
      have heq : withGE (({ s with toSharedState := SharedState.logOp off len #[] s.toSharedState } :
            EVM.State).replaceStackAndIncrPC r)
          (g - UInt256.ofNat (memoryExpansionCost s .LOG0)
            - UInt256.ofNat (C' (charged s .LOG0) .LOG0)) (e + 1)
          = at_ c (logged st (mem.readWithPadding off.toNat len.toNat)) mem
              (mAfter aw off.toNat len.toNat)
              (g - UInt256.ofNat (memoryExpansionCost s .LOG0)
                - UInt256.ofNat (C' (charged s .LOG0) .LOG0))
              (pc + 1) r (e + 1) :=
        withGE_shared_replace_at c st mem aw g pc (off :: len :: r) r e _ _ _ rfl rfl
      exact Eq.mp (congrArg (XStepAt vj (f + 1) _ s) heq) h

/-! ## The halts

A halt is not a `Reaches`: it is the instruction `X` stops at. What the
composition into `Ξ` needs is the decode, `Z`'s acceptance, the `StepOk` at any
fuel, and what `H` publishes. -/

/-- Everything `RunUntil.X_success` / `X_revert` and `XiHalts` consume about the
halting instruction, packaged. -/
structure Halt (vj : Array UInt256) (x : EVM.State) (w : Operation .EVM) (out : ByteArray) : Prop where
  decode : decodeAt x = (w, none)
  charge : Z vj w x = .ok (charged x w, C' (charged x w) w)
  step : ∀ f, ∃ post, StepOk (f + 1) (C' (charged x w) w) (w, none) (charged x w) post ∧
    H post.toMachineState w = some out

theorem halt_RETURN {kind : Kind} {vj : Array UInt256} {code : ByteArray}
    {c : XiCall kind} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc : Nat} {off len : UInt256} {r : Stack UInt256} {e : Nat} {B : Nat}
    (hsite : opcodeAt code pc = some (.RETURN, none)) (hcode : st.executionEnv.code = code)
    (haw : aw.toNat ≤ B) (hspan : (off.toNat + len.toNat + 31) / 32 ≤ B) (hB : B < UInt256.size)
    {M : Nat} (hM : memBound B = M) (hgas : M ≤ g.toNat) (hlen : r.length ≤ 1024) :
    Halt vj (at_ c st mem aw g pc (off :: len :: r) e) .RETURN
      (mem.readWithPadding off.toNat len.toNat) := by
  subst hM
  set s := at_ c st mem aw g pc (off :: len :: r) e with hs
  have hμ : (memoryExpansionCost.μᵢ' s .RETURN).toNat ≤ B := by
    show (mAfter aw off.toNat len.toNat).toNat ≤ B
    exact toNat_mAfter_le haw hspan hB
  have hmc := memcost_le_of_M_le hμ
  have hC : C' (charged s .RETURN) .RETURN = 0 := C'_RETURN _
  refine ⟨decodeAt_of_code_pc (st := s) (by simpa [hs] using hcode) rfl hsite, ?_, fun f => ?_⟩
  · exact Z_memop (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) rfl rfl (by simp [hs])
      (by simpa [hs] using hlen)
      (by rw [hC]; show memoryExpansionCost s .RETURN + 0 ≤ g.toNat; omega)
      (fun h => absurd h (by decide))
  · refine ⟨_, stepOk_halt (f := f) (by decide) (step_RETURN (s := s) rfl), ?_⟩
    rfl

theorem halt_REVERT {kind : Kind} {vj : Array UInt256} {code : ByteArray}
    {c : XiCall kind} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc : Nat} {off len : UInt256} {r : Stack UInt256} {e : Nat} {B : Nat}
    (hsite : opcodeAt code pc = some (.REVERT, none)) (hcode : st.executionEnv.code = code)
    (haw : aw.toNat ≤ B) (hspan : (off.toNat + len.toNat + 31) / 32 ≤ B) (hB : B < UInt256.size)
    {M : Nat} (hM : memBound B = M) (hgas : M ≤ g.toNat) (hlen : r.length ≤ 1024) :
    Halt vj (at_ c st mem aw g pc (off :: len :: r) e) .REVERT
      (mem.readWithPadding off.toNat len.toNat) := by
  subst hM
  set s := at_ c st mem aw g pc (off :: len :: r) e with hs
  have hμ : (memoryExpansionCost.μᵢ' s .REVERT).toNat ≤ B := by
    show (mAfter aw off.toNat len.toNat).toNat ≤ B
    exact toNat_mAfter_le haw hspan hB
  have hmc := memcost_le_of_M_le hμ
  have hC : C' (charged s .REVERT) .REVERT = 0 := C'_REVERT _
  refine ⟨decodeAt_of_code_pc (st := s) (by simpa [hs] using hcode) rfl hsite, ?_, fun f => ?_⟩
  · exact Z_memop (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) rfl rfl (by simp [hs])
      (by simpa [hs] using hlen)
      (by rw [hC]; show memoryExpansionCost s .REVERT + 0 ≤ g.toNat; omega)
      (fun h => absurd h (by decide))
  · refine ⟨_, stepOk_halt (f := f) (by decide) (step_REVERT (s := s) rfl), ?_⟩
    rfl

theorem halt_STOP {kind : Kind} {vj : Array UInt256} {code : ByteArray}
    {c : XiCall kind} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256}
    {pc : Nat} {stk : Stack UInt256} {e : Nat}
    (hsite : opcodeAt code pc = some (.STOP, none)) (hcode : st.executionEnv.code = code)
    (hlen : stk.length ≤ 1024) :
    Halt vj (at_ c st mem aw g pc stk e) .STOP .empty := by
  set s := at_ c st mem aw g pc stk e with hs
  have hch : charged s .STOP = s := charged_eq_self (memcost_STOP s)
  refine ⟨decodeAt_of_code_pc (st := s) (by simpa [hs] using hcode) rfl hsite, ?_, fun f => ?_⟩
  · have h := Z_of_facts vj .STOP s (d := 0) (a := 0)
      (by rw [memcost_STOP]; exact Nat.zero_le _) (by rw [hch, C'_STOP]; exact Nat.zero_le _)
      rfl rfl (Nat.zero_le _) (by simp [hs]; omega)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (by decide)
      (fun _ => by simp +decide [W]) (fun h => absurd h (by decide)) (by decide)
    exact h
  · refine ⟨_, stepOk_halt (f := f) (by decide) (step_STOP s), ?_⟩
    rfl

end Eip8282.Audit.EntryReach
