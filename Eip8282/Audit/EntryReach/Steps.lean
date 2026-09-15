import Eip8282.Audit.Execution.State
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















/-! ## The memory and log writers, as functions of the machine components -/














/-! ## Listed blocks -/



/-! ## `JUMPI` -/





/-! ## `SSTORE` -/



/-! ## The memory writers

Each takes the memory-expansion charge symbolically, bounded by the caller. -/



















/-! ## The halts

A halt is not a `Reaches`: it is the instruction `X` stops at. What the
composition into `Ξ` needs is the decode, `Z`'s acceptance, the `StepOk` at any
fuel, and what `H` publishes. -/





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



end Eip8282.Audit.EntryReach
