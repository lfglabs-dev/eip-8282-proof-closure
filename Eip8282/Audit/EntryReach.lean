import Eip8282.Audit.EntryReach.Deposit
import Eip8282.Audit.EntryReach.Exit
import Eip8282.Audit.UniversalBoundary

/-!
# ENTRY-REACH: from `c.entry` to the endpoint partition

`Eip8282.Audit.EntryReach.Deposit` and `.Exit` follow every complete `Ξ` message
call into the two pinned runtimes from the entry machine to the halting
instruction it reaches, one theorem per endpoint. This module turns those
completed paths into what the boundary layer consumes:

* `xiHalts_of_ends` — a completed path *is* a halting witness (`XiHalts`), given
  fuel for its step count. This is the object `TerminationClosure` asks for.
* `observe_of_ends` — the observation of the whole `Ξ` call is the exit
  instruction's own, at the bytes the path names. No `EndpointAgrees`, no `hend`,
  no premise about the model: `observation_of_halts` applied to the witness.
* `Deposit.halts` / `Exit.halts` — the branch words partition every call with
  write permission into the listed endpoints, so every such call halts.

What remains open after this slice is stated in the hypotheses, not hidden:
the fee loop's termination on words (`FeeLoopEnds`), the gas and fuel the paths
consume, and write permission. Relating the branch words to `Model.userCall` and
discharging these from `AdmissibleCall` is the OPERANDS/GAS work that follows.
-/

namespace Eip8282.Audit.EntryReach

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec
open Eip8282.Audit.XiTransport
open Eip8282.Audit.UniversalBoundary (XiHalts observation_of_halts)
open Eip8282.Audit.Model (Kind)

/-! ## A completed path is a halting witness -/

theorem halting_RETURN : Halting .RETURN = true := by decide
theorem halting_REVERT : Halting .REVERT = true := by decide
theorem halting_STOP : Halting .STOP = true := by decide

/-- **A completed path is a halting witness.** With fuel for its step count and
one more for the halting instruction, the run `XRuns` produces, closed by the
`RunUntil.stop` the halting decode licenses, is the `RunUntil` of `XiHalts`; the
`Halt` package supplies the decode, the `Z` charge and the step. -/
theorem xiHalts_of_ends {kind : Kind} {c : XiCall kind} {K : Nat} {x : EVM.State}
    {w : Operation .EVM} {out : ByteArray} (h : Ends c K x w out) (hw : Halting w = true)
    (hfuel : K + 2 ≤ c.fuel) :
    ∃ hx : XiHalts c, hx.exit = x ∧ hx.op = w ∧ haltData hx.post.toMachineState w = out := by
  obtain ⟨⟨k, hk, hreach⟩, hhalt⟩ := h
  obtain ⟨tr, hrun⟩ := hreach (c.fuel - k - 1)
  have hf : c.fuel - k - 1 + 1 + k = c.fuel := by omega
  rw [hf] at hrun
  obtain ⟨post, hstep, hH⟩ := hhalt.step (c.fuel - k - 2)
  have hrem : c.fuel - k - 2 + 1 = c.fuel - k - 1 := by omega
  rw [hrem] at hstep
  have hout : haltData post.toMachineState w = out := by
    have := H_eq_haltData (μ := post.toMachineState) hw
    rw [this] at hH
    exact Option.some.inj hH
  refine ⟨{
    rem := c.fuel - k - 1
    gasCost := _
    trace := tr ++ []
    exit := x
    mid := charged x w
    post := post
    op := w
    arg := none
    run := runUntil_of_xRuns hrun
      (RunUntil.stop (by rw [hhalt.decode]; exact stopOrHalting_of_halting hw))
    decode := hhalt.decode
    charge := hhalt.charge
    stepOk := hstep }, rfl, rfl, hout⟩

/-- **The observation of a completed path.** The complete `Ξ` call observes the
halting instruction the path reaches, at the bytes the path names. -/
theorem observe_of_ends {kind : Kind} {c : XiCall kind} {K : Nat} {x : EVM.State}
    {w : Operation .EVM} {out : ByteArray} (h : Ends c K x w out) (hw : Halting w = true)
    (hfuel : K + 2 ≤ c.fuel) :
    observe c.result = some (exitObservation w out) := by
  obtain ⟨hx, -, hop, hout⟩ := xiHalts_of_ends h hw hfuel
  rw [observation_of_halts hx, hop, hout]

/-! ## The deposit partition -/

namespace Deposit

variable (c : XiCall .deposit)

/-- The user side's fee-loop premise, with the gas and fuel its widest endpoint
(the accepted submission) consumes. -/
def UserBudget : Prop :=
  ∃ (n : Nat) (o' i' : UInt256), FeeLoopEnds c n o' i' ∧
    87 * n + 190000 ≤ c.gas.toNat ∧ 24 * n + 152 ≤ c.fuel

/-- **Every deposit call with write permission halts.** The caller word, the
inhibitor, the calldata size, the value, the fee, the amount floor and the stake
partition the calls into the nine endpoints; each has a completed path. -/
theorem halts (hperm : c.env.perm = true) (hgas : 2500000 ≤ c.gas.toNat)
    (hfuel : 8502 ≤ c.fuel) (hfee : callerWord c ≠ sysW → excessWord c ≠ INH → UserBudget c) :
    Nonempty (XiHalts c) := by
  by_cases hsys : callerWord c = sysW
  · obtain ⟨_, _, _, _, _, _, _, hend⟩ := system_returns c hsys hperm hgas
    obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_RETURN (by omega)
    exact ⟨hx⟩
  by_cases hinh : excessWord c = INH
  · obtain ⟨_, _, hend⟩ := user_inhibited c hsys hinh (by omega)
    obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
    exact ⟨hx⟩
  obtain ⟨n, o', i', hfee, hg, hf⟩ := hfee hsys hinh
  by_cases h184 : cdsizeWord c = UInt256.ofNat 184
  · by_cases hlt : valueWord c < feeWord o'
    · obtain ⟨_, _, hend⟩ := user_underpay_reverts c hsys hinh hfee h184 hlt (by omega)
      obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
      exact ⟨hx⟩
    by_cases hfloor : amountWord c < UInt256.ofNat 1000000000
    · obtain ⟨_, _, hend⟩ := user_amountFloor_reverts c hsys hinh hfee h184 hlt hfloor (by omega)
      obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
      exact ⟨hx⟩
    by_cases hstake : (valueWord c - feeWord o') < UInt256.ofNat 1000000000 * amountWord c
    · obtain ⟨_, _, hend⟩ :=
        user_stake_reverts c hsys hinh hfee h184 hlt hfloor hstake (by omega)
      obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
      exact ⟨hx⟩
    obtain ⟨_, _, hend⟩ :=
      user_append_stops c hsys hinh hperm hfee h184 hlt hfloor hstake (by omega)
    obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_STOP (by omega)
    exact ⟨hx⟩
  by_cases h0 : cdsizeWord c = ⟨0⟩
  · by_cases hval : valueWord c = ⟨0⟩
    · obtain ⟨_, _, hend⟩ := user_getter_returns c hsys hinh hfee h0 hval (by omega)
      obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_RETURN (by omega)
      exact ⟨hx⟩
    obtain ⟨_, _, hend⟩ := user_paidGetter_reverts c hsys hinh hfee h0 hval (by omega)
    obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
    exact ⟨hx⟩
  obtain ⟨_, _, hend⟩ := user_badsize_reverts c hsys hinh hfee h184 h0 (by omega)
  obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
  exact ⟨hx⟩

/-- **The fee getter's observation**, end to end: the call returns the 32-byte
word `fee` the loop computed. -/
theorem observe_getter (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = ⟨0⟩) (hval : valueWord c = ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) (hf : 24 * n + 82 ≤ c.fuel) :
    observe c.result = some (exitObservation .RETURN
      ((mstoreMem (mem₀ c) (UInt256.ofNat 0) (feeWord o')).readWithPadding 0 32)) := by
  obtain ⟨_, _, hend⟩ := user_getter_returns c huser hen hfee hsize hval hg
  exact observe_of_ends hend halting_RETURN (by omega)

/-- **The system drain's observation**, end to end: the call returns the staged
records, `184 · min(tail − head, 64)` bytes of them. -/
theorem observe_system (hsys : callerWord c = sysW) (hperm : c.env.perm = true)
    (hg : 2500000 ≤ c.gas.toNat) (hf : 8502 ≤ c.fuel) :
    observe c.result = some (exitObservation .RETURN
      ((drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat).readWithPadding 0
        (UInt256.ofNat 184 * drainWord c).toNat)) := by
  obtain ⟨_, _, _, _, _, _, _, hend⟩ := system_returns c hsys hperm hg
  exact observe_of_ends hend halting_RETURN (by omega)

end Deposit

/-! ## The exit partition -/

namespace Exit

variable (c : XiCall .exit)

/-- The user side's fee-loop premise, with the gas and fuel its widest endpoint
(the accepted request) consumes. -/
def UserBudget : Prop :=
  ∃ (n : Nat) (o' i' : UInt256), FeeLoopEnds c n o' i' ∧
    87 * n + 150000 ≤ c.gas.toNat ∧ 24 * n + 122 ≤ c.fuel

/-- **Every exit call with write permission halts.** The caller word, the
inhibitor, the calldata size, the value and the fee partition the calls into the
seven endpoints; each has a completed path. -/
theorem halts (hperm : c.env.perm = true) (hgas : 250000 ≤ c.gas.toNat)
    (hfuel : 802 ≤ c.fuel) (hfee : callerWord c ≠ sysW → excessWord c ≠ INH → UserBudget c) :
    Nonempty (XiHalts c) := by
  by_cases hsys : callerWord c = sysW
  · obtain ⟨_, _, _, _, _, _, _, hend⟩ := system_returns c hsys hperm hgas
    obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_RETURN (by omega)
    exact ⟨hx⟩
  by_cases hinh : excessWord c = INH
  · obtain ⟨_, _, hend⟩ := user_inhibited c hsys hinh (by omega)
    obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
    exact ⟨hx⟩
  obtain ⟨n, o', i', hfee, hg, hf⟩ := hfee hsys hinh
  by_cases h48 : cdsizeWord c = UInt256.ofNat 48
  · by_cases hlt : valueWord c < feeWord o'
    · obtain ⟨_, _, hend⟩ := user_underpay_reverts c hsys hinh hfee h48 hlt (by omega)
      obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
      exact ⟨hx⟩
    obtain ⟨_, _, hend⟩ := user_append_stops c hsys hinh hperm hfee h48 hlt (by omega)
    obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_STOP (by omega)
    exact ⟨hx⟩
  by_cases h0 : cdsizeWord c = ⟨0⟩
  · by_cases hval : valueWord c = ⟨0⟩
    · obtain ⟨_, _, hend⟩ := user_getter_returns c hsys hinh hfee h0 hval (by omega)
      obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_RETURN (by omega)
      exact ⟨hx⟩
    obtain ⟨_, _, hend⟩ := user_paidGetter_reverts c hsys hinh hfee h0 hval (by omega)
    obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
    exact ⟨hx⟩
  obtain ⟨_, _, hend⟩ := user_badsize_reverts c hsys hinh hfee h48 h0 (by omega)
  obtain ⟨hx, -⟩ := xiHalts_of_ends hend halting_REVERT (by omega)
  exact ⟨hx⟩

/-- **The fee getter's observation**, end to end. -/
theorem observe_getter (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = ⟨0⟩) (hval : valueWord c = ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) (hf : 24 * n + 82 ≤ c.fuel) :
    observe c.result = some (exitObservation .RETURN
      ((mstoreMem (mem₀ c) (UInt256.ofNat 0) (feeWord o')).readWithPadding 0 32)) := by
  obtain ⟨_, _, hend⟩ := user_getter_returns c huser hen hfee hsize hval hg
  exact observe_of_ends hend halting_RETURN (by omega)

/-- **The system drain's observation**, end to end: `68 · min(tail − head, 16)`
bytes of staged records. -/
theorem observe_system (hsys : callerWord c = sysW) (hperm : c.env.perm = true)
    (hg : 250000 ≤ c.gas.toNat) (hf : 802 ≤ c.fuel) :
    observe c.result = some (exitObservation .RETURN
      ((drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat).readWithPadding 0
        (UInt256.ofNat 68 * drainWord c).toNat)) := by
  obtain ⟨_, _, _, _, _, _, _, hend⟩ := system_returns c hsys hperm hg
  exact observe_of_ends hend halting_RETURN (by omega)

end Exit

end Eip8282.Audit.EntryReach
