import Eip8282.Audit.EntryReach

/-!
# Actual state payloads at complete execution endpoints

These lemmas retain the successful `Ξ` payload instead of projecting only its
return observation. `Ξ` starts after the message-call value transfer; rollback
and that transfer belong to the enclosing message-call layer. No abstract-model
post-state agreement is assumed. Getter results remain conditional on a completed
word fee loop and the explicitly stated execution resources.
-/

namespace Eip8282.Audit.Integrator.EndpointState

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.XiTransport
open Eip8282.Audit.UniversalBoundary (XiHalts)
open Eip8282.Audit.EntryReach
open Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)

set_option maxHeartbeats 1600000

/-- `Ξ` preserves every field of a successful `X` result that it publishes. -/
theorem result_of_X_success {kind : Kind} (c : XiCall kind) {post : EVM.State}
    {out : ByteArray}
    (hX : X c.fuel (jumpdestsOf kind) c.entry = .ok (.success post out)) :
    c.result = .ok (.success
      (post.createdAccounts, post.accountMap, post.gasAvailable, post.substate) out) := by
  unfold XiCall.result Ξ
  change (do
    let r ← X c.fuel (D_J c.env.code ⟨0⟩) c.entry
    match r with
    | .success st o => Except.ok (ExecutionResult.success
        (st.createdAccounts, st.accountMap, st.gasAvailable, st.substate) o)
    | .revert g o => Except.ok (ExecutionResult.revert g o)) = _
  rw [Xi_validJumps_eq c.code_pinned, hX]
  rfl

/-- A reverted `Ξ` publishes remaining gas and data, with no success world. -/
theorem result_of_X_revert {kind : Kind} (c : XiCall kind) {gas : UInt256}
    {out : ByteArray}
    (hX : X c.fuel (jumpdestsOf kind) c.entry = .ok (.revert gas out)) :
    c.result = .ok (.revert gas out) := by
  unfold XiCall.result Ξ
  change (do
    let r ← X c.fuel (D_J c.env.code ⟨0⟩) c.entry
    match r with
    | .success st o => Except.ok (ExecutionResult.success
        (st.createdAccounts, st.accountMap, st.gasAvailable, st.substate) o)
    | .revert g o => Except.ok (ExecutionResult.revert g o)) = _
  rw [Xi_validJumps_eq c.code_pinned, hX]
  rfl

/-- The complete halting witness fixes the full result, including its world,
logs, created accounts and remaining gas on success. -/
theorem result_of_halts {kind : Kind} {c : XiCall kind} (w : XiHalts c) :
    c.result = if w.op = .REVERT then
      .ok (.revert w.post.gasAvailable (haltData w.post.toMachineState w.op))
    else .ok (.success
      (w.post.createdAccounts, w.post.accountMap, w.post.gasAvailable, w.post.substate)
      (haltData w.post.toMachineState w.op)) := by
  by_cases hop : w.op = .REVERT
  · rw [if_pos hop]
    exact result_of_X_revert c
      (w.run.X_revert w.decode w.charge w.stepOk (exit_H w.run w.decode _) hop)
  · rw [if_neg hop]
    exact result_of_X_success c
      (w.run.X_success w.decode w.charge w.stepOk (exit_H w.run w.decode _) hop)

/-- A concrete reached `RETURN` preserves the endpoint's account map, created
accounts and entire substate. The return instruction changes only machine state
and execution bookkeeping; its remaining gas is retained as an existential. -/
theorem result_of_return_ends {kind : Kind} {c : XiCall kind} {K : Nat}
    {x : EVM.State} {off len : UInt256} {r : Stack UInt256} {out : ByteArray}
    (hend : Ends c K x .RETURN out) (hstack : x.stack = off :: len :: r)
    (hfuel : K + 2 ≤ c.fuel) :
    ∃ gas, c.result = .ok (.success
      (x.createdAccounts, x.accountMap, gas, x.substate) out) := by
  obtain ⟨⟨k, hk, hreach⟩, hhalt⟩ := hend
  obtain ⟨tr, hrun⟩ := hreach (c.fuel - k - 1)
  have hf : c.fuel - k - 1 + 1 + k = c.fuel := by omega
  rw [hf] at hrun
  have hrun' := runUntil_of_xRuns hrun
    (RunUntil.stop (by rw [hhalt.decode]; exact stopOrHalting_of_halting EntryReach.halting_RETURN))
  obtain ⟨post, hstep, hH⟩ := hhalt.step (c.fuel - k - 2)
  have hconcrete := stepOk_halt (f := c.fuel - k - 2) (by decide : .RETURN ∈ allOps)
    (Eip8282.Audit.SymExec.step_RETURN hstack)
  have heq := Step.deterministic_ok hstep hconcrete
  subst post
  have hrem : c.fuel - k - 2 + 1 = c.fuel - k - 1 := by omega
  rw [hrem] at hstep
  have hX := hrun'.X_success hhalt.decode hhalt.charge hstep hH
    (by decide : (Operation.RETURN : Operation .EVM) ≠ .REVERT)
  have hres := result_of_X_success c hX
  exact ⟨_, hres⟩

/-- A reached `STOP` publishes the endpoint's actual world and logs. This is
the transport needed by the successful append paths, independent of their
record-format and storage-update proofs. -/
theorem result_of_stop_ends {kind : Kind} {c : XiCall kind} {K : Nat}
    {x : EVM.State} {out : ByteArray}
    (hend : Ends c K x .STOP out) (hfuel : K + 2 ≤ c.fuel) :
    ∃ gas, c.result = .ok (.success
      (x.createdAccounts, x.accountMap, gas, x.substate) out) := by
  obtain ⟨⟨k, hk, hreach⟩, hhalt⟩ := hend
  obtain ⟨tr, hrun⟩ := hreach (c.fuel - k - 1)
  have hf : c.fuel - k - 1 + 1 + k = c.fuel := by omega
  rw [hf] at hrun
  have hrun' := runUntil_of_xRuns hrun
    (RunUntil.stop (by rw [hhalt.decode]; exact stopOrHalting_of_halting EntryReach.halting_STOP))
  obtain ⟨post, hstep, hH⟩ := hhalt.step (c.fuel - k - 2)
  have hconcrete := stepOk_halt (f := c.fuel - k - 2) (by decide : .STOP ∈ allOps)
    (Eip8282.Audit.SymExec.step_STOP x)
  have heq := Step.deterministic_ok hstep hconcrete
  subst post
  have hrem : c.fuel - k - 2 + 1 = c.fuel - k - 1 := by omega
  rw [hrem] at hstep
  have hX := hrun'.X_success hhalt.decode hhalt.charge hstep hH
    (by decide : (Operation.STOP : Operation .EVM) ≠ .REVERT)
  have hres := result_of_X_success c hX
  exact ⟨_, hres⟩

/-- Deposit getter: all accounts (hence every storage slot and balance) and
the existing log sequence are preserved in the actual successful `Ξ` result. -/
theorem deposit_getter_preserves_state (c : XiCall .deposit)
    (huser : Deposit.callerWord c ≠ sysW) (hen : Deposit.excessWord c ≠ INH)
    {n : Nat} {o i : UInt256} (hfee : Deposit.FeeLoopEnds c n o i)
    (hsize : Deposit.cdsizeWord c = ⟨0⟩) (hval : Deposit.valueWord c = ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) (hf : 24 * n + 82 ≤ c.fuel) :
    ∃ gas substate, c.result = .ok (.success
      (c.createdAccounts, c.σ, gas, substate)
      ((mstoreMem (Deposit.mem₀ c) (UInt256.ofNat 0) (Deposit.feeWord o)).readWithPadding 0 32)) ∧ substate.logSeries = c.substate.logSeries := by
  obtain ⟨g, e, hend⟩ := Deposit.user_getter_returns c huser hen hfee hsize hval hg
  obtain ⟨gas, hres⟩ := result_of_return_ends hend rfl hf
  exact ⟨gas, _, hres, rfl⟩

/-- Exit getter: the same preservation statement for the other pinned runtime. -/
theorem exit_getter_preserves_state (c : XiCall .exit)
    (huser : Exit.callerWord c ≠ sysW) (hen : Exit.excessWord c ≠ INH)
    {n : Nat} {o i : UInt256} (hfee : Exit.FeeLoopEnds c n o i)
    (hsize : Exit.cdsizeWord c = ⟨0⟩) (hval : Exit.valueWord c = ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) (hf : 24 * n + 82 ≤ c.fuel) :
    ∃ gas substate, c.result = .ok (.success
      (c.createdAccounts, c.σ, gas, substate)
      ((mstoreMem (Exit.mem₀ c) (UInt256.ofNat 0) (Exit.feeWord o)).readWithPadding 0 32)) ∧ substate.logSeries = c.substate.logSeries := by
  obtain ⟨g, e, hend⟩ := Exit.user_getter_returns c huser hen hfee hsize hval hg
  obtain ⟨gas, hres⟩ := result_of_return_ends hend rfl hf
  exact ⟨gas, _, hres, rfl⟩

/-- An opaque-to-elaboration name for the existing concrete append expression.
This is definitionally the same state; the wrapper avoids repeated expansion
of its nested storage writes while elaborating result payload projections. -/
def depositAppendState (c : XiCall .deposit) : EvmYul.State .EVM := Deposit.appendedSt c

/-- The corresponding name for the concrete exit append expression. -/
def exitAppendState (c : XiCall .exit) : EvmYul.State .EVM := Exit.appendedSt c

/-- Specialize the STOP transport with a symbolic world before instantiating
large concrete storage expressions. This keeps state projection reduction local. -/
theorem result_of_stop_at_ends {kind : Kind} {c : XiCall kind} {K : Nat}
    {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {pc e : Nat}
    {stack : Stack UInt256} {out : ByteArray}
    (hend : Ends c K (at_ c st mem aw g pc stack e) .STOP out)
    (hfuel : K + 2 ≤ c.fuel) :
    ∃ gas, c.result = .ok (.success
      (st.createdAccounts, st.accountMap, gas, st.substate) out) :=
  result_of_stop_ends hend hfuel

/-- The successful deposit call publishes the entire concrete append state.
The storage/log expressions are the existing execution helpers; this lemma
does not yet identify them with an independent authentic-record specification. -/
theorem deposit_append_result (c : XiCall .deposit)
    (huser : Deposit.callerWord c ≠ sysW) (hen : Deposit.excessWord c ≠ INH)
    (hperm : c.env.perm = true) {n : Nat} {o i : UInt256}
    (hfee : Deposit.FeeLoopEnds c n o i)
    (hsize : Deposit.cdsizeWord c = UInt256.ofNat 184)
    (hpaid : ¬ Deposit.valueWord c < Deposit.feeWord o)
    (hfloor : ¬ Deposit.amountWord c < UInt256.ofNat 1000000000)
    (hstake : ¬ (Deposit.valueWord c - Deposit.feeWord o) <
      UInt256.ofNat 1000000000 * Deposit.amountWord c)
    (hg : 87 * n + 190000 ≤ c.gas.toNat) (hf : 24 * n + 152 ≤ c.fuel) :
    ∃ gas, c.result = .ok (.success
      ((depositAppendState c).createdAccounts, (depositAppendState c).accountMap,
        gas, (depositAppendState c).substate) .empty) := by
  obtain ⟨g, e, hend⟩ := Deposit.user_append_stops c huser hen hperm hfee
    hsize hpaid hfloor hstake hg
  have hres := result_of_stop_at_ends (c := c) (st := Deposit.appendedSt c) hend hf
  simpa only [depositAppendState] using hres

/-- The corresponding full concrete success payload for an exit append. -/
theorem exit_append_result (c : XiCall .exit)
    (huser : Exit.callerWord c ≠ sysW) (hen : Exit.excessWord c ≠ INH)
    (hperm : c.env.perm = true) {n : Nat} {o i : UInt256}
    (hfee : Exit.FeeLoopEnds c n o i)
    (hsize : Exit.cdsizeWord c = UInt256.ofNat 48)
    (hpaid : ¬ Exit.valueWord c < Exit.feeWord o)
    (hg : 87 * n + 150000 ≤ c.gas.toNat) (hf : 24 * n + 122 ≤ c.fuel) :
    ∃ gas, c.result = .ok (.success
      ((exitAppendState c).createdAccounts, (exitAppendState c).accountMap,
        gas, (exitAppendState c).substate) .empty) := by
  obtain ⟨g, e, hend⟩ := Exit.user_append_stops c huser hen hperm hfee hsize hpaid hg
  have hres := result_of_stop_at_ends (c := c) (st := Exit.appendedSt c) hend hf
  simpa only [exitAppendState] using hres

/-- Deposit SYSTEM calls publish the actual drained buffer and control writes.
The `Touched` witnesses constrain the intermediate worlds supplied by the
execution proof; none is an unconstrained assumed final world. Record encoding
and FIFO agreement with an independent specification remain separate proofs. -/
theorem deposit_system_result (c : XiCall .deposit)
    (hsys : Deposit.callerWord c = sysW) (hperm : c.env.perm = true)
    (hg : 2500000 ≤ c.gas.toNat) (hf : 8502 ≤ c.fuel) :
    ∃ (st' stX : EvmYul.State .EVM) (gas : UInt256),
      Touched (entrySt c) st' ∧
      Touched (Deposit.headStore c (Deposit.drainWord c) st') stX ∧
      let post := (stX.sstore (UInt256.ofNat 0) (Deposit.newExcess c stX)).sstore (UInt256.ofNat 1) (UInt256.ofNat 0)
      c.result = .ok (.success
        (post.createdAccounts, post.accountMap, gas, post.substate)
        ((Deposit.drainMem (entrySt c) (Deposit.headWord₀ c) (Deposit.mem₀ c)
          (Deposit.drainWord c).toNat).readWithPadding 0
          (UInt256.ofNat 184 * Deposit.drainWord c).toNat)) := by
  obtain ⟨st', stX, aw, g, e, ht, htX, hend⟩ := Deposit.system_returns c hsys hperm hg
  obtain ⟨gas, hres⟩ := result_of_return_ends hend rfl hf
  exact ⟨st', stX, gas, ht, htX, hres⟩

/-- The corresponding full concrete SYSTEM result for the exit runtime. -/
theorem exit_system_result (c : XiCall .exit)
    (hsys : Exit.callerWord c = sysW) (hperm : c.env.perm = true)
    (hg : 250000 ≤ c.gas.toNat) (hf : 802 ≤ c.fuel) :
    ∃ (st' stX : EvmYul.State .EVM) (gas : UInt256),
      Touched (entrySt c) st' ∧
      Touched (Exit.headStore c (Exit.drainWord c) st') stX ∧
      let post := (stX.sstore (UInt256.ofNat 0) (Exit.newExcess c stX)).sstore (UInt256.ofNat 1) (UInt256.ofNat 0)
      c.result = .ok (.success
        (post.createdAccounts, post.accountMap, gas, post.substate)
        ((Exit.drainMem (entrySt c) (Exit.headWord₀ c) (Exit.mem₀ c)
          (Exit.drainWord c).toNat).readWithPadding 0
          (UInt256.ofNat 68 * Exit.drainWord c).toNat)) := by
  obtain ⟨st', stX, aw, g, e, ht, htX, hend⟩ := Exit.system_returns c hsys hperm hg
  obtain ⟨gas, hres⟩ := result_of_return_ends hend rfl hf
  exact ⟨st', stX, gas, ht, htX, hres⟩

#print axioms result_of_halts
#print axioms result_of_return_ends
#print axioms result_of_stop_ends
#print axioms deposit_getter_preserves_state
#print axioms exit_getter_preserves_state
#print axioms deposit_append_result
#print axioms exit_append_result
#print axioms deposit_system_result
#print axioms exit_system_result

end Eip8282.Audit.Integrator.EndpointState
