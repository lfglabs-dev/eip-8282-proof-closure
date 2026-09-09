import Eip8282.Audit.Integrator.SuccessfulAppend

/-!
# Actual opcode debits on supported runtime paths

These lemmas recover natural-number gas accounting from the accepted `Z` and
executed `StepOk` of the pinned evaluator. Fuel and syntactic step count are not
used as substitutes for gas. The supported opcode set excludes CALL/CREATE and
other child-frame operations which can return gas. Whole-call and transaction
accounting require an actual supported path and remain separate boundaries.
-/
namespace Eip8282.Audit.Integrator.ActualAppendGas

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open SuccessInversion

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- Acceptance supplies both no-underflow checks and the exact opcode cost. -/
theorem accepted_gas {vj : Array UInt256} {op : Operation .EVM}
    {pre mid : EVM.State} {cost : Nat}
    (h : Z vj op pre = .ok (mid, cost)) :
    memoryExpansionCost pre op ≤ pre.gasAvailable.toNat ∧
      mid.gasAvailable.toNat = pre.gasAvailable.toNat - memoryExpansionCost pre op ∧
      cost ≤ mid.gasAvailable.toNat ∧ cost = C' mid op := by
  have hm := Z_ok_state h
  simp only [Z, Bind.bind, Except.bind, pure, Except.pure] at h
  have hmem := Nat.le_of_not_gt (elim_guard_not h)
  replace h := elim_guard h
  have hcost := Nat.le_of_not_gt (elim_guard_not h)
  repeat replace h := elim_guard h
  have hc := (congrArg Prod.snd (Except.ok.inj h)).symm
  change cost = C' (zMid pre op) op at hc
  refine ⟨hmem, ?_, ?_, ?_⟩
  · rw [hm]
    exact toNat_sub_ofNat hmem
  · rw [hm, hc]
    exact hcost
  · rw [hm]
    exact hc

/-- The raw supported opcode semantics preserve gas; its debit is performed
by EVM.step, before invoking this semantics. -/
theorem opcode_preserves_gas {op : Operation .EVM} (hop : op ∈ allOps)
    {arg : Option (UInt256 × Nat)} {pre post : EVM.State}
    (h : EvmYul.step op arg pre = .ok post) : post.gasAvailable = pre.gasAvailable := by
  have he := step_withGE hop arg pre pre.gasAvailable pre.execLength
  have hself : withGE pre pre.gasAvailable pre.execLength = pre := rfl
  rw [hself, h] at he
  have hh : post = withGE post pre.gasAvailable pre.execLength := Except.ok.inj he
  have hg := congrArg (fun st : EVM.State => st.gasAvailable) hh
  exact hg

/-- An actual supported opcode step debits precisely the supplied cost. The
accepted Z premise, supplied separately below, establishes cost sufficiency. -/
theorem step_gas {op : Operation .EVM} (hop : op ∈ allOps)
    {arg : Option (UInt256 × Nat)} {pre post : EVM.State} {fuel cost : Nat}
    (h : StepOk fuel cost (op,arg) pre post) :
    post.gasAvailable = pre.gasAvailable - UInt256.ofNat cost := by
  cases fuel with
  | zero => change Except.error ExecutionException.OutOfFuel = Except.ok post at h; cases h
  | succ fuel =>
      change EvmYul.EVM.step (fuel+1) cost (some (op,arg)) pre = .ok post at h
      rw [EVM_step_eq_step hop] at h
      exact opcode_preserves_gas hop h

/-- Exact natural debit from actual accepted and executed semantics. No gas
sufficiency or predicted post-state premise is assumed. -/
theorem accepted_step_debit {vj : Array UInt256} {op : Operation .EVM}
    (hop : op ∈ allOps) {arg : Option (UInt256 × Nat)}
    {pre mid post : EVM.State} {fuel cost : Nat}
    (hz : Z vj op pre = .ok (mid,cost)) (hs : StepOk fuel cost (op,arg) mid post) :
    post.gasAvailable.toNat + memoryExpansionCost pre op + cost = pre.gasAvailable.toNat := by
  obtain ⟨hm, he, hc, _⟩ := accepted_gas hz
  have hp := step_gas hop hs
  have hn : post.gasAvailable.toNat = mid.gasAvailable.toNat - cost := by
    rw [hp]
    exact toNat_sub_ofNat hc
  omega

/-- LOG0's actual opcode cost, with its actual stack length operand. -/
theorem accepted_log_cost {vj : Array UInt256} {pre mid : EVM.State}
    {cost : Nat} {off len : UInt256} {stk : Stack UInt256}
    (hstack : pre.stack = off :: len :: stk)
    (hz : Z vj .LOG0 pre = .ok (mid,cost)) :
    cost = 375 + 8 * len.toNat := by
  obtain ⟨_, _, _, hc⟩ := accepted_gas hz
  rw [hc]
  have hm : mid.stack = off :: len :: stk := (Z_ok_stack hz).trans hstack
  simp only [C', hm, List.getElem!_cons_succ, List.getElem!_cons_zero,
    GasConstants.Glog, GasConstants.Glogdata]

/-- Inverting actual success at LOG0 yields its charged next state and the
same successful continuation. This is an actual local debit, not a fuel count. -/
theorem success_log_debit {fuel : Nat} {vj : Array UInt256}
    {pre final : EVM.State} {out : ByteArray} {off len : UInt256} {stk : Stack UInt256}
    (hdecode : decodeAt pre = (.LOG0,none)) (hstack : pre.stack = off :: len :: stk)
    (h : X fuel vj pre = .ok (.success final out)) :
    ∃ rest post, fuel = rest+1 ∧
      X rest vj post = .ok (.success final out) ∧
      post.gasAvailable.toNat + memoryExpansionCost pre .LOG0 + (375+8*len.toNat) =
        pre.gasAvailable.toNat := by
  obtain ⟨rest, cost, mid, post, hf, hz, hs, _, ht⟩ :=
    success_continue hdecode (by decide) h
  have hd := accepted_step_debit (by decide : Operation.LOG0 ∈ allOps) hz hs
  rw [accepted_log_cost hstack hz] at hd
  exact ⟨rest, post, hf, ht, hd⟩

/-- Every actual supported nonhalting step pays at least its opcode cost.
Memory expansion is additional and nonnegative. -/
theorem xstep_debit {vj : Array UInt256} {fuel cost : Nat} {pre post : EVM.State}
    (hop : (decodeAt pre).1 ∈ allOps) (h : XStepAt vj fuel cost pre post) :
    post.gasAvailable.toNat + cost ≤ pre.gasAvailable.toNat := by
  obtain ⟨mid, hz, hs, _⟩ := h
  have hd := accepted_step_debit hop hz hs
  omega

/-- The sum is over opcode charges actually carried by the evaluator's trace.
It deliberately excludes memory charges, so it is a lower bound on debit. -/
def opcodeCharges (trace : List Labelled) : Nat := (trace.map (fun step => step.2.1)).sum

def Supported (trace : List Labelled) : Prop := ∀ step ∈ trace, step.2.2.1 ∈ allOps

/-- Natural gas telescopes on a real XRuns trace, under explicit opcode
support. No assumption about the final gas or its desired value occurs. -/
theorem xruns_debit {vj : Array UInt256} {fuel rest : Nat} {pre post : EVM.State}
    {trace : List Labelled} (h : XRuns vj fuel pre trace rest post) (hop : Supported trace) :
    post.gasAvailable.toNat + opcodeCharges trace ≤ pre.gasAvailable.toNat := by
  induction h with
  | refl => simp [opcodeCharges]
  | @cons fuel cost rest pre mid post trace hs ht ih =>
      have hh : (decodeAt pre).1 ∈ allOps := hop (fuel, cost, decodeAt pre) (by simp)
      have hd := xstep_debit hh hs
      have htail : Supported trace := fun x hx => hop x (by simp [hx])
      have hi := ih htail
      simp only [opcodeCharges, List.map_cons, List.sum_cons]
      change post.gasAvailable.toNat + (cost + opcodeCharges trace) ≤ _
      omega

/-- The pinned exit append LOG0 debits at least 919 gas at its actual site.
This is a local statement: reaching this site from call entry remains separate. -/
theorem exit_log_site {fuel : Nat} {pre final : EVM.State} {out : ByteArray}
    {off : UInt256} {stk : Stack UInt256}
    (hcode : pre.executionEnv.code = Eip8282.Audit.Bytecode.exitRuntime)
    (hpc : pre.pc = UInt256.ofNat 217)
    (hstack : pre.stack = off :: UInt256.ofNat 68 :: stk)
    (h : X fuel Eip8282.Audit.Jumpdests.exitJumpdests pre = .ok (.success final out)) :
    ∃ rest post, fuel = rest+1 ∧
      X rest Eip8282.Audit.Jumpdests.exitJumpdests post = .ok (.success final out) ∧
      post.gasAvailable.toNat + 919 ≤ pre.gasAvailable.toNat := by
  obtain ⟨rest, post, hf, hx, hg⟩ := success_log_debit
    (decodeAt_of_code_pc hcode hpc exit_s217) hstack h
  refine ⟨rest, post, hf, hx, ?_⟩
  change post.gasAvailable.toNat + memoryExpansionCost pre .LOG0 + (375+8*68) = _ at hg
  omega

/-- The pinned deposit append LOG0 debits at least 1847 gas at its actual site.
The opcode and size are tied to the actual decoded state, not a gas estimate. -/
theorem deposit_log_site {fuel : Nat} {pre final : EVM.State} {out : ByteArray}
    {off : UInt256} {stk : Stack UInt256}
    (hcode : pre.executionEnv.code = Eip8282.Audit.Bytecode.depositRuntime)
    (hpc : pre.pc = UInt256.ofNat 276)
    (hstack : pre.stack = off :: UInt256.ofNat 184 :: stk)
    (h : X fuel Eip8282.Audit.Jumpdests.depositJumpdests pre = .ok (.success final out)) :
    ∃ rest post, fuel = rest+1 ∧
      X rest Eip8282.Audit.Jumpdests.depositJumpdests post = .ok (.success final out) ∧
      post.gasAvailable.toNat + 1847 ≤ pre.gasAvailable.toNat := by
  obtain ⟨rest, post, hf, hx, hg⟩ := success_log_debit
    (decodeAt_of_code_pc hcode hpc deposit_s276) hstack h
  refine ⟨rest, post, hf, hx, ?_⟩
  change post.gasAvailable.toNat + memoryExpansionCost pre .LOG0 + (375+8*184) = _ at hg
  omega

/-- A genuine supported prefix and suffix transfer the LOG0 debit to their
endpoints. The middle step is checked by Z and StepOk, so its cost is derived
from the stack, not assumed to satisfy the desired lower bound. -/
theorem trace_log_debit {vj : Array UInt256} {start atLog afterLog finish : EVM.State}
    {fStart fLog fFinish cost : Nat} {beforeTrace afterTrace : List Labelled}
    {off len : UInt256} {stk : Stack UInt256}
    (hp : XRuns vj fStart start beforeTrace (fLog+1) atLog) (hsp : Supported beforeTrace)
    (hd : decodeAt atLog = (.LOG0,none)) (hstack : atLog.stack = off :: len :: stk)
    (hl : XStepAt vj fLog cost atLog afterLog)
    (hs : XRuns vj fLog afterLog afterTrace fFinish finish) (hss : Supported afterTrace) :
    finish.gasAvailable.toNat + (375+8*len.toNat) ≤ start.gasAvailable.toNat := by
  have hbeforeTrace := xruns_debit hp hsp
  have hafterTrace := xruns_debit hs hss
  obtain ⟨mid, hz, hstep, _⟩ := hl
  rw [hd] at hz hstep
  have hcharge := accepted_log_cost hstack hz
  have hdebit := accepted_step_debit (by decide : Operation.LOG0 ∈ allOps) hz hstep
  rw [hcharge] at hdebit
  omega

/-- Halting steps have the same debit law; this finishes a trace bound without
assuming anything about the gas returned by the final successful result. -/
theorem success_final_step_debit {fuel : Nat} {vj : Array UInt256}
    {pre final : EVM.State} {out : ByteArray}
    (hop : (decodeAt pre).1 ∈ allOps)
    (hh : Halting (decodeAt pre).1 = true)
    (h : X fuel vj pre = .ok (.success final out)) :
    final.gasAvailable.toNat ≤ pre.gasAvailable.toNat := by
  obtain ⟨rest, cost, op, arg, mid, post, _, hd, hz, hs, hc⟩ := success_step h
  have hm : op ∈ allOps := by rw [hd] at hop; exact hop
  have hg := accepted_step_debit hm hz hs
  rcases hc with ⟨hn, _⟩ | ⟨_, _, he⟩
  · have hn' := H_eq_none_iff.mp hn
    rw [hd] at hh
    change Halting op = true at hh
    rw [hn'] at hh
    cases hh
  · subst post
    omega

/-- An actual evaluator path through a LOG0, finishing at a supported halt.
This is a witness in the existing XRuns/StepOk relations, not a new interpreter
or an assumption about desired gas. Extracting it from arbitrary successful
append classification remains the next whole-call obligation. -/
def LogPath {kind : Eip8282.Audit.Model.Kind}
    (q : Eip8282.Audit.XiTransport.XiCall kind) (len : UInt256) : Prop :=
  ∃ atLog afterLog finish fLog fFinish cost beforeTrace afterTrace off stk,
    XRuns (Eip8282.Audit.XiTransport.jumpdestsOf kind) q.fuel q.entry
      beforeTrace (fLog+1) atLog ∧ Supported beforeTrace ∧
    decodeAt atLog = (.LOG0,none) ∧ atLog.stack = off :: len :: stk ∧
    XStepAt (Eip8282.Audit.XiTransport.jumpdestsOf kind) fLog cost atLog afterLog ∧
    XRuns (Eip8282.Audit.XiTransport.jumpdestsOf kind) fLog afterLog afterTrace fFinish finish ∧
    Supported afterTrace ∧ (decodeAt finish).1 ∈ allOps ∧ Halting (decodeAt finish).1 = true

/-- The actual Ξ result retains the debit established by a real supported log
path. No sufficient-resource or final-gas premise occurs. -/
theorem xi_log_debit {kind : Eip8282.Audit.Model.Kind}
    (q : Eip8282.Audit.XiTransport.XiCall kind) (len : UInt256) (hpath : LogPath q len)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : q.result = .ok (.success (created,world,gas,substate) out)) :
    gas.toNat + (375+8*len.toNat) ≤ q.gas.toNat := by
  obtain ⟨atLog, afterLog, finish, fLog, fFinish, cost, beforeTrace, afterTrace,
    off, stk, hp, hsp, hd, hstack, hl, hs, hss, hop, hh⟩ := hpath
  obtain ⟨final, hfinal, hx⟩ := xi_success_X q h
  have hgas : final.gasAvailable = gas := congrArg (fun p => p.2.2.1) hfinal
  rw [hp.X_eq, hl.X_succ, hs.X_eq] at hx
  have hhalt := success_final_step_debit hop hh hx
  have htrace := trace_log_debit hp hsp hd hstack hl hs hss
  rw [hgas] at hhalt
  change finish.gasAvailable.toNat + (375+8*len.toNat) ≤ q.gas.toNat at htrace
  omega

/-- Θ forwards the same remaining gas, including its empty-world fallback.
The supported real log path is explicit until append inversion extracts it. -/
theorem theta_log_debit (c : MessageCall.Context) {kind : Eip8282.Audit.Model.Kind}
    (hcode : c.code = Eip8282.Audit.Correspondence.runtimeCode kind) (len : UInt256)
    (hpath : LogPath (CallBridge.codeCall c hcode (c.fuel-1)) len)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created,world,gas,substate,true,out)) :
    gas.toNat + (375+8*len.toNat) ≤ c.gas.toNat := by
  have hf : c.fuel = (c.fuel-1)+1 := by
    have hp := SuccessfulQuote.positive_fuel c h
    omega
  obtain ⟨ew, es, he, _, _⟩ := CallSuccess.codeCall_of_success c hcode (c.fuel-1) hf h
  exact xi_log_debit (CallBridge.codeCall c hcode (c.fuel-1)) len hpath he

#print axioms accepted_gas
#print axioms accepted_step_debit
#print axioms success_log_debit
#print axioms xruns_debit
#print axioms exit_log_site
#print axioms deposit_log_site
#print axioms trace_log_debit
#print axioms success_final_step_debit
#print axioms xi_log_debit
#print axioms theta_log_debit

end Eip8282.Audit.Integrator.ActualAppendGas
