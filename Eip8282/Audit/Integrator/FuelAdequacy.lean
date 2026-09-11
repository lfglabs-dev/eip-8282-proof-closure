import Eip8282.Audit.Integrator.RecursiveGasProgress
import Eip8282.Audit.Integrator.OpcodeCostPositive
import Eip8282.Audit.Integrator.NestedCertificateAll

/-! A concrete evaluator-fuel bound for every request retained by the actual
certificate. The gas rank counts semantic recursion, not wall-clock work. -/
namespace Eip8282.Audit.Integrator.FuelAdequacy
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open NestedEvents
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def phase : Request → Nat
  | .step .. => 1 | .x .. => 2 | .xi .. => 3 | .theta .. | .lambda .. => 4

def required (q : Request) : Nat := 5 * q.gas + phase q

def Adequate (q : Request) : Prop := required q ≤ q.fuel

theorem phase_bounds (q : Request) : 1 ≤ phase q ∧ phase q ≤ 4 := by
  cases q <;> simp [phase]

theorem adequate_positive {q : Request} (h : Adequate q) : 0 < q.fuel := by
  have hp := phase_bounds q
  unfold Adequate required at h
  omega

theorem uniform_bound (q : Request) (h : 5 * (q.gas + 1) ≤ q.fuel) : Adequate q := by
  have hp := phase_bounds q
  unfold Adequate required
  omega

theorem accepted_nonhalting_drop {fuel cost : Nat} {vj : Array UInt256}
    {op : Operation .EVM} {arg : Option (UInt256 × Nat)} {pre mid post : EVM.State}
    (hz : Z vj op pre = .ok (mid,cost))
    (hs : StepOk fuel cost (op,arg) mid post) (hh : H post.toMachineState op = none) :
    post.gasAvailable.toNat < pre.gasAvailable.toNat := by
  by_cases ho : OrdinaryGas.Ordinary op
  · have hc := OpcodeCostPositive.accepted_nonhalting_cost hz hh
    have hd := OrdinaryGas.accepted_step_debit ho hz hs
    omega
  · exact RecursiveGasProgress.recursive_step_drop fuel ho hz hs

theorem selected_child_adequate {n : Nat} {a : StepArgs} {q : Request}
    (hc : StepChild n a (some q)) (h : Adequate (.step n a)) : Adequate q := by
  have hg := RecursiveGasProgress.selected_child_gas_lt hc
  have hf := RecursiveGasProgress.selected_child_fuel_gap hc
  have hp := phase_bounds q
  change 5 * a.pre.gasAvailable.toNat + 1 ≤ n at h
  change 5 * q.gas + phase q ≤ q.fuel
  omega

theorem at_adequate {q inner : Request} {result : q.Outcome} {r : inner.Outcome}
    {tree : EventTree} {path : EventTree.Address}
    (loc : RequestAt q result tree path inner r) (hq : Adequate q) : Adequate inner := by
  induction loc with
  | here body => exact hq
  | xStepError hz hs loc ih =>
      apply ih
      simp only [Adequate, required, phase, Request.gas, Request.fuel,
        StepArgs.ofGuard] at hq ⊢
      omega
  | xNextChild hz hs hh tail loc ih =>
      apply ih
      simp only [Adequate, required, phase, Request.gas, Request.fuel,
        StepArgs.ofGuard] at hq ⊢
      omega
  | xNextTail hz hs hh tail loc ih =>
      have hd := accepted_nonhalting_drop hz (sound hs) hh
      apply ih
      simp only [Adequate, required, phase, Request.gas, Request.fuel] at hq ⊢
      omega
  | xHalt hz hs hh hn loc ih =>
      apply ih
      simp only [Adequate, required, phase, Request.gas, Request.fuel,
        StepArgs.ofGuard] at hq ⊢
      omega
  | xRevert hz hs hh hr loc ih =>
      apply ih
      simp only [Adequate, required, phase, Request.gas, Request.fuel,
        StepArgs.ofGuard] at hq ⊢
      omega
  | xi body loc ih =>
      apply ih
      simp only [Adequate, required, phase, Request.gas, Request.fuel,
        XiArgs.entry, WrapperEventDebit.entry] at hq ⊢
      omega
  | thetaCode bytes hc body loc ih =>
      apply ih
      simp only [Adequate, required, phase, Request.gas, Request.fuel,
        ThetaArgs.xiArgs, ThetaArgs.context] at hq ⊢
      omega
  | lambdaInit bytes hp body loc ih =>
      apply ih
      simp only [Adequate, required, phase, Request.gas, Request.fuel,
        LambdaArgs.xiArgs, LambdaArgs.context] at hq ⊢
      omega
  | stepChild hc body loc ih => exact ih (selected_child_adequate hc hq)

private theorem ite_no_fuel {α : Type} (p : Prop) [Decidable p]
    (x y : Except ExecutionException α)
    (hx : x ≠ .error .OutOfFuel) (hy : y ≠ .error .OutOfFuel) :
    (if p then x else y) ≠ .error .OutOfFuel := by
  split <;> assumption

theorem guard_no_fuel (vj : Array UInt256) (op : Operation .EVM) (pre : EVM.State) :
    Z vj op pre ≠ .error .OutOfFuel := by
  simp only [Z, Bind.bind, Except.bind, pure, Except.pure]
  repeat' first | apply ite_no_fuel | (intro h; cases h)

private theorem dup_no_fuel (n : Nat) (pre : EVM.State) :
    EvmYul.dup n pre ≠ .error .OutOfFuel := by
  intro h
  unfold EvmYul.dup at h
  dsimp only at h
  split at h <;> cases h

private theorem swap_no_fuel (n : Nat) (pre : EVM.State) :
    EvmYul.swap n pre ≠ .error .OutOfFuel := by
  intro h
  unfold EvmYul.swap at h
  dsimp only at h
  split at h <;> cases h

private theorem selfdestruct_no_fuel (arg : Option (UInt256 × Nat)) (pre : EVM.State) :
    EvmYul.step (τ := .EVM) .SELFDESTRUCT arg pre ≠ .error .OutOfFuel := by
  intro h
  obtain ⟨sh,pc,stk,ex⟩ := pre
  cases stk with
  | nil => cases h
  | cons dest stk =>
      change (if sh.createdAccounts.contains sh.executionEnv.codeOwner then
        Except.ok _ else Except.ok _) = Except.error ExecutionException.OutOfFuel at h
      split at h <;> cases h

theorem raw_no_fuel {op : Operation .EVM} (ho : OrdinaryGas.Ordinary op)
    (hv : op ≠ .INVALID) (arg : Option (UInt256 × Nat)) (pre : EVM.State) :
    EvmYul.step op arg pre ≠ .error .OutOfFuel := by
  intro h
  cases op <;> rename_i op <;> cases op
  all_goals first
    | exact False.elim (hv rfl)
    | (simp only [OrdinaryGas.Ordinary, Operation.isCall, Operation.isCreate,
        Bool.true_eq_false, false_and, and_false] at ho; done)
    | exact selfdestruct_no_fuel arg pre h
    | exact dup_no_fuel _ pre h
    | exact swap_no_fuel _ pre h
    | skip
  all_goals
    obtain ⟨sh, pc, stk, ex⟩ := pre
    rcases arg with _ | ⟨v,n⟩
    all_goals rcases stk with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, tail⟩⟩⟩⟩⟩⟩
    all_goals first | cases h | (split at h <;> cases h)

theorem creation_no_fuel (k : CreationGas.Variant) (n : Nat) (a : StepArgs)
    (hop : a.op = CreationGas.opcode k) :
    (Request.step (n+1) a).eval ≠ .error .OutOfFuel := by
  have hs := creation_stack k a hop
  change EVM.step (n+1) a.cost (some (a.op,a.arg)) a.mid ≠ _
  rw [hop]
  by_cases hn : CreationGas.nonceAllowed a.mid
  · by_cases hg : CreationGas.gate a.mid (operand a 0) (operand a 1) (operand a 2)
    · rw [CreationOutcome.admitted_equation k n a.cost a.mid a.arg
        (operand a 0) (operand a 1) (operand a 2) (creationSalt k a) (creationRest k a) hs hn hg]
      intro he
      have he := (CreationOutcome.finish_error_iff _ _ _ _ _ _ _ _).mp he
      cases he.2
    · rw [CreationOutcome.denied_equation k n a.cost a.mid a.arg
        (operand a 0) (operand a 1) (operand a 2) (creationSalt k a) (creationRest k a) hs (Or.inr hg)]
      intro he
      have he := (CreationOutcome.finish_error_iff _ _ _ _ _ _ _ _).mp he
      cases he.2
  · rw [CreationOutcome.denied_equation k n a.cost a.mid a.arg
      (operand a 0) (operand a 1) (operand a 2) (creationSalt k a) (creationRest k a) hs (Or.inl hn)]
    intro he
    have he := (CreationOutcome.finish_error_iff _ _ _ _ _ _ _ _).mp he
    cases he.2

theorem xi_no_fuel (n : Nat) (a : XiArgs)
    (h : NoOutOfFuel (.x n a.jumps a.entry) (Request.x n a.jumps a.entry).eval) :
    NoOutOfFuel (.xi (n+1) a) (Request.xi (n+1) a).eval := by
  intro he
  change Ξ (n+1) a.created a.genesis a.blocks a.world a.original a.gas a.substate a.env = _ at he
  unfold Ξ at he
  change (show XiResult from do
    let result ← X n a.jumps a.entry
    match result with
    | .success post out => pure (.success
        (post.createdAccounts,post.accountMap,post.gasAvailable,post.substate) out)
    | .revert gas out => pure (.revert gas out)) = Except.error ExecutionException.OutOfFuel at he
  cases hx : X n a.jumps a.entry with
  | error err =>
      simp only [hx, Bind.bind, Except.bind] at he
      cases he
      exact h hx
  | ok result =>
      cases result <;> simp only [hx, Bind.bind, Except.bind, pure, Except.pure] at he
      all_goals cases he

theorem theta_code_no_fuel (n : Nat) (a : ThetaArgs) (bytes : ByteArray)
    (hc : a.code = .Code bytes)
    (h : NoOutOfFuel (.xi n (a.xiArgs bytes)) (Request.xi n (a.xiArgs bytes)).eval) :
    NoOutOfFuel (.theta (n+1) a) (Request.theta (n+1) a).eval := by
  change (a.context n bytes).execution ≠ .error .OutOfFuel at h
  change (Request.theta (n+1) a).eval ≠ _
  rw [thetaArgs_result a n bytes hc, MessageCall.result_eq_settle]
  cases he : (a.context n bytes).execution with
  | error err =>
      cases err <;> simp_all +decide [MessageCall.Context.settle]
  | ok result =>
      cases result <;> simp [MessageCall.Context.settle]

theorem lambda_no_fuel (n : Nat) (a : LambdaArgs) (bytes : ByteArray)
    (hp : a.preimage = some bytes)
    (h : NoOutOfFuel (.xi n (a.xiArgs bytes)) (Request.xi n (a.xiArgs bytes)).eval) :
    NoOutOfFuel (.lambda (n+1) a) (Request.lambda (n+1) a).eval := by
  change (a.context n).execution (CreationSettlement.address bytes) ≠ .error .OutOfFuel at h
  change (Request.lambda (n+1) a).eval ≠ _
  rw [lambdaArgs_result, CreationSettlement.result_eq_settle (a.context n) hp]
  cases he : (a.context n).execution (CreationSettlement.address bytes) with
  | error err => cases err <;> simp_all +decide [CreationSettlement.Context.settle]
  | ok result => cases result <;> simp [CreationSettlement.Context.settle]

theorem precompile_returns (target : AccountAddress) (world : AccountMap .EVM) (gas : UInt256)
    (ss : Substate) (env : ExecutionEnv .EVM) :
    ∃ result, ReturnedGas.precompileResult target world gas ss env = .ok result := by
  unfold ReturnedGas.precompileResult
  split <;> exact ⟨_,rfl⟩

theorem theta_precompile_no_fuel (n : Nat) (a : ThetaArgs) (target : AccountAddress)
    (hc : a.code = .Precompiled target) :
    NoOutOfFuel (.theta (n+1) a) (Request.theta (n+1) a).eval := by
  intro h
  let c := a.context 0 ByteArray.empty
  let env : ExecutionEnv .EVM := { c.environment with code := ByteArray.empty }
  change Θ (n+1) a.hashes a.created a.genesis a.blocks a.world a.original a.substate
    a.source a.origin a.target a.code a.gas a.price a.value a.apparent a.data a.depth a.header
    a.permission = .error .OutOfFuel at h
  rw [hc] at h
  have hh : (do
    let (cr,z,w,g,ss,data) ← ReturnedGas.precompileResult target c.entryWorld c.gas c.substate env
    pure (cr,if w == ∅ then c.world else w,g,if w == ∅ then c.substate else ss,z,data)) =
      Except.error ExecutionException.OutOfFuel := by
    convert h using 1
    unfold Θ ReturnedGas.precompileResult
    dsimp only
    split
    all_goals first | rfl | (split <;> first | rfl | contradiction)
  obtain ⟨result,he⟩ := precompile_returns target c.entryWorld c.gas c.substate env
  obtain ⟨cr,z,w,g,ss,data⟩ := result
  simp only [he, Bind.bind, Except.bind, pure, Except.pure] at hh
  cases hh

theorem call_no_fuel (n : Nat) (a : StepArgs) (hop : a.op = .CALL)
    (safe : ∀ q, StepChild (n+2) a (some q) → NoOutOfFuel q q.eval) :
    NoOutOfFuel (.step (n+2) a) (Request.step (n+2) a).eval := by
  intro h
  change EVM.step (n+2) a.cost (some (a.op,a.arg)) a.mid = _ at h
  rw [hop] at h
  have he := (CallOutcome.step_call_error_iff n a.cost a.mid a.arg
    (operand a 0) (operand a 1) (operand a 2) (operand a 3) (operand a 4)
    (operand a 5) (operand a 6) (a.mid.stack.drop 7) (call_stack a hop) .OutOfFuel).mp h
  have hc : StepChild (n+2) a (some (.theta n (dispatchCallArgs a.mid
      (operand a 0) (operand a 1) (operand a 2) (operand a 3) (operand a 4)))) := by
    unfold StepChild
    rw [selectedChild_call n a hop, if_pos he.1]
  have hn := safe _ hc
  apply hn
  exact he.2

theorem family_no_fuel (k : CallFamilyGas.Variant) (n : Nat) (a : StepArgs)
    (hop : a.op = CallFamilyGas.opcode k)
    (safe : ∀ q, StepChild (n+2) a (some q) → NoOutOfFuel q q.eval) :
    NoOutOfFuel (.step (n+2) a) (Request.step (n+2) a).eval := by
  intro h
  change EVM.step (n+2) a.cost (some (a.op,a.arg)) a.mid = _ at h
  rw [hop] at h
  have he := (CallOutcome.step_family_error_iff k n a.cost a.mid a.arg
    (operand a 0) (operand a 1) (familyValue k a) (familyInOff k a) (familyInLen k a)
    (familyOutOff k a) (familyOutLen k a) (familyRest k a) (family_stack k a hop) .OutOfFuel).mp h
  have hc : StepChild (n+2) a (some (.theta n (familyArgs k a.mid
      (operand a 0) (operand a 1) (familyValue k a) (familyInOff k a) (familyInLen k a)))) := by
    unfold StepChild
    rw [selectedChild_family k n a hop, if_pos he.1]
  have hn := safe _ hc
  apply hn
  exact he.2

theorem recursive_adequate_two {n : Nat} {a : StepArgs}
    (ho : ¬ OrdinaryGas.Ordinary a.op) (ha : Adequate (.step n a)) : 2 ≤ n := by
  have hh : Halting a.op = false := by
    simp only [OrdinaryGas.ordinary_iff, not_and_or, not_not] at ho
    rcases ho with h | h | h | h | h | h <;> rw [h] <;> rfl
  have hp := OpcodeCostPositive.opcode_cost_positive a.mid a.op
    (OrdinaryGas.accepted_valid a.guard) hh
  have hg := ActualAppendGas.accepted_gas a.guard
  simp only [Adequate, required, Request.fuel, Request.gas, phase] at ha
  omega

theorem step_no_fuel (n : Nat) (a : StepArgs) (ha : Adequate (.step n a))
    (safe : ∀ q, StepChild n a (some q) → NoOutOfFuel q q.eval) :
    NoOutOfFuel (.step n a) (Request.step n a).eval := by
  by_cases ho : OrdinaryGas.Ordinary a.op
  · have hn := adequate_positive ha
    cases n with
    | zero => change 0 < 0 at hn; omega
    | succ n =>
      change EVM.step (n+1) a.cost (some (a.op,a.arg)) a.mid ≠ _
      rw [OrdinaryGas.dispatch ho]
      exact raw_no_fuel ho (OrdinaryGas.accepted_valid a.guard) a.arg _
  · have hn := recursive_adequate_two ho ha
    obtain ⟨m,rfl⟩ : ∃ m, n = m+2 := ⟨n-2,by omega⟩
    simp only [OrdinaryGas.ordinary_iff, not_and_or, not_not] at ho
    rcases ho with hop | hop | hop | hop | hop | hop
    · exact call_no_fuel m a hop safe
    · exact family_no_fuel .callcode m a hop safe
    · exact family_no_fuel .delegatecall m a hop safe
    · exact family_no_fuel .staticcall m a hop safe
    · exact creation_no_fuel .create (m+1) a hop
    · exact creation_no_fuel .create2 (m+1) a hop

theorem no_out_of_fuel {q : Request} {result : q.Outcome} {tree : EventTree}
    (cert : Cert q result tree) (hq : Adequate q) : NoOutOfFuel q result := by
  induction cert with
  | xZero => have hp := adequate_positive hq; contradiction
  | xGuardError hz =>
      intro he
      cases he
      exact guard_no_fuel _ _ _ hz
  | xStepError hz hs ih =>
      have hn := ih (at_adequate (.xStepError hz hs (.here hs)) hq)
      intro he
      cases he
      exact hn rfl
  | xNext hz hs hh tail ihs iht =>
      exact iht (at_adequate (.xNextTail hz hs hh tail (.here tail)) hq)
  | xHalt => intro h; cases h
  | xRevert => intro h; cases h
  | xiZero => have hp := adequate_positive hq; contradiction
  | xi body ih => exact xi_no_fuel _ _ (ih (at_adequate (.xi body (.here body)) hq))
  | thetaZero => have hp := adequate_positive hq; contradiction
  | thetaPrecompile target hc => exact theta_precompile_no_fuel _ _ target hc
  | thetaCode bytes hc body ih =>
      exact theta_code_no_fuel _ _ bytes hc
        (ih (at_adequate (.thetaCode bytes hc body (.here body)) hq))
  | lambdaZero => have hp := adequate_positive hq; contradiction
  | @lambdaNoPreimage n a hp =>
      obtain ⟨bytes,he⟩ := CreationPreimageTotal.lambdaArgs_total a
      rw [hp] at he
      cases he
  | lambdaInit bytes hp body ih =>
      exact lambda_no_fuel _ _ bytes hp
        (ih (at_adequate (.lambdaInit bytes hp body (.here body)) hq))
  | stepNone hc =>
      apply step_no_fuel _ _ hq
      intro q hsome
      have he := stepChild_unique hc hsome
      cases he
  | stepChild hc body ih =>
      apply step_no_fuel _ _ hq
      intro q hsome
      have he := Option.some.inj (stepChild_unique hc hsome)
      subst q
      exact ih (selected_child_adequate hc hq)

theorem every_no_out_of_fuel {q : Request} {result : q.Outcome} {tree : EventTree}
    (cert : Cert q result tree) (hq : Adequate q) : Every NoOutOfFuel q result tree := by
  intro path inner r loc
  obtain ⟨innerTree,body⟩ := RequestAt.cert_inner loc
  exact no_out_of_fuel body (at_adequate loc hq)

theorem actual_lambda_returns {q : Request} {result : q.Outcome} {tree : EventTree}
    (cert : Cert q result tree) (hq : Adequate q)
    {path : EventTree.Address} {fuel : Nat} {a : LambdaArgs} {r : LambdaResult}
    (loc : RequestAt q result tree path (.lambda fuel a) r) :
    ∃ returned, (Request.lambda fuel a).eval = .ok returned :=
  NestedEvents.lambda_returns (every_no_out_of_fuel cert hq) loc

#print axioms uniform_bound
#print axioms accepted_nonhalting_drop
#print axioms at_adequate
#print axioms no_out_of_fuel
#print axioms every_no_out_of_fuel
#print axioms actual_lambda_returns
end Eip8282.Audit.Integrator.FuelAdequacy
