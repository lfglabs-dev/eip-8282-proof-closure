import Eip8282.Audit.Integrator.NestedEventCert

/-!
# Gas accounting for the complete nested certificate

The certificate contains no gas hypothesis. The selected child's debit is
derived inductively from its actual certificate, then transported through the
literal CALL/CREATE operation. Local LOG0 markers are charged by X exactly once.
An error residual of zero is only accounting notation, not returned EVM gas.
-/
namespace Eip8282.Audit.Integrator.NestedEvents
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def localCharge (a : StepArgs) : StepResult → Nat
  | .error _ => 0
  | .ok _ => if a.op = .LOG0 ∧ 68 ≤ (a.pre.stack.getD 1 ⟨0⟩).toNat then 919 else 0

def extra (q : Request) : q.Outcome → Nat :=
  match q with
  | .step _ a => localCharge a
  | _ => fun _ => 0

theorem localCharge_zero {a : StepArgs} (hop : a.op ≠ .LOG0) (r : StepResult) :
    localCharge a r = 0 := by
  cases r <;> simp [localCharge, hop]

/-- Every successful local marker is paid by its accepted LOG0 instruction. -/
theorem step_local_debit (n : Nat) (a : StepArgs) :
    (Request.step n a).residual (Request.step n a).eval +
      localCharge a (Request.step n a).eval ≤ a.pre.gasAvailable.toNat := by
  cases hs : (Request.step n a).eval with
  | error err => exact Nat.zero_le _
  | ok post =>
      by_cases hm : a.op = .LOG0 ∧ 68 ≤ (a.pre.stack.getD 1 ⟨0⟩).toNat
      · obtain ⟨hop,hlen⟩ := hm
        have hz : Z a.vj .LOG0 a.pre = .ok (a.mid,a.cost) := hop ▸ a.guard
        have hsize := ReturnedGas.accepted_stack hz
        have htwo : 2 ≤ a.pre.stack.length := by simpa only [δ, Option.getD_some] using hsize
        obtain ⟨off,len,rest,hstack⟩ : ∃ off len rest, a.pre.stack = off::len::rest := by
          rcases he : a.pre.stack with _ | ⟨off, _ | ⟨len,rest⟩⟩ <;> simp_all
        have hd := OrdinaryGas.accepted_step_debit
          (show OrdinaryGas.Ordinary a.op from hop ▸ (by decide)) a.guard hs
        have hc := ActualAppendGas.accepted_log_cost hstack hz
        have hl : 68 ≤ len.toNat := by
          simpa only [hstack, List.getD_cons_succ, List.getD_cons_zero] using hlen
        change post.gasAvailable.toNat + localCharge a (.ok post) ≤ _
        rw [localCharge, if_pos ⟨hop,hlen⟩]
        omega
      · have hd := ReturnedGas.step_remaining n a.guard hs
        change post.gasAvailable.toNat + localCharge a (.ok post) ≤ _
        simpa only [localCharge, if_neg hm, Nat.add_zero] using hd

theorem call_child_debit (n : Nat) (a : StepArgs) (hop : a.op = .CALL)
    (hg : CallOutcome.Gate a.mid (operand a 2)) (charge : Nat)
    (hchild :
      let q := Request.theta n (dispatchCallArgs a.mid (operand a 0) (operand a 1)
        (operand a 2) (operand a 3) (operand a 4))
      q.residual q.eval + charge ≤ q.gas) :
    (Request.step (n+2) a).residual (Request.step (n+2) a).eval + charge ≤
      a.pre.gasAvailable.toNat := by
  have hz : Z a.vj .CALL a.pre = .ok (a.mid,a.cost) := hop ▸ a.guard
  have hstack := (Z_ok_stack a.guard).symm.trans (call_stack a hop)
  have hb :
      (Request.theta n (dispatchCallArgs a.mid (operand a 0) (operand a 1)
        (operand a 2) (operand a 3) (operand a 4))).gas ≤
      Ccallgas (AccountAddress.ofUInt256 (operand a 1)) (AccountAddress.ofUInt256 (operand a 1))
        (operand a 2) (operand a 0) a.mid.accountMap a.mid.toMachineState a.mid.substate :=
    Nat.mod_le _ _
  have hd := RecursiveEventDebit.call_charge n a.arg (operand a 0) (operand a 1)
    (operand a 2) (operand a 3) (operand a 4) (operand a 5) (operand a 6)
    (a.mid.stack.drop 7) hstack hz hg charge (hchild.trans hb)
  simpa only [Request.residual, Request.eval, hop, dispatchCallArgs_eval] using hd

theorem family_child_debit (k : CallFamilyGas.Variant) (n : Nat) (a : StepArgs)
    (hop : a.op = CallFamilyGas.opcode k)
    (hg : CallFamilyGas.gate k a.mid (familyValue k a)) (charge : Nat)
    (hchild :
      let q := Request.theta n (familyArgs k a.mid (operand a 0) (operand a 1)
        (familyValue k a) (familyInOff k a) (familyInLen k a))
      q.residual q.eval + charge ≤ q.gas) :
    (Request.step (n+2) a).residual (Request.step (n+2) a).eval + charge ≤
      a.pre.gasAvailable.toNat := by
  have hz : Z a.vj (CallFamilyGas.opcode k) a.pre = .ok (a.mid,a.cost) := hop ▸ a.guard
  have hstack := (Z_ok_stack a.guard).symm.trans (family_stack k a hop)
  have hb :
      (Request.theta n (familyArgs k a.mid (operand a 0) (operand a 1)
        (familyValue k a) (familyInOff k a) (familyInLen k a))).gas ≤
      CallFamilyGas.allowance k a.mid (operand a 0) (operand a 1) (familyValue k a) :=
    Nat.mod_le _ _
  have hd := RecursiveEventDebit.family_charge k n a.arg (operand a 0) (operand a 1)
    (familyValue k a) (familyInOff k a) (familyInLen k a) (familyOutOff k a) (familyOutLen k a)
    (familyRest k a) hstack hz hg charge (hchild.trans hb)
  simpa only [Request.residual, Request.eval, hop, familyArgs_eval] using hd

theorem creation_child_debit (k : CreationGas.Variant) (n : Nat) (a : StepArgs)
    (hop : a.op = CreationGas.opcode k) (hn : CreationGas.nonceAllowed a.mid)
    (hg : CreationGas.gate a.mid (operand a 0) (operand a 1) (operand a 2)) (charge : Nat)
    (hchild :
      let q := Request.lambda n (creationArgs k a.cost a.mid (operand a 0) (operand a 1)
        (operand a 2) (creationSalt k a))
      q.residual q.eval + charge ≤ q.gas) :
    (Request.step (n+1) a).residual (Request.step (n+1) a).eval + charge ≤
      a.pre.gasAvailable.toNat := by
  have hz : Z a.vj (CreationGas.opcode k) a.pre = .ok (a.mid,a.cost) := hop ▸ a.guard
  have hstack := (Z_ok_stack a.guard).symm.trans (creation_stack k a hop)
  have hb :
      (Request.lambda n (creationArgs k a.cost a.mid (operand a 0) (operand a 1)
        (operand a 2) (creationSalt k a))).gas ≤ CreationGas.allowance a.cost a.mid :=
    Nat.mod_le _ _
  have hd := RecursiveEventDebit.creation_charge k n a.arg (operand a 0) (operand a 1)
    (operand a 2) (creationSalt k a) (creationRest k a) hstack hz hn hg charge (hchild.trans hb)
  simpa only [Request.residual, Request.eval, hop, creationArgs_eval] using hd

theorem selected_child_not_ordinary {n : Nat} {a : StepArgs} {q : Request}
    (hc : StepChild n a (some q)) : ¬ OrdinaryGas.Ordinary a.op := by
  intro ho
  unfold StepChild at hc
  cases n with
  | zero => cases hc
  | succ n =>
      cases hop : a.op <;> simp_all [selectedChild, OrdinaryGas.ordinary_iff]

theorem selected_child_not_log {n : Nat} {a : StepArgs} {q : Request}
    (hc : StepChild n a (some q)) : a.op ≠ .LOG0 := by
  intro hop
  apply selected_child_not_ordinary hc
  simpa only [hop] using (show OrdinaryGas.Ordinary .LOG0 from by decide)

/-- The selected child's independent budget pays its contribution through the
actual recursive opcode, regardless of either final outcome. -/
theorem selected_child_debit {n : Nat} {a : StepArgs} {q : Request}
    (hc : StepChild n a (some q)) (charge : Nat)
    (hchild : q.residual q.eval + charge ≤ q.gas) :
    (Request.step n a).residual (Request.step n a).eval + charge ≤
      a.pre.gasAvailable.toNat := by
  have ho := selected_child_not_ordinary hc
  simp only [OrdinaryGas.ordinary_iff, not_and_or, not_not] at ho
  cases n with
  | zero => cases hc
  | succ n =>
      rcases ho with hop | hop | hop | hop | hop | hop
      · cases n with
        | zero => simp [StepChild, selectedChild, hop] at hc
        | succ n =>
            unfold StepChild at hc
            rw [selectedChild_call n a hop] at hc
            split at hc
            · cases Option.some.inj hc
              exact call_child_debit n a hop ‹_› charge hchild
            · cases hc
      · cases n with
        | zero => simp [StepChild, selectedChild, hop] at hc
        | succ n =>
            unfold StepChild at hc
            rw [selectedChild_family .callcode n a hop] at hc
            split at hc
            · cases Option.some.inj hc
              exact family_child_debit .callcode n a hop ‹_› charge hchild
            · cases hc
      · cases n with
        | zero => simp [StepChild, selectedChild, hop] at hc
        | succ n =>
            unfold StepChild at hc
            rw [selectedChild_family .delegatecall n a hop] at hc
            split at hc
            · cases Option.some.inj hc
              exact family_child_debit .delegatecall n a hop ‹_› charge hchild
            · cases hc
      · cases n with
        | zero => simp [StepChild, selectedChild, hop] at hc
        | succ n =>
            unfold StepChild at hc
            rw [selectedChild_family .staticcall n a hop] at hc
            split at hc
            · cases Option.some.inj hc
              exact family_child_debit .staticcall n a hop ‹_› charge hchild
            · cases hc
      · unfold StepChild at hc
        rw [selectedChild_creation .create n a hop] at hc
        split at hc
        · cases Option.some.inj hc
          exact creation_child_debit .create n a hop (And.left ‹_›) (And.right ‹_›) charge hchild
        · cases hc
      · unfold StepChild at hc
        rw [selectedChild_creation .create2 n a hop] at hc
        split at hc
        · cases Option.some.inj hc
          exact creation_child_debit .create2 n a hop (And.left ‹_›) (And.right ‹_›) charge hchild
        · cases hc

theorem theta_residual_bound (n : Nat) (a : ThetaArgs) :
    (Request.theta n a).residual (Request.theta n a).eval ≤ a.gas.toNat := by
  cases he : (Request.theta n a).eval with
  | error err => exact Nat.zero_le _
  | ok result =>
      obtain ⟨created,world,gas,ss,z,out⟩ := result
      exact ReturnedGas.theta_remaining n he

/-- Every event in the complete certificate is charged once. This induction
includes all failed requests and their selected descendants; the final outcome
need not be successful or committed. -/
theorem gas_bound {q : Request} {result : q.Outcome} {tree : EventTree}
    (h : Cert q result tree) :
    q.residual result + extra q result + 919*tree.count ≤ q.gas := by
  induction h with
  | xZero => exact Nat.zero_le _
  | xGuardError => exact Nat.zero_le _
  | xStepError hz hs ih =>
      simpa [Request.residual, Request.gas, extra, localCharge,
        StepArgs.ofGuard, FrameEvents.residual, RecursiveEventDebit.stepResidual,
        EventTree.count] using ih
  | @xNext n cost vj pre mid post result child next hz hs hh tail ihs iht =>
      simp [Request.residual, Request.gas, extra, localCharge, StepArgs.ofGuard,
        EventTree.count, FrameEvents.Marked, RecursiveEventDebit.stepResidual] at ihs iht ⊢
      split_ifs at ihs ⊢ <;> omega
  | @xHalt n cost vj pre mid post out child hz hs hh hn ih =>
      simp [Request.residual, Request.gas, extra, localCharge, StepArgs.ofGuard,
        EventTree.count, FrameEvents.Marked, FrameEvents.residual, ReturnedGas.xGas,
        RecursiveEventDebit.stepResidual] at ih ⊢
      split_ifs at ih ⊢ <;> omega
  | @xRevert n cost vj pre mid post out child hz hs hh hr ih =>
      simp [Request.residual, Request.gas, extra, localCharge, StepArgs.ofGuard,
        EventTree.count, FrameEvents.Marked, FrameEvents.residual, ReturnedGas.xGas,
        RecursiveEventDebit.stepResidual] at ih ⊢
      split_ifs at ih ⊢ <;> omega
  | xiZero => exact Nat.zero_le _
  | @xi n a tree body ih =>
      simp only [extra, Request.residual, Request.gas, Nat.add_zero] at ih ⊢
      change WrapperEventDebit.xiResidual
        (Ξ (n+1) a.created a.genesis a.blocks a.world a.original a.gas a.substate a.env) +
          919*tree.count ≤ a.gas.toNat
      rw [WrapperEventDebit.xi_residual]
      exact ih
  | thetaZero => exact Nat.zero_le _
  | @thetaPrecompile n a target hc =>
      simpa only [extra, EventTree.count, Nat.mul_zero, Nat.add_zero, Request.gas] using
        theta_residual_bound (n+1) a
  | @thetaCode n a bytes tree hc body ih =>
      have hb := WrapperEventDebit.theta_charge (a.context n bytes) (919*tree.count) ih
      simp only [extra, Request.residual, Request.gas, Nat.add_zero]
      rw [thetaArgs_result a n bytes hc]
      exact hb
  | lambdaZero => exact Nat.zero_le _
  | @lambdaNoPreimage n a hp =>
      simp only [extra, Request.residual, Request.gas, EventTree.count,
        Nat.mul_zero, Nat.add_zero]
      rw [lambdaArgs_result, WrapperEventDebit.lambda_no_preimage (a.context n) hp]
      exact Nat.zero_le _
  | @lambdaInit n a bytes tree hp body ih =>
      have hb := WrapperEventDebit.lambda_charge (a.context n) hp (919*tree.count) ih
      simp only [extra, Request.residual, Request.gas, Nat.add_zero]
      rw [lambdaArgs_result]
      exact hb
  | @stepNone n a hc =>
      simpa only [extra, Request.gas, EventTree.count, Nat.mul_zero, Nat.add_zero] using
        step_local_debit n a
  | @stepChild n a q tree hc body ih =>
      have hchild : q.residual q.eval + 919*tree.count ≤ q.gas := by omega
      have hb := selected_child_debit hc (919*tree.count) hchild
      simpa only [extra, localCharge_zero (selected_child_not_log hc),
        Nat.add_zero, Request.gas] using hb

#print axioms step_local_debit
#print axioms call_child_debit
#print axioms family_child_debit
#print axioms creation_child_debit
#print axioms selected_child_not_log
#print axioms selected_child_debit
#print axioms gas_bound
end Eip8282.Audit.Integrator.NestedEvents
