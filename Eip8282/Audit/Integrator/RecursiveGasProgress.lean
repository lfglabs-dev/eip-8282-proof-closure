import Eip8282.Audit.Integrator.NestedEventDebit

/-! Strict gas progress of actual recursive dispatch, including caught creation errors.
No child success, funding, or evaluator adequacy is assumed. -/
namespace Eip8282.Audit.Integrator.RecursiveGasProgress
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open CallGasAccounting NestedEvents
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem stipend_margin (target recipient : AccountAddress) (value : UInt256)
    (world : AccountMap .EVM) (ss : Substate) :
    stipend value + 100 ≤ Cextra target recipient value world ss := by
  have ha : 100 ≤ Caccess target ss := by
    unfold Caccess
    split <;> decide
  by_cases hz : value = ⟨0⟩
  · simp only [stipend, hz, if_true]
    unfold Cextra
    omega
  · have hv : value.val ≠ 0 := by
      intro he
      exact hz (congrArg UInt256.mk he)
    have hn : (value != (⟨0⟩ : UInt256)) = true := by
      change (!(value.val == (0 : Fin UInt256.size))) = true
      simp [hv]
    unfold stipend Cextra Cxfer
    rw [if_neg hz, hn, if_pos rfl]
    unfold GasConstants.Gcallstipend GasConstants.Gcallvalue
    omega

theorem callgas_margin (target recipient : AccountAddress) (value requested : UInt256)
    (world : AccountMap .EVM) (machine : MachineState) (ss : Substate) :
    Ccallgas target recipient value requested world machine ss + 100 ≤
      Ccall target recipient value requested world machine ss := by
  rw [callgas_eq]
  have hm := stipend_margin target recipient value world ss
  unfold Ccall
  omega

theorem creation_cost (kind : CreationGas.Variant) {vj : Array UInt256}
    {pre mid : EVM.State} {cost : Nat}
    (hz : Z vj (CreationGas.opcode kind) pre = .ok (mid,cost)) : 32000 ≤ cost := by
  have hc := (ActualAppendGas.accepted_gas hz).2.2.2
  cases kind <;> simp only [CreationGas.opcode, C', GasConstants.Gcreate] at hc <;> omega

theorem creation_allowance_margin (kind : CreationGas.Variant) {vj : Array UInt256}
    {pre mid : EVM.State} {cost : Nat}
    (hz : Z vj (CreationGas.opcode kind) pre = .ok (mid,cost)) :
    CreationGas.allowance cost mid + 32000 ≤ pre.gasAvailable.toNat := by
  obtain ⟨_,hmid,hcost,_⟩ := ActualAppendGas.accepted_gas hz
  have hl := (CreationGas.forwarded_fit cost mid).1
  have hs : (stepPre cost mid).gasAvailable.toNat = mid.gasAvailable.toNat-cost :=
    toNat_sub_ofNat hcost
  have hc := creation_cost kind hz
  omega

theorem selected_child_fuel_gap {n : Nat} {a : StepArgs} {q : Request}
    (h : StepChild n a (some q)) : q.fuel + 1 = n ∨ q.fuel + 2 = n := by
  unfold StepChild selectedChild at h
  split at h
  · cases h
  · split at h
    all_goals repeat first | split at h | (cases h)
    all_goals simp_all [Request.fuel] <;> omega

/-- CREATE uses one fuel decrement; the CALL dispatcher/helper pair uses two. -/
theorem selected_child_fuel_exact {n : Nat} {a : StepArgs} {q : Request}
    (h : StepChild n a (some q)) :
    q.fuel + (if a.op = .CREATE ∨ a.op = .CREATE2 then 1 else 2) = n := by
  unfold StepChild selectedChild at h
  split at h
  · cases h
  · split at h
    all_goals repeat first | split at h | (cases h)
    all_goals simp_all [Request.fuel]

theorem call_step (fuel : Nat) 
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat} {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::rest)
    (hz : Z vj .CALL pre = .ok (mid,cost))
    (hs : StepOk (fuel+2) cost (.CALL,arg) mid post) : post.gasAvailable.toNat < pre.gasAvailable.toNat := by
  have hm := stipend_margin (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
    value mid.accountMap mid.substate
  by_cases hg : value ≤ (mid.accountMap.get? mid.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧ mid.executionEnv.depth < 1024
  · obtain ⟨cr,w,g,ss,z,out,hchild,hd⟩ := CallDispatchGas.accepted_step_call_debit fuel
      requested target value inOff inLen outOff outLen rest hstack hz hg hs
    have hb := ReturnedGas.theta_remaining fuel hchild
    have hf := (CallGasAccounting.accepted_call_forwarded_fit hstack hz).2
    change g.toNat ≤ (UInt256.ofNat (Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
      value requested mid.accountMap mid.toMachineState mid.substate)).toNat at hb
    rw [hf] at hb
    have he := hd hb
    omega
  · have he := (CallDispatchGas.accepted_step_call_denied_debit fuel
      requested target value inOff inLen outOff outLen rest hstack hz hg hs).2
    omega

theorem family_step (kind : CallFamilyGas.Variant) (fuel : Nat) 
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat} {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = CallFamilyGas.stack kind requested target value inOff inLen outOff outLen rest)
    (hz : Z vj (CallFamilyGas.opcode kind) pre = .ok (mid,cost))
    (hs : StepOk (fuel+2) cost (CallFamilyGas.opcode kind,arg) mid post) :
    post.gasAvailable.toNat < pre.gasAvailable.toNat := by
  have hm := stipend_margin (AccountAddress.ofUInt256 target)
    (AccountAddress.ofUInt256 (CallFamilyGas.recipient kind mid target))
    (CallFamilyGas.transfer kind value) mid.accountMap mid.substate
  have ho : 100 ≤ CallFamilyGas.overhead kind mid target value := by
    unfold CallFamilyGas.overhead
    omega
  by_cases hg : CallFamilyGas.gate kind mid value
  · obtain ⟨cr,w,g,ss,z,out,hchild,hd⟩ := CallFamilyGas.accepted_step_debit kind fuel
      requested target value inOff inLen outOff outLen rest hstack hz hg hs
    have hb := ReturnedGas.theta_remaining fuel hchild
    change g.toNat ≤ (UInt256.ofNat (CallFamilyGas.allowance kind mid requested target value)).toNat at hb
    rw [(CallFamilyGas.accepted_forwarded_fit kind hstack hz).2] at hb
    have he := hd hb
    omega
  · have he := (CallFamilyGas.accepted_denied_debit kind fuel
      requested target value inOff inLen outOff outLen rest hstack hz hg hs).2
    omega

theorem creation_step (kind : CreationGas.Variant) (fuel : Nat) 
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat} {arg : Option (UInt256 × Nat)}
    (value off len salt : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = CreationGas.stack kind value off len salt rest)
    (hz : Z vj (CreationGas.opcode kind) pre = .ok (mid,cost))
    (hs : StepOk (fuel+1) cost (CreationGas.opcode kind,arg) mid post) :
    post.gasAvailable.toNat < pre.gasAvailable.toNat := by
  have hm := creation_cost kind hz
  by_cases hn : CreationGas.nonceAllowed mid
  · by_cases hg : CreationGas.gate mid value off len
    · rcases CreationGas.accepted_child_debit kind fuel value off len salt rest hstack hz hn hg hs with hchild | herr
      · obtain ⟨addr,cr,w,g,ss,z,out,hchild,hd⟩ := hchild
        have hb := ReturnedGas.lambda_remaining fuel hchild
        change g.toNat ≤ (UInt256.ofNat (CreationGas.allowance cost mid)).toNat at hb
        rw [(CreationGas.forwarded_fit cost mid).2] at hb
        have he := hd hb
        omega
      · obtain ⟨err,_,hd,_⟩ := herr
        omega
    · have he := (CreationGas.accepted_denied_debit kind fuel value off len salt rest hstack hz (Or.inr hg) hs).1
      omega
  · have he := (CreationGas.accepted_denied_debit kind fuel value off len salt rest hstack hz (Or.inl hn) hs).1
    omega



theorem call_allowance_lt (a : StepArgs) (hop : a.op = .CALL) (n : Nat) :
    (Request.theta n (dispatchCallArgs a.mid (operand a 0) (operand a 1)
      (operand a 2) (operand a 3) (operand a 4))).gas < a.pre.gasAvailable.toNat := by
  have hz : Z a.vj .CALL a.pre = .ok (a.mid,a.cost) := hop ▸ a.guard
  have hstack := (Z_ok_stack a.guard).symm.trans (call_stack a hop)
  have hc := accepted_call_cost hstack hz
  have hm := callgas_margin (AccountAddress.ofUInt256 (operand a 1))
    (AccountAddress.ofUInt256 (operand a 1)) (operand a 2) (operand a 0)
    a.mid.accountMap a.mid.toMachineState a.mid.substate
  have hg := ActualAppendGas.accepted_gas hz
  have hb : (Request.theta n (dispatchCallArgs a.mid (operand a 0) (operand a 1)
      (operand a 2) (operand a 3) (operand a 4))).gas ≤
      Ccallgas (AccountAddress.ofUInt256 (operand a 1)) (AccountAddress.ofUInt256 (operand a 1))
        (operand a 2) (operand a 0) a.mid.accountMap a.mid.toMachineState a.mid.substate :=
    Nat.mod_le _ _
  omega

theorem family_allowance_lt (k : CallFamilyGas.Variant) (a : StepArgs)
    (hop : a.op = CallFamilyGas.opcode k) (n : Nat) :
    (Request.theta n (familyArgs k a.mid (operand a 0) (operand a 1)
      (familyValue k a) (familyInOff k a) (familyInLen k a))).gas < a.pre.gasAvailable.toNat := by
  have hz : Z a.vj (CallFamilyGas.opcode k) a.pre = .ok (a.mid,a.cost) := hop ▸ a.guard
  have hstack := (Z_ok_stack a.guard).symm.trans (family_stack k a hop)
  have hc := CallFamilyGas.accepted_cost k hstack hz
  have hm := callgas_margin (AccountAddress.ofUInt256 (operand a 1))
    (AccountAddress.ofUInt256 (CallFamilyGas.recipient k a.mid (operand a 1)))
    (CallFamilyGas.transfer k (familyValue k a)) (operand a 0)
    a.mid.accountMap a.mid.toMachineState a.mid.substate
  have hg := ActualAppendGas.accepted_gas hz
  have hb : (Request.theta n (familyArgs k a.mid (operand a 0) (operand a 1)
      (familyValue k a) (familyInOff k a) (familyInLen k a))).gas ≤
      CallFamilyGas.allowance k a.mid (operand a 0) (operand a 1) (familyValue k a) := Nat.mod_le _ _
  unfold CallFamilyGas.allowance at hb
  omega

theorem creation_allowance_lt (k : CreationGas.Variant) (a : StepArgs)
    (hop : a.op = CreationGas.opcode k) (n : Nat) :
    (Request.lambda n (creationArgs k a.cost a.mid (operand a 0) (operand a 1)
      (operand a 2) (creationSalt k a))).gas < a.pre.gasAvailable.toNat := by
  have hm := creation_allowance_margin k (hop ▸ a.guard)
  have hb : (Request.lambda n (creationArgs k a.cost a.mid (operand a 0) (operand a 1)
      (operand a 2) (creationSalt k a))).gas ≤ CreationGas.allowance a.cost a.mid := Nat.mod_le _ _
  omega

theorem selected_child_gas_lt {n : Nat} {a : StepArgs} {q : Request}
    (hc : StepChild n a (some q)) : q.gas < a.pre.gasAvailable.toNat := by
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
              exact call_allowance_lt a hop n
            · cases hc
      · cases n with
        | zero => simp [StepChild, selectedChild, hop] at hc
        | succ n =>
            unfold StepChild at hc
            rw [selectedChild_family .callcode n a hop] at hc
            split at hc
            · cases Option.some.inj hc
              exact family_allowance_lt .callcode a hop n
            · cases hc
      · cases n with
        | zero => simp [StepChild, selectedChild, hop] at hc
        | succ n =>
            unfold StepChild at hc
            rw [selectedChild_family .delegatecall n a hop] at hc
            split at hc
            · cases Option.some.inj hc
              exact family_allowance_lt .delegatecall a hop n
            · cases hc
      · cases n with
        | zero => simp [StepChild, selectedChild, hop] at hc
        | succ n =>
            unfold StepChild at hc
            rw [selectedChild_family .staticcall n a hop] at hc
            split at hc
            · cases Option.some.inj hc
              exact family_allowance_lt .staticcall a hop n
            · cases hc
      · unfold StepChild at hc
        rw [selectedChild_creation .create n a hop] at hc
        split at hc
        · cases Option.some.inj hc
          exact creation_allowance_lt .create a hop n
        · cases hc
      · unfold StepChild at hc
        rw [selectedChild_creation .create2 n a hop] at hc
        split at hc
        · cases Option.some.inj hc
          exact creation_allowance_lt .create2 a hop n
        · cases hc


private theorem stack3 (s : Stack UInt256) (h : 3 ≤ s.length) :
    ∃ a0 a1 a2 rest, s = a0::a1::a2::rest := by
  rcases s with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, rest⟩⟩⟩ <;> simp_all

private theorem stack4 (s : Stack UInt256) (h : 4 ≤ s.length) :
    ∃ a0 a1 a2 a3 rest, s = a0::a1::a2::a3::rest := by
  rcases s with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, rest⟩⟩⟩⟩ <;> simp_all

private theorem stack6 (s : Stack UInt256) (h : 6 ≤ s.length) :
    ∃ a0 a1 a2 a3 a4 a5 rest, s = a0::a1::a2::a3::a4::a5::rest := by
  rcases s with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, rest⟩⟩⟩⟩⟩⟩ <;> simp_all

private theorem stack7 (s : Stack UInt256) (h : 7 ≤ s.length) :
    ∃ a0 a1 a2 a3 a4 a5 a6 rest, s = a0::a1::a2::a3::a4::a5::a6::rest := by
  rcases s with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, rest⟩⟩⟩⟩⟩⟩⟩ <;> simp_all

theorem recursive_step_drop (fuel : Nat)
    {vj : Array UInt256} {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {pre mid post : EVM.State} {cost : Nat}
    (ho : ¬ OrdinaryGas.Ordinary op)
    (hz : Z vj op pre = .ok (mid,cost))
    (hs : StepOk fuel cost (op,arg) mid post) :
    post.gasAvailable.toNat < pre.gasAvailable.toNat := by
  cases fuel with
  | zero => cases hs
  | succ fuel =>
    have hsize := ReturnedGas.accepted_stack hz
    simp only [OrdinaryGas.ordinary_iff, not_and_or, not_not] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨a0,a1,a2,a3,a4,a5,a6,rest,hstack⟩ := stack7 pre.stack (by simpa only [δ, Option.getD_some] using hsize)
      cases fuel with
      | zero =>
        have hpop : mid.stack.pop7 = some (rest,a0,a1,a2,a3,a4,a5,a6) := by
          rw [Z_ok_stack hz, hstack]
          rfl
        simp only [StepOk, Step, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at hs
        rw [hpop] at hs
        change Except.error ExecutionException.OutOfFuel = Except.ok post at hs
        cases hs
      | succ fuel =>
        exact call_step fuel a0 a1 a2 a3 a4 a5 a6 rest hstack hz hs
    · obtain ⟨a0,a1,a2,a3,a4,a5,a6,rest,hstack⟩ := stack7 pre.stack (by simpa only [δ, Option.getD_some] using hsize)
      cases fuel with
      | zero =>
        have hpop : mid.stack.pop7 = some (rest,a0,a1,a2,a3,a4,a5,a6) := by
          rw [Z_ok_stack hz, hstack]
          rfl
        simp only [StepOk, Step, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at hs
        rw [hpop] at hs
        change Except.error ExecutionException.OutOfFuel = Except.ok post at hs
        cases hs
      | succ fuel =>
        exact family_step .callcode fuel a0 a1 a2 a3 a4 a5 a6 rest hstack hz hs
    · obtain ⟨a0,a1,a2,a3,a4,a5,rest,hstack⟩ := stack6 pre.stack (by simpa only [δ, Option.getD_some] using hsize)
      cases fuel with
      | zero =>
        have hpop : mid.stack.pop6 = some (rest,a0,a1,a2,a3,a4,a5) := by
          rw [Z_ok_stack hz, hstack]
          rfl
        simp only [StepOk, Step, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at hs
        rw [hpop] at hs
        change Except.error ExecutionException.OutOfFuel = Except.ok post at hs
        cases hs
      | succ fuel =>
        exact family_step .delegatecall fuel a0 a1 ⟨0⟩ a2 a3 a4 a5 rest hstack hz hs
    · obtain ⟨a0,a1,a2,a3,a4,a5,rest,hstack⟩ := stack6 pre.stack (by simpa only [δ, Option.getD_some] using hsize)
      cases fuel with
      | zero =>
        have hpop : mid.stack.pop6 = some (rest,a0,a1,a2,a3,a4,a5) := by
          rw [Z_ok_stack hz, hstack]
          rfl
        simp only [StepOk, Step, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at hs
        rw [hpop] at hs
        change Except.error ExecutionException.OutOfFuel = Except.ok post at hs
        cases hs
      | succ fuel =>
        exact family_step .staticcall fuel a0 a1 ⟨0⟩ a2 a3 a4 a5 rest hstack hz hs
    · obtain ⟨a0,a1,a2,rest,hstack⟩ := stack3 pre.stack (by simpa only [δ, Option.getD_some] using hsize)
      exact creation_step .create fuel a0 a1 a2 ⟨0⟩ rest hstack hz hs
    · obtain ⟨a0,a1,a2,a3,rest,hstack⟩ := stack4 pre.stack (by simpa only [δ, Option.getD_some] using hsize)
      exact creation_step .create2 fuel a0 a1 a2 a3 rest hstack hz hs

#print axioms stipend_margin
#print axioms callgas_margin
#print axioms creation_cost
#print axioms creation_allowance_margin
#print axioms selected_child_fuel_exact
#print axioms selected_child_fuel_gap
#print axioms selected_child_gas_lt
#print axioms call_step
#print axioms family_step
#print axioms creation_step
#print axioms recursive_step_drop
end Eip8282.Audit.Integrator.RecursiveGasProgress
