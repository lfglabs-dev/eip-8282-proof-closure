import Eip8282.Audit.Integrator.ActualAppendGas

/-!
# Actual CALL child gas settlement

These are projections of the pinned EVM.call and Theta semantics. The child
result is recovered from the actual call result, not supplied as a predicted
post-state. The arithmetic layer retains a local child remaining-gas bound;
it does not assume or establish aggregate call-tree debit accounting. Both
funded and denied helper branches are covered. Relating EVM.step CALL dispatch
(including its instruction-count update), other CALL-family stack layouts,
CREATE, precompiles and ancestor error traces remains separate.
-/
namespace Eip8282.Audit.Integrator.CallGasAccounting

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open ActualAppendGas
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
set_option autoImplicit false

/-- Literal child Theta invocation in the funded, below-depth-limit call branch. -/
def child (fuel : Nat) (hashes : List ByteArray)
    (requested source recipient target value apparent inOff inLen : UInt256)
    (permission : Bool) (pre : EVM.State) :=
  Θ fuel hashes pre.createdAccounts pre.genesisBlockHeader pre.blocks
    pre.accountMap pre.σ₀
    (pre.addAccessedAccount (AccountAddress.ofUInt256 target)).substate
    (AccountAddress.ofUInt256 source) pre.executionEnv.sender
    (AccountAddress.ofUInt256 recipient)
    (toExecute .EVM pre.accountMap (AccountAddress.ofUInt256 target))
    (UInt256.ofNat (Ccallgas (AccountAddress.ofUInt256 target)
      (AccountAddress.ofUInt256 recipient) value requested
      pre.accountMap pre.toMachineState pre.substate))
    (UInt256.ofNat pre.executionEnv.gasPrice) value apparent
    (pre.memory.readWithPadding inOff.toNat inLen.toNat)
    (pre.executionEnv.depth+1) pre.executionEnv.header permission

/-- Recover the actual child invocation and exact word-gas settlement. This
covers successful and false-status child results, with the same gas equation. -/
theorem call_child_result_gas
    (fuel cost : Nat) (hashes : List ByteArray)
    (requested source recipient target value apparent inOff inLen outOff outLen : UInt256)
    (permission : Bool) (pre post : EVM.State) (x : UInt256)
    (hgate : value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      pre.executionEnv.depth < 1024)
    (hcall : EvmYul.EVM.call (fuel+1) cost hashes requested source recipient target
      value apparent inOff inLen outOff outLen permission pre = .ok (x,post)) :
    ∃ created world returnedGas substate success out,
      child fuel hashes requested source recipient target value apparent inOff inLen permission pre =
        .ok (created,world,returnedGas,substate,success,out) ∧
      post.gasAvailable = pre.gasAvailable - UInt256.ofNat cost + returnedGas := by
  cases he : child fuel hashes requested source recipient target value apparent inOff inLen permission pre with
  | error err =>
      unfold child at he
      simp only [EvmYul.EVM.call, hgate, true_and, ↓reduceIte, he, Bind.bind, Except.bind] at hcall
      cases hcall
  | ok res =>
      rcases res with ⟨created, world, returnedGas, substate, success, out⟩
      refine ⟨created, world, returnedGas, substate, success, out, rfl, ?_⟩
      unfold child at he
      simp only [EvmYul.EVM.call, hgate, true_and, ↓reduceIte, he, Bind.bind, Except.bind,
        pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hcall
      have hp := hcall.2
      exact (congrArg (fun st : EVM.State => st.gasAvailable) hp).symm

/-- The stipend is determined by actual transferred value, not apparent value. -/
def stipend (value : UInt256) : Nat := if value = ⟨0⟩ then 0 else GasConstants.Gcallstipend

theorem callgas_eq (target recipient : AccountAddress) (value requested : UInt256)
    (world : AccountMap .EVM) (machine : MachineState) (substate : Substate) :
    Ccallgas target recipient value requested world machine substate =
      Cgascap target recipient value requested world machine substate + stipend value := by
  rcases value with ⟨⟨n, hn⟩⟩
  cases n with
  | zero => rfl
  | succ n => rfl

theorem stipend_le_extra (target recipient : AccountAddress) (value : UInt256)
    (world : AccountMap .EVM) (substate : Substate) :
    stipend value ≤ Cextra target recipient value world substate := by
  by_cases hz : value = ⟨0⟩
  · simp [stipend, hz]
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

theorem callgas_le_call (target recipient : AccountAddress) (value requested : UInt256)
    (world : AccountMap .EVM) (machine : MachineState) (substate : Substate) :
    Ccallgas target recipient value requested world machine substate ≤
      Ccall target recipient value requested world machine substate := by
  rw [callgas_eq, Ccall]
  exact Nat.add_le_add_left (stipend_le_extra target recipient value world substate) _

/-- Actual Z acceptance identifies CALL's exact charge on its charged state. -/
theorem accepted_call_cost {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    {requested target value inOff inLen outOff outLen : UInt256} {stk : Stack UInt256}
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::stk)
    (hz : Z vj .CALL pre = .ok (mid,cost)) :
    cost = Ccall (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
      value requested mid.accountMap mid.toMachineState mid.substate := by
  have hs := (Z_ok_stack hz).trans hstack
  rw [(accepted_gas hz).2.2.2]
  simp only [C', hs, List.getElem!_cons_succ, List.getElem!_cons_zero]

/-- A local algebraic projection. Its word settlement input comes from the
actual call theorem, and cost sufficiency from actual accepted Z. -/
theorem settlement_nat (target recipient : AccountAddress) (value requested : UInt256)
    (pre : EVM.State) (postGas returnedGas : UInt256) (cost : Nat)
    (hc : cost = Ccall target recipient value requested pre.accountMap pre.toMachineState pre.substate)
    (hs : cost ≤ pre.gasAvailable.toNat)
    (hr : returnedGas.toNat ≤ Ccallgas target recipient value requested
      pre.accountMap pre.toMachineState pre.substate)
    (he : postGas = pre.gasAvailable - UInt256.ofNat cost + returnedGas) :
    (UInt256.ofNat (Ccallgas target recipient value requested
      pre.accountMap pre.toMachineState pre.substate)).toNat =
      Ccallgas target recipient value requested pre.accountMap pre.toMachineState pre.substate ∧
    postGas.toNat +
      (Ccallgas target recipient value requested pre.accountMap pre.toMachineState pre.substate - returnedGas.toNat) +
      (Cextra target recipient value pre.accountMap pre.substate - stipend value) = pre.gasAvailable.toNat := by
  have hb := callgas_le_call target recipient value requested pre.accountMap pre.toMachineState pre.substate
  rw [← hc] at hb
  have hfit : Ccallgas target recipient value requested pre.accountMap pre.toMachineState pre.substate < UInt256.size :=
    hb.trans_lt (hs.trans_lt pre.gasAvailable.val.isLt)
  refine ⟨toNat_ofNat_lit _ hfit, ?_⟩
  have hsub := toNat_sub_ofNat hs
  have hadd : (pre.gasAvailable - UInt256.ofNat cost).toNat + returnedGas.toNat < UInt256.size := by
    rw [hsub]
    have hg : pre.gasAvailable.toNat < UInt256.size := pre.gasAvailable.val.isLt
    omega
  rw [he, toNat_add_of_lt _ _ hadd, hsub]
  have hext := stipend_le_extra target recipient value pre.accountMap pre.substate
  rw [callgas_eq] at hr ⊢
  unfold Ccall at hc
  omega

/-- A genuine child result and a remaining-gas bound yield the natural debit
identity. All word fits follow from actual Z, including the stipend allowance.
This theorem concerns EVM.call on Z's charged state; opcode dispatch and aggregate
call-tree accounting are separate layers. -/
theorem accepted_call_child_debit
    (fuel : Nat) (hashes : List ByteArray)
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat}
    (requested target value inOff inLen outOff outLen source apparent : UInt256)
    (permission : Bool) (stk : Stack UInt256) (x : UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::stk)
    (hz : Z vj .CALL pre = .ok (mid,cost))
    (hgate : value ≤ (mid.accountMap.get? mid.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      mid.executionEnv.depth < 1024)
    (hcall : EvmYul.EVM.call (fuel+1) cost hashes requested source target target
      value apparent inOff inLen outOff outLen permission mid = .ok (x,post)) :
    ∃ created world returnedGas substate success out,
      child fuel hashes requested source target target value apparent inOff inLen permission mid =
        .ok (created,world,returnedGas,substate,success,out) ∧
      (returnedGas.toNat ≤ Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        value requested mid.accountMap mid.toMachineState mid.substate →
        post.gasAvailable.toNat +
          (Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
            value requested mid.accountMap mid.toMachineState mid.substate - returnedGas.toNat) +
          (Cextra (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
            value mid.accountMap mid.substate - stipend value) + memoryExpansionCost pre .CALL =
          pre.gasAvailable.toNat) := by
  obtain ⟨created, world, returnedGas, substate, success, out, hchild, hgas⟩ :=
    call_child_result_gas fuel cost hashes requested source target target value apparent
      inOff inLen outOff outLen permission mid post x hgate hcall
  refine ⟨created, world, returnedGas, substate, success, out, hchild, ?_⟩
  intro hreturn
  obtain ⟨hm, hmid, hcost, _⟩ := accepted_gas hz
  have hd := (settlement_nat (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
    value requested mid post.gasAvailable returnedGas cost
    (accepted_call_cost hstack hz) hcost hreturn hgas).2
  omega

/-- Forwarded gas fits its word before knowing anything about child execution. -/
theorem accepted_call_forwarded_fit {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    {requested target value inOff inLen outOff outLen : UInt256} {stk : Stack UInt256}
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::stk)
    (hz : Z vj .CALL pre = .ok (mid,cost)) :
    let b := Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
      value requested mid.accountMap mid.toMachineState mid.substate
    b < UInt256.size ∧ (UInt256.ofNat b).toNat = b := by
  have hc := accepted_call_cost hstack hz
  have hb := callgas_le_call (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
    value requested mid.accountMap mid.toMachineState mid.substate
  rw [← hc] at hb
  have hfit := (hb.trans (accepted_gas hz).2.2.1).trans_lt mid.gasAvailable.val.isLt
  exact ⟨hfit, toNat_ofNat_lit _ hfit⟩

/-- The denied funds/depth branch invokes no child and credits back callgas.
This is the actual helper result, including the value-carrying stipend. -/
theorem call_denied_gas
    (fuel cost : Nat) (hashes : List ByteArray)
    (requested source recipient target value apparent inOff inLen outOff outLen : UInt256)
    (permission : Bool) (pre post : EVM.State) (x : UInt256)
    (hgate : ¬ (value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      pre.executionEnv.depth < 1024))
    (hcall : EvmYul.EVM.call (fuel+1) cost hashes requested source recipient target
      value apparent inOff inLen outOff outLen permission pre = .ok (x,post)) :
    x = ⟨0⟩ ∧ post.gasAvailable = pre.gasAvailable - UInt256.ofNat cost +
      UInt256.ofNat (Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 recipient)
        value requested pre.accountMap pre.toMachineState pre.substate) := by
  simp only [EvmYul.EVM.call, hgate, ↓reduceIte, Bind.bind, Except.bind,
    Bool.not_false, Bool.true_or, Except.ok.injEq, Prod.mk.injEq] at hcall
  exact ⟨hcall.1.symm, (congrArg (fun st : EVM.State => st.gasAvailable) hcall.2).symm⟩


#print axioms call_child_result_gas
#print axioms callgas_le_call
#print axioms accepted_call_cost
#print axioms settlement_nat
#print axioms accepted_call_child_debit
#print axioms accepted_call_forwarded_fit
#print axioms call_denied_gas

end Eip8282.Audit.Integrator.CallGasAccounting
