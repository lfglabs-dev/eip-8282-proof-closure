import Eip8282.Audit.Integrator.CreationGas

/-!
# The exact world selected by actual CREATE/CREATE2 dispatch

A completed child contributes its actual returned world. A caught Lambda error
contributes the evaluator's literal empty map. This is an execution projection,
not an assumption of funding conservation or a reconstructed journal.
-/
namespace Eip8282.Audit.Integrator.CreationWorld
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open CreationGas
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem step_world (kind : Variant) (fuel cost : Nat) {pre post : EVM.State}
    {arg : Option (UInt256 × Nat)} (value off len salt : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = stack kind value off len salt rest)
    (hnonce : nonceAllowed pre) (hgate : gate pre value off len)
    (h : StepOk (fuel+1) cost (opcode kind,arg) pre post) :
    (∃ addr created world gas substate success out,
      child kind fuel cost pre value off len salt = .ok (addr,created,world,gas,substate,success,out) ∧
      post.accountMap = world) ∨
    (∃ err, child kind fuel cost pre value off len salt = .error err ∧ post.accountMap = ∅) := by
  have hn : ¬ (pre.accountMap.get? pre.executionEnv.codeOwner |>.getD default).nonce.toNat ≥ 2^64-1 :=
    Nat.not_le.mpr hnonce
  have hg : value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding off.toNat len.toNat).size ≤ 49152 := hgate
  cases he : child kind fuel cost pre value off len salt with
  | error err =>
    right
    refine ⟨err,rfl,?_⟩
    unfold child at he
    cases kind with
    | create =>
      have hs : pre.stack.pop3 = some (rest,value,off,len) := by rw [hstack]; rfl
      simp only [StepOk, Step, opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at h
      rw [hs] at h
      simp only [hn, hg, true_and, ↓reduceIte] at h
      dsimp only [stepPre, init, saltBytes] at he
      rw [he] at h
      replace h := elim_guard h
      rw [← Except.ok.inj h]
      rfl
    | create2 =>
      have hs : pre.stack.pop4 = some (rest,value,off,len,salt) := by rw [hstack]; rfl
      simp only [StepOk, Step, opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at h
      rw [hs] at h
      simp only [hn, hg, true_and, ↓reduceIte] at h
      dsimp only [stepPre, init, saltBytes] at he
      rw [he] at h
      replace h := elim_guard h
      rw [← Except.ok.inj h]
      rfl
  | ok result =>
    obtain ⟨addr,cr,world,gas,ss,z,out⟩ := result
    left
    refine ⟨addr,cr,world,gas,ss,z,out,rfl,?_⟩
    unfold child at he
    cases kind with
    | create =>
      have hs : pre.stack.pop3 = some (rest,value,off,len) := by rw [hstack]; rfl
      simp only [StepOk, Step, opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at h
      rw [hs] at h
      simp only [hn, hg, true_and, ↓reduceIte] at h
      dsimp only [stepPre, init, saltBytes] at he
      rw [he] at h
      replace h := elim_guard h
      rw [← Except.ok.inj h]
      rfl
    | create2 =>
      have hs : pre.stack.pop4 = some (rest,value,off,len,salt) := by rw [hstack]; rfl
      simp only [StepOk, Step, opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at h
      rw [hs] at h
      simp only [hn, hg, true_and, ↓reduceIte] at h
      dsimp only [stepPre, init, saltBytes] at he
      rw [he] at h
      replace h := elim_guard h
      rw [← Except.ok.inj h]
      rfl

#print axioms step_world
end Eip8282.Audit.Integrator.CreationWorld
