import Eip8282.Audit.Integrator.CallFamilyGas

/-!
# Worlds published by actual CALL-family dispatch

The admitted helper publishes precisely its actual child Θ result's account map,
including false-status results. Denied dispatch leaves the account map unchanged.
No child funding theorem, gas bound or predicted post-state is a premise. Source,
recipient, code target and actual/apparent values remain those of literal dispatch.
-/
namespace Eip8282.Audit.Integrator.CallWorld

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open CallGasAccounting
open CallDispatchGas (entered)

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- Exact world projection of the actual admitted EVM.call helper. Its gate is
the executable owner's funds/depth test, even for arbitrary source parameters. -/
theorem call_child_world
    (fuel cost : Nat) (hashes : List ByteArray)
    (requested source recipient target value apparent inOff inLen outOff outLen : UInt256)
    (permission : Bool) (pre post : EVM.State) (x : UInt256)
    (hgate : value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      pre.executionEnv.depth < 1024)
    (hcall : EVM.call (fuel+1) cost hashes requested source recipient target
      value apparent inOff inLen outOff outLen permission pre = .ok (x,post)) :
    ∃ created world gas substate success out,
      child fuel hashes requested source recipient target value apparent inOff inLen permission pre =
        .ok (created,world,gas,substate,success,out) ∧ post.accountMap = world := by
  cases he : child fuel hashes requested source recipient target value apparent inOff inLen permission pre with
  | error err =>
      unfold child at he
      simp only [EVM.call, hgate, true_and, ↓reduceIte, he, Bind.bind, Except.bind] at hcall
      cases hcall
  | ok result =>
      obtain ⟨created,world,gas,substate,success,out⟩ := result
      refine ⟨created,world,gas,substate,success,out,rfl,?_⟩
      unfold child at he
      simp only [EVM.call, hgate, true_and, ↓reduceIte, he, Bind.bind, Except.bind,
        pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hcall
      exact (congrArg (fun st : EVM.State => st.accountMap) hcall.2).symm

/-- A denied helper invokes no child and preserves its actual input world. -/
theorem call_denied_world
    (fuel cost : Nat) (hashes : List ByteArray)
    (requested source recipient target value apparent inOff inLen outOff outLen : UInt256)
    (permission : Bool) (pre post : EVM.State) (x : UInt256)
    (hgate : ¬ (value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      pre.executionEnv.depth < 1024))
    (hcall : EVM.call (fuel+1) cost hashes requested source recipient target
      value apparent inOff inLen outOff outLen permission pre = .ok (x,post)) :
    x = ⟨0⟩ ∧ post.accountMap = pre.accountMap := by
  simp only [EVM.call, hgate, ↓reduceIte, Bind.bind, Except.bind,
    Bool.not_false, Bool.true_or, Except.ok.injEq, Prod.mk.injEq] at hcall
  exact ⟨hcall.1.symm, (congrArg (fun st : EVM.State => st.accountMap) hcall.2).symm⟩

/-- CALL's stack/PC replacement publishes the same actual child world. -/
theorem step_call_world (fuel cost : Nat) {pre post : EVM.State}
    {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::rest)
    (hgate : value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      pre.executionEnv.depth < 1024)
    (h : StepOk (fuel+2) cost (.CALL,arg) pre post) :
    ∃ created world gas substate success out,
      child fuel pre.executionEnv.blobVersionedHashes requested
        (UInt256.ofNat pre.executionEnv.codeOwner) target target value value inOff inLen
        pre.executionEnv.perm (entered pre) = .ok (created,world,gas,substate,success,out) ∧
      post.accountMap = world := by
  obtain ⟨x,middle,hh,hpost⟩ :=
    CallDispatchGas.step_call_helper fuel cost requested target value inOff inLen outOff outLen rest hstack h
  obtain ⟨created,world,gas,substate,success,out,hchild,hworld⟩ :=
    call_child_world fuel cost pre.executionEnv.blobVersionedHashes requested
      (UInt256.ofNat pre.executionEnv.codeOwner) target target value value inOff inLen outOff outLen
      pre.executionEnv.perm (entered pre) middle x hgate hh
  refine ⟨created,world,gas,substate,success,out,hchild,?_⟩
  rw [hpost]
  exact hworld

theorem step_call_denied_world (fuel cost : Nat) {pre post : EVM.State}
    {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::rest)
    (hgate : ¬ (value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
      pre.executionEnv.depth < 1024))
    (h : StepOk (fuel+2) cost (.CALL,arg) pre post) :
    post.stack = ⟨0⟩::rest ∧ post.accountMap = pre.accountMap := by
  obtain ⟨x,middle,hh,hpost⟩ :=
    CallDispatchGas.step_call_helper fuel cost requested target value inOff inLen outOff outLen rest hstack h
  obtain ⟨hx,hworld⟩ := call_denied_world fuel cost pre.executionEnv.blobVersionedHashes requested
    (UInt256.ofNat pre.executionEnv.codeOwner) target target value value inOff inLen outOff outLen
    pre.executionEnv.perm (entered pre) middle x hgate hh
  rw [hpost, hx]
  exact ⟨rfl,hworld⟩

/-- CALLCODE/DELEGATECALL/STATICCALL retain their actual distinct argument
layouts. The world is the returned Θ world, not a separately chosen state. -/
theorem step_family_world (kind : CallFamilyGas.Variant) (fuel cost : Nat)
    {pre post : EVM.State} {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = CallFamilyGas.stack kind requested target value inOff inLen outOff outLen rest)
    (hgate : CallFamilyGas.gate kind pre value)
    (h : StepOk (fuel+2) cost (CallFamilyGas.opcode kind,arg) pre post) :
    ∃ created world gas substate success out,
      CallFamilyGas.childResult kind fuel pre requested target value inOff inLen =
        .ok (created,world,gas,substate,success,out) ∧ post.accountMap = world := by
  obtain ⟨x,middle,hh,hpost⟩ :=
    CallFamilyGas.step_helper kind fuel cost requested target value inOff inLen outOff outLen rest hstack h
  obtain ⟨created,world,gas,substate,success,out,hchild,hworld⟩ :=
    call_child_world fuel cost pre.executionEnv.blobVersionedHashes requested
      (CallFamilyGas.source kind pre) (CallFamilyGas.recipient kind pre target) target
      (CallFamilyGas.transfer kind value) (CallFamilyGas.apparent kind pre value)
      inOff inLen outOff outLen (CallFamilyGas.permission kind pre) (entered pre) middle x hgate hh
  refine ⟨created,world,gas,substate,success,out,hchild,?_⟩
  rw [hpost]
  exact hworld

theorem step_family_denied_world (kind : CallFamilyGas.Variant) (fuel cost : Nat)
    {pre post : EVM.State} {arg : Option (UInt256 × Nat)}
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = CallFamilyGas.stack kind requested target value inOff inLen outOff outLen rest)
    (hgate : ¬ CallFamilyGas.gate kind pre value)
    (h : StepOk (fuel+2) cost (CallFamilyGas.opcode kind,arg) pre post) :
    post.stack = ⟨0⟩::rest ∧ post.accountMap = pre.accountMap := by
  obtain ⟨x,middle,hh,hpost⟩ :=
    CallFamilyGas.step_helper kind fuel cost requested target value inOff inLen outOff outLen rest hstack h
  obtain ⟨hx,hworld⟩ := call_denied_world fuel cost pre.executionEnv.blobVersionedHashes requested
    (CallFamilyGas.source kind pre) (CallFamilyGas.recipient kind pre target) target
    (CallFamilyGas.transfer kind value) (CallFamilyGas.apparent kind pre value)
    inOff inLen outOff outLen (CallFamilyGas.permission kind pre) (entered pre) middle x hgate hh
  rw [hpost, hx]
  exact ⟨rfl,hworld⟩

#print axioms call_child_world
#print axioms call_denied_world
#print axioms step_call_world
#print axioms step_call_denied_world
#print axioms step_family_world
#print axioms step_family_denied_world
end Eip8282.Audit.Integrator.CallWorld
