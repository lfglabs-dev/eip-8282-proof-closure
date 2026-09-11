import Eip8282.Audit.Integrator.OrdinaryGas
import Eip8282.Audit.Integrator.CreationSettlement

/-!
# Actual CREATE/CREATE2 gas accounting

The dispatcher catches every Lambda exception, including proof OutOfFuel, and
continues with zero returned child gas and an empty account map. That behavior
is retained literally. No child remaining-gas or aggregate debit is invented.
-/
namespace Eip8282.Audit.Integrator.CreationGas

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open ActualAppendGas
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

inductive Variant where | create | create2 deriving DecidableEq

def opcode : Variant → Operation .EVM | .create => .CREATE | .create2 => .CREATE2

def stack (kind : Variant) (value off len salt : UInt256) (rest : Stack UInt256) : Stack UInt256 :=
  match kind with
  | .create => value::off::len::rest
  | .create2 => value::off::len::salt::rest

def saltBytes (kind : Variant) (salt : UInt256) : Option ByteArray :=
  match kind with | .create => none | .create2 => some salt.toByteArray

def init (pre : EVM.State) (off len : UInt256) : ByteArray :=
  pre.memory.readWithPadding off.toNat len.toNat

def nonceAllowed (pre : EVM.State) : Prop :=
  (pre.accountMap.get? pre.executionEnv.codeOwner |>.getD default).nonce.toNat < 2^64-1

def gate (pre : EVM.State) (value off len : UInt256) : Prop :=
  value ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ∧
    pre.executionEnv.depth < 1024 ∧ (init pre off len).size ≤ 49152

/-- Forwarding uses gas after opcode cost, unlike CALL's Ccallgas calculation. -/
def allowance (cost : Nat) (pre : EVM.State) : Nat := L (stepPre cost pre).gasAvailable.toNat

/-- Literal Lambda invocation after the actual nonce increment. Fuel zero is
kept: its OutOfFuel is caught by CREATE, rather than propagated as for CALL. -/
def child (kind : Variant) (fuel cost : Nat) (pre : EVM.State) (value off len salt : UInt256) :=
  let charged := stepPre cost pre
  let owner := charged.executionEnv.codeOwner
  let account := charged.accountMap.get? owner |>.getD default
  let world := charged.accountMap.insert owner {account with nonce := account.nonce+⟨1⟩}
  Lambda fuel charged.executionEnv.blobVersionedHashes charged.createdAccounts charged.genesisBlockHeader
    charged.blocks world charged.σ₀ charged.substate owner charged.executionEnv.sender
    (UInt256.ofNat (L charged.gasAvailable.toNat)) (UInt256.ofNat charged.executionEnv.gasPrice)
    value (init charged off len) (UInt256.ofNat (charged.executionEnv.depth+1))
    (saltBytes kind salt) charged.executionEnv.header charged.executionEnv.perm

/-- Actual creation dispatch with admitted nonce/funds/depth/code length either
receives a real Lambda tuple or catches a real Lambda exception. -/
theorem step_child (kind : Variant) (fuel cost : Nat) {pre post : EVM.State}
    {arg : Option (UInt256 × Nat)} (value off len salt : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = stack kind value off len salt rest)
    (hnonce : nonceAllowed pre) (hgate : gate pre value off len)
    (h : StepOk (fuel+1) cost (opcode kind,arg) pre post) :
    (∃ addr created world returnedGas substate success out,
      child kind fuel cost pre value off len salt = .ok (addr,created,world,returnedGas,substate,success,out) ∧
      post.gasAvailable = UInt256.ofNat ((stepPre cost pre).gasAvailable.toNat - allowance cost pre + returnedGas.toNat)) ∨
    (∃ err, child kind fuel cost pre value off len salt = .error err ∧
      post.gasAvailable = UInt256.ofNat ((stepPre cost pre).gasAvailable.toNat - allowance cost pre) ∧
      post.accountMap = ∅ ∧ post.stack = ⟨0⟩::rest ∧ post.returnData = .empty) := by
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
      have hp := (Except.ok.inj h).symm
      rw [hp]
      exact ⟨rfl,rfl,rfl,rfl⟩
    | create2 =>
      have hs : pre.stack.pop4 = some (rest,value,off,len,salt) := by rw [hstack]; rfl
      simp only [StepOk, Step, opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at h
      rw [hs] at h
      simp only [hn, hg, true_and, ↓reduceIte] at h
      dsimp only [stepPre, init, saltBytes] at he
      rw [he] at h
      replace h := elim_guard h
      have hp := (Except.ok.inj h).symm
      rw [hp]
      exact ⟨rfl,rfl,rfl,rfl⟩
  | ok result =>
    obtain ⟨addr,created,world,returnedGas,substate,success,out⟩ := result
    left
    refine ⟨addr,created,world,returnedGas,substate,success,out,rfl,?_⟩
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
      have hp := (Except.ok.inj h).symm
      rw [hp]
      rfl
    | create2 =>
      have hs : pre.stack.pop4 = some (rest,value,off,len,salt) := by rw [hstack]; rfl
      simp only [StepOk, Step, opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at h
      rw [hs] at h
      simp only [hn, hg, true_and, ↓reduceIte] at h
      dsimp only [stepPre, init, saltBytes] at he
      rw [he] at h
      replace h := elim_guard h
      have hp := (Except.ok.inj h).symm
      rw [hp]
      rfl

/-- Denial at either creation gate invokes no child. The actual final overflow
check must still have passed, as required by StepOk; no liveness is asserted. -/
theorem step_denied (kind : Variant) (fuel cost : Nat) {pre post : EVM.State}
    {arg : Option (UInt256 × Nat)} (value off len salt : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = stack kind value off len salt rest)
    (hdenied : ¬ nonceAllowed pre ∨ ¬ gate pre value off len)
    (h : StepOk (fuel+1) cost (opcode kind,arg) pre post) :
    post.gasAvailable = UInt256.ofNat ((stepPre cost pre).gasAvailable.toNat - allowance cost pre +
      (UInt256.ofNat (allowance cost pre)).toNat) ∧ post.stack = ⟨0⟩::rest ∧
      post.accountMap = pre.accountMap ∧ post.returnData = .empty := by
  have hexhaust : (pre.accountMap.get? pre.executionEnv.codeOwner |>.getD default).nonce.toNat ≥ 2^64-1 ∨
      ¬ gate pre value off len := by
    rcases hdenied with hn | hg
    · exact Or.inl (Nat.le_of_not_gt hn)
    · exact Or.inr hg
  cases kind with
  | create =>
    have hs : pre.stack.pop3 = some (rest,value,off,len) := by rw [hstack]; rfl
    simp only [StepOk, Step, opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at h
    rw [hs] at h
    rcases hexhaust with hn | hg
    · simp only [hn, ↓reduceIte] at h
      replace h := elim_guard h
      rw [← Except.ok.inj h]
      exact ⟨rfl,rfl,rfl,rfl⟩
    · unfold gate init at hg
      by_cases hn : (pre.accountMap.get? pre.executionEnv.codeOwner |>.getD default).nonce.toNat ≥ 2^64-1
      all_goals
        simp only [hn, hg, ↓reduceIte] at h
        replace h := elim_guard h
        rw [← Except.ok.inj h]
        exact ⟨rfl,rfl,rfl,rfl⟩
  | create2 =>
    have hs : pre.stack.pop4 = some (rest,value,off,len,salt) := by rw [hstack]; rfl
    simp only [StepOk, Step, opcode, EVM.step, Bind.bind, Except.bind, pure, Except.pure] at h
    rw [hs] at h
    rcases hexhaust with hn | hg
    · simp only [hn, ↓reduceIte] at h
      replace h := elim_guard h
      rw [← Except.ok.inj h]
      exact ⟨rfl,rfl,rfl,rfl⟩
    · unfold gate init at hg
      by_cases hn : (pre.accountMap.get? pre.executionEnv.codeOwner |>.getD default).nonce.toNat ≥ 2^64-1
      all_goals
        simp only [hn, hg, ↓reduceIte] at h
        replace h := elim_guard h
        rw [← Except.ok.inj h]
        exact ⟨rfl,rfl,rfl,rfl⟩

/-- The post-charge word and L ensure forwarding always fits its word. -/
theorem forwarded_fit (cost : Nat) (pre : EVM.State) :
    allowance cost pre ≤ (stepPre cost pre).gasAvailable.toNat ∧
    (UInt256.ofNat (allowance cost pre)).toNat = allowance cost pre := by
  have hl : allowance cost pre ≤ (stepPre cost pre).gasAvailable.toNat := Nat.sub_le _ _
  exact ⟨hl, toNat_ofNat_lit _ (hl.trans_lt (stepPre cost pre).gasAvailable.val.isLt)⟩

/-- Exact natural settlement after creation's actual word opcode debit. A local
bound on returned child gas suffices; all parent additions then fit a word. -/
theorem settlement_nat (cost : Nat) (pre : EVM.State) (returnedGas postGas : UInt256)
    (hc : cost ≤ pre.gasAvailable.toNat) (hr : returnedGas.toNat ≤ allowance cost pre)
    (he : postGas = UInt256.ofNat ((stepPre cost pre).gasAvailable.toNat - allowance cost pre + returnedGas.toNat)) :
    postGas.toNat + (allowance cost pre - returnedGas.toNat) + cost = pre.gasAvailable.toNat := by
  have hq : (stepPre cost pre).gasAvailable.toNat = pre.gasAvailable.toNat - cost := toNat_sub_ofNat hc
  have hl := (forwarded_fit cost pre).1
  have hw : (stepPre cost pre).gasAvailable.toNat < UInt256.size := (stepPre cost pre).gasAvailable.val.isLt
  have hfit : (stepPre cost pre).gasAvailable.toNat - allowance cost pre + returnedGas.toNat < UInt256.size := by omega
  rw [he, toNat_ofNat_lit _ hfit]
  omega

/-- Real admitted CREATE/CREATE2 either debits an actual completed Lambda child,
conditionally on its local remaining-gas bound, or consumes the whole allowance
when that actual Lambda raises any exception (including OutOfFuel). -/
theorem accepted_child_debit (kind : Variant) (fuel : Nat)
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat}
    {arg : Option (UInt256 × Nat)} (value off len salt : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = stack kind value off len salt rest)
    (hz : Z vj (opcode kind) pre = .ok (mid,cost))
    (hnonce : nonceAllowed mid) (hgate : gate mid value off len)
    (h : StepOk (fuel+1) cost (opcode kind,arg) mid post) :
    (∃ addr created world returnedGas substate success out,
      child kind fuel cost mid value off len salt = .ok (addr,created,world,returnedGas,substate,success,out) ∧
      (returnedGas.toNat ≤ allowance cost mid →
        post.gasAvailable.toNat + (allowance cost mid - returnedGas.toNat) + cost +
          memoryExpansionCost pre (opcode kind) = pre.gasAvailable.toNat)) ∨
    (∃ err, child kind fuel cost mid value off len salt = .error err ∧
      post.gasAvailable.toNat + allowance cost mid + cost + memoryExpansionCost pre (opcode kind) = pre.gasAvailable.toNat ∧
      post.accountMap = ∅ ∧ post.stack = ⟨0⟩::rest ∧ post.returnData = .empty) := by
  obtain ⟨hm,hmid,hcost,_⟩ := accepted_gas hz
  rcases step_child kind fuel cost value off len salt rest ((Z_ok_stack hz).trans hstack) hnonce hgate h with ht | ht
  · obtain ⟨addr,created,world,returnedGas,substate,success,out,hchild,hgas⟩ := ht
    left
    refine ⟨addr,created,world,returnedGas,substate,success,out,hchild,?_⟩
    intro hr
    have hd := settlement_nat cost mid returnedGas post.gasAvailable hcost hr hgas
    omega
  · obtain ⟨err,hchild,hgas,hw,hs,ho⟩ := ht
    right
    refine ⟨err,hchild,?_,hw,hs,ho⟩
    have hd := settlement_nat cost mid ⟨0⟩ post.gasAvailable hcost (Nat.zero_le _) hgas
    change post.gasAvailable.toNat + (allowance cost mid - 0) + cost = mid.gasAvailable.toNat at hd
    omega

/-- Denied dispatch pays opcode and memory cost only; no Lambda is inserted. -/
theorem accepted_denied_debit (kind : Variant) (fuel : Nat)
    {vj : Array UInt256} {pre mid post : EVM.State} {cost : Nat}
    {arg : Option (UInt256 × Nat)} (value off len salt : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = stack kind value off len salt rest)
    (hz : Z vj (opcode kind) pre = .ok (mid,cost))
    (hdenied : ¬ nonceAllowed mid ∨ ¬ gate mid value off len)
    (h : StepOk (fuel+1) cost (opcode kind,arg) mid post) :
    post.gasAvailable.toNat + cost + memoryExpansionCost pre (opcode kind) = pre.gasAvailable.toNat ∧
      post.stack = ⟨0⟩::rest ∧ post.accountMap = mid.accountMap ∧ post.returnData = .empty := by
  obtain ⟨hgas,hs,hw,ho⟩ := step_denied kind fuel cost value off len salt rest ((Z_ok_stack hz).trans hstack) hdenied h
  obtain ⟨hm,hmid,hcost,_⟩ := accepted_gas hz
  have hfit := (forwarded_fit cost mid).2
  have hd := settlement_nat cost mid (UInt256.ofNat (allowance cost mid)) post.gasAvailable hcost
    (by rw [hfit]) hgas
  rw [hfit, Nat.sub_self, Nat.add_zero] at hd
  exact ⟨by omega,hs,hw,ho⟩

/-- A successful actual Lambda result pays its code-deposit cost from the exact
init result. Address-preimage success is explicit; no post-world is assumed. -/
theorem lambda_code_debit (c : CreationSettlement.Context) {preimage : ByteArray}
    (hp : c.preimage = some preimage)
    {addr : AccountAddress} {created : Std.TreeSet AccountAddress compare}
    {world : AccountMap .EVM} {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (addr,created,world,gas,substate,true,out)) :
    ∃ initWorld initGas code,
      c.execution (CreationSettlement.address preimage) = .ok (.success (created,initWorld,initGas,substate) code) ∧
      gas.toNat + GasConstants.Gcodedeposit * code.size = initGas.toNat := by
  obtain ⟨iw,ig,code,he,hf,_,_,hg,_⟩ := CreationSettlement.success_inversion c hp h
  refine ⟨iw,ig,code,he,?_⟩
  have hc : GasConstants.Gcodedeposit * code.size ≤ ig.toNat := by
    by_contra hn
    have hl : ig.toNat < GasConstants.Gcodedeposit * code.size := Nat.lt_of_not_ge hn
    simp [CreationSettlement.Context.depositFailure, hl] at hf
  have hfit : ig.toNat - GasConstants.Gcodedeposit * code.size < UInt256.size :=
    (Nat.sub_le _ _).trans_lt ig.val.isLt
  rw [hg, toNat_ofNat_lit _ hfit]
  omega

#print axioms step_child
#print axioms step_denied
#print axioms forwarded_fit
#print axioms settlement_nat
#print axioms accepted_child_debit
#print axioms accepted_denied_debit
#print axioms lambda_code_debit
end Eip8282.Audit.Integrator.CreationGas
