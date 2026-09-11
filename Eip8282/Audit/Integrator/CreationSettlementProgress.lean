import Eip8282.Audit.Integrator.CreationOutcome
import Eip8282.Audit.Integrator.ReturnedGas

/-! Successful actual creation settlement under a protocol-sized gas input.
Returned gas is bounded from the actual Lambda equation. The WORD addition
check is proved, rather than supplied as a no-wrap assumption. -/
namespace Eip8282.Audit.Integrator.CreationSettlementProgress
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open CreationGas CreationOutcome
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

def successfulPost (cost : Nat) (pre : EVM.State) (off len : UInt256)
    (rest : Stack UInt256) (address : AccountAddress)
    (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (ss : Substate) : EVM.State :=
  let charged := stepPre cost pre
  let post : EVM.State := { charged with
    accountMap := world
    createdAccounts := created
    substate := ss
    activeWords := UInt256.ofNat (MachineState.M charged.activeWords.toNat off.toNat len.toNat)
    returnData := .empty
    gasAvailable := UInt256.ofNat (charged.gasAvailable.toNat-L charged.gasAvailable.toNat+gas.toNat) }
  post.replaceStackAndIncrPC (UInt256.ofNat address::rest)

/-- All surviving child fields and the caller continuation are explicit. -/
theorem post_fields (cost : Nat) (pre : EVM.State) (off len : UInt256)
    (rest : Stack UInt256) (address : AccountAddress)
    (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (ss : Substate) :
    let post := successfulPost cost pre off len rest address created world gas ss
    post.accountMap = world ∧ post.createdAccounts = created ∧ post.substate = ss ∧
      post.stack = UInt256.ofNat address::rest ∧ post.pc = pre.pc+UInt256.ofNat 1 ∧
      post.returnData = .empty ∧ post.executionEnv = pre.executionEnv := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem actual_child_gas (kind : Variant) (fuel cost : Nat) (pre : EVM.State)
    (value off len salt : UInt256) (address : AccountAddress)
    (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (ss : Substate) (out : ByteArray)
    (hr : child kind fuel cost pre value off len salt = .ok (address,created,world,gas,ss,true,out)) :
    gas.toNat ≤ allowance cost pre := by
  have hb := ReturnedGas.lambda_remaining fuel hr
  change gas.toNat ≤ (UInt256.ofNat (allowance cost pre)).toNat at hb
  rw [(forwarded_fit cost pre).2] at hb
  exact hb

theorem word_guard (charged gas : UInt256) (hb : charged.toNat ≤ 2^64)
    (hg : gas.toNat ≤ L charged.toNat) :
    ¬ (charged+gas).toNat < L charged.toNat := by
  have hl : L charged.toNat ≤ charged.toNat := Nat.sub_le _ _
  have hn : 2*(2^64) < UInt256.size := by decide +kernel
  have hfit : charged.toNat+gas.toNat < UInt256.size := by omega
  rw [toNat_add_of_lt _ _ hfit]
  omega

theorem settle_success (kind : Variant) (fuel cost : Nat) (pre : EVM.State)
    (value off len salt : UInt256) (rest : Stack UInt256) (address : AccountAddress)
    (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (ss : Substate) (out : ByteArray)
    (hr : child kind fuel cost pre value off len salt = .ok (address,created,world,gas,ss,true,out))
    (hgate : gate pre value off len)
    (hb : (stepPre cost pre).gasAvailable.toNat ≤ 2^64) :
    settle cost pre value off len rest (.ok (address,created,world,gas,ss,true,out)) =
      .ok (successfulPost cost pre off len rest address created world gas ss) := by
  have hgas := actual_child_gas kind fuel cost pre value off len salt address created world gas ss out hr
  have hguard := word_guard (stepPre cost pre).gasAvailable gas hb hgas
  have hd : ¬ (stepPre cost pre).executionEnv.depth = 1024 := by
    have := hgate.2.1
    change ¬ pre.executionEnv.depth = 1024
    omega
  have hv : ¬ value > ((stepPre cost pre).accountMap.get? (stepPre cost pre).executionEnv.codeOwner
      |>.option ⟨0⟩ (·.balance)) := by
    exact Nat.not_lt.mpr hgate.1
  have hi : ¬ (init (stepPre cost pre) off len).size > 49152 := Nat.not_lt.mpr hgate.2.2
  simp only [settle,select,finish,Bind.bind,Except.bind,pure,Except.pure]
  rw [if_neg hguard]
  simp only [Bool.true_eq_false,hd,hv,hi,or_self,if_false,if_true]
  rfl

theorem post_gas (cost : Nat) (pre : EVM.State) (off len : UInt256)
    (rest : Stack UInt256) (address : AccountAddress)
    (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (ss : Substate)
    (hg : gas.toNat ≤ allowance cost pre) :
    (successfulPost cost pre off len rest address created world gas ss).gasAvailable.toNat =
      (stepPre cost pre).gasAvailable.toNat/64+gas.toNat := by
  have hl : L (stepPre cost pre).gasAvailable.toNat ≤ (stepPre cost pre).gasAvailable.toNat := Nat.sub_le _ _
  have hw : (stepPre cost pre).gasAvailable.toNat < UInt256.size :=
    (stepPre cost pre).gasAvailable.val.isLt
  have hfit : (stepPre cost pre).gasAvailable.toNat - L (stepPre cost pre).gasAvailable.toNat + gas.toNat <
      UInt256.size := by change gas.toNat ≤ L (stepPre cost pre).gasAvailable.toNat at hg; omega
  change (UInt256.ofNat _).toNat = _
  rw [toNat_ofNat_lit _ hfit]
  unfold L
  omega

theorem step_success (kind : Variant) (fuel cost : Nat) (pre : EVM.State)
    (arg : Option (UInt256 × Nat)) (value off len salt : UInt256) (rest : Stack UInt256)
    (address : AccountAddress) (created : Std.TreeSet AccountAddress compare)
    (world : AccountMap .EVM) (gas : UInt256) (ss : Substate) (out : ByteArray)
    (hstack : pre.stack = stack kind value off len salt rest)
    (hn : nonceAllowed pre) (hgate : gate pre value off len)
    (hr : child kind fuel cost pre value off len salt = .ok (address,created,world,gas,ss,true,out))
    (hb : (stepPre cost pre).gasAvailable.toNat ≤ 2^64) :
    EVM.step (fuel+1) cost (some (opcode kind,arg)) pre =
      .ok (successfulPost cost pre off len rest address created world gas ss) ∧
    (stepPre cost pre).gasAvailable.toNat/64 ≤
      (successfulPost cost pre off len rest address created world gas ss).gasAvailable.toNat := by
  constructor
  · rw [admitted_equation kind fuel cost pre arg value off len salt rest hstack hn hgate,hr]
    exact settle_success kind fuel cost pre value off len salt rest address created world gas ss out hr hgate hb
  · rw [post_gas cost pre off len rest address created world gas ss
      (actual_child_gas kind fuel cost pre value off len salt address created world gas ss out hr)]
    omega

#print axioms post_fields
#print axioms actual_child_gas
#print axioms word_guard
#print axioms settle_success
#print axioms post_gas
#print axioms step_success
end Eip8282.Audit.Integrator.CreationSettlementProgress
