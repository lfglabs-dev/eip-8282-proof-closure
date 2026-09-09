import Eip8282.Audit.Integrator.CallOutcome
import Eip8282.Audit.Integrator.CreationOutcome
import Eip8282.Audit.Integrator.ReturnedGas

/-!
# Child-charge transport through all actual recursive step outcomes

These are induction edges, not a completed call-tree counting theorem. The
child charge bound remains an explicit induction hypothesis on the SAME literal
child result. The conclusion charges it once through the actual parent step,
including error outcomes. No successful parent or child status is required.
-/
namespace Eip8282.Audit.Integrator.RecursiveEventDebit
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open CallGasAccounting
open CallDispatchGas (entered)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1400000

/-- Error zeroes are accounting residuals only, never invented returned gas. -/
def stepResidual : Except ExecutionException EVM.State → Nat
  | .error _ => 0 | .ok state => state.gasAvailable.toNat

def thetaResidual : Except ExecutionException
    (Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray) → Nat
  | .error _ => 0 | .ok (_,_,gas,_,_,_) => gas.toNat

def lambdaResidual : CreationOutcome.ChildResult → Nat
  | .error _ => 0 | .ok (_,_,_,gas,_,_,_) => gas.toNat

/-- CALL's child charge is paid from allowance minus returned gas; no complete
CALL opcode charge is added a second time to the descendant charge. -/
theorem call_charge (fuel : Nat) {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    (arg : Option (UInt256 × Nat))
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = requested::target::value::inOff::inLen::outOff::outLen::rest)
    (hz : Z vj .CALL pre = .ok (mid,cost)) (hgate : CallOutcome.Gate mid value)
    (charge : Nat)
    (hchild : thetaResidual (child fuel mid.executionEnv.blobVersionedHashes requested
      (UInt256.ofNat mid.executionEnv.codeOwner) target target value value inOff inLen
      mid.executionEnv.perm (entered mid)) + charge ≤
      Ccallgas (AccountAddress.ofUInt256 target) (AccountAddress.ofUInt256 target)
        value requested mid.accountMap mid.toMachineState mid.substate) :
    stepResidual (EVM.step (fuel+2) cost (some (.CALL,arg)) mid) + charge ≤ pre.gasAvailable.toNat := by
  cases he : EVM.step (fuel+2) cost (some (.CALL,arg)) mid with
  | error err =>
      have hb := (CallOutcome.accepted_call_allowance_le hstack hz).2.2
      change 0+charge ≤ _
      omega
  | ok post =>
      obtain ⟨created,world,gas,ss,z,out,hc,hd⟩ :=
        CallDispatchGas.accepted_step_call_debit fuel requested target value inOff inLen outOff outLen rest
          hstack hz hgate he
      rw [hc] at hchild
      change gas.toNat+charge ≤ _ at hchild
      have hd := hd (by omega)
      change post.gasAvailable.toNat+charge ≤ _
      omega

/-- All three other CALL variants use their own exact value/allowance rules. -/
theorem family_charge (kind : CallFamilyGas.Variant) (fuel : Nat)
    {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    (arg : Option (UInt256 × Nat))
    (requested target value inOff inLen outOff outLen : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = CallFamilyGas.stack kind requested target value inOff inLen outOff outLen rest)
    (hz : Z vj (CallFamilyGas.opcode kind) pre = .ok (mid,cost))
    (hgate : CallFamilyGas.gate kind mid value) (charge : Nat)
    (hchild : thetaResidual (CallFamilyGas.childResult kind fuel mid requested target value inOff inLen) +
      charge ≤ CallFamilyGas.allowance kind mid requested target value) :
    stepResidual (EVM.step (fuel+2) cost (some (CallFamilyGas.opcode kind,arg)) mid) + charge ≤
      pre.gasAvailable.toNat := by
  cases he : EVM.step (fuel+2) cost (some (CallFamilyGas.opcode kind,arg)) mid with
  | error err =>
      have hb := (CallOutcome.accepted_family_allowance_le kind hstack hz).2.2
      change 0+charge ≤ _
      omega
  | ok post =>
      obtain ⟨created,world,gas,ss,z,out,hc,hd⟩ :=
        CallFamilyGas.accepted_step_debit kind fuel requested target value inOff inLen outOff outLen rest
          hstack hz hgate he
      rw [hc] at hchild
      change gas.toNat+charge ≤ _ at hchild
      have hd := hd (by omega)
      change post.gasAvailable.toNat+charge ≤ _
      omega

/-- CREATE retains the charged subtree after caught child errors, including
OutOfFuel. Post-child guard rejection is also covered via accounting residual 0. -/
theorem creation_charge (kind : CreationGas.Variant) (fuel : Nat)
    {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    (arg : Option (UInt256 × Nat)) (value off len salt : UInt256) (rest : Stack UInt256)
    (hstack : pre.stack = CreationGas.stack kind value off len salt rest)
    (hz : Z vj (CreationGas.opcode kind) pre = .ok (mid,cost))
    (hnonce : CreationGas.nonceAllowed mid) (hgate : CreationGas.gate mid value off len)
    (charge : Nat)
    (hchild : lambdaResidual (CreationGas.child kind fuel cost mid value off len salt) + charge ≤
      CreationGas.allowance cost mid) :
    stepResidual (EVM.step (fuel+1) cost (some (CreationGas.opcode kind,arg)) mid) + charge ≤
      pre.gasAvailable.toNat := by
  cases he : EVM.step (fuel+1) cost (some (CreationGas.opcode kind,arg)) mid with
  | error err =>
      have hb := CreationOutcome.accepted_allowance_le kind hz
      change 0+charge ≤ _
      omega
  | ok post =>
      rcases CreationGas.accepted_child_debit kind fuel value off len salt rest hstack hz hnonce hgate he with hc | hc
      · obtain ⟨a,created,world,gas,ss,z,out,hc,hd⟩ := hc
        rw [hc] at hchild
        change gas.toNat+charge ≤ _ at hchild
        have hd := hd (by omega)
        change post.gasAvailable.toNat+charge ≤ _
        omega
      · obtain ⟨err,hc,hd,_,_,_⟩ := hc
        rw [hc] at hchild
        change 0+charge ≤ _ at hchild
        change post.gasAvailable.toNat+charge ≤ _
        omega

/-- A no-child edge needs no new charge; all outcomes are included. -/
theorem uncharged_step {vj : Array UInt256} {pre mid : EVM.State} {cost fuel : Nat}
    {op : Operation .EVM} (arg : Option (UInt256 × Nat))
    (hz : Z vj op pre = .ok (mid,cost)) :
    stepResidual (EVM.step fuel cost (some (op,arg)) mid) ≤ pre.gasAvailable.toNat := by
  cases he : EVM.step fuel cost (some (op,arg)) mid with
  | error err => exact Nat.zero_le _
  | ok post => exact ReturnedGas.step_remaining fuel hz he

#print axioms call_charge
#print axioms family_charge
#print axioms creation_charge
#print axioms uncharged_step
end Eip8282.Audit.Integrator.RecursiveEventDebit
