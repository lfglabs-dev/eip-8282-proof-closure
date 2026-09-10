import Eip8282.Audit.Integrator.SystemDepositTrace
import Eip8282.Audit.Integrator.SystemExitTrace

/-! A common consumer for both actual annotated SYSTEM constructions. The
operation budget, storage-write count, endpoint capacity and RETURN operands
belong to one execution witness. Reference replay and its meters are separate. -/
namespace Eip8282.Audit.Integrator.SystemTraceWitness
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall)
open SystemTraceAnnotations SystemPathBudget
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

def Path (vj : Array UInt256) (steps words outputBytes : Nat) (pre : EVM.State) : Prop :=
  ∃ post out ops,
    ReachesOps vj ops pre post ∧ ops.length ≤ steps ∧ weight storeWeight ops ≤ 4 ∧
    (∀ op ∈ ops, Allowed op) ∧ post.activeWords.toNat ≤ words ∧
    (∃ len : UInt256, post.stack = [UInt256.ofNat 0,len] ∧ len.toNat ≤ outputBytes) ∧
    Halt vj post .RETURN out

theorem deposit (c : XiCall .deposit) (system : Deposit.callerWord c = sysW)
    (permission : c.env.perm = true) (gas : 2500000 ≤ c.gas.toNat) :
    Path depositJumpdests 8500 400 11776 c.entry := by
  obtain ⟨st,stX,aw,g,e,_,_,haw,hr,hh⟩ := SystemDepositTrace.system_returns c system permission gas
  obtain ⟨ops,hlen,hstores,hallowed,hops⟩ := hr
  refine ⟨_,_,ops,hops,hlen,hstores,hallowed,haw,?_,hh⟩
  refine ⟨_,rfl,?_⟩
  have hc := Deposit.drainWord_le c
  rw [toNat_ofNat_mul_of_lt 184 _ (by rw [size_eq]; omega)]
  omega

theorem exit (c : XiCall .exit) (system : Exit.callerWord c = sysW)
    (permission : c.env.perm = true) (gas : 250000 ≤ c.gas.toNat) :
    Path exitJumpdests 800 40 1088 c.entry := by
  obtain ⟨st,stX,aw,g,e,_,_,haw,hr,hh⟩ := SystemExitTrace.system_returns c system permission gas
  obtain ⟨ops,hlen,hstores,hallowed,hops⟩ := hr
  refine ⟨_,_,ops,hops,hlen,hstores,hallowed,haw,?_,hh⟩
  refine ⟨_,rfl,?_⟩
  have hc := Exit.drainWord_le c
  rw [toNat_ofNat_mul_of_lt 68 _ (by rw [size_eq]; omega)]
  omega

/-- Specialize the fuel-polymorphic path once; annotations stay attached to
that same actual XRuns. RETURN contributes one operation and zero SSTOREs. -/
theorem instantiate {vj : Array UInt256} {steps words outputBytes fuel : Nat} {pre : EVM.State}
    (path : Path vj steps words outputBytes pre) (enough : steps+1 ≤ fuel) :
    ∃ post out tr rem,
      XRuns vj fuel pre tr (rem+1) post ∧
      (operations tr ++ [Operation.RETURN]).length ≤ steps+1 ∧
      weight storeWeight (operations tr ++ [Operation.RETURN]) ≤ 4 ∧
      (∀ op ∈ operations tr ++ [Operation.RETURN], Allowed op) ∧
      post.activeWords.toNat ≤ words ∧
      (∃ len : UInt256, post.stack = [UInt256.ofNat 0,len] ∧ len.toNat ≤ outputBytes) ∧
      Halt vj post .RETURN out := by
  obtain ⟨post,out,ops,hr,hl,hs,ha,hm,ho,hh⟩ := path
  obtain ⟨tr,ht,he⟩ := hr (fuel-ops.length-1)
  rw [show fuel-ops.length-1+1+ops.length = fuel by omega] at ht
  refine ⟨post,out,tr,fuel-ops.length-1,ht,?_,?_,?_,hm,ho,hh⟩
  · rw [he,List.length_append,List.length_singleton]; omega
  · rw [he,weight_append]
    simpa [weight,storeWeight] using hs
  · rw [he]
    intro op hop
    rcases List.mem_append.mp hop with h | h
    · exact ha op h
    · have : op = .RETURN := by simpa using h
      subst op
      decide +kernel

#print axioms deposit
#print axioms exit
#print axioms instantiate
end Eip8282.Audit.Integrator.SystemTraceWitness
