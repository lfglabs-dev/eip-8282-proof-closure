import Eip8282.Audit.Integrator.SystemPathBudget
import Eip8282.Audit.Integrator.Topics.ReferenceStorage

/-! Source-shaped ordinary execution prices for the exact SYSTEM opcode union.
EL0cc100eb190b64b23baba72dac0165652eaec252, cached vm/gas.py SHA256
41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c.
The accompanying source receipt records every instruction body and tier binding.
The audited source-to-formalization boundary remains explicit: these are not
charges proved paid by executable Python. SSTORE and memory expansion are
separate components; unsupported operations have no price in this table. -/
namespace Eip8282.Audit.Integrator.ReferenceOrdinaryGas
open EvmYul EvmYul.EVM
open SystemPathBudget
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-- Ordinary execution component only. SLOAD warmth is a literal source branch. -/
def ordinaryCost (op : Operation .EVM) (warm : Bool) : Option Nat :=
  match op with
  | .STOP | .RETURN | .REVERT => some 0
  | .CALLER | .CALLVALUE | .CALLDATASIZE | .POP | .PUSH0 => some 2
  | .ADD | .SUB | .LT | .GT | .EQ | .ISZERO | .AND | .SHL | .SHR
  | .CALLDATALOAD | .MSTORE | .MSTORE8
  | .PUSH1 | .PUSH2 | .PUSH4 | .PUSH8 | .PUSH20 | .PUSH32
  | .DUP1 | .DUP2 | .DUP3 | .DUP4 | .DUP5
  | .SWAP1 | .SWAP2 | .SWAP3 | .SWAP4 => some 3
  | .MUL | .DIV => some 5
  | .JUMP => some 8
  | .JUMPI => some 10
  | .JUMPDEST => some 1
  | .SLOAD => some (if warm then 100 else 2100)
  | _ => none

/-- The separately budgeted operations cannot accidentally enter as free prices. -/
theorem excluded (warm : Bool) :
    ordinaryCost .SSTORE warm = none ∧ ordinaryCost .LOG0 warm = none ∧
    ordinaryCost .CALLDATACOPY warm = none := ⟨rfl,rfl,rfl⟩

theorem defined_bound {op : Operation .EVM} (warm : Bool)
    (ha : Allowed op) (hs : op ≠ .SSTORE) :
    ∃ n, ordinaryCost op warm = some n ∧ n ≤ 2100 := by
  obtain ⟨ha,hlog,hcopy⟩ := ha
  simp only [RuntimeOpcodeScope.allowedOps,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases warm <;> simp_all [ordinaryCost]

/-- Literal source-shaped execution-meter subtraction, with memory charged once. -/
theorem charge {op : Operation .EVM} {warm : Bool} {n memoryDelta : Nat}
    (meter : ReferenceStorageGas.Meter) (_hc : ordinaryCost op warm = some n)
    (hg : n+memoryDelta ≤ meter.execution) :
    ∃ post, ReferenceStorageGas.chargeExecution meter (n+memoryDelta) = some post ∧
      post.execution = meter.execution-(n+memoryDelta) ∧
      post.reservoir = meter.reservoir := by
  unfold ReferenceStorageGas.chargeExecution
  rw [if_pos hg]
  exact ⟨_,rfl,rfl,rfl⟩

/-- A coarse execution reserve pays either SLOAD branch and every fixed base. -/
theorem charge_bounded {op : Operation .EVM} (warm : Bool) (ha : Allowed op)
    (hs : op ≠ .SSTORE) (meter : ReferenceStorageGas.Meter) (memoryDelta : Nat)
    (hg : 2100+memoryDelta ≤ meter.execution) :
    ∃ n post, ordinaryCost op warm = some n ∧
      ReferenceStorageGas.chargeExecution meter (n+memoryDelta) = some post ∧
      meter.execution-(2100+memoryDelta) ≤ post.execution ∧
      post.reservoir = meter.reservoir := by
  obtain ⟨n,hc,hn⟩ := defined_bound warm ha hs
  obtain ⟨post,hp,he,hr⟩ := charge (memoryDelta := memoryDelta) meter hc (by omega)
  exact ⟨n,post,hc,hp,by omega,hr⟩

/-- One component of a complete actual operation-list annotation. SSTORE has
zero ordinary contribution because its full price is accounted separately. -/
def Price (op : Operation .EVM) (n : Nat) : Prop :=
  (op = .SSTORE ∧ n = 0) ∨ ∃ warm, ordinaryCost op warm = some n

private theorem price_bound {op : Operation .EVM} {n : Nat}
    (ha : Allowed op) (hp : Price op n) : n ≤ 2100 := by
  rcases hp with ⟨_,rfl⟩ | ⟨warm,hc⟩
  · decide
  · have hs : op ≠ .SSTORE := by intro he; subst op; cases hc
    obtain ⟨m,hm,hbound⟩ := defined_bound warm ha hs
    have he : m = n := Option.some.inj (hm.symm.trans hc)
    exact he ▸ hbound

/-- The bound concerns the supplied actual operation list and its pointwise
literal prices, not a list chosen solely to satisfy a desired total. -/
theorem list_bound {ops : List (Operation .EVM)} {prices : List Nat}
    (ha : ∀ op ∈ ops, Allowed op) (hp : List.Forall₂ Price ops prices) :
    prices.sum ≤ 2100*ops.length := by
  revert ha
  induction hp with
  | nil => intro _; simp
  | @cons op n ops prices hhead htail ih =>
    intro ha
    have hn := price_bound (ha op (by simp)) hhead
    have ht := ih (fun o ho => ha o (by simp [ho]))
    simp only [List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

/-- Price annotation is constructible for every actually allowed list, with no
assumed warmth history. A cold choice suffices for this upper-bound producer. -/
theorem annotate (ops : List (Operation .EVM)) (ha : ∀ op ∈ ops, Allowed op) :
    ∃ prices, List.Forall₂ Price ops prices ∧ prices.sum ≤ 2100*ops.length := by
  have hp : ∃ prices, List.Forall₂ Price ops prices := by
    induction ops with
    | nil => exact ⟨[],.nil⟩
    | cons op ops ih =>
      obtain ⟨prices,ht⟩ := ih (fun o ho => ha o (by simp [ho]))
      by_cases hs : op = .SSTORE
      · exact ⟨0::prices,.cons (Or.inl ⟨hs,rfl⟩) ht⟩
      · obtain ⟨n,hc,_⟩ := defined_bound false (ha op (by simp)) hs
        exact ⟨n::prices,.cons (Or.inr ⟨false,hc⟩) ht⟩
  obtain ⟨prices,hp⟩ := hp
  exact ⟨prices,hp,list_bound ha hp⟩

#print axioms excluded
#print axioms defined_bound
#print axioms charge
#print axioms charge_bounded
#print axioms list_bound
#print axioms annotate
end Eip8282.Audit.Integrator.ReferenceOrdinaryGas
