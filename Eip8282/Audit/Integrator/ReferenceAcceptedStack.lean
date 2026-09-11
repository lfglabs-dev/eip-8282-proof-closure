import Eip8282.Audit.Integrator.ReferenceStackOps

/-! Construct actual operand witnesses from accepted Z. These producers do not
assume a desired stack decomposition or any reference post-state. DUP/SWAP
witnesses use the source end-oriented shapes consumed by ReferenceStackOps.
Decode, running-PC, ownership and whole-step transport are separate layers. -/
namespace Eip8282.Audit.Integrator.ReferenceAcceptedStack
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open ReferenceStackOps ReferenceWordOps
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-- The actual underflow and overflow guards, for any admitted opcode. -/
theorem bounds {vj : Array UInt256} {op : Operation .EVM}
    {pre mid : EVM.State} {cost : Nat} (hz : Z vj op pre = .ok (mid,cost)) :
    (δ op).getD 0 ≤ pre.stack.length ∧
    pre.stack.length - (δ op).getD 0 + (α op).getD 0 ≤ 1024 := by
  refine ⟨Z_ok_stack_length hz,?_⟩
  simp only [Z,Bind.bind,Except.bind,pure,Except.pure] at hz
  iterate 7 replace hz := elim_guard hz
  exact Nat.le_of_not_lt (elim_guard_not hz)

theorem pop1 {vj : Array UInt256} {op : Operation .EVM}
    {pre mid : EVM.State} {cost : Nat} (hz : Z vj op pre = .ok (mid,cost))
    (arity : 1 ≤ (δ op).getD 0) :
    ∃ rest x, pre.stack = x::rest ∧ pre.stack.pop = some (rest,x) := by
  have hl := (bounds hz).1
  cases hs : pre.stack with
  | nil => simp only [hs,List.length_nil] at hl; omega
  | cons x rest => exact ⟨rest,x,rfl,rfl⟩

theorem pop2 {vj : Array UInt256} {op : Operation .EVM}
    {pre mid : EVM.State} {cost : Nat} (hz : Z vj op pre = .ok (mid,cost))
    (arity : 2 ≤ (δ op).getD 0) :
    ∃ rest x y, pre.stack = x::y::rest ∧ pre.stack.pop2 = some (rest,x,y) := by
  have hl := (bounds hz).1
  cases hs : pre.stack with
  | nil => simp only [hs,List.length_nil] at hl; omega
  | cons x tail =>
    cases tail with
    | nil => simp only [hs,List.length_cons,List.length_nil] at hl; omega
    | cons y rest => exact ⟨rest,x,y,rfl,rfl⟩

theorem pop3 {vj : Array UInt256} {op : Operation .EVM}
    {pre mid : EVM.State} {cost : Nat} (hz : Z vj op pre = .ok (mid,cost))
    (arity : 3 ≤ (δ op).getD 0) :
    ∃ rest x y z, pre.stack = x::y::z::rest ∧ pre.stack.pop3 = some (rest,x,y,z) := by
  have hl := (bounds hz).1
  cases hs : pre.stack with
  | nil => simp only [hs,List.length_nil] at hl; omega
  | cons x tail =>
    cases tail with
    | nil => simp only [hs,List.length_cons,List.length_nil] at hl; omega
    | cons y tail =>
      cases tail with
      | nil => simp only [hs,List.length_cons,List.length_nil] at hl; omega
      | cons z rest => exact ⟨rest,x,y,z,rfl,rfl⟩

private theorem split_at (s : Stack UInt256) (n : Nat) (hn : n < s.length) :
    ∃ above x below, above.length = n ∧ s = above ++ x::below := by
  induction n generalizing s with
  | zero =>
    cases s with
    | nil => simp at hn
    | cons x below => exact ⟨[],x,below,rfl,rfl⟩
  | succ n ih =>
    cases s with
    | nil => simp at hn
    | cons top tail =>
      obtain ⟨above,x,below,hlen,hshape⟩ := ih tail (by simpa using hn)
      exact ⟨top::above,x,below,by simp [hlen],by simp [hshape]⟩

/-- The source DUP input shape is constructed from actual accepted depth. -/
theorem dup_inputs {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    (op : Operation.DOp) (hz : Z vj (.Dup op) pre = .ok (mid,cost)) :
    ∃ base above x, above.length+1 = dupDepth op ∧
      pre.stack = fromPython (base++[x]++above) := by
  have hl := (accepted_dup_capacity op hz).1
  have hd := (dup_depth op).1
  obtain ⟨above,x,below,hlen,hshape⟩ := split_at pre.stack (dupDepth op-1) (by omega)
  refine ⟨below.reverse,above.reverse,x,?_,?_⟩
  · simp only [List.length_reverse,hlen]
    omega
  · simpa [fromPython,List.reverse_append,List.append_assoc] using hshape

/-- Source SWAP indices are selected from the actual input, including its top. -/
theorem swap_inputs {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    (op : Operation.ExOp) (hz : Z vj (.Exchange op) pre = .ok (mid,cost)) :
    ∃ base middle x top, middle.length+1 = swapDepth op ∧
      pre.stack = fromPython (base++[x]++middle++[top]) := by
  have hl := (accepted_swap_capacity op hz).1
  have hd := (swap_depth op).1
  cases hs : pre.stack with
  | nil => simp only [hs,List.length_nil] at hl; omega
  | cons top tail =>
    have ht : swapDepth op-1 < tail.length := by
      simp only [hs,List.length_cons] at hl
      omega
    obtain ⟨middle,x,below,hlen,hshape⟩ := split_at tail (swapDepth op-1) ht
    refine ⟨below.reverse,middle.reverse,x,top,?_,?_⟩
    · simp only [List.length_reverse,hlen]
      omega
    · simp [fromPython,List.reverse_append,List.append_assoc,hshape]

#print axioms bounds
#print axioms pop1
#print axioms pop2
#print axioms pop3
#print axioms dup_inputs
#print axioms swap_inputs
end Eip8282.Audit.Integrator.ReferenceAcceptedStack
