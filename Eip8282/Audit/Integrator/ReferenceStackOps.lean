import Eip8282.Audit.Integrator.ReferenceControlOps

/-! Successful DUP1..16/SWAP1..16 stack transport. Source: archived EL
0cc100eb190b64b23baba72dac0165652eaec252 vm/instructions/stack.py,
`dup_n` and `swap_n`. Python uses end indices; the pinned stack uses its head.
The source-to-formalization boundary remains audited, not an executable Python
refinement. Exact input decompositions identify the selected source element;
no poststack equality is assumed. Gas/error ordering is outside this module. -/
namespace Eip8282.Audit.Integrator.ReferenceStackOps
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open ReferenceWordOps
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

def dupDepth : Operation.DOp → Nat
  | .DUP1 => 1
  | .DUP2 => 2
  | .DUP3 => 3
  | .DUP4 => 4
  | .DUP5 => 5
  | .DUP6 => 6
  | .DUP7 => 7
  | .DUP8 => 8
  | .DUP9 => 9
  | .DUP10 => 10
  | .DUP11 => 11
  | .DUP12 => 12
  | .DUP13 => 13
  | .DUP14 => 14
  | .DUP15 => 15
  | .DUP16 => 16

def swapDepth : Operation.ExOp → Nat
  | .SWAP1 => 1
  | .SWAP2 => 2
  | .SWAP3 => 3
  | .SWAP4 => 4
  | .SWAP5 => 5
  | .SWAP6 => 6
  | .SWAP7 => 7
  | .SWAP8 => 8
  | .SWAP9 => 9
  | .SWAP10 => 10
  | .SWAP11 => 11
  | .SWAP12 => 12
  | .SWAP13 => 13
  | .SWAP14 => 14
  | .SWAP15 => 15
  | .SWAP16 => 16

/-- The source DUP item_number is depth-1. -/
theorem dup_depth (op : Operation.DOp) : 1 ≤ dupDepth op ∧ dupDepth op ≤ 16 := by
  cases op <;> decide

theorem swap_depth (op : Operation.ExOp) : 1 ≤ swapDepth op ∧ swapDepth op ≤ 16 := by
  cases op <;> decide

theorem dup_dispatch (op : Operation.DOp) (s : EVM.State) :
    EvmYul.step (.Dup op) none s = EvmYul.dup (dupDepth op) s := by
  cases op <;> rfl

theorem swap_dispatch (op : Operation.ExOp) (s : EVM.State) :
    EvmYul.step (.Exchange op) none s = EvmYul.swap (swapDepth op) s := by
  cases op <;> rfl

/-- An exact source end-index equation; `above` contains the shallower items. -/
theorem source_index (base above : List UInt256) (x : UInt256) :
    (base++[x]++above)[(base++[x]++above).length-1-above.length]? = some x := by
  have hn : (base++[x]++above).length-1-above.length = base.length := by simp
  rw [hn]
  simp [List.append_assoc]

theorem source_dup_index (op : Operation.DOp) (base above : List UInt256) (x : UInt256)
    (depth : above.length+1 = dupDepth op) :
    (base++[x]++above)[(base++[x]++above).length-1-(dupDepth op-1)]? = some x := by
  rw [← depth]
  simpa only [Nat.add_sub_cancel] using source_index base above x

theorem source_swap_indices (op : Operation.ExOp) (base middle : List UInt256)
    (x top : UInt256) (depth : middle.length+1 = swapDepth op) :
    (base++[x]++middle++[top])[(base++[x]++middle++[top]).length-1-swapDepth op]? = some x ∧
    (base++[x]++middle++[top])[(base++[x]++middle++[top]).length-1]? = some top := by
  constructor
  · have h := source_index base (middle++[top]) x
    simpa only [List.length_append,List.length_singleton,depth,List.append_assoc] using h
  · have h := source_index (base++[x]++middle) [] top
    simpa only [List.append_nil,List.length_nil,Nat.sub_zero] using h

private theorem accepted_capacity {vj : Array UInt256} {op : Operation .EVM}
    {pre mid : EVM.State} {cost : Nat} (hz : Z vj op pre = .ok (mid,cost)) :
    pre.stack.length - (δ op).getD 0 + (α op).getD 0 ≤ 1024 := by
  simp only [Z,Bind.bind,Except.bind,pure,Except.pure] at hz
  iterate 7 replace hz := elim_guard hz
  exact Nat.le_of_not_lt (elim_guard_not hz)

/-- Actual admission supplies the reference DUP push-capacity gate. -/
theorem accepted_dup_capacity {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    (op : Operation.DOp) (hz : Z vj (.Dup op) pre = .ok (mid,cost)) :
    dupDepth op ≤ pre.stack.length ∧ pre.stack.length < 1024 := by
  have hl := Z_ok_stack_length hz
  have hu := accepted_capacity hz
  cases op <;> simp [δ,α,dupDepth] at * <;> omega

theorem accepted_swap_capacity {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    (op : Operation.ExOp) (hz : Z vj (.Exchange op) pre = .ok (mid,cost)) :
    swapDepth op+1 ≤ pre.stack.length ∧ pre.stack.length ≤ 1024 := by
  have hl := Z_ok_stack_length hz
  have hu := accepted_capacity hz
  cases op <;> simp [δ,α,swapDepth] at * <;> omega

private theorem dup_split (s : EVM.State) (above below : List UInt256) (x : UInt256)
    (hs : s.stack = (above++[x])++below) :
    EvmYul.dup (above.length+1) s = .ok (s.replaceStackAndIncrPC (x::s.stack)) := by
  have ht : s.stack.take (above.length+1) = above++[x] := by
    rw [hs]
    exact List.take_left' (by simp)
  simp [EvmYul.dup,ht]

private theorem swap_split (s : EVM.State) (middle below : List UInt256) (x top : UInt256)
    (hs : s.stack = (top::(middle++[x]))++below) :
    EvmYul.swap (middle.length+1) s =
      .ok (s.replaceStackAndIncrPC ((x::(middle++[top]))++below)) := by
  have ht : s.stack.take (middle.length+1+1) = top::(middle++[x]) := by
    rw [hs]
    exact List.take_left' (by simp)
  have hb : s.stack.drop (middle.length+1+1) = below := by
    rw [hs]
    exact List.drop_left' (by simp)
  have hlast : (top::(middle++[x])).getLast? = some x := by
    rw [← List.cons_append]
    exact List.getLast?_concat
  simp [EvmYul.swap,ht,hb,List.append_assoc,hlast]

/-- Literal reference DUP result is an end-push of the indexed source item. -/
theorem dup_step (op : Operation.DOp) (s : EVM.State)
    (base above : List UInt256) (x : UInt256)
    (depth : above.length+1 = dupDepth op)
    (hs : s.stack = fromPython (base++[x]++above)) :
    EvmYul.step (.Dup op) none s =
      .ok (s.replaceStackAndIncrPC (fromPython ((base++[x]++above)++[x]))) := by
  rw [dup_dispatch,← depth]
  have hshape : s.stack = (above.reverse++[x])++base.reverse := by
    simpa [fromPython,List.reverse_append,List.append_assoc] using hs
  have h := dup_split s above.reverse base.reverse x hshape
  simpa [fromPython,List.reverse_append,hs] using h

/-- Literal reference SWAP exchanges its two end-indexed elements. -/
theorem swap_step (op : Operation.ExOp) (s : EVM.State)
    (base middle : List UInt256) (x top : UInt256)
    (depth : middle.length+1 = swapDepth op)
    (hs : s.stack = fromPython (base++[x]++middle++[top])) :
    EvmYul.step (.Exchange op) none s =
      .ok (s.replaceStackAndIncrPC (fromPython (base++[top]++middle++[x]))) := by
  rw [swap_dispatch,← depth]
  have hshape : s.stack = (top::(middle.reverse++[x]))++base.reverse := by
    simpa [fromPython,List.reverse_append,List.append_assoc] using hs
  have h := swap_split s middle.reverse base.reverse x top hshape
  simpa [fromPython,List.reverse_append,List.append_assoc] using h

/-- Actual Z acceptance transports the input stack to the state dispatched by X. -/
theorem accepted_dup {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    (op : Operation.DOp) (hz : Z vj (.Dup op) pre = .ok (mid,cost))
    (base above : List UInt256) (x : UInt256)
    (depth : above.length+1 = dupDepth op)
    (hs : pre.stack = fromPython (base++[x]++above)) :
    EvmYul.step (.Dup op) none mid =
      .ok (mid.replaceStackAndIncrPC (fromPython ((base++[x]++above)++[x]))) :=
  dup_step op mid base above x depth ((Z_ok_stack hz).trans hs)

theorem accepted_swap {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    (op : Operation.ExOp) (hz : Z vj (.Exchange op) pre = .ok (mid,cost))
    (base middle : List UInt256) (x top : UInt256)
    (depth : middle.length+1 = swapDepth op)
    (hs : pre.stack = fromPython (base++[x]++middle++[top])) :
    EvmYul.step (.Exchange op) none mid =
      .ok (mid.replaceStackAndIncrPC (fromPython (base++[top]++middle++[x]))) :=
  swap_step op mid base middle x top depth ((Z_ok_stack hz).trans hs)

/-- Running PC parity is unsigned addition only under the explicit width bound. -/
theorem next_pc (s : EVM.State) (stack : Stack UInt256)
    (fit : s.pc.toNat+1 < UInt256.size) :
    (s.replaceStackAndIncrPC stack).pc.toNat = s.pc.toNat+1 :=
  ReferenceControlOps.next_pc s stack 1 fit

#print axioms dup_depth
#print axioms swap_depth
#print axioms source_index
#print axioms source_dup_index
#print axioms source_swap_indices
#print axioms accepted_dup_capacity
#print axioms accepted_swap_capacity
#print axioms dup_step
#print axioms swap_step
#print axioms accepted_dup
#print axioms accepted_swap
#print axioms next_pc
end Eip8282.Audit.Integrator.ReferenceStackOps
