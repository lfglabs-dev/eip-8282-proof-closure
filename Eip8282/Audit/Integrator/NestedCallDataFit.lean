import Eip8282.Audit.Integrator.NestedCallOccurrence

/-! Actual selected CALL-family input widths, propagated through complete Theta
locations. Only a literal root Theta needs its own data-size admission fact.
The unconditional padded-read upper bound is used: no machine-word padding
identity, exact requested-length equality or per-child size premise is assumed. -/
namespace Eip8282.Audit.Integrator.NestedCallDataFit
open EvmYul EvmYul.EVM
open NestedEvents
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- A caller-supplied root Theta may have arbitrary ByteArray input. All other
request forms obtain any descendant Theta data from actual selected reads. -/
def RootFits : Request → Prop
  | .theta _ a => a.data.size < UInt256.size
  | _ => True

theorem read_data_fit (memory : ByteArray) (off len : UInt256) :
    (memory.readWithPadding off.toNat len.toNat).size < UInt256.size := by
  have hb := Eip8282.Audit.XiTransport.size_readWithPadding_le memory off.toNat len.toNat
  have hl : len.toNat < UInt256.size := len.val.isLt
  exact hb.trans_lt hl

private theorem dispatch_fit (n : Nat) (pre : EVM.State)
    (requested target value off len : UInt256) :
    RootFits (.theta n (dispatchCallArgs pre requested target value off len)) := by
  exact read_data_fit _ off len

private theorem family_fit (kind : CallFamilyGas.Variant) (n : Nat) (pre : EVM.State)
    (requested target value off len : UInt256) :
    RootFits (.theta n (familyArgs kind pre requested target value off len)) := by
  exact read_data_fit _ off len

/-- Derived for every actual selected child, irrespective of its outcome. -/
theorem selected_child_fit {n : Nat} {a : StepArgs} {q : Request}
    (h : StepChild n a (some q)) : RootFits q := by
  unfold StepChild selectedChild at h
  split at h
  · cases h
  · split at h
    all_goals repeat first | split at h | contradiction
    all_goals simp only [Option.some.injEq, reduceCtorEq] at h
    all_goals subst q
    all_goals first
      | exact dispatch_fit _ _ _ _ _ _ _
      | exact family_fit _ _ _ _ _ _ _ _
      | exact True.intro

/-- All actual located Theta inputs fit, including errored calls and calls
whose enclosing journals are later discarded. No committed-history claim. -/
theorem call_data_fit {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt q result tree path f a r) (fit : RootFits q) :
    a.data.size < UInt256.size := by
  induction loc with
  | here body => exact fit
  | xStepError _ _ _ ih => exact ih trivial
  | xNextChild _ _ _ _ _ ih => exact ih trivial
  | xNextTail _ _ _ _ _ ih => exact ih trivial
  | xHalt _ _ _ _ _ ih => exact ih trivial
  | xRevert _ _ _ _ _ ih => exact ih trivial
  | xi body inner ih => exact ih trivial
  | thetaCode _ _ _ _ ih => exact ih trivial
  | lambdaInit _ _ _ _ ih => exact ih trivial
  | stepChild hc body inner ih => exact ih (selected_child_fit hc)

#print axioms read_data_fit
#print axioms selected_child_fit
#print axioms call_data_fit
end Eip8282.Audit.Integrator.NestedCallDataFit
