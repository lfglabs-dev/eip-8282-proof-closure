import Eip8282.Audit.Integrator.NestedAppendCount

/-!
# Append counts of actual nested prefixes

Invocation paths compose through the same certified execution, including
reverting ancestors. Every locally successful append of an actual inner Xi
therefore occurs in the outer complete set. This supplies a derived bound for
nested journal checkpoints; it does not identify committed records.
-/
namespace Eip8282.Audit.Integrator.NestedEvents.XiAt
open EvmYul EvmYul.EVM
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- Locate a descendant of an already located actual invocation. Both trees
are fixed by their actual certificates, not supplied as independent histories. -/
theorem compose {q : Request} {result : q.Outcome} {tree innerTree : EventTree}
    {path innerPath : EventTree.Address} {f g : Nat} {a b : XiArgs} {r s : XiResult}
    (outer : XiAt q result tree path f a r)
    (inner : XiAt (.xi f a) r innerTree innerPath g b s) :
    XiAt q result tree (path ++ innerPath) g b s := by
  induction outer with
  | here body =>
    have ht := NestedEvents.deterministic (cert_top inner) body
    subst innerTree
    exact inner
  | xStepError hz hs _ ih => exact .xStepError hz hs (ih inner)
  | xNextChild hz hs hh ht _ ih => exact .xNextChild hz hs hh ht (ih inner)
  | xNextTail hz hs hh ht _ ih => exact .xNextTail hz hs hh ht (ih inner)
  | xHalt hz hs hh hn _ ih => exact .xHalt hz hs hh hn (ih inner)
  | xRevert hz hs hh hr _ ih => exact .xRevert hz hs hh hr (ih inner)
  | xi body _ ih => exact .xi body (ih inner)
  | thetaCode bytes hc body _ ih => exact .thetaCode bytes hc body (ih inner)
  | lambdaInit bytes hp body _ ih => exact .lambdaInit bytes hp body (ih inner)
  | stepChild hc body _ ih => exact .stepChild hc body (ih inner)

end Eip8282.Audit.Integrator.NestedEvents.XiAt

namespace Eip8282.Audit.Integrator.NestedAppendPrefix
open EvmYul EvmYul.EVM
open NestedEvents NestedAppendCount
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem append_embeds {q : Request} {result : q.Outcome} {tree innerTree : EventTree}
    {path innerPath : EventTree.Address} {f : Nat} {a : XiArgs} {r : XiResult}
    (outer : XiAt q result tree path f a r)
    (inner : IsAppendFrame (.xi f a) r innerTree innerPath) :
    IsAppendFrame q result tree (path ++ innerPath) := by
  obtain ⟨kind,call,loc,hu,hsize,hs⟩ := inner
  exact ⟨kind,call,XiAt.compose outer loc,hu,hsize,hs⟩

/-- The complete inner append set injects into the complete outer append set.
The prefix is an actual invocation location and never a caller-provided map. -/
theorem count_le {q : Request} {result : q.Outcome} {tree innerTree : EventTree}
    {path : EventTree.Address} {f : Nat} {a : XiArgs} {r : XiResult}
    (outer : XiAt q result tree path f a r) :
    count (.xi f a) r innerTree ≤ count q result tree := by
  classical
  unfold count
  apply Finset.card_le_card_of_injOn (fun innerPath => path ++ innerPath)
  · intro p hp
    exact mem_frames_iff.mpr (append_embeds outer (mem_frames_iff.mp hp))
  · intro p hp p' hp' he
    exact List.append_cancel_left he

/-- Every actual inner invocation's all-append count fits the actual parent
transaction's reported gas, including final failed transactions. -/
theorem transaction_prefix (c : RefundAccounting.Context) {world : AccountMap .EVM}
    {substate : Substate} {success : Bool} {used : UInt256}
    (hr : c.result = .ok (world,substate,success,used)) :
    ∃ tree, Cert (TransactionEventBounds.request c)
      (TransactionEventBounds.request c).eval tree ∧
      ∀ (innerTree : EventTree) (path : EventTree.Address) (f : Nat) (a : XiArgs) (r : XiResult),
        XiAt (TransactionEventBounds.request c) (TransactionEventBounds.request c).eval
          tree path f a r → count (.xi f a) r innerTree ≤ used.toNat := by
  obtain ⟨tree,hc,hb,_⟩ := transaction_appends c hr
  exact ⟨tree,hc,fun _ _ _ _ _ h => (count_le h).trans hb⟩

#print axioms NestedEvents.XiAt.compose
#print axioms append_embeds
#print axioms count_le
#print axioms transaction_prefix
end Eip8282.Audit.Integrator.NestedAppendPrefix
