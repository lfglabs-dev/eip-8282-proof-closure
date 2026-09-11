import Eip8282.Audit.Integrator.NestedFrameIdentity
import Eip8282.Audit.Integrator.NestedEventProjection
import Eip8282.Audit.Integrator.TransactionEventBounds
import Mathlib.Data.Finset.Card

/-!
# All locally successful audited append invocations in an actual execution

The set is defined by the actual XiAt relation, not by a supplied list of calls.
Every member owns a marked occurrence in the same extracted tree. Filtering the
finite set of event owners loses no successful append, even when an ancestor
later reverts or a CREATE settlement rejects its child's result. Those events
bound execution work; they do not count finally committed queue records.
-/
namespace Eip8282.Audit.Integrator.NestedAppendCount
open EvmYul EvmYul.EVM
open NestedEvents NestedFrameOwnership
open Eip8282.Audit.XiTransport (XiCall)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

/-- An actual invocation of either pinned runtime which locally succeeds on
nonempty, correctly sized user input. No caller-supplied enumeration is used. -/
def IsAppendFrame (root : Request) (result : root.Outcome) (tree : EventTree)
    (path : EventTree.Address) : Prop :=
  ∃ (kind : Eip8282.Audit.Model.Kind) (call : XiCall kind),
    XiAt root result tree path (call.fuel+1) (rootXiArgs call) call.result ∧
    call.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr ∧
    call.env.calldata.size = (match kind with | .deposit => 184 | .exit => 48) ∧
    ∃ (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
      (gas : UInt256) (substate : Substate) (out : ByteArray),
      call.result = .ok (.success (created,world,gas,substate) out)

/-- A successful audited frame supplies a continuation-only event at its own
root. The actual traversal proves the root grammar, rather than assuming it. -/
theorem owns_event {root : Request} {result : root.Outcome} {tree : EventTree}
    {path : EventTree.Address} (h : IsAppendFrame root result tree path) :
    FrameRoot path ∧ ∃ instruction, owned path instruction ∈ tree.occurrences := by
  obtain ⟨kind,call,loc,huser,hsize,created,world,gas,substate,out,hs⟩ := h
  obtain ⟨inner,cert,embed⟩ := XiAt.at_tree loc
  obtain ⟨event,_,_,he⟩ := successful_append_address call huser (by cases kind <;> exact hsize) hs cert
  exact ⟨XiAt.frame_root loc, call.fuel-(event+1), embed _ he⟩

/-- No two different successful invocation roots can be charged to the same
selected local event, including ancestor/descendant frame pairs. -/
theorem distinct_events {root : Request} {result : root.Outcome} {tree : EventTree}
    {p q : EventTree.Address} {i j : Nat}
    (hp : IsAppendFrame root result tree p) (hq : IsAppendFrame root result tree q)
    (hne : p ≠ q) : owned p i ≠ owned q j :=
  owned_distinct (owns_event hp).1 (owns_event hq).1 hne

/-- Finite candidate owners cover every actual successful append frame. -/
theorem owner_coverage {root : Request} {result : root.Outcome} {tree : EventTree}
    {path : EventTree.Address} (h : IsAppendFrame root result tree path) :
    path ∈ tree.occurrences.map owner := by
  obtain ⟨hr,i,he⟩ := owns_event h
  exact List.mem_map.mpr ⟨owned path i,he,owner_owned path i hr⟩

/-- The complete finite set of locally successful audited invocation roots. -/
noncomputable def frames (root : Request) (result : root.Outcome) (tree : EventTree) :
    Finset EventTree.Address := by
  classical
  exact (tree.occurrences.map owner).toFinset.filter (IsAppendFrame root result tree)

/-- Completeness and soundness: finite filtering omits no actual append frame
and inserts no frame which lacks an actual successful runtime invocation. -/
theorem mem_frames_iff {root : Request} {result : root.Outcome} {tree : EventTree}
    {path : EventTree.Address} : path ∈ frames root result tree ↔
      IsAppendFrame root result tree path := by
  classical
  simp only [frames, Finset.mem_filter, List.mem_toFinset]
  exact ⟨And.right, fun h => ⟨owner_coverage h,h⟩⟩

noncomputable def count (root : Request) (result : root.Outcome) (tree : EventTree) : Nat :=
  (frames root result tree).card

/-- The count is over ALL successful audited invocations in the actual tree,
not an arbitrary supplied subcollection. Several qualifying code images or
witness proofs at the same invocation root do not duplicate it. XiAt.identity
proves that such a root identifies unique actual inputs and result. Runtime
clones and delegated execution of the pinned bytes are included in this
conservative work bound; canonical target/storage ownership is not assumed. -/
theorem count_le_events (root : Request) (result : root.Outcome) (tree : EventTree) :
    count root result tree ≤ tree.count := by
  classical
  have hf := Finset.card_filter_le (tree.occurrences.map owner).toFinset
    (IsAppendFrame root result tree)
  have hl := List.toFinset_card_le (tree.occurrences.map owner)
  have he := EventTree.occurrences_length tree
  simp only [List.length_map] at hl
  exact (Nat.le_trans hf hl).trans_eq he

/-- Actual completed pinned Υ executions, with either final status, bound all
locally successful audited append frames by reported gas after capped refunds.
Rollback does not erase executed frames from this work metric. -/
theorem transaction_appends (c : RefundAccounting.Context) {world : AccountMap .EVM}
    {substate : Substate} {success : Bool} {used : UInt256}
    (hr : c.result = .ok (world,substate,success,used)) :
    ∃ tree, Cert (TransactionEventBounds.request c)
      (TransactionEventBounds.request c).eval tree ∧
      count (TransactionEventBounds.request c) (TransactionEventBounds.request c).eval tree ≤ used.toNat ∧
      ∀ other, Cert (TransactionEventBounds.request c)
        (TransactionEventBounds.request c).eval other → other = tree := by
  obtain ⟨tree,hc,_,hb,hu⟩ := TransactionEventBounds.transaction_events c hr
  exact ⟨tree,hc,(count_le_events _ _ tree).trans hb,hu⟩

#print axioms owns_event
#print axioms distinct_events
#print axioms owner_coverage
#print axioms mem_frames_iff
#print axioms count_le_events
#print axioms transaction_appends
end Eip8282.Audit.Integrator.NestedAppendCount
