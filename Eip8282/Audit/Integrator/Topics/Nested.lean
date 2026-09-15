import Eip8282.Audit.Integrator.FundingHistory
import Eip8282.Audit.Integrator.NestedCallOccurrence
import Eip8282.Audit.Integrator.NestedEventProjection
import Eip8282.Audit.Integrator.NestedFrameFunding
import Eip8282.Audit.Integrator.NestedFrameOccurrence
import Eip8282.Audit.Integrator.Topics.Transaction3
import Mathlib.Data.Finset.Card

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## NestedFrameIdentity -/

/-!
# Unique actual Xi identity at a structural frame path

The same path in the same actual nested certificate cannot denote different
Xi invocations. This includes all outcomes and preserves full execution inputs,
not only the code or target account. No frame list or global count is assumed.
-/
namespace Eip8282.Audit.Integrator.NestedEvents.XiAt
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem identity {q : Request} {result₁ result₂ : q.Outcome} {tree₁ tree₂ : EventTree}
    {path : EventTree.Address} {f₁ f₂ : Nat} {a₁ a₂ : XiArgs} {r₁ r₂ : XiResult}
    (h₁ : XiAt q result₁ tree₁ path f₁ a₁ r₁)
    (h₂ : XiAt q result₂ tree₂ path f₂ a₂ r₂) :
    f₁ = f₂ ∧ a₁ = a₂ ∧ r₁ = r₂ := by
  induction h₁ generalizing tree₂ f₂ a₂ r₂ with
  | here body =>
      cases h₂ with
      | here body₂ => exact ⟨rfl, rfl, outcome_deterministic body body₂⟩
      | xi _ loc => exact False.elim (x_nonempty loc rfl)
  | xStepError hz hs loc ih =>
      cases h₂ with
      | xStepError hz₂ hs₂ loc₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          exact ih loc₂
      | xNextChild hz₂ hs₂ _ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xHalt hz₂ hs₂ _ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xRevert hz₂ hs₂ _ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
  | xNextChild hz hs hh ht loc ih =>
      cases h₂ with
      | xStepError hz₂ hs₂ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xNextChild hz₂ hs₂ hh₂ ht₂ loc₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          exact ih loc₂
      | xHalt hz₂ hs₂ hh₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          cases hh.symm.trans hh₂
      | xRevert hz₂ hs₂ hh₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          cases hh.symm.trans hh₂
  | xNextTail hz hs hh ht loc ih =>
      cases h₂ with
      | xNextTail hz₂ hs₂ hh₂ ht₂ loc₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          exact ih loc₂
  | xHalt hz hs hh hn loc ih =>
      cases h₂ with
      | xStepError hz₂ hs₂ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xRevert _ _ _ hr₂ _ => exact False.elim (hn hr₂)
      | xNextChild hz₂ hs₂ hh₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          cases hh.symm.trans hh₂
      | xHalt hz₂ hs₂ _ _ loc₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          exact ih loc₂
  | xRevert hz hs hh hr loc ih =>
      cases h₂ with
      | xStepError hz₂ hs₂ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xHalt _ _ _ hn₂ _ => exact False.elim (hn₂ hr)
      | xNextChild hz₂ hs₂ hh₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          cases hh.symm.trans hh₂
      | xRevert hz₂ hs₂ _ _ loc₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          exact ih loc₂
  | xi body loc ih =>
      cases h₂ with
      | here => exact False.elim (x_nonempty loc rfl)
      | xi _ loc₂ => exact ih loc₂
  | thetaCode bytes hc body loc ih =>
      cases h₂ with
      | thetaCode _ hc₂ _ loc₂ =>
          cases ToExecute.Code.inj (hc.symm.trans hc₂)
          exact ih loc₂
  | lambdaInit bytes hp body loc ih =>
      cases h₂ with
      | lambdaInit _ hp₂ _ loc₂ =>
          cases Option.some.inj (hp.symm.trans hp₂)
          exact ih loc₂
  | stepChild hc body loc ih =>
      cases h₂ with
      | stepChild hc₂ _ loc₂ =>
          cases Option.some.inj (stepChild_unique hc hc₂)
          exact ih loc₂

#print axioms identity
end Eip8282.Audit.Integrator.NestedEvents.XiAt

end

section

/-! ## NestedAppendCount -/

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

end

section

/-! ## NestedAppendPrefix -/

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

end

section

/-! ## NestedCallDataFit -/

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

end

section

/-! ## NestedCallFunding -/

/-!
# Actual nested message-call funding, including failed and reverted ancestors

All Theta inputs are located in the actual certified evaluator. The real
selected-child gates supply transfer affordability. Together with the complete
funding history, this removes per-nested-call wealth assumptions; provenance
and bounds of the history's external credits remain explicit protocol inputs.
-/
namespace Eip8282.Audit.Integrator.NestedFunding
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open NestedEvents TransferFunding
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private theorem theta_x_guard {fuel : Nat} {vj : Array UInt256} {pre : EVM.State}
    {result : XResult} {tree : EventTree} {path : EventTree.Address}
    {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt (.x fuel vj pre) result tree path f a r) :
    ∃ mid cost, Z vj (decodeAt pre).1 pre = .ok (mid,cost) := by
  cases loc with
  | xStepError hz _ _ => exact ⟨_,_,hz⟩
  | xNextChild hz _ _ _ _ => exact ⟨_,_,hz⟩
  | xNextTail hz _ _ _ _ => exact ⟨_,_,hz⟩
  | xHalt hz _ _ _ _ => exact ⟨_,_,hz⟩
  | xRevert hz _ _ _ _ => exact ⟨_,_,hz⟩

/-- Alias creation executes INVALID; it cannot contain even a failed message
call, so its potentially inflated temporary entry does not enter this bound. -/
theorem invalid_has_no_call {fuel : Nat} {outer : XiArgs}
    {result : XiResult} {tree : EventTree} {path : EventTree.Address}
    {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (invalid : outer.env.code = ⟨#[0xfe]⟩)
    (loc : ThetaAt (.xi fuel outer) result tree path f a r) : False := by
  cases loc with
  | xi body inner =>
    obtain ⟨mid,cost,hz⟩ := theta_x_guard inner
    have hd : decodeAt outer.entry = (.INVALID, none) :=
      decodeAt_of_code_pc invalid rfl (by decide +kernel)
    rw [hd] at hz
    exact OrdinaryGas.accepted_valid hz rfl

/-- Both affordability and the world's budget are derived at every actual
message-call input, before its transfer and regardless of its final status. -/
theorem call_input_funds {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt q result tree path f a r) (funded : GoodFunding q) :
    GoodFunding (.theta f a) ∧ worldFunds a.world ≤ worldFunds (inputWorld q) := by
  induction loc with
  | here body => exact ⟨funded,Nat.le_refl _⟩
  | xStepError _ _ _ ih => exact ih trivial
  | xNextChild _ _ _ _ _ ih => exact ih trivial
  | @xNextTail n cost f vj pre mid post result child next path a r hz hs hh ht inner ih =>
    obtain ⟨ha,hb⟩ := ih trivial
    exact ⟨ha,hb.trans (ExecutionFunding.step_funds n hz (sound hs))⟩
  | xHalt _ _ _ _ _ ih => exact ih trivial
  | xRevert _ _ _ _ _ ih => exact ih trivial
  | xi body inner ih => exact ih trivial
  | @thetaCode n f outer a r bytes tree path hc body inner ih =>
    obtain ⟨ha,hb⟩ := ih trivial
    exact ⟨ha,hb.trans (theta_entry funded bytes)⟩
  | @lambdaInit n f outer a r bytes tree path hp body inner ih =>
    by_cases he : outer.source = CreationSettlement.address bytes
    · exact False.elim (invalid_has_no_call (lambda_alias_invalid funded he) inner)
    · obtain ⟨ha,hb⟩ := ih trivial
      exact ⟨ha,hb.trans (lambda_entry_distinct funded he)⟩
  | stepChild hc body inner ih =>
    obtain ⟨hf,hb⟩ := selected_child_funding hc
    obtain ⟨ha,hw⟩ := ih hf
    exact ⟨ha,hw.trans hb⟩

/-- This concerns the actual transfer, not a DELEGATECALL's apparent CALLVALUE. -/
theorem call_value_le_root {q : Request} {result : q.Outcome} {tree : EventTree}
    {path : EventTree.Address} {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt q result tree path f a r) (funded : GoodFunding q) :
    a.value.toNat ≤ worldFunds (inputWorld q) := by
  obtain ⟨ha,hw⟩ := call_input_funds loc funded
  exact (ha.trans (balance_le_funds a.world a.source)).trans hw

theorem transaction_call_value (c : RefundAccounting.Context) {account : Account .EVM}
    (ha : TransactionFunding.Admission c account)
    {tree : EventTree} {path : EventTree.Address} {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt (TransactionEventBounds.request c)
      (TransactionEventBounds.request c).eval tree path f a r) :
    a.value.toNat ≤ worldFunds c.world := by
  have hb := call_value_le_root loc (admitted_request c ha)
  rw [request_world] at hb
  have hd := TransactionFunding.checkpoint_debit c ha
  omega

/-- The complete actual funding history now supplies every nested transfer
ceiling. Only initial funds plus explicit credits need a protocol-derived bound;
no intermediate balance or per-child funding cap is assumed. -/
theorem history_call_value_lt {initial : AccountMap .EVM} {credits : Nat}
    (c : RefundAccounting.Context) {account : Account .EVM}
    (history : FundingHistory.Trace initial credits c.world)
    (ha : TransactionFunding.Admission c account)
    (budget : worldFunds initial + credits < FundedDomain.fundingCeiling)
    {tree : EventTree} {path : EventTree.Address} {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt (TransactionEventBounds.request c)
      (TransactionEventBounds.request c).eval tree path f a r) :
    a.value.toNat < FundedDomain.fundingCeiling :=
  ((transaction_call_value c ha loc).trans (FundingHistory.trace_funds history)).trans_lt budget

#print axioms invalid_has_no_call
#print axioms call_input_funds
#print axioms call_value_le_root
#print axioms transaction_call_value
#print axioms history_call_value_lt
end Eip8282.Audit.Integrator.NestedFunding

end

section

/-! ## NestedCallIdentity -/

/-!
# Unique actual Theta identity at a structural frame path

The same path in the same actual nested certificate cannot denote different
Theta invocations. This includes all outcomes and preserves full execution inputs,
not only the code or target account. No frame list or global count is assumed.
-/
namespace Eip8282.Audit.Integrator.NestedEvents.ThetaAt
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private theorem xi_nonempty {fuel : Nat} {outer : XiArgs} {result : XiResult}
    {tree : EventTree} {path : EventTree.Address} {f : Nat} {a : ThetaArgs} {r : ThetaResult}
    (h : ThetaAt (.xi fuel outer) result tree path f a r) : path ≠ [] := by
  cases h with
  | xi body loc => exact x_nonempty loc

theorem identity {q : Request} {result₁ result₂ : q.Outcome} {tree₁ tree₂ : EventTree}
    {path : EventTree.Address} {f₁ f₂ : Nat} {a₁ a₂ : ThetaArgs} {r₁ r₂ : ThetaResult}
    (h₁ : ThetaAt q result₁ tree₁ path f₁ a₁ r₁)
    (h₂ : ThetaAt q result₂ tree₂ path f₂ a₂ r₂) :
    f₁ = f₂ ∧ a₁ = a₂ ∧ r₁ = r₂ := by
  induction h₁ generalizing tree₂ f₂ a₂ r₂ with
  | here body =>
      cases h₂ with
      | here body₂ => exact ⟨rfl, rfl, outcome_deterministic body body₂⟩
      | thetaCode _ _ _ loc => exact False.elim (xi_nonempty loc rfl)
  | xStepError hz hs loc ih =>
      cases h₂ with
      | xStepError hz₂ hs₂ loc₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          exact ih loc₂
      | xNextChild hz₂ hs₂ _ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xHalt hz₂ hs₂ _ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xRevert hz₂ hs₂ _ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
  | xNextChild hz hs hh ht loc ih =>
      cases h₂ with
      | xStepError hz₂ hs₂ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xNextChild hz₂ hs₂ hh₂ ht₂ loc₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          exact ih loc₂
      | xHalt hz₂ hs₂ hh₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          cases hh.symm.trans hh₂
      | xRevert hz₂ hs₂ hh₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          cases hh.symm.trans hh₂
  | xNextTail hz hs hh ht loc ih =>
      cases h₂ with
      | xNextTail hz₂ hs₂ hh₂ ht₂ loc₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          exact ih loc₂
  | xHalt hz hs hh hn loc ih =>
      cases h₂ with
      | xStepError hz₂ hs₂ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xRevert _ _ _ hr₂ _ => exact False.elim (hn hr₂)
      | xNextChild hz₂ hs₂ hh₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          cases hh.symm.trans hh₂
      | xHalt hz₂ hs₂ _ _ loc₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          exact ih loc₂
  | xRevert hz hs hh hr loc ih =>
      cases h₂ with
      | xStepError hz₂ hs₂ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases outcome_deterministic hs hs₂
      | xHalt _ _ _ hn₂ _ => exact False.elim (hn₂ hr)
      | xNextChild hz₂ hs₂ hh₂ _ _ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          cases hh.symm.trans hh₂
      | xRevert hz₂ hs₂ _ _ loc₂ =>
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj (hz.symm.trans hz₂))
          cases Except.ok.inj (outcome_deterministic hs hs₂)
          exact ih loc₂
  | xi body loc ih =>
      cases h₂ with
      | xi _ loc₂ => exact ih loc₂
  | thetaCode bytes hc body loc ih =>
      cases h₂ with
      | here => exact False.elim (xi_nonempty loc rfl)
      | thetaCode _ hc₂ _ loc₂ =>
          cases ToExecute.Code.inj (hc.symm.trans hc₂)
          exact ih loc₂
  | lambdaInit bytes hp body loc ih =>
      cases h₂ with
      | lambdaInit _ hp₂ _ loc₂ =>
          cases Option.some.inj (hp.symm.trans hp₂)
          exact ih loc₂
  | stepChild hc body loc ih =>
      cases h₂ with
      | stepChild hc₂ _ loc₂ =>
          cases Option.some.inj (stepChild_unique hc hc₂)
          exact ih loc₂

#print axioms identity
end Eip8282.Audit.Integrator.NestedEvents.ThetaAt

end
