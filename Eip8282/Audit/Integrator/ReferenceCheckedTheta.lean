import Eip8282.Audit.Integrator.Topics.ReferenceChecked
import Eip8282.Audit.Integrator.NestedProtectedJournal
import Eip8282.Audit.Integrator.WorldNonempty
import Eip8282.Audit.Integrator.TransferFrame

/-! Computed protected-frame outcomes feed the three public predicates through
one pinned Theta receipt with synthetic replay resources. Every other call
input is retained, including the pre-transfer world and both value fields.
This is an effect-proof receipt, not an identification with a canonical source
receipt: source gas, full source account journal and occurrence identity still
need their own producers. The journal invariant/budget are supplied by the
existing history interface, whose canonical Ethereum extraction remains open.
-/
namespace Eip8282.Audit.Integrator.ReferenceCheckedTheta
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.XiTransport (XiCall)
open ReachableCalls (Contract PinnedCall Transition)
open JournalInvariant (modelKind Invariant)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceCheckedTerminalStep
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- Only proof resources change. Theta and Xi each consume one wrapper level. -/
def replay (c : MessageCall.Context) (events : List Event) (extra : Nat) : MessageCall.Context :=
  { c with
      fuel := events.length + 3
      gas := UInt256.ofNat (222*(ReferenceExecutionLedger.work events+extra)+2301) }

theorem context (c : MessageCall.Context) (events : List Event) (extra : Nat) :
    (replay c events extra).entryWorld = c.entryWorld ∧
    (replay c events extra).environment = c.environment ∧
    (replay c events extra).world = c.world ∧
    (replay c events extra).originalWorld = c.originalWorld ∧
    (replay c events extra).substate = c.substate ∧
    (replay c events extra).value = c.value ∧
    (replay c events extra).apparentValue = c.apparentValue := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

private theorem pinned {kind : Contract} {c : MessageCall.Context}
    (hc : PinnedCall kind c) (events : List Event) (extra : Nat) :
    PinnedCall kind (replay c events extra) :=
  ⟨hc.target,hc.code,hc.installed,hc.ordinaryValue⟩

private theorem code_pinned {kind : Contract} {c : MessageCall.Context}
    (hc : PinnedCall kind c) : c.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
  cases kind <;> exact hc.code

/-- Exact Xi payload, rather than only the status/output observation. -/
private theorem xi_success {kind : Eip8282.Audit.Model.Kind} (c : XiCall kind)
    {post : EVM.State} {out : ByteArray}
    (actual : X c.fuel (D_J c.env.code ⟨0⟩) c.entry = .ok (.success post out)) :
    c.result = .ok (.success (post.createdAccounts,post.accountMap,post.gasAvailable,post.substate) out) := by
  unfold XiCall.result Ξ
  change (do
    let result ← X c.fuel (D_J c.env.code ⟨0⟩) c.entry
    match result with
    | .success st output => Except.ok (ExecutionResult.success (st.createdAccounts,st.accountMap,st.gasAvailable,st.substate) output)
    | .revert gas output => Except.ok (ExecutionResult.revert gas output) : EvmRunner.RunResult) = _
  rw [actual]
  rfl

private theorem xi_revert {kind : Eip8282.Audit.Model.Kind} (c : XiCall kind)
    {gas : UInt256} {out : ByteArray}
    (actual : X c.fuel (D_J c.env.code ⟨0⟩) c.entry = .ok (.revert gas out)) :
    c.result = .ok (.revert gas out) := by
  unfold XiCall.result Ξ
  change (do
    let result ← X c.fuel (D_J c.env.code ⟨0⟩) c.entry
    match result with
    | .success st output => Except.ok (ExecutionResult.success (st.createdAccounts,st.accountMap,st.gasAvailable,st.substate) output)
    | .revert gas output => Except.ok (ExecutionResult.revert gas output) : EvmRunner.RunResult) = _
  rw [actual]
  rfl

/-- Same complete replay receipt and all three public observations. A reverted
internal view is retained for inspection but never used as the committed world. -/
def Completed (kind : Contract) (c : MessageCall.Context)
    (parent : ReferenceStorageView.Parent) (events : List Event)
    (view : View) (success : Bool) (output : ByteArray) : Prop :=
  ∃ extra post,
    ReferenceCheckedCompletion.Observations parent view post ∧
    let created := if success then post.createdAccounts else c.created
    let world := if success then post.accountMap else c.world
    let substate := if success then post.substate else c.substate
    (replay c events extra).result = .ok (created,world,post.gasAvailable,substate,success,output) ∧
    NestedProtectedJournal.Observed kind (replay c events extra) created world substate success output

private theorem guarantees {kind : Contract} {c : MessageCall.Context}
    (hc : PinnedCall kind c) {budget : Nat}
    (hi : Invariant kind budget c.world) (hb : budget < 2^128)
    (hd : c.calldata.size < UInt256.size) {events : List Event} {extra : Nat}
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {output : ByteArray}
    (actual : (replay c events extra).result = .ok (created,world,gas,substate,success,output)) :
    NestedProtectedJournal.Observed kind (replay c events extra) created world substate success output := by
  let t : Transition kind c.world world :=
    ⟨replay c events extra,pinned hc events extra,rfl,created,gas,substate,success,output,actual⟩
  exact JournalGuarantees.completed t hi hb hd

/-- Transport an already derived complete X endpoint to the actual enclosing
Theta of this replay call, preserving both success and full revert settlement. -/
private theorem endpoint {kind : Contract} {c : MessageCall.Context}
    (hc : PinnedCall kind c) {parent : ReferenceStorageView.Parent}
    {budget : Nat} (hi : Invariant kind budget c.world) (hb : budget < 2^128)
    (hd : c.calldata.size < UInt256.size) {events : List Event} {extra : Nat}
    {post : EVM.State} {view : View} {success : Bool} {output : ByteArray}
    (observed : ReferenceCheckedCompletion.Observations parent view post)
    (actual : X (events.length+2) (D_J (ReferenceRuntimeSites.runtime (modelKind kind)).code ⟨0⟩)
      (ReferenceSourceReplayEntry.call (CallBridge.codeCall c (code_pinned hc) 0) events extra).entry =
      (if success then .ok (.success post output) else .ok (.revert post.gasAvailable output))) :
    Completed kind c parent events view success output := by
  let r := replay c events extra
  have hr : r.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
    change c.code = _
    exact code_pinned hc
  have hf : r.fuel = (events.length+2)+1 := rfl
  have hj : (CallBridge.codeCall r hr (events.length+2)).env.code =
      (ReferenceRuntimeSites.runtime (modelKind kind)).code := by
    change c.code = _
    rw [code_pinned hc]
    cases kind <;> rfl
  have he : (CallBridge.codeCall r hr (events.length+2)).entry =
      (ReferenceSourceReplayEntry.call (CallBridge.codeCall c (code_pinned hc) 0) events extra).entry := by
    rfl
  cases success with
  | false =>
    have hx : X (CallBridge.codeCall r hr (events.length+2)).fuel
        (D_J (CallBridge.codeCall r hr (events.length+2)).env.code ⟨0⟩)
        (CallBridge.codeCall r hr (events.length+2)).entry = .ok (.revert post.gasAvailable output) := by
      rw [hj,he]
      change X (events.length+2) _ _ = _
      simpa only [Bool.false_eq_true,if_false,if_true] using actual
    have receipt := CallBridge.rolls_back_endpoint r hr (events.length+2) hf post.gasAvailable output
      (xi_revert _ hx)
    exact ⟨extra,post,observed,receipt,guarantees hc hi hb hd receipt⟩
  | true =>
    have hx : X (CallBridge.codeCall r hr (events.length+2)).fuel
        (D_J (CallBridge.codeCall r hr (events.length+2)).env.code ⟨0⟩)
        (CallBridge.codeCall r hr (events.length+2)).entry = .ok (.success post output) := by
      rw [hj,he]
      change X (events.length+2) _ _ = _
      simpa only [Bool.false_eq_true,if_false,if_true] using actual
    have receipt := CallBridge.commits_endpoint r hr (events.length+2) hf
      post.createdAccounts post.accountMap post.gasAvailable post.substate output
      (xi_success _ hx) (WorldNonempty.beq_empty_false_of_hasOwner observed.owner)
    exact ⟨extra,post,observed,receipt,guarantees hc hi hb hd receipt⟩

/-- No success, X trace or replay receipt is supplied: the actual checked
terminal computes that endpoint. Internal domain premises are obtained from
one journal invariant, retaining its explicit history/budget obligation. -/
theorem terminal {kind : Contract} {c : MessageCall.Context} (hc : PinnedCall kind c)
    {parent : ReferenceStorageView.Parent} {tx : ReferenceStorageView.Tx}
    {warm : Warm} {pre : Meter} {fuel : Nat} {events : List Event} {result : End}
    {destinations : List Nat} {ownerExists : Bool} {budget : Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent ByteArray.empty fuel
      (initial (CallBridge.codeCall c (code_pinned hc) 0) tx) warm pre = some (events,.terminal result))
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c (code_pinned hc) 0).entry.toState)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code_pinned hc) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (hi : Invariant kind budget c.world) (hb : budget < 2^128) (hd : c.calldata.size < UInt256.size) :
    Completed kind c parent events result.view (decide (result.halt ≠ .reverted)) result.output := by
  obtain ⟨extra,post,execution,observed⟩ := ReferenceCheckedExecution.terminal
    (CallBridge.codeCall c (code_pinned hc) 0) context actual slots (TransferFrame.pinned_codeCall_hasOwner c hc (code_pinned hc) 0) warmRelated grant
  apply endpoint hc hi hb hd observed (extra := extra)
  by_cases h : result.halt = .reverted <;> simpa only [h,ne_eq,not_true_eq_false,
    not_false_eq_true,decide_true,decide_false,Bool.false_eq_true,if_false,if_true] using execution

/-- A computed genuine EOF uses the identical receipt/guarantee consumer. -/
theorem eof {kind : Contract} {c : MessageCall.Context} (hc : PinnedCall kind c)
    {parent : ReferenceStorageView.Parent} {tx : ReferenceStorageView.Tx}
    {warm finalWarm : Warm} {pre final : Meter} {fuel : Nat} {events : List Event}
    {view : View} {output : ByteArray} {destinations : List Nat} {ownerExists : Bool} {budget : Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent ByteArray.empty fuel
      (initial (CallBridge.codeCall c (code_pinned hc) 0) tx) warm pre = some (events,.eof view finalWarm final output))
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c (code_pinned hc) 0).entry.toState)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code_pinned hc) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (hi : Invariant kind budget c.world) (hb : budget < 2^128) (hd : c.calldata.size < UInt256.size) :
    output = ByteArray.empty ∧ Completed kind c parent events view true output := by
  obtain ⟨empty,_,post,execution,observed⟩ := ReferenceCheckedEOF.execution
    (CallBridge.codeCall c (code_pinned hc) 0) context actual slots (TransferFrame.pinned_codeCall_hasOwner c hc (code_pinned hc) 0) warmRelated grant
  exact ⟨empty,endpoint hc hi hb hd observed execution⟩

#print axioms context
#print axioms terminal
#print axioms eof
end Eip8282.Audit.Integrator.ReferenceCheckedTheta
