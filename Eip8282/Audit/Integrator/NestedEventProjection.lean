import Eip8282.Audit.Integrator.NestedEventCert
import Eip8282.Audit.Integrator.AppendEvents

/-!
# Local append occurrences inside the same actual nested tree

Projection follows only continuation edges of one X frame. Selected child
frames remain in the tree but are not folded into the local fuel labels.
The actual certificate supplies fuel bounds for the structural-address map.
No global frame ownership, protocol history or new bytecode execution is assumed.
-/
namespace Eip8282.Audit.Integrator.NestedEvents
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall jumpdestsOf)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- Root marker uses the exact instruction fuel; only NEXT is frame-local. -/
def localEvents : Nat → EventTree → List Nat
  | _, .done => []
  | n, .step marked _ next =>
      (if marked then [n-1] else []) ++ localEvents (n-1) next

/-- Forgetting selected children recovers the actual all-outcome frame trace. -/
theorem local_projection {fuel : Nat} {vj : Array UInt256} {pre : EVM.State}
    {result : XResult} {tree : EventTree}
    (h : Cert (.x fuel vj pre) result tree) :
    FrameEvents.Trace vj fuel pre result (localEvents fuel tree) := by
  induction fuel generalizing pre result tree with
  | zero => cases h; exact .zero _
  | succ n ih =>
      cases h with
      | xGuardError hz => exact .guardError hz
      | xStepError hz hs =>
          simpa only [localEvents, Bool.false_eq_true, ↓reduceIte, List.nil_append] using
            FrameEvents.Trace.stepError hz (sound hs)
      | xNext hz hs hh ht =>
          simpa [localEvents, FrameEvents.emit] using
            FrameEvents.Trace.next hz (sound hs) hh (ih ht)
      | xHalt hz hs hh hn =>
          simpa [localEvents, FrameEvents.emit] using
            FrameEvents.Trace.halt hz (sound hs) hh hn
      | xRevert hz hs hh hr =>
          simpa [localEvents, FrameEvents.emit] using
            FrameEvents.Trace.revert hz (sound hs) hh hr

/-- A marker's root address, independently of its selected child's shape. -/
private theorem emitted_address (n event : Nat) (marked : Bool) (child next : EventTree)
    (he : event ∈ (if marked then [n] else [])) :
    List.replicate (n+1-(event+1)) true ∈ (EventTree.step marked child next).occurrences := by
  cases marked with
  | false => cases he
  | true =>
      have h : event = n := List.mem_singleton.mp he
      subst event
      simpa only [Nat.sub_self, List.replicate_zero] using
        (EventTree.root_mem_iff true child next).mpr rfl

/-- Local fuel positions map into the same tree via continuation-only paths.
The certificate is essential: arbitrary trees can have more NEXT nodes than fuel. -/
theorem local_address {fuel event : Nat} {vj : Array UInt256} {pre : EVM.State}
    {result : XResult} {tree : EventTree}
    (h : Cert (.x fuel vj pre) result tree)
    (he : event ∈ localEvents fuel tree) :
    List.replicate (fuel-(event+1)) true ∈ tree.occurrences := by
  induction fuel generalizing pre result tree with
  | zero => cases h; cases he
  | succ n ih =>
      cases h with
      | xGuardError hz => cases he
      | xStepError hz hs => simp [localEvents] at he
      | xNext hz hs hh ht =>
          simp only [localEvents, Nat.add_sub_cancel, List.mem_append] at he
          rcases he with here | later
          · exact emitted_address n event _ _ _ here
          · have hlt := FrameEvents.occurrence_lt (local_projection ht) event later
            have ha := ih ht later
            have hn : n+1-(event+1) = (n-(event+1))+1 := by omega
            rw [hn, List.replicate_succ]
            exact (EventTree.next_mem_iff _ _ _ _).mpr ha
      | xHalt hz hs hh hn =>
          simp only [localEvents, Nat.add_sub_cancel, List.append_nil] at he
          exact emitted_address n event _ _ _ he
      | xRevert hz hs hh hr =>
          simp only [localEvents, Nat.add_sub_cancel, List.append_nil] at he
          exact emitted_address n event _ _ _ he

/-- A supplied actual append LOG path selects an event in this very certificate,
including paths whose subsequent continuation errors or reverts. -/
theorem path_address {kind : Eip8282.Audit.Model.Kind} (q : XiCall kind)
    (len : UInt256) (hlen : 68 ≤ len.toNat) (path : ActualAppendGas.LogPath q len)
    {result : XResult} {tree : EventTree}
    (h : Cert (.x q.fuel (jumpdestsOf kind) q.entry) result tree) :
    ∃ event, event ∈ localEvents q.fuel tree ∧
      List.replicate (q.fuel-(event+1)) true ∈ tree.occurrences := by
  obtain ⟨event, he⟩ := AppendEvents.path_occurrence q len hlen path (local_projection h)
  exact ⟨event, he, local_address h he⟩

/-- Literal Ξ inputs of the existing audited call, without a second execution. -/
def rootXiArgs {kind : Eip8282.Audit.Model.Kind} (q : XiCall kind) : XiArgs :=
  { created := q.createdAccounts, genesis := q.genesisBlockHeader, blocks := q.blocks,
    world := q.σ, original := q.σ₀, gas := q.gas, substate := q.substate, env := q.env }

def rootXi {kind : Eip8282.Audit.Model.Kind} (q : XiCall kind) : Request :=
  .xi (q.fuel+1) (rootXiArgs q)

theorem rootXi_eval {kind : Eip8282.Audit.Model.Kind} (q : XiCall kind) :
    (rootXi q).eval = q.result := rfl

private theorem rootXiArgs_entry {kind : Eip8282.Audit.Model.Kind} (q : XiCall kind) :
    (rootXiArgs q).entry = q.entry := rfl

private theorem rootXiArgs_jumps {kind : Eip8282.Audit.Model.Kind} (q : XiCall kind) :
    (rootXiArgs q).jumps = jumpdestsOf kind :=
  Eip8282.Audit.XiTransport.Xi_validJumps_eq q.code_pinned

/-- The one Ξ wrapper exposes exactly its inner X certificate and fuel. -/
theorem rootXi_body {kind : Eip8282.Audit.Model.Kind} (q : XiCall kind)
    {result : XiResult} {tree : EventTree} (h : Cert (rootXi q) result tree) :
    Cert (.x q.fuel (jumpdestsOf kind) q.entry)
      (X q.fuel (jumpdestsOf kind) q.entry) tree := by
  cases h with
  | xi body =>
      change Cert (.x q.fuel (rootXiArgs q).jumps q.entry)
        (X q.fuel (rootXiArgs q).jumps q.entry) tree at body
      rw [rootXiArgs_jumps] at body
      exact body

/-- The existing successful audited append receipt selects a local occurrence
in the SAME root-Ξ tree. This is a local injection edge, not global uniqueness. -/
theorem successful_append_address {kind : Eip8282.Audit.Model.Kind} (q : XiCall kind)
    (huser : q.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hsize : q.env.calldata.size = match kind with | .deposit => 184 | .exit => 48)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (executed : q.result = .ok (.success (created,world,gas,substate) out))
    {result : XiResult} {tree : EventTree} (h : Cert (rootXi q) result tree) :
    ∃ event, event ∈ localEvents q.fuel tree ∧ event < q.fuel ∧
      List.replicate (q.fuel-(event+1)) true ∈ tree.occurrences := by
  have body := rootXi_body q h
  have trace := local_projection body
  have occurrence : ∃ event, event ∈ localEvents q.fuel tree := by
    cases kind with
    | deposit => exact AppendEvents.deposit_occurrence q huser hsize executed trace
    | exit => exact AppendEvents.exit_occurrence q huser hsize executed trace
  obtain ⟨event, he⟩ := occurrence
  exact ⟨event, he, FrameEvents.occurrence_lt trace event he, local_address body he⟩

#print axioms local_projection
#print axioms local_address
#print axioms path_address
#print axioms rootXi_eval
#print axioms rootXi_body
#print axioms successful_append_address
end Eip8282.Audit.Integrator.NestedEvents
