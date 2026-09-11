import Eip8282.Audit.Integrator.ReferenceCallPotential

/-! Finite compositional ledger of literal source resource operations. Child
work is counted in its recursive subtree once; a CALL parent's overhead excludes
its stipend. The relation records resource equations, not an execution of the
Python interpreter. Extracting it from actual source frames, including their
journals and protected append occurrences, remains a producer obligation.
There is no bound on the number of events, children or iterations. -/
namespace Eip8282.Audit.Integrator.ReferenceExecutionLedger
open EvmYul ReferenceMeterRollback ReferenceMeterBoundary ReferenceMeterPath
open ReferenceCallGrant ReferenceChildMeter ReferenceCallChildBoundary
open ReferenceExecutionPotential ReferenceCallPotential
set_option autoImplicit false
set_option maxHeartbeats 2000000

def eventWork : Event → Nat
  | .ordinary amount => amount
  | .store warm original current new => (ReferenceStorageGas.classify warm original current new).execution

def work (events : List Event) : Nat := (events.map eventWork).sum

theorem work_cast (events : List Event) :
    (work events : Int) = (events.map ReferenceMeterConservation.actualExec).sum := by
  induction events with
  | nil => rfl
  | cons event events ih =>
    simp only [work,List.map_cons,List.sum_cons,Int.natCast_add] at ih ⊢
    rw [ih]
    cases event <;> rfl

/-- CREATE's postcharge grant has no stipend and no UInt256 truncation of the
source Uint execution meter. The full state reservoir is drained to the child. -/
def creationSplit (charged : Meter) : Split :=
  let withheld := maximum charged.execution
  {parent := {charged with execution := charged.execution-withheld,reservoir := 0},
   childExecution := withheld,childState := charged.reservoir,withheld := withheld}

theorem creation_potential (charged : Meter) :
    potential (creationSplit charged).parent+potential (start (creationSplit charged)) = potential charged := by
  simp only [creationSplit,maximum,start,init,potential]
  omega

/-- All source creation preflight/collision decisions remain with the source
adapter. Here an entered child shares the exact post-state-charge grant and
settled merge. State credit on failed creation preserves the potential. -/
theorem creation_work {pre : Meter} {chargedCore : ReferenceStorageGas.Meter}
    {child final : Meter} {stateAmount childWork : Nat}
    (charged : ReferenceStorageGas.chargeState (core pre) stateAmount = some chargedCore)
    (outcome : Outcome) (newAccount : Bool)
    (workBound : potential child+childWork ≤ potential (start (creationSplit (update pre chargedCore))))
    (finished : finish true newAccount outcome (creationSplit (update pre chargedCore)) child = some final) :
    potential final+childWork ≤ potential pre := by
  have hcharge := state_preserves charged
  have hgrant := creation_potential (update pre chargedCore)
  have hsettle := settle_nonincrease outcome child
  unfold finish at finished
  cases hm : incorporate (creationSplit (update pre chargedCore)).parent
      (settle outcome child) (failed outcome) with
  | none => simp only [hm,Option.map_none] at finished; contradiction
  | some merged =>
    simp only [hm,Option.map_some,Option.some.injEq] at finished
    subst final
    have hmerge := incorporate_preserves hm
    have hcredit : potential (refill true newAccount outcome merged) = potential merged := by
      unfold refill
      split
      · exact credit_preserves _ _
      · rfl
    rw [hcredit]
    omega

inductive Run : Meter → Meter → Nat → Prop where
  | refl (m : Meter) : Run m m 0
  | trans {pre mid post : Meter} {first second : Nat}
      (head : Run pre mid first) (tail : Run mid post second) : Run pre post (first+second)
  | paid {pre post : Meter} (events : List Event)
      (actual : runFull events pre = some post) : Run pre post (work events)
  | state {pre : Meter} {post : ReferenceStorageGas.Meter} (amount : Nat)
      (actual : ReferenceStorageGas.chargeState (core pre) amount = some post) : Run pre (update pre post) 0
  | credit (pre : Meter) (amount : Nat) : Run pre (ReferenceCallChildBoundary.credit pre amount) 0
  | commit {pre post : Meter} (actual : ReferenceMeterRollback.commit pre = some post) : Run pre post 0
  | restore (pre : Meter) : Run pre (ReferenceMeterRollback.restore pre) 0
  | entry {pre post : Meter} (grant : Nat) (actual : restoreToEntry grant pre = some post) : Run pre post 0
  | refund (pre : Meter) (delta : Int) : Run pre {pre with refund := pre.refund+delta} 0
  | settle (pre : Meter) (outcome : Outcome) : Run pre (ReferenceChildMeter.settle outcome pre) 0
  | call {pre charged child final : Meter} {childWork : Nat}
      (cold delegated delegationCold hasValue deadRecipient : Bool) (memoryCost : Nat)
      (prepared : prepare cold delegated delegationCold hasValue deadRecipient memoryCost pre = some charged)
      (requested : UInt256) (outcome : Outcome)
      (body : Run (start (split hasValue requested charged)) child childWork)
      (finished : finish hasValue deadRecipient outcome (split hasValue requested charged) child = some final) :
      Run pre final (overhead cold delegated delegationCold hasValue memoryCost+childWork)
  | create {pre child final : Meter} {chargedCore : ReferenceStorageGas.Meter} {childWork : Nat}
      (stateAmount : Nat) (charged : ReferenceStorageGas.chargeState (core pre) stateAmount = some chargedCore)
      (outcome : Outcome) (newAccount : Bool)
      (body : Run (start (creationSplit (update pre chargedCore))) child childWork)
      (finished : finish true newAccount outcome (creationSplit (update pre chargedCore)) child = some final) :
      Run pre final childWork

/-- Arbitrary finite nested resource executions. Revert/exception settlement
cannot remove already counted child work; state credit cannot manufacture it. -/
theorem bounded {pre post : Meter} {executed : Nat} (h : Run pre post executed) :
    potential post+executed ≤ potential pre := by
  induction h with
  | refl => omega
  | trans _ _ first second => omega
  | paid events actual =>
    have h := paid_work actual
    have hc := work_cast events
    omega
  | state amount actual => rw [state_preserves actual]; omega
  | credit pre amount => rw [credit_preserves]; omega
  | commit actual => rw [commit_preserves actual]; omega
  | restore pre => rw [restore_preserves]; omega
  | entry grant actual => rw [entry_preserves actual]; omega
  | refund pre delta => simp [potential]
  | settle pre outcome => simpa only [Nat.add_zero] using settle_nonincrease outcome pre
  | call cold delegated delegationCold hasValue deadRecipient memoryCost prepared requested outcome body finished ih =>
    have hb := call_work prepared requested outcome ih finished
    omega
  | create stateAmount charged outcome newAccount body finished ih =>
    exact creation_work charged outcome newAccount ih finished

#print axioms work_cast
#print axioms creation_potential
#print axioms creation_work
#print axioms bounded
end Eip8282.Audit.Integrator.ReferenceExecutionLedger
