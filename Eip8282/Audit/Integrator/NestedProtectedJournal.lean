import Eip8282.Audit.Integrator.JournalGuarantees
import Eip8282.Audit.Integrator.ProtectedJournalStep
import Eip8282.Audit.Integrator.CallOwnerCoherence
import Eip8282.Audit.Integrator.NestedCallDataFit
import Eip8282.Audit.Integrator.NestedCallFunding
import Eip8282.Audit.Integrator.SubstateSelfdestructFrame

/-!
# Bind actual nested protected requests to the three guarantee consumers

The history producer derives all located call input widths and transferred
value bounds. The atomic producer uses actual Theta code selection and its
result equation, never an independently executed synthetic replacement.
Its journal invariant is still an input until complete recursive history
extraction supplies it; neither this bridge nor a bounded execution test
establishes protocol reachability by itself.
-/
namespace Eip8282.Audit.Integrator.NestedProtectedJournal
open EvmYul EvmYul.EVM
open NestedEvents JournalInvariant
open ReachableCalls (Contract address runtime)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def Input (a : ThetaArgs) : Prop :=
  a.data.size < UInt256.size ∧
    (a.source ≠ Eip8282.Audit.EvmRunner.sysAddr → a.value.toNat < FundedDomain.fundingCeiling)

def Inputs (q : Request) (result : q.Outcome) (tree : EventTree) : Prop :=
  ∀ (path : EventTree.Address) (fuel : Nat) (a : ThetaArgs) (r : ThetaResult),
    ThetaAt q result tree path fuel a r → Input a

/-- All nested call input premises follow from one actual funding history and
the root admission width. External-credit provenance/budget remain explicit. -/
theorem inputs_from_history {initial : World} {credits : Nat}
    (c : RefundAccounting.Context) {account : Account .EVM}
    (history : FundingHistory.Trace initial credits c.world)
    (ha : TransactionFunding.Admission c account)
    (budget : TransferFunding.worldFunds initial + credits < FundedDomain.fundingCeiling)
    (fit : NestedCallDataFit.RootFits (TransactionEventBounds.request c))
    (tree : EventTree) :
    Inputs (TransactionEventBounds.request c) (TransactionEventBounds.request c).eval tree := by
  intro path fuel a r loc
  exact ⟨NestedCallDataFit.call_data_fit loc fit,
    fun _ => NestedFunding.history_call_value_lt c history ha budget loc⟩

private theorem code_body {fuel : Nat} {a : ThetaArgs} {bytes : ByteArray} {tree : EventTree}
    (hc : a.code = .Code bytes)
    (cert : Cert (.theta (fuel+1) a) (Request.theta (fuel+1) a).eval tree) :
    Cert (ProtectedJournalStep.executionRequest (a.context fuel bytes))
      (a.context fuel bytes).execution tree := by
  cases cert with
  | thetaPrecompile target hp => rw [hc] at hp; cases hp
  | thetaCode other hp body =>
    have he : other = bytes := ToExecute.Code.inj (hp.symm.trans hc)
    subst other
    exact body

def Observed (kind : Contract) (c : MessageCall.Context)
    (created : Created) (world : World) (substate : Substate) (success : Bool) (out : ByteArray) : Prop :=
  ∃ queue : List (QueueInvariant.Record (modelKind kind)),
    DirectGuarantees.SubmitObserved (modelKind kind) c created world substate success out ∧
    DirectDrain.Observed (modelKind kind) c world success out queue ∧
    DirectControl.Observed (modelKind kind) c created world substate success out

/-- A selected actual protected Theta supplies its own exact execution,
transition, public observations and post-journal. Input funding, size and code
selection are independent of the state invariant to be propagated globally. -/
theorem atomic_call {kind : Contract} {fuel : Nat} {a : ThetaArgs} {tree : EventTree}
    (cert : Cert (.theta (fuel+1) a) (Request.theta (fuel+1) a).eval tree)
    (coherent : CallOwnerCoherence.Coherent kind a) (target : a.target = address kind)
    (inputs : Input a) {budget : Nat} (hb : budget < 2^128)
    (hi : Invariant kind budget a.world)
    (hn : address kind ∉ a.substate.selfDestructSet)
    {created : Created} {world : World} {gas : UInt256} {substate : Substate}
    {success : Bool} {out : ByteArray}
    (hr : (Request.theta (fuel+1) a).eval = .ok (created,world,gas,substate,success,out)) :
    Invariant kind (budget+tree.count) world ∧
      address kind ∉ substate.selfDestructSet ∧
      Observed kind (a.context fuel (runtime kind)) created world substate success out := by
  have hcode := (coherent target).1
  have executed : (a.context fuel (runtime kind)).result =
      .ok (created,world,gas,substate,success,out) :=
    (thetaArgs_result a fuel (runtime kind) hcode).symm.trans hr
  let t : ReachableCalls.Transition kind a.world world :=
    { call := a.context fuel (runtime kind),
      pinned := CallOwnerCoherence.pinned fuel hi.1 coherent target,
      pre := rfl, created := created, gas := gas, substate := substate,
      success := success, output := out, executed := executed }
  have ha : ConcreteHistory.Allowed t.call := inputs
  have body : Cert (ProtectedJournalStep.executionRequest t.call) t.call.execution tree :=
    code_body hcode cert
  have hc : t.call.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
    cases kind <;> rfl
  exact ⟨ProtectedJournalStep.preserves t ha body hb hi,
    SubstateSelfdestructFrame.theta_exclusion t.call hc executed hn,
    JournalGuarantees.completed t hi hb inputs.1⟩

#print axioms inputs_from_history
#print axioms atomic_call
end Eip8282.Audit.Integrator.NestedProtectedJournal
