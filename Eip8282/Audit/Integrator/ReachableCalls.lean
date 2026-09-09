import Eip8282.Audit.Integrator.MessageCall
import Eip8282.Audit.Bytecode

/-!
# Concrete call histories, with bound pre- and post-worlds

This is the call-transition component of reachability, parameterised by an
initial full account map. It is NOT yet constructor-to-protocol reachability:
the initializer and versioned protocol rules must be supplied and justified
separately. In particular it proves no queue, funding or no-wrap invariant.

Unlike the earlier draft, a step cannot select an unrelated post-state: its
world is the one returned by the actual `Θ` call. An interpreter error cannot
extend the history. Ordinary EVM failures can extend it, retaining the world
according to the message-call semantics rather than an assumed rollback.

`Allowed` is a named environment policy. Protocol consumers must instantiate
it with externally justified rules, not the invariant they intend to prove.
-/

namespace Eip8282.Audit.Integrator.ReachableCalls

open EvmYul EvmYul.EVM
open Eip8282.Audit.Integrator.MessageCall

/-- The two audited contract kinds, independent of the legacy fee model. -/
inductive Contract where
  | deposit
  | exit
  deriving DecidableEq, Repr

def runtime : Contract → ByteArray
  | .deposit => Bytecode.depositRuntime
  | .exit => Bytecode.exitRuntime

def address : Contract → AccountAddress
  | .deposit => EvmRunner.depositAddr
  | .exit => EvmRunner.exitAddr

/-- A normal call executes the code actually installed at the audited address.
It cannot silently replace that code or use a different apparent CALLVALUE. -/
structure PinnedCall (kind : Contract) (c : Context) : Prop where
  target : c.target = address kind
  code : c.code = runtime kind
  installed : ∃ account, c.world.get? c.target = some account ∧ account.code = c.code
  ordinaryValue : c.apparentValue = c.value

/-- A concrete message-call transition, retaining its actual success flag,
remaining gas, accrued substate and return bytes. -/
structure Transition (kind : Contract) (before after : AccountMap .EVM) where
  call : Context
  pinned : PinnedCall kind call
  pre : call.world = before
  created : Std.TreeSet AccountAddress compare
  gas : UInt256
  substate : Substate
  success : Bool
  output : ByteArray
  executed : call.result = .ok (created, after, gas, substate, success, output)

/-- A history of actual calls from an explicit initial world. The policy may
restrict environments; the transition itself binds both account maps. -/
inductive From (kind : Contract) (initial : AccountMap .EVM)
    (Allowed : Context → Prop) : AccountMap .EVM → Prop where
  | initial : From kind initial Allowed initial
  | call {before after : AccountMap .EVM}
      (prior : From kind initial Allowed before)
      (transition : Transition kind before after)
      (allowed : Allowed transition.call) : From kind initial Allowed after

/-- A concrete REVERT step cannot choose an unrelated after-world. -/
theorem transition_revert_world {kind : Contract} {before after : AccountMap .EVM}
    (t : Transition kind before after) (gas : UInt256) (out : ByteArray)
    (h : t.call.execution = .ok (.revert gas out)) : after = before := by
  have hr := revert_restores_world t.call gas out h
  have hex := t.executed
  rw [hr] at hex
  have heq := Except.ok.inj hex
  have hw := congrArg (fun p => p.2.1) heq
  exact hw.symm.trans t.pre

/-- Genuine exceptional halts likewise cannot choose an unrelated world. -/
theorem transition_exception_world {kind : Contract} {before after : AccountMap .EVM}
    (t : Transition kind before after) (err : ExecutionException)
    (h : t.call.execution = .error err) (hreal : (err == .OutOfFuel) = false) :
    after = before := by
  have hr := exceptional_halt_restores_world t.call err h hreal
  have hex := t.executed
  rw [hr] at hex
  have heq := Except.ok.inj hex
  have hw := congrArg (fun p => p.2.1) heq
  exact hw.symm.trans t.pre

/-- Proof-evaluator exhaustion does not produce a history transition. -/
theorem transition_not_outOfFuel {kind : Contract} {before after : AccountMap .EVM}
    (t : Transition kind before after) : t.call.execution ≠ .error .OutOfFuel := by
  intro h
  have hr := evaluation_exhaustion_is_error t.call h
  have hex := t.executed
  rw [hr] at hex
  cases hex

#print axioms transition_revert_world
#print axioms transition_exception_world
#print axioms transition_not_outOfFuel

end Eip8282.Audit.Integrator.ReachableCalls
