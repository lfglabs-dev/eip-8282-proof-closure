import Eip8282.Audit.UserXiCorrespondence
import Eip8282.Audit.Reachable

/-!
# The universal `Ξ ↔ Model` boundary, and the single premise that is missing

R2/R3 compose one whole call. R4 (`Eip8282.Audit.XiTransport`) closes the
`X → Ξ` layer and the exit-instruction layer with no premise. R5
(`Eip8282.Audit.Reachable`) closes the coverage direction of the storage guard.
What none of them does is state, in one place, **the universal claim the
campaign is actually aiming at** together with **exactly what is still owed for
it**.

This module does only that. It adds no guarantee ID, registers no parent,
strengthens nothing, and proves nothing about `Ξ` that R4 did not already prove.

## The two objects

`UniversalXiCorrespondence kind` is the target:

```
∀ c s call, PreCallRepresents kind c s call → AdmissibleCall c s call →
  ∃ w : XiHalts c,
    observe c.result = some (observeModel (Model.step s call)) ∧
      PostStateAgrees c s (Model.step s call)
```

with `c.result` the complete `EvmYul.EVM.Ξ` message call into the pinned runtime
for `kind`. `PreCallRepresents` and `AdmissibleCall` together are the guard, and every
component of it is a named hypothesis rather than an implicit convention:

* **state** — `PreCallRepresents kind c s call`: the world `Ξ` starts from holds
  the pinned predeploy, with `WellFormed` packed storage. On a user call this
  is the post-value-transfer entry world, while `s` remains the pre-transfer
  model state, and the tail has room for an append; on a system call it is the
  ordinary `Represents` relation;
* **call** — `env`: the abstract `call` is the message call `Ξ` is actually
  making (sender, calldata, value, code owner, caller class), not an unrelated
  step (`UserXiCorrespondence.UserCallEnv` on the user side); system calls
  additionally bind value to zero;
* **reachability** — `reachable`: `s` is a `Model.Reachable` state, i.e. one the
  two constructors and the two calls can build, not an arbitrary inhabitant of
  `Model.State`;
* **gas / fuel** — `gas_ge`, `fuel_ge`: `≥ 30M` gas and `≥ 300000` interpreter
  fuel.  The latter covers the known 64-record deposit-drain budget, for which
  the registered trace suite documents that 80000 is insufficient;
* **termination** — separately, `TerminationClosure` says the run reaches a
  halting instruction with fuel to spare. This is an *assumption*, not a
  theorem: nothing here proves the pinned runtimes terminate within
  `universalFuelBound`.

`EndpointClosure kind` is the endpoint/post-state half of the named OPEN
`A-ABSTRACT-TX` (HIGH) — historically `hend` / `EndpointAgrees`, restated by R4
at equal strength as `ExitAgrees`:

```
∀ c s call, PreCallRepresents kind c s call → AdmissibleCall c s call →
  ∀ w : XiHalts c,
    ExitAgrees w.op (haltData w.post.toMachineState w.op) (Model.step s call) ∧
      PostStateAgrees c s (Model.step s call)
```

## What is proved here, and what is not

`UniversalClosure kind := TerminationClosure kind ∧ EndpointClosure kind` is
the complete residual. `universal_iff_endpointClosure` proves it and the target
are **equivalent**. That is the whole content of this module, and it cuts both
ways:

* `universal_of_endpointClosure` — the universal correspondence follows from the
  combined termination and endpoint/post-state residual and nothing else.
* `endpointClosure_of_universal` — that combined residual is not an artefact of
  how the proof is staged. Anyone who proves the universal claim has proved both
  parts, so neither can be routed around, weakened, or split into a cheaper
  hypothesis.

`UniversalClosure` is **not proved here, and nothing in this repository proves
either component**. A green build of this module is therefore *not* evidence
that `Ξ` agrees with `Model.step`; it is evidence that the one named gap has the
two explicit components recorded in `audit/assumptions.yaml`. `A-ABSTRACT-TX`
stays OPEN at HIGH.

Nothing here observes chain state either, so `A-PINNED-SOURCE` is untouched and
stays OPEN.
-/

namespace Eip8282.Audit.UniversalBoundary

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Step (campaignGasBound)
open Eip8282.Audit.Correspondence (targetAddr)
open Eip8282.Audit.XiTransport
open Eip8282.Audit.WellFormed

/-! ## Termination, as an explicit assumption -/

/-- **A halting witness for a complete `Ξ` call.** The non-halting prefix runs
to `exit` with fuel to spare, `exit` decodes to `op`, `op` is charged, and it
steps to `post`.

This is the R2/R3/R4 run decomposition packaged as data so that it can be
quantified over. No theorem in this repository produces one for an arbitrary
admissible call; that is recorded separately by `TerminationClosure`. -/
structure XiHalts {kind : Kind} (c : XiCall kind) where
  /-- Fuel left over when the run stopped; positivity is what records *why*. -/
  rem : Nat
  gasCost : Nat
  trace : List Labelled
  exit : EVM.State
  mid : EVM.State
  post : EVM.State
  op : Operation .EVM
  arg : Option (UInt256 × Nat)
  run : RunUntil (fun w => Halting w) (jumpdestsOf kind) c.fuel c.entry
    trace (rem + 1) exit
  decode : decodeAt exit = (op, arg)
  charge : Z (jumpdestsOf kind) op exit = .ok (mid, gasCost)
  stepOk : StepOk rem gasCost (op, arg) mid post

/-! ## The admissibility guard -/

/-- Fuel sufficient for the known worst-case 64-record deposit drain.  The
registered CFG parents retain their existing 80000-step `CallHyp` scope; this
is the stronger bound required by the universal `Ξ` termination target. -/
def universalFuelBound : Nat := 300000

/-- The abstract step is the message call `Ξ` is making.

On the user side this is R2's `UserCallEnv` verbatim — sender, calldata, wei
value, owning predeploy, and a non-`SYSTEM_ADDR` caller. On the system side the
corresponding binding is that the caller *is* `SYSTEM_ADDR` with zero wei, as
in `runDepositSystem` / `runExitSystem`; the
`calldataNonempty` flag is tied to the actual `Ξ` calldata: the model's
control write must describe the same system call the pinned runtime receives. -/
def CallEnv {kind : Kind} (c : XiCall kind) : Model.Step → Prop
  | .user caller calldata value =>
      UserXiCorrespondence.UserCallEnv c caller calldata value
  | .system calldataNonempty =>
      c.env.codeOwner = targetAddr kind ∧
        c.env.sender = EvmRunner.sysAddr ∧
        c.env.weiValue = EvmRunner.ZERO_U256 ∧
        calldataNonempty = !c.env.calldata.isEmpty

/-- **Every hypothesis the universal claim is made under, as named fields.**

The state abstraction is deliberately *not* a field here. It is
`PreCallRepresents kind c s call`, carried as a separate hypothesis, so that
the target below reads `PreCallRepresents σ s call → AdmissibleCall σ call → …`
and neither premise can hide inside the other.

Nothing below is derived from anything else either: `PreCallRepresents` does
not imply `reachable` (`WellFormed` is a shape predicate, which is exactly what
`A-REACHABLE` was about), and neither implies `halts`. -/
structure AdmissibleCall {kind : Kind} (c : XiCall kind) (s : Model.State)
    (call : Model.Step) : Prop where
  /-- The abstract step is this very message call. -/
  env : CallEnv c call
  /-- `s` is built by the constructors and the two calls, not arbitrary. -/
  reachable : Model.Reachable s
  /-- Campaign gas bound, as on `CallHyp`. -/
  gas_ge : c.gas.toNat ≥ campaignGasBound
  /-- Universal interpreter-fuel bound, covering the known 64-record drain. -/
  fuel_ge : c.fuel ≥ universalFuelBound

/-- The concrete `Ξ` body starts after EVM message-call setup.  Consequently a
user entry account already contains `value`, whereas `Model.userCall` consumes
the pre-transfer state and credits that value exactly once on an accepted
submission. This relation binds both views explicitly, so the post-state
balance comparison uses the model's post-transfer balance.

The final user conjunct is the `AppendHyp.tail` boundary: a successful append
at `2^64 - 1` would create a storage image outside `WellFormed`, which this
universal target promises to preserve.

System calls carry no value-transfer distinction and use the ordinary state
abstraction. -/
def PreCallRepresents {kind : Kind} (c : XiCall kind) (s : Model.State)
    (call : Model.Step) : Prop :=
  match call with
  | .user _ _ value =>
      ∃ acc : Account .EVM,
        c.entry.accountMap.get? (targetAddr kind) = some acc ∧
          acc.code = Eip8282.Audit.Correspondence.runtimeCode kind ∧
          WellFormed kind acc.storage ∧
          s = toModel kind acc.storage (acc.balance.toNat - value) ∧
          acc.balance.toNat = s.balance + value ∧
          queueTail acc.storage + 1 < 2 ^ 64
  | .system _ => Represents kind c.entry s

/-- The post-call account map of a successful `Ξ` result refines the model
outcome state at the pinned predeploy. A revert carries no post account map in
`Ξ`; its required state relation is consequently the EVM rollback relation.
Errors are not a successful correspondence observation. -/
def PostStateAgrees {kind : Kind} (c : XiCall kind) (pre : Model.State)
    (out : Model.Outcome) : Prop :=
  match c.result with
  | .ok (.success (_, σ, _, _) _) =>
      ∃ acc : Account .EVM,
        σ.get? (targetAddr kind) = some acc ∧
          acc.code = Eip8282.Audit.Correspondence.runtimeCode kind ∧
          WellFormed kind acc.storage ∧
          out.state = toModel kind acc.storage acc.balance.toNat
  | .ok (.revert _ _) => out.state = pre
  | .error _ => False

/-! ## The unconditional half

R4 already fixes the observation of the whole call from the run alone. Restated
here against `XiHalts` so the boundary theorem below is a one-liner.
-/

/-- **No premise about the model.** The complete `Ξ` call observes exactly the
halting instruction the code run exits on. This is `A-ABSTRACT-TX`-free: it is
`XiTransport.observe_result_of_run`, which takes no `ExitAgrees`. -/
theorem observation_of_halts {kind : Kind} {c : XiCall kind} (w : XiHalts c) :
    observe c.result =
      some (exitObservation w.op (haltData w.post.toMachineState w.op)) :=
  observe_result_of_run c w.run w.decode w.charge w.stepOk

/-! ## The boundary -/

/-- **The residual, per admissible call.** The exit instruction's own
observation agrees with the model outcome, at every halting witness.

This is the named OPEN `A-ABSTRACT-TX`. It is a *premise* everywhere it appears
and is discharged nowhere. -/
def EndpointObligation {kind : Kind} (c : XiCall kind) (s : Model.State)
    (call : Model.Step) : Prop :=
  ∀ w : XiHalts c,
    ExitAgrees w.op (haltData w.post.toMachineState w.op) (Model.step s call) ∧
      PostStateAgrees c s (Model.step s call)

/-- The residual in its original `hend` / `EndpointAgrees` clothing. R4's
`endpointAgrees_iff_exitAgrees` makes the two interchangeable, so restating the
premise never changed its strength. -/
theorem endpointObligation_iff_endpointAgrees {kind : Kind} (c : XiCall kind)
    (s : Model.State) (call : Model.Step) :
    EndpointObligation c s call ↔
      ∀ w : XiHalts c,
        EndpointAgrees
          (if w.op = .REVERT then
              .revert w.post.gasAvailable (haltData w.post.toMachineState w.op)
            else .success w.post (haltData w.post.toMachineState w.op))
          (Model.step s call) ∧
          PostStateAgrees c s (Model.step s call) := by
  constructor
  · intro h w
    exact ⟨endpointAgrees_iff_exitAgrees.mpr (h w).1, (h w).2⟩
  · intro h w
    exact ⟨endpointAgrees_iff_exitAgrees.mp (h w).1, (h w).2⟩

/-- **The observation boundary, at one call.** Given a halting witness, the
whole-call observation is *equivalent* to endpoint agreement. The separate
post-state relation and universal termination obligation are intentionally not
hidden in this observation-only equivalence. -/
theorem correspondence_iff_exitAgrees {kind : Kind} {c : XiCall kind}
    {s : Model.State} {call : Model.Step} (w : XiHalts c) :
    observe c.result = some (observeModel (Model.step s call))
      ↔ ExitAgrees w.op (haltData w.post.toMachineState w.op)
          (Model.step s call) := by
  constructor
  · intro h
    exact Option.some.inj ((observation_of_halts w).symm.trans h)
  · intro h
    rw [observation_of_halts w]
    exact congrArg some h

/-- **Target shape, with the premise explicit.**

`PreCallRepresents σ s call → AdmissibleCall σ call → observe (runΞ pinnedBytecode σ call)
= observeModel (Model.step s call)` — with `hend` written out as the hypothesis
it is. `hrep` relates the pre-transfer model world to `Ξ`'s entry world;
`hadm` supplies call binding, reachability, gas and fuel; `hend` is
`A-ABSTRACT-TX` and is
supplied by the caller, never by this repository.

`hrep` and `hadm` are marked unused on purpose. The conclusion follows from the
run decomposition, `hend`, and the explicit post-state premise alone, which is
exactly the negative result: every admissibility hypothesis is already paid for,
and tightening any of them buys nothing while the two correspondence premises
are open. Termination is not among those premises; it is supplied separately by
`TerminationClosure` when this single-call result is lifted to the universal
target. -/
theorem xi_correspondence_of_admissible {kind : Kind} {c : XiCall kind}
    {s : Model.State} {call : Model.Step}
    (_hrep : PreCallRepresents c s call) (_hadm : AdmissibleCall c s call)
    (w : XiHalts c)
    (hend : ExitAgrees w.op (haltData w.post.toMachineState w.op)
      (Model.step s call))
    (hpost : PostStateAgrees c s (Model.step s call)) :
    observe c.result = some (observeModel (Model.step s call)) ∧
      PostStateAgrees c s (Model.step s call) :=
  ⟨(correspondence_iff_exitAgrees w).mpr hend, hpost⟩

/-! ## The universal statements -/

/-- **The claim the campaign is aiming at.** Not proved.

This is the target shape verbatim: for the pinned runtime of `kind`, every
`Ξ` message call out of a world that `PreCallRepresents` the pre-transfer
abstract state `s`, made
under the admissibility guard, observes what `Model.step s call` observes. -/
def UniversalXiCorrespondence (kind : Kind) : Prop :=
  ∀ (c : XiCall kind) (s : Model.State) (call : Model.Step),
    PreCallRepresents c s call → AdmissibleCall c s call →
      ∃ w : XiHalts c,
        observe c.result = some (observeModel (Model.step s call)) ∧
          PostStateAgrees c s (Model.step s call)

/-- **The explicit termination residual.** No admissibility hypothesis hides
this obligation: every in-scope call must be shown to reach a halt. -/
def TerminationClosure (kind : Kind) : Prop :=
  ∀ (c : XiCall kind) (s : Model.State) (call : Model.Step),
    PreCallRepresents c s call → AdmissibleCall c s call → Nonempty (XiHalts c)

/-- **The named OPEN `A-ABSTRACT-TX`, universally quantified.** Not proved. -/
def EndpointClosure (kind : Kind) : Prop :=
  ∀ (c : XiCall kind) (s : Model.State) (call : Model.Step),
    PreCallRepresents c s call → AdmissibleCall c s call →
      EndpointObligation c s call

/-- The exact residual is termination plus endpoint/post-state agreement. -/
def UniversalClosure (kind : Kind) : Prop :=
  TerminationClosure kind ∧ EndpointClosure kind

/-- The combined termination and endpoint/post-state residual is sufficient. -/
theorem universal_of_endpointClosure {kind : Kind} (h : UniversalClosure kind) :
    UniversalXiCorrespondence kind := by
  intro c s call hrep hadm
  obtain ⟨w⟩ := h.1 c s call hrep hadm
  exact ⟨w, xi_correspondence_of_admissible hrep hadm w
    (h.2 c s call hrep hadm w).1 (h.2 c s call hrep hadm w).2⟩

/-- The combined residual is not an artefact of proof staging: proving the
universal claim *is* proving it. There is no cheaper hypothesis to look for. -/
theorem endpointClosure_of_universal {kind : Kind}
    (h : UniversalXiCorrespondence kind) : UniversalClosure kind := by
  constructor
  · intro c s call hrep hadm
    obtain ⟨w, _, _⟩ := h c s call hrep hadm
    exact ⟨w⟩
  · intro c s call hrep hadm w
    obtain ⟨_, hobs, hpost⟩ := h c s call hrep hadm
    exact ⟨(correspondence_iff_exitAgrees w).mp hobs, hpost⟩

/-- **The boundary.** The universal `Ξ ↔ Model` correspondence under the
admissibility guard and the open `A-ABSTRACT-TX` combined residual are the same
statement. This module proves the equivalence; it proves **neither side**. -/
theorem universal_iff_endpointClosure (kind : Kind) :
    UniversalXiCorrespondence kind ↔ UniversalClosure kind :=
  ⟨endpointClosure_of_universal, universal_of_endpointClosure⟩

end Eip8282.Audit.UniversalBoundary
