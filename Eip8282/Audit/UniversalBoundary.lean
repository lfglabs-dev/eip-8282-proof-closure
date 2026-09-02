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
∀ c s call, PreCallRepresents c s call → AdmissibleCall c s call →
  ∃ w : XiHalts c,
    observe c.result = some (observeModel (Model.step s call)) ∧
      PostStateAgrees c s call (Model.step s call)
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
  making — `CALLER` source, calldata, value, code owner, caller class and
  branch-dependent write permission — not an unrelated step. On the user side
  this is `UserCallBinding`; on
  the system side it is `SystemCallBinding`, which additionally binds value to
  zero and the control flag to the actual calldata;
* **gas / fuel** — `gas_ge`, `fuel_ge`: `≥ 30M` gas and `≥ 300000` interpreter
  fuel.  The latter covers the known 64-record deposit-drain budget, for which
  the registered trace suite documents that 80000 is insufficient;
* **arithmetic** — `WordExactCall.noWrap`: `StepNoWrap`, the branch-sensitive
  word-exactness fact used by the R5 support lemmas.  It is deliberately **not**
  a premise of this campaign target: the model computes in unbounded `Nat`, the
  pinned runtimes in 256-bit words, and high-excess images therefore remain in
  the universal boundary until the model or a refinement proof accounts for
  word semantics. An enabled user step
  needs `FeeQuoteNoWrap`: the `bump_excess` fold `effectiveExcess s` and every
  intermediate of the `fake_expo` loop that computes `Model.currentFee s` fit
  the word, and the loop ends before the model's fuel does
  (`fakeExpoFitsWord`); an inhibited user step reverts before any arithmetic.
  An enabled empty-calldata system step needs
  `s.storedExcess + s.count < 2 ^ 256`, the sum `update_excess` forms before
  comparing it with the target; the nonempty-calldata latch and the inhibited
  clear store a constant. Without these bounds a well-formed image such as
  `wrapExcessImage` (`SLOT_EXCESS = 2 ^ 256 - 2`, `SLOT_COUNT = 10`) is
  admissible and `PostStateAgrees` is unsatisfiable there for every `Ξ`
  result, making the target refutable rather than open; and bounding only the
  folded excess, or only the stored result `Model.nextExcess`, still admits
  `wideExcessImage` and `wrapWindowImage`, where an intermediate word wraps
  although the model's input or result fits;
* **termination** — separately, `TerminationClosure` says the run reaches a
  halting instruction with fuel to spare. This is an *assumption*, not a
  theorem: nothing here proves the pinned runtimes terminate within
  `universalFuelBound`.

`EndpointClosure kind` is the endpoint/post-state half of the named OPEN
`A-ABSTRACT-TX` (HIGH) — historically `hend` / `EndpointAgrees`, restated by R4
at equal strength as `ExitAgrees`:

```
∀ c s call, PreCallRepresents c s call → AdmissibleCall c s call →
  ∀ w : XiHalts c,
    ExitAgrees w.op (haltData w.post.toMachineState w.op) (Model.step s call) ∧
      PostStateAgrees c s call (Model.step s call)
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
open Eip8282.Audit.Model (Kind inhibited effectiveExcess nextExcess)
open Eip8282.Audit.Step (campaignGasBound)
open Eip8282.Audit.Correspondence (targetAddr)
open Eip8282.Audit.XiTransport
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Reachable (setSlot applySystem systemControlWrite drainCount nextExcessOf
  DrainHyp)

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

/-- **The user side of the call binding.** The pinned runtime dispatches and
records the immediate caller (`ExecutionEnv.source`, `Iₛ`), not transaction
origin (`ExecutionEnv.sender`, `Iₒ`).  This binding therefore ties the model
caller directly to `source`, while leaving origin free for forwarded calls.

* `canonical`: `Model.Address` is an unbounded `Nat`, while
  `EvmRunner.toAddress` maps it into the EVM's 160-bit address space, so the
  caller the model records must already be the canonical value the runtime
  stores.
* `source_eq`: `CALLER` pushes `ExecutionEnv.source` (`Iₛ`, see
  `Step.callerWord`), and the exit runtime packs that word into the queued
  record.
* `user`: the source is not `SYSTEM_ADDR`, so the opening gate takes the user
  path. Write permission is guarded separately by `StepWrites`, since fee
  getters and rejected user submissions do not execute `SSTORE`. -/
structure UserCallBinding {kind : Kind} (c : XiCall kind)
    (caller : Model.Address) (calldata : List Model.Byte) (value : Model.Wei) :
    Prop where
  /-- The pinned code runs as the predeploy that owns it. -/
  owner : c.env.codeOwner = targetAddr kind
  /-- The abstract calldata is the byte string `Ξ` was handed. -/
  calldata_eq : bytes c.env.calldata = calldata
  /-- The abstract value is the wei the message call carries. -/
  value_eq : c.env.weiValue.toNat = value
  /-- The model caller is a canonical 160-bit address. -/
  canonical : caller < 2 ^ 160
  /-- `CALLER` (`ExecutionEnv.source`) is the modeled caller. -/
  source_eq : c.env.source = EvmRunner.toAddress caller
  /-- The immediate caller takes the user, rather than system, dispatch path. -/
  user : c.env.source ≠ EvmRunner.sysAddr

/-- **The system side of the call binding.** The caller *is* `SYSTEM_ADDR` —
as transaction sender and as the `CALLER` source the opening gate reads — with
zero wei and write permission, as in `runDepositSystem` / `runExitSystem`. The
`calldataNonempty` flag is tied to the actual `Ξ` calldata: the model's control
write must describe the same system call the pinned runtime receives. -/
structure SystemCallBinding {kind : Kind} (c : XiCall kind)
    (calldataNonempty : Bool) : Prop where
  /-- The pinned code runs as the predeploy that owns it. -/
  owner : c.env.codeOwner = targetAddr kind
  /-- The transaction sender is `SYSTEM_ADDR`. -/
  sender_eq : c.env.sender = EvmRunner.sysAddr
  /-- `CALLER` (`ExecutionEnv.source`) is `SYSTEM_ADDR`. -/
  source_eq : c.env.source = EvmRunner.sysAddr
  /-- System calls carry no value; `Model.Step.system` has no value field. -/
  value_zero : c.env.weiValue = EvmRunner.ZERO_U256
  /-- The model's control flag is the emptiness of the actual calldata. -/
  calldata_flag : calldataNonempty = !c.env.calldata.isEmpty
  /-- The drain writes control words, so it needs a writable environment. -/
  writable : c.env.perm = true

/-- The abstract step is the message call `Ξ` is making: `UserCallBinding` on
the user side, `SystemCallBinding` on the system side. -/
def CallEnv {kind : Kind} (c : XiCall kind) : Model.Step → Prop
  | .user caller calldata value => UserCallBinding c caller calldata value
  | .system calldataNonempty => SystemCallBinding c calldataNonempty

/-! ## Word arithmetic

The model computes in unbounded `Nat`; the pinned runtimes compute in 256-bit
words. `StepNoWrap` admits a step only on the branches whose word arithmetic is
exact, read off the pinned source (`main.eas`) branch by branch:

* **user, inhibited** — the opening `SLOAD; DUP1; PUSH32 INHIBITOR; EQ; JUMPI`
  refuses before any arithmetic: no bound;
* **user, enabled** — `bump_excess` folds `effectiveExcess s` with one `ADD`,
  then the shared `fake_expo` loop quotes the fee with `ADD output + accum`,
  `MUL accum * numerator`, `MUL denominator * i` and a `DIV` per iteration and
  `DIV output / denominator` at the end (`PSubmit1.FakeExpo` §6 pins those
  opcodes at deposit PCs 100–131 / exit PCs 99–130): `FeeQuoteNoWrap s`;
* **system, nonempty calldata** — `set_inhibitor` stores `INHIBITOR`: no bound;
* **system, empty calldata, inhibited** — `zero_excess` stores `0`: no bound;
* **system, empty calldata, enabled** — `update_excess` forms
  `added_count + excess` with one `ADD` *before* comparing it with the target,
  so the sum must fit the word, not merely the stored result `Model.nextExcess`:
  `s.storedExcess + s.count < 2 ^ 256`. This is the sum bound R5's
  `DrainHyp.noWrap` originally carried, restricted to the one branch that
  computes it; `DrainHyp` itself now asks only for the stored result to fit
  (`Reachable.nextExcessOf_lt_size_iff`), which this implies.

`nextExcess_lt_size_of_stepNoWrap` derives the result bound R5's `DrainHyp`
carries from the system-side guard, so nothing R5 states is lost. None of this
runs `Ξ`: the guard excludes the states at which the two arithmetics are known
to differ; that they agree elsewhere is part of the open residual.
-/

/-- **Every word the pinned `fake_expo` loop computes, checked against the
word.** `fakeExpoFitsWord num den fuel i output accum = true` says that the run
of `Model.fakeExponential.go num den fuel i output accum` never leaves the
256-bit word the shared `fake_expo.eas` body computes in: at every executed
iteration the `ADD` `output + accum`, the `MUL` `accum * num` and the `MUL`
`den * i` are below `UInt256.size` (the `ADD` `i + 1` cannot wrap, `i` being at
most one past the fuel), and the loop reaches `accum = 0` before the fuel is
spent. The last conjunct is not about a wrap: the pinned loop exits only on
`accum = 0`, whereas `go` returns `output / den` when its fuel runs out
whatever `accum` holds, so a fuel-exhausted run with `accum ≠ 0` disagrees
with the runtime without any word overflowing
(`fakeExpoFitsWord_fuel_boundary`). -/
def fakeExpoFitsWord (num den : Nat) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, accum => accum == 0
  | fuel + 1, i, output, accum =>
    accum == 0 ||
      (decide (output + accum < UInt256.size) &&
        decide (accum * num < UInt256.size) &&
        decide (den * i < UInt256.size) &&
        fakeExpoFitsWord num den fuel (i + 1) (output + accum)
          (accum * num / (den * i)))

/-- **The user-side arithmetic guard.** `Model.currentFee s` is
`fakeExponential minRequestFee (effectiveExcess s) feeUpdateFraction`, i.e. the
loop entered at `i = 1`, `output = 0`, `accum = minRequestFee * feeUpdateFraction`
with fuel `256` (`PSubmit1.FakeExpo.fakeExponential_eq_go`). The first conjunct
is the `bump_excess` `ADD`; the second is that loop, word by word. Bounding the
folded excess alone is not enough: `wideExcessImage` satisfies the first
conjunct and fails the second at the loop's first `MUL`. -/
def FeeQuoteNoWrap (s : Model.State) : Prop :=
  effectiveExcess s < UInt256.size ∧
    fakeExpoFitsWord (effectiveExcess s) Model.feeUpdateFraction 256 1 0
      (Model.minRequestFee * Model.feeUpdateFraction) = true

instance (s : Model.State) : Decidable (FeeQuoteNoWrap s) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Arithmetic bounds for exactly the branches that compute in the word, as
listed above: the fee quote's fold and loop on an enabled user step, the excess
sum on an enabled empty-calldata system step. Inhibited user calls revert before
either computation; nonempty system calls latch `inhibitor`, and inhibited empty
system calls clear to zero. Those branches therefore stay in scope even at a
wrapping pre-image. -/
def StepNoWrap (s : Model.State) : Model.Step → Prop
  | .user _ _ _ => inhibited s = true ∨ FeeQuoteNoWrap s
  | .system b => b = true ∨ inhibited s = true ∨ s.storedExcess + s.count < UInt256.size

instance (s : Model.State) : (call : Model.Step) → Decidable (StepNoWrap s call)
  | .user _ _ _ => inferInstanceAs (Decidable (_ ∨ _))
  | .system _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The system-side guard bounds the stored result: `nextExcess` is `inhibitor`,
`0`, or at most the bounded sum. This is what R5's `DrainHyp.noWrap` asks for,
so every lemma R5 states under `DrainHyp` still applies
(`drainHyp_of_admissible`). -/
theorem nextExcess_lt_size_of_stepNoWrap {s : Model.State} {b : Bool}
    (h : StepNoWrap s (.system b)) : nextExcess s b < UInt256.size := by
  have hinh : Model.inhibitor < UInt256.size := by decide
  have hzero : 0 < UInt256.size := by decide
  rcases h with hb | hi | hsum
  · subst hb
    simpa [nextExcess] using hinh
  · cases b
    · simp [nextExcess, hi, hzero]
    · simpa [nextExcess] using hinh
  · cases b
    · simp only [nextExcess, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> omega
    · simpa [nextExcess] using hinh

/-- **Every hypothesis the universal claim is made under, as named fields.**

The state abstraction is deliberately *not* a field here. It is
`PreCallRepresents kind c s call`, carried as a separate hypothesis, so that
the target below reads `PreCallRepresents σ s call → AdmissibleCall σ call → …`
and neither premise can hide inside the other.

`PreCallRepresents` carries the well-formed concrete-state guard, while the
remaining fields constrain only this call.  `StepNoWrap` is intentionally a
separate `WordExactCall` witness rather than a field here: it records where the
unbounded model and 256-bit runtime arithmetic are known to agree for support
lemmas, but cannot silently shrink the campaign's well-formed-state boundary.
Termination is deliberately not a field: `TerminationClosure` records it
separately. -/
structure AdmissibleCall {kind : Kind} (c : XiCall kind) (s : Model.State)
    (call : Model.Step) : Prop where
  /-- The abstract step is this very message call. -/
  env : CallEnv c call
  /-- Campaign gas bound, as on `CallHyp`. -/
  gas_ge : c.gas.toNat ≥ campaignGasBound
  /-- Universal interpreter-fuel bound, covering the known 64-record drain. -/
  fuel_ge : c.fuel ≥ universalFuelBound
  /-- Calls which can execute `SSTORE` have write permission. Read-only user
  branches remain admissible under `STATICCALL`. -/
  writable : (match call with
    | .user caller calldata value =>
        Model.userCall s caller calldata value =
          .success (Model.appendRecord s caller calldata value) []
    | .system _ => True) → c.env.perm = true

/-- A separately named word-exactness witness.  R5's storage-transition lemmas
need it because `Reachable.applySystem` stores a `UInt256`; it is not an
admissibility premise of `UniversalXiCorrespondence`, whose announced boundary
is every well-formed call with the campaign call, gas and fuel guards. -/
structure WordExactCall (s : Model.State) (call : Model.Step) : Prop where
  /-- Every branch that computes in the word is bounded by `StepNoWrap`. -/
  noWrap : StepNoWrap s call

/-- The concrete `Ξ` body starts after EVM message-call setup.  Consequently a
user entry account already contains `value`, whereas `Model.userCall` consumes
the pre-transfer state and credits that value exactly once on an accepted
submission. This relation binds both views explicitly, so the post-state
balance comparison uses the model's post-transfer balance.

The final user conjunct is the `AppendHyp.tail` boundary, but it is conditional
on the model taking its successful append branch. A successful append at
`2^64 - 1` would create a storage image outside `WellFormed`, which this
universal target promises to preserve. Fee getters and rejected submissions do
not append, so they remain in scope at that otherwise valid tail boundary.

System calls carry no value-transfer distinction and use the ordinary state
abstraction. -/
def UserAppends (s : Model.State) (caller : Model.Address)
    (calldata : List Model.Byte) (value : Model.Wei) : Prop :=
  Model.userCall s caller calldata value =
    .success (Model.appendRecord s caller calldata value) []

/-- Whether this particular abstract step writes a new packed queue item. -/
def StepAppends (s : Model.State) : Model.Step → Prop
  | .user caller calldata value => UserAppends s caller calldata value
  | .system _ => False

/-- Whether the modeled call can reach an `SSTORE`. System calls always write
control words; user calls write only on their successful append branch. -/
def StepWrites (s : Model.State) : Model.Step → Prop
  | .user caller calldata value => UserAppends s caller calldata value
  | .system _ => True

/-- Slots a modeled call is allowed to change.  The abstract equality below
covers the control words and live queue; this frame closes the remaining
packed-storage surface, including stale and out-of-window words. -/
def MayWriteSlot {kind : Kind} (σ : Storage) (s : Model.State) : Model.Step → Nat → Prop
  | .user caller calldata value, slot =>
      (UserAppends s caller calldata value ∧
        (slot = SLOT_COUNT ∨ slot = QUEUE_TAIL ∨
          itemBase kind (queueTail σ) ≤ slot ∧
            slot < itemBase kind (queueTail σ) + slotsPerItem kind))
  | .system _, slot => slot = SLOT_EXCESS ∨ slot = SLOT_COUNT ∨ slot = QUEUE_HEAD ∨ slot = QUEUE_TAIL

/-- The model decoder intentionally ignores packed-word padding.  The boundary
must not: a deposit consumes only the first 184 bytes of six words, while an
exit consumes a 160-bit source and the first 48 bytes of its two pubkey words.
The comparison includes the decoded model record *and* the ignored bits, so it
is an equality with the canonical packed item rather than an unconstrained
item window: `decodeItem` fixes the 184 calldata bytes of a deposit and the
zero conjunct fixes the 8 trailing bytes of its sixth word; for an exit the
width bound fixes the whole first word to the 160-bit source and the zero
conjunct fixes the 16 trailing bytes of the second pubkey word. Every bit of
the `slotsPerItem kind` appended words is thereby determined. -/
def CanonicalAppendedItem (kind : Kind) (σ : Storage) (idx : Nat)
    (record : Model.Record) : Prop :=
  decodeItem kind σ idx = record ∧
    match kind with
    | .deposit =>
        loadNat σ (itemBase .deposit idx + 5) % 256 ^ 8 = 0
    | .exit =>
        loadNat σ (itemBase .exit idx) < 256 ^ 20 ∧
          loadNat σ (itemBase .exit idx + 2) % 256 ^ 16 = 0

/-- **Every storage key outside the modeled write set is preserved.**

The frame is quantified over the `UInt256` keys of the `Storage` map itself,
so a key names exactly one slot. Quantifying over an unbounded `Nat` slot
would let `2 ^ 256 + SLOT_COUNT`, which `MayWriteSlot` does not classify as
writable, alias the count word through `UInt256.ofNat`'s wrap-around and make
the frame unsatisfiable for every state-changing call.
`storageFrameAgrees_iff_loadU256` is the same frame read through `loadU256`
at canonical slot numbers. -/
def StorageFrameAgrees {kind : Kind} (pre post : Storage) (s : Model.State)
    (call : Model.Step) : Prop :=
  ∀ key : UInt256, ¬ MayWriteSlot (kind := kind) pre s call key.toNat →
    post.getD key (UInt256.ofNat 0) = pre.getD key (UInt256.ofNat 0)

private theorem ofNat_toNat (u : UInt256) : UInt256.ofNat u.toNat = u := by
  rcases u with ⟨⟨n, hn⟩⟩
  show UInt256.mk (Fin.ofNat _ n) = UInt256.mk ⟨n, hn⟩
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt hn)

/-- The frame over `UInt256` keys is the frame over canonical `Nat` slots read
through `loadU256`: below `UInt256.size` the two views name the same cells. -/
theorem storageFrameAgrees_iff_loadU256 {kind : Kind} (pre post : Storage)
    (s : Model.State) (call : Model.Step) :
    StorageFrameAgrees (kind := kind) pre post s call ↔
      ∀ slot : Nat, slot < UInt256.size →
        ¬ MayWriteSlot (kind := kind) pre s call slot →
          loadU256 post slot = loadU256 pre slot := by
  constructor
  · intro h slot hslot hw
    have hkey := h (UInt256.ofNat slot)
    rw [Eip8282.Audit.Reachable.toNat_ofNat_lt hslot] at hkey
    exact hkey hw
  · intro h key hw
    have hslot := h key.toNat key.val.isLt hw
    unfold loadU256 at hslot
    rwa [ofNat_toNat] at hslot

/-! ## The system write set

`MayWriteSlot` exempts the four control words from the frame on a system step,
and the abstract equality cannot pin the two pointers on its own: `toModel`
reads `QUEUE_HEAD` / `QUEUE_TAIL` only through `queueOf`, which sees the
*difference* of the pointers and the item words between them. A full drain
from an image with `HEAD = TAIL = 5` — a reachable empty queue — that leaves
both words at `5` therefore decodes to the same empty queue as the `(0, 0)`
reset `Reachable.applySystem` performs, and a nonempty full drain is ambiguous
in the same way. Permitting the control words to change is not the same as
saying what they become. `SystemControlAgrees` says it: every control word of
the committed image is the one `applySystem` stores, read through `loadU256`
at the canonical slot numbers. Together with the frame this determines the
committed storage at every key (`system_post_storage_eq_applySystem`).

User steps need no counterpart. The frame keeps `SLOT_EXCESS` and
`QUEUE_HEAD` (neither is in the user write set); the abstract equality fixes
`SLOT_COUNT` and, through `queueOf_length` on the `WellFormed` post-image,
`QUEUE_TAIL`.
-/

/-- **The control words after a system call are `Reachable.applySystem`'s.**
The four slots listed are exactly the system case of `MayWriteSlot`, so the
frame fixes every other key and this fixes the write set itself. -/
def SystemControlAgrees (kind : Kind) (pre post : Storage) (calldataNonempty : Bool) :
    Prop :=
  ∀ slot : Nat,
    slot = SLOT_EXCESS ∨ slot = SLOT_COUNT ∨ slot = QUEUE_HEAD ∨ slot = QUEUE_TAIL →
      loadU256 post slot = loadU256 (applySystem kind pre calldataNonempty) slot

/-- The control-word obligation of a modeled step: `SystemControlAgrees` on the
system side; on the user side the frame and the abstract equality already
determine all four words, as explained above. -/
def ControlWordsAgree (kind : Kind) (pre post : Storage) : Model.Step → Prop
  | .user _ _ _ => True
  | .system calldataNonempty => SystemControlAgrees kind pre post calldataNonempty

/-- A key other than the written slot reads the same after one `SSTORE`,
whatever value was stored. Unlike `Reachable.loadNat_setSlot_ne` this needs no
bound on the value, which is what lets `systemControlWrite` be read past
without a `DrainHyp`. -/
private theorem getD_setSlot_of_ne (σ : Storage) {slot : Nat} (value : Nat)
    (key : UInt256) (hslot : slot < UInt256.size) (hne : key.toNat ≠ slot) :
    (setSlot σ slot value).getD key (UInt256.ofNat 0) = σ.getD key (UInt256.ofNat 0) := by
  unfold setSlot
  rw [Std.TreeMap.getD_insert]
  have hcmp : ¬ compare (UInt256.ofNat slot) key = .eq := by
    intro h
    have h' : compare (UInt256.ofNat slot) (UInt256.ofNat key.toNat) = .eq := by
      rwa [ofNat_toNat]
    exact hne ((Eip8282.Audit.Reachable.compare_ofNat_eq_iff hslot key.val.isLt).mp h').symm
  rw [if_neg hcmp]

private theorem loadU256_setSlot_of_ne (σ : Storage) {slot : Nat} (value : Nat) {q : Nat}
    (hslot : slot < UInt256.size) (hq : q < UInt256.size) (hne : q ≠ slot) :
    loadU256 (setSlot σ slot value) q = loadU256 σ q := by
  unfold loadU256
  refine getD_setSlot_of_ne σ value (UInt256.ofNat q) hslot ?_
  rw [Eip8282.Audit.Reachable.toNat_ofNat_lt hq]
  exact hne

/-- The modeled transition satisfies the frame: `applySystem` writes only the
four control words. -/
theorem applySystem_storageFrameAgrees (kind : Kind) (pre : Storage) (s : Model.State)
    (b : Bool) :
    StorageFrameAgrees (kind := kind) pre (applySystem kind pre b) s (.system b) := by
  intro key hw
  simp only [MayWriteSlot, not_or] at hw
  obtain ⟨h0, h1, h2, h3⟩ := hw
  obtain ⟨s0, s1, s2, s3⟩ := Eip8282.Audit.Reachable.control_slots_lt_size
  unfold applySystem systemControlWrite
  split
  · rw [getD_setSlot_of_ne _ _ _ s3 h3, getD_setSlot_of_ne _ _ _ s2 h2,
      getD_setSlot_of_ne _ _ _ s1 h1, getD_setSlot_of_ne _ _ _ s0 h0]
  · rw [getD_setSlot_of_ne _ _ _ s2 h2, getD_setSlot_of_ne _ _ _ s1 h1,
      getD_setSlot_of_ne _ _ _ s0 h0]

/-- The modeled transition satisfies the control-word conjunct, so the
strengthened post-state relation is inhabited by exactly the transition R5
states rather than by nothing. -/
theorem applySystem_systemControlAgrees (kind : Kind) (pre : Storage) (b : Bool) :
    SystemControlAgrees kind pre (applySystem kind pre b) b :=
  fun _ _ => rfl

/-- **Frame plus control words determine the committed storage.** On a system
step the two conjuncts leave no key free: the post-image reads as
`applySystem` everywhere. This is the statement the ledger's "`Ξ` realises
`applySystem`" residual is about, now expressible at the boundary. -/
theorem system_post_storage_eq_applySystem {kind : Kind} {pre post : Storage}
    {s : Model.State} {b : Bool}
    (hframe : StorageFrameAgrees (kind := kind) pre post s (.system b))
    (hctl : SystemControlAgrees kind pre post b) :
    ∀ key : UInt256,
      post.getD key (UInt256.ofNat 0) =
        (applySystem kind pre b).getD key (UInt256.ofNat 0) := by
  intro key
  by_cases hw : MayWriteSlot (kind := kind) pre s (.system b) key.toNat
  · simp only [MayWriteSlot] at hw
    have h := hctl key.toNat hw
    unfold loadU256 at h
    rwa [ofNat_toNat] at h
  · rw [hframe key hw, applySystem_storageFrameAgrees kind pre s b key hw]

/-- Each control word, read as a natural number. -/
theorem systemControlAgrees_loadNat {kind : Kind} {pre post : Storage} {b : Bool}
    (h : SystemControlAgrees kind pre post b) {slot : Nat}
    (hslot : slot = SLOT_EXCESS ∨ slot = SLOT_COUNT ∨ slot = QUEUE_HEAD ∨ slot = QUEUE_TAIL) :
    loadNat post slot = loadNat (applySystem kind pre b) slot := by
  unfold loadNat
  rw [h slot hslot]

/-- **The control words, spelled out.** Under R5's drain hypothesis the four
words are `nextExcess`, zero, and the drained pointers: `QUEUE_HEAD` advanced
by the drained count with `QUEUE_TAIL` unchanged on a partial drain, both
reset to zero on a full one. -/
theorem system_post_control_words {kind : Kind} {pre post : Storage} {b : Bool}
    (h : SystemControlAgrees kind pre post b) (hd : DrainHyp kind pre b) :
    slotExcess post = nextExcessOf kind pre b ∧
      slotCount post = 0 ∧
      (if queueHead pre + drainCount kind pre = queueTail pre then
        queueHead post = 0 ∧ queueTail post = 0
      else
        queueHead post = queueHead pre + drainCount kind pre ∧
          queueTail post = queueTail pre) := by
  have hE : slotExcess post = slotExcess (applySystem kind pre b) :=
    systemControlAgrees_loadNat h (Or.inl rfl)
  have hC : slotCount post = slotCount (applySystem kind pre b) :=
    systemControlAgrees_loadNat h (Or.inr (Or.inl rfl))
  have hH : queueHead post = queueHead (applySystem kind pre b) :=
    systemControlAgrees_loadNat h (Or.inr (Or.inr (Or.inl rfl)))
  have hT : queueTail post = queueTail (applySystem kind pre b) :=
    systemControlAgrees_loadNat h (Or.inr (Or.inr (Or.inr rfl)))
  rw [hE, hC, hH, hT]
  exact ⟨Eip8282.Audit.Reachable.applySystem_excess hd,
    Eip8282.Audit.Reachable.applySystem_count hd,
    Eip8282.Audit.Reachable.applySystem_pointers hd⟩

/-- **A full drain resets both pointers**, whatever nonzero equal values they
held before. This is the case the exemption used to leave open. -/
theorem system_full_drain_resets_pointers {kind : Kind} {pre post : Storage} {b : Bool}
    (h : SystemControlAgrees kind pre post b) (hd : DrainHyp kind pre b)
    (hfull : queueHead pre + drainCount kind pre = queueTail pre) :
    queueHead post = 0 ∧ queueTail post = 0 := by
  have := (system_post_control_words h hd).2.2
  rwa [if_pos hfull] at this

/-- **Regression.** After a full drain a committed image with a nonzero
pointer does not satisfy the control-word conjunct, even though `toModel`
reads the same empty queue off it. Before `SystemControlAgrees` the frame
exempted both slots and nothing else observed them. -/
theorem full_drain_nonzero_pointer_rejected {kind : Kind} {pre post : Storage} {b : Bool}
    (hd : DrainHyp kind pre b)
    (hfull : queueHead pre + drainCount kind pre = queueTail pre)
    (hstale : queueHead post ≠ 0 ∨ queueTail post ≠ 0) :
    ¬ SystemControlAgrees kind pre post b := by
  intro h
  have hreset := system_full_drain_resets_pointers h hd hfull
  rcases hstale with hs | hs
  · exact hs hreset.1
  · exact hs hreset.2

/-- An empty queue with equal pointers is a full drain of nothing. -/
theorem full_drain_of_pointers_eq {kind : Kind} {pre : Storage}
    (heq : queueHead pre = queueTail pre) :
    queueHead pre + drainCount kind pre = queueTail pre := by
  unfold drainCount
  omega

/-- The two control-word `SSTORE`s alone leave `QUEUE_HEAD` where it was. -/
theorem queueHead_systemControlWrite (kind : Kind) (σ : Storage) (b : Bool) :
    queueHead (systemControlWrite kind σ b) = queueHead σ := by
  obtain ⟨s0, s1, s2, _⟩ := Eip8282.Audit.Reachable.control_slots_lt_size
  unfold queueHead loadNat systemControlWrite
  rw [loadU256_setSlot_of_ne _ _ s1 s2 (by decide), loadU256_setSlot_of_ne _ _ s0 s2 (by decide)]

/-- The reviewer's instance: `HEAD = TAIL = 5`, a well-formed image whose
queue is empty and whose pointers are equal and nonzero. -/
def stalePointerImage : Storage := storageFromList [(0, 100), (1, 5), (2, 5), (3, 5)]

/-- **Canary for the finding.** From `stalePointerImage`, a run that performs
the two control-word writes and skips the pointer reset — leaving
`HEAD = TAIL = 5` — is rejected by `SystemControlAgrees` for either predeploy
and either calldata flag. -/
theorem stalePointerImage_rejected (kind : Kind) (b : Bool) :
    ¬ SystemControlAgrees kind stalePointerImage
      (systemControlWrite kind stalePointerImage b) b :=
  full_drain_nonzero_pointer_rejected (by
    cases kind <;> cases b <;> exact ⟨by decide, by decide⟩)
    (full_drain_of_pointers_eq (by decide))
    (Or.inl (by rw [queueHead_systemControlWrite]; decide))

/-! ## The receipt

`observe` records status and return bytes, the conjuncts above record the
committed account, and neither sees the `Substate`. P-SUBMIT-1 does: an
accepted submission publishes one anonymous `LOG0` (`push RECORD_SIZE; push 0;
log0` in both pinned runtimes, after the record has been staged in memory),
and the registered traces pin its payload. The universal target therefore
carries the log series too. `Ξ` starts from the entry substate `c.substate`
and `LOG0` only ever `push`es (`EvmYul.SharedState.log`), so the committed
series is the entry series plus exactly what the step publishes.
-/

/-- The payload of the receipt an accepted submission publishes: the 184-byte
deposit calldata verbatim, or the 20-byte big-endian `CALLER` followed by the
48-byte exit pubkey — 68 bytes, the same layout the system drain returns for
an exit record. -/
def appendLogData (kind : Kind) (caller : Model.Address)
    (calldata : List Model.Byte) : List Model.Byte :=
  match kind with
  | .deposit => calldata
  | .exit => Model.toBeBytes caller 20 ++ calldata

/-- **The log series a modeled step leaves behind.** On an accepted user
submission the committed series is the entry series plus one anonymous entry
from the predeploy carrying `appendLogData`; a fee getter or a rejected
submission that still succeeds publishes nothing, and neither does a system
call (the drain path has no `LOG` instruction). A revert discards the
substate, so there the model's rollback state is the whole obligation. -/
def LogsAgree {kind : Kind} (c : XiCall kind) (s : Model.State) (call : Model.Step)
    (post : Substate) : Prop :=
  match call with
  | .user caller calldata value =>
      (UserAppends s caller calldata value →
        ∃ e : LogEntry,
          post.logSeries = c.substate.logSeries.push e ∧
            e.address = targetAddr kind ∧ e.topics = #[] ∧
              bytes e.data = appendLogData kind caller calldata) ∧
      (¬ UserAppends s caller calldata value →
        post.logSeries = c.substate.logSeries)
  | .system _ => post.logSeries = c.substate.logSeries

def PreCallRepresents {kind : Kind} (c : XiCall kind) (s : Model.State)
    (call : Model.Step) : Prop :=
  match call with
  | .user caller calldata value =>
      ∃ acc : Account .EVM,
        c.entry.accountMap.get? (targetAddr kind) = some acc ∧
          acc.code = Eip8282.Audit.Correspondence.runtimeCode kind ∧
          WellFormed kind acc.storage ∧
          s = toModel kind acc.storage (acc.balance.toNat - value) ∧
          acc.balance.toNat = s.balance + value ∧
          (UserAppends s caller calldata value →
            queueTail acc.storage + 1 < 2 ^ 64)
  | .system _ => Represents kind c.entry s

/-- A user-call entry world is already post-transfer, while the abstract state
remains pre-transfer; it has append room precisely when the model takes the
successful append branch. This projection makes both guard obligations
available without unfolding the authoritative boundary. -/
theorem user_pretransfer_balance_and_append_room {kind : Kind} {c : XiCall kind}
    {s : Model.State} {caller : Model.Address} {calldata : List Model.Byte} {value : Model.Wei}
    (h : PreCallRepresents c s (.user caller calldata value))
    (happend : UserAppends s caller calldata value) :
    ∃ acc : Account .EVM,
      c.entry.accountMap.get? (targetAddr kind) = some acc ∧
        acc.balance.toNat = s.balance + value ∧
          queueTail acc.storage + 1 < 2 ^ 64 := by
  rcases h with ⟨acc, hacc, _, _, _, hbalance, htail⟩
  exact ⟨acc, hacc, hbalance, htail happend⟩

/-- System calls at the universal boundary have no unmodelled value transfer. -/
theorem system_call_value_zero {kind : Kind} {c : XiCall kind} {calldataNonempty : Bool}
    (h : CallEnv c (.system calldataNonempty)) :
    c.env.weiValue = EvmRunner.ZERO_U256 :=
  h.value_zero

/-- The `CALLER` word a user step is dispatched on is the modeled caller, and
it is not `SYSTEM_ADDR`: the opening `CALLER; PUSH20 SYSTEM_ADDR; EQ; JUMPI`
gate sends the call down the user path R2 composes. (`sender` agrees with it by
`UserCallEnv.sender_eq`; the gate itself never reads `sender`.) -/
theorem user_call_source {kind : Kind} {c : XiCall kind} {caller : Model.Address}
    {calldata : List Model.Byte} {value : Model.Wei}
    (h : CallEnv c (.user caller calldata value)) :
    c.env.source = EvmRunner.toAddress caller ∧ c.env.source ≠ EvmRunner.sysAddr :=
  ⟨h.source_eq, h.user⟩

/-- The `CALLER` word a system step is dispatched on is `SYSTEM_ADDR`. -/
theorem system_call_source {kind : Kind} {c : XiCall kind} {calldataNonempty : Bool}
    (h : CallEnv c (.system calldataNonempty)) :
    c.env.source = EvmRunner.sysAddr :=
  h.source_eq

/-- An admissible state-changing call runs in a writable environment. A
read-only user branch does not need this: fee getters and rejected submissions
perform no `SSTORE`, so `STATICCALL` remains in the universal target. -/
theorem admissible_call_writable {kind : Kind} {c : XiCall kind} {s : Model.State}
    {call : Model.Step} (h : AdmissibleCall c s call) (hw : StepWrites s call) :
    c.env.perm = true := by
  cases call <;> exact h.writable hw

/-- The post-call account map of a successful `Ξ` result refines the model
outcome state at the pinned predeploy: the abstraction of the committed
storage, the frame outside the modeled write set, the control words a system
step leaves behind (`ControlWordsAgree`, pinned to `Reachable.applySystem`
rather than merely exempted from the frame), the canonical padded words of
an appended item, and the log series (`LogsAgree`: the entry series plus the
one anonymous `LOG0` an accepted submission publishes, unchanged otherwise).
A revert carries no post account map or substate in
`Ξ`; its required state relation is consequently the EVM rollback relation.
Errors are not a successful correspondence observation. -/
def PostStateAgrees {kind : Kind} (c : XiCall kind) (pre : Model.State)
    (call : Model.Step) (out : Model.Outcome) : Prop :=
  match c.result with
  | .ok (.success (_, σ, _, substate) _) =>
      ∃ acc : Account .EVM,
        σ.get? (targetAddr kind) = some acc ∧
          acc.code = Eip8282.Audit.Correspondence.runtimeCode kind ∧
          WellFormed kind acc.storage ∧
          out.state = toModel kind acc.storage acc.balance.toNat ∧
          LogsAgree c pre call substate ∧
          ∀ preAcc : Account .EVM,
            c.entry.accountMap.get? (targetAddr kind) = some preAcc →
              StorageFrameAgrees (kind := kind) preAcc.storage acc.storage pre call ∧
                ControlWordsAgree kind preAcc.storage acc.storage call ∧
                (StepAppends pre call →
                  ∃ record,
                    out.state.queue = pre.queue ++ [record] ∧
                      CanonicalAppendedItem kind acc.storage
                        (queueTail preAcc.storage) record)
  | .ok (.revert _ _) => out.state = pre
  | .error _ => False

/-- **Read the control-word conjunct back out of the boundary.** On a
successful system call the committed predeploy storage is `applySystem` of the
entry storage at every key: the frame and `SystemControlAgrees` together leave
nothing to the run's discretion, and in particular a full drain must reset both
pointers (`system_full_drain_resets_pointers`). -/
theorem postStateAgrees_system_storage {kind : Kind} {c : XiCall kind} {s : Model.State}
    {b : Bool} {out : Model.Outcome}
    {created : Std.TreeSet AccountAddress compare} {σ : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {o : ByteArray}
    (h : PostStateAgrees c s (.system b) out)
    (hres : c.result = .ok (.success (created, σ, gas, substate) o))
    {preAcc : Account .EVM}
    (hpre : c.entry.accountMap.get? (targetAddr kind) = some preAcc) :
    ∃ acc : Account .EVM,
      σ.get? (targetAddr kind) = some acc ∧
        ∀ key : UInt256,
          acc.storage.getD key (UInt256.ofNat 0) =
            (applySystem kind preAcc.storage b).getD key (UInt256.ofNat 0) := by
  unfold PostStateAgrees at h
  rw [hres] at h
  obtain ⟨acc, hacc, _, _, _, _, hpost⟩ := h
  obtain ⟨hframe, hctl, _⟩ := hpost preAcc hpre
  have hctl' : SystemControlAgrees kind preAcc.storage acc.storage b := hctl
  exact ⟨acc, hacc, system_post_storage_eq_applySystem hframe hctl'⟩

/-- **Read the receipt back out of the boundary.** On a successful accepted
submission the committed log series is the entry series plus one anonymous
entry from the predeploy whose data is `appendLogData`: the 184-byte deposit
calldata, or the caller and the 48-byte exit pubkey. -/
theorem postStateAgrees_append_log {kind : Kind} {c : XiCall kind} {s : Model.State}
    {caller : Model.Address} {calldata : List Model.Byte} {value : Model.Wei}
    {out : Model.Outcome}
    {created : Std.TreeSet AccountAddress compare} {σ : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {o : ByteArray}
    (h : PostStateAgrees c s (.user caller calldata value) out)
    (hres : c.result = .ok (.success (created, σ, gas, substate) o))
    (happend : UserAppends s caller calldata value) :
    ∃ e : LogEntry,
      substate.logSeries = c.substate.logSeries.push e ∧
        e.address = targetAddr kind ∧ e.topics = #[] ∧
          bytes e.data = appendLogData kind caller calldata := by
  unfold PostStateAgrees at h
  rw [hres] at h
  obtain ⟨_, _, _, _, _, hlog, _⟩ := h
  exact hlog.1 happend

/-- **No receipt on the paths that publish nothing.** A successful fee
getter, and a successful system call, leave the log series exactly as `Ξ`
found it. -/
theorem postStateAgrees_system_logs {kind : Kind} {c : XiCall kind} {s : Model.State}
    {b : Bool} {out : Model.Outcome}
    {created : Std.TreeSet AccountAddress compare} {σ : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {o : ByteArray}
    (h : PostStateAgrees c s (.system b) out)
    (hres : c.result = .ok (.success (created, σ, gas, substate) o)) :
    substate.logSeries = c.substate.logSeries := by
  unfold PostStateAgrees at h
  rw [hres] at h
  obtain ⟨_, _, _, _, _, hlog, _⟩ := h
  exact hlog

/-- **Non-vacuity of the receipt obligation.** The receipt the pinned runtimes
publish — one anonymous entry from the predeploy carrying `appendLogData` —
satisfies it. -/
theorem logsAgree_of_receipt {kind : Kind} {c : XiCall kind} {s : Model.State}
    {caller : Model.Address} {calldata : List Model.Byte} {value : Model.Wei}
    {post : Substate} {data : ByteArray}
    (happend : UserAppends s caller calldata value)
    (hpost : post.logSeries = c.substate.logSeries.push ⟨targetAddr kind, #[], data⟩)
    (hdata : bytes data = appendLogData kind caller calldata) :
    LogsAgree c s (.user caller calldata value) post := by
  unfold LogsAgree
  exact ⟨fun _ => ⟨_, hpost, rfl, rfl, hdata⟩, fun hn => absurd happend hn⟩

/-- **Canary for the `LOG0`-size mutant.** `Eip8282.Tests.PSubmit1Mutant`
cuts the write-path `LOG0` data size to zero while leaving storage and output
intact. An accepted deposit whose one receipt carries no data does not satisfy
the log obligation: the entry must carry the 184-byte calldata. -/
theorem logsAgree_rejects_empty_deposit_receipt {c : XiCall .deposit} {s : Model.State}
    {caller : Model.Address} {calldata : List Model.Byte} {value : Model.Wei}
    {post : Substate} {e : LogEntry}
    (happend : UserAppends s caller calldata value)
    (hlen : calldata.length = 184)
    (hpost : post.logSeries = c.substate.logSeries.push e)
    (hempty : e.data = ByteArray.empty) :
    ¬ LogsAgree c s (.user caller calldata value) post := by
  intro h
  obtain ⟨e', he', _, _, hdata⟩ := h.1 happend
  rw [hpost] at he'
  obtain rfl := Array.push_inj_right.mp he'
  rw [hempty, bytes_empty] at hdata
  have hl := congrArg List.length hdata
  simp only [appendLogData, List.length_nil, hlen] at hl
  exact absurd hl (by decide)

/-- **A silent accepted submission is rejected.** If the committed series is
the entry series, the obligation fails: an accepted submission must publish
exactly one entry. -/
theorem logsAgree_rejects_silent_append {kind : Kind} {c : XiCall kind} {s : Model.State}
    {caller : Model.Address} {calldata : List Model.Byte} {value : Model.Wei}
    {post : Substate} (happend : UserAppends s caller calldata value)
    (hsilent : post.logSeries = c.substate.logSeries) :
    ¬ LogsAgree c s (.user caller calldata value) post := by
  intro h
  obtain ⟨e, he, _⟩ := h.1 happend
  have hsize := congrArg Array.size he
  rw [hsilent, Array.size_push] at hsize
  omega

/-! ## The arithmetic guard at the entry image

`Model.nextExcess` is unbounded `Nat`. `Reachable.applySystem` — like the
`SSTORE` it stands for — stores it through `UInt256.ofNat`, so the two agree
only when the result is below `2 ^ 256`. `WellFormed` bounds the pointers, not
`SLOT_EXCESS` or `SLOT_COUNT`, so the state guard on its own admits images
where the modeled excess leaves the word. R5 names the result bound
`DrainHyp.noWrap`; the separate `WordExactCall.noWrap` carries the sharper sum
bound for the R5 support lemmas. The bridge below hands that explicit witness
to every lemma R5 states under `DrainHyp`. The canaries after it are the
reviewers' instances: `wrapExcessImage`, where without a word-semantics
refinement `PostStateAgrees` is unsatisfiable for every `Ξ` result;
`wrapWindowImage`, where the stored result fits the word but the pinned `ADD`
that computes it does not; and `wideExcessImage`, where the folded excess fits
the word but the fee loop's first `MUL` does not. They remain in the campaign
boundary and are the explicit reason `A-ABSTRACT-TX` cannot be retired by the
word-exact support result.
-/

/-- The system-side state guard, read at the account the entry world holds. -/
theorem system_represents_fields {kind : Kind} {c : XiCall kind} {s : Model.State}
    {b : Bool} (hrep : PreCallRepresents c s (.system b)) {acc : Account .EVM}
    (hacc : c.entry.accountMap.get? (targetAddr kind) = some acc) :
    WellFormed kind acc.storage ∧ s = toModel kind acc.storage acc.balance.toNat := by
  obtain ⟨acc', hacc', _, hwf, hs⟩ := hrep
  rw [hacc] at hacc'
  obtain rfl := Option.some.inj hacc'
  exact ⟨hwf, hs⟩

/-- The separate word-exactness witness, read at the entry image, is
`DrainHyp.noWrap`. -/
theorem admissible_system_noWrap {kind : Kind} {c : XiCall kind} {s : Model.State}
    {b : Bool} (hrep : PreCallRepresents c s (.system b))
    (hword : WordExactCall s (.system b)) {acc : Account .EVM}
    (hacc : c.entry.accountMap.get? (targetAddr kind) = some acc) :
    nextExcessOf kind acc.storage b < UInt256.size := by
  obtain ⟨_, hs⟩ := system_represents_fields hrep hacc
  have hnw : nextExcess s b < UInt256.size := nextExcess_lt_size_of_stepNoWrap hword.noWrap
  rw [hs] at hnw
  exact hnw

/-- **The word-exact support witness supplies R5's drain hypothesis.**
`WellFormed` comes from the state guard and `noWrap` from `WordExactCall`, so every lemma R5
states under `DrainHyp` — `applySystem_excess`, `applySystem_count`,
`applySystem_pointers`, `applySystem_wellFormed`, `toModel_applySystem` — and
`system_post_control_words` above apply whenever the explicit word-exact
support witness is supplied. -/
theorem drainHyp_of_admissible {kind : Kind} {c : XiCall kind} {s : Model.State}
    {b : Bool} (hrep : PreCallRepresents c s (.system b))
    (hword : WordExactCall s (.system b)) {acc : Account .EVM}
    (hacc : c.entry.accountMap.get? (targetAddr kind) = some acc) :
    DrainHyp kind acc.storage b :=
  ⟨(system_represents_fields hrep hacc).1, admissible_system_noWrap hrep hword hacc⟩

/-- **Non-vacuity of the word-exact support relation.** At every system call
with the explicit word-exact witness
the transition R5 states abstracts to exactly the model outcome:
`applySystem` of the entry image, at the entry balance, is
`(Model.step s (.system b)).state`. With `applySystem_storageFrameAgrees` and
`applySystem_systemControlAgrees` this shows the intended transition satisfies
every conjunct of `PostStateAgrees`'s success case that does not mention the
`Ξ` result. `noWrap` is what pays for it: at `wrapExcessImage` the same
equation is false (`wrapExcessImage_applySystem_ne_step`). -/
theorem admissible_system_applySystem_toModel {kind : Kind} {c : XiCall kind}
    {s : Model.State} {b : Bool} (hrep : PreCallRepresents c s (.system b))
    (hword : WordExactCall s (.system b)) {acc : Account .EVM}
    (hacc : c.entry.accountMap.get? (targetAddr kind) = some acc) :
    toModel kind (applySystem kind acc.storage b) acc.balance.toNat =
      (Model.step s (.system b)).state := by
  have hd := drainHyp_of_admissible hrep hword hacc
  rw [(system_represents_fields hrep hacc).2]
  exact Eip8282.Audit.Reachable.toModel_applySystem hd _

/-- The reviewer's instance: a `WellFormed` deposit image with an empty queue,
`SLOT_EXCESS = 2 ^ 256 - 2` and `SLOT_COUNT = 10`. -/
def wrapExcessImage : Storage :=
  storageFromList [(0, UInt256.size - 2), (1, 10), (2, 0), (3, 0)]

/-- The state guard alone admits it: `WellFormed` bounds the pointers only. -/
theorem wrapExcessImage_wellFormed : WellFormed .deposit wrapExcessImage := by decide

/-- `noWrap` rejects the empty-calldata call: `2 ^ 256 - 2 + 10` is not below
the word, and the call is neither the nonempty-calldata latch nor an inhibited
clear. -/
theorem wrapExcessImage_not_noWrap :
    ¬ StepNoWrap (toModel .deposit wrapExcessImage 0) (.system false) := by decide

/-- On empty calldata the model's next excess is `2 ^ 256 - 2 + 10 - 8`, i.e.
`2 ^ 256`: one past the word. -/
theorem wrapExcessImage_nextExcess :
    nextExcessOf .deposit wrapExcessImage false = UInt256.size := by decide

/-- `applySystem` stores that value through `UInt256.ofNat`, i.e. as `0`. -/
theorem wrapExcessImage_applySystem_excess :
    slotExcess (applySystem .deposit wrapExcessImage false) = 0 := by decide

/-- The model outcome at the wrap image carries the unwrapped `2 ^ 256`. -/
private theorem wrapExcessImage_step_excess (bal : Model.Wei) :
    (Model.step (toModel .deposit wrapExcessImage bal) (.system false)).state.storedExcess
      = UInt256.size := by
  show Model.nextExcess (toModel .deposit wrapExcessImage bal) false = UInt256.size
  rw [Eip8282.Audit.Reachable.nextExcess_toModel]
  exact wrapExcessImage_nextExcess

/-- So R5's abstraction equation fails at this image: `toModel_applySystem`'s
`DrainHyp.noWrap` is load-bearing, not decorative. -/
theorem wrapExcessImage_applySystem_ne_step (bal : Model.Wei) :
    toModel .deposit (applySystem .deposit wrapExcessImage false) bal ≠
      (Model.step (toModel .deposit wrapExcessImage bal) (.system false)).state := by
  intro h
  have hE := congrArg Model.State.storedExcess h
  rw [toModel_excess, wrapExcessImage_applySystem_excess, wrapExcessImage_step_excess] at hE
  exact absurd hE (by decide)

/-- **The gap, at the reviewer's image.** A system call from
`wrapExcessImage` on empty calldata is admissible but not word-exact, and no `Ξ` result satisfies
`PostStateAgrees` there: on success the committed excess word is below
`2 ^ 256` while the model outcome holds `2 ^ 256`; on revert the model outcome
would have to equal the pre-state, whose excess is `2 ^ 256 - 2`; an error is
never a correspondence. The campaign universal target is therefore explicitly
blocked at this call until its arithmetic semantics are refined. -/
theorem wrapExcessImage_postState_unsatisfiable (c : XiCall .deposit) (bal : Model.Wei) :
    ¬ PostStateAgrees c (toModel .deposit wrapExcessImage bal) (.system false)
        (Model.step (toModel .deposit wrapExcessImage bal) (.system false)) := by
  intro h
  unfold PostStateAgrees at h
  split at h
  · obtain ⟨acc, _, _, _, hstate, _⟩ := h
    have hlt : slotExcess acc.storage < UInt256.size :=
      (loadU256 acc.storage SLOT_EXCESS).val.isLt
    have hE := congrArg Model.State.storedExcess hstate
    rw [wrapExcessImage_step_excess, toModel_excess] at hE
    omega
  · have hE := congrArg Model.State.storedExcess h
    rw [wrapExcessImage_step_excess, toModel_excess] at hE
    exact absurd hE (by decide)
  · exact h

/-- **Canary for the finding.** The campaign boundary retains this step; only
the optional word-exact support witness fails. -/
theorem wrapExcessImage_not_wordExact (bal : Model.Wei) :
    ¬ WordExactCall (toModel .deposit wrapExcessImage bal) (.system false) :=
  fun h => wrapExcessImage_not_noWrap h.noWrap

/-- The blind spot of a bound on the stored result alone: a `WellFormed` deposit
image with an empty queue, `SLOT_EXCESS = 2 ^ 256 - 5` and `SLOT_COUNT = 10`.
The sum is `2 ^ 256 + 5`, while the model's next excess `2 ^ 256 - 3` fits the
word. -/
def wrapWindowImage : Storage :=
  storageFromList [(0, UInt256.size - 5), (1, 10), (2, 0), (3, 0)]

/-- The state guard admits it and `Model.nextExcess` fits, so a guard reading
only the stored result would admit the empty-calldata system call. -/
theorem wrapWindowImage_result_fits :
    WellFormed .deposit wrapWindowImage ∧
      nextExcess (toModel .deposit wrapWindowImage 0) false < UInt256.size :=
  ⟨by decide, by decide⟩

/-- The pinned `update_excess` adds `added_count + excess` in the word before
comparing it with the target, and `2 ^ 256 + 5` is not below the word:
`StepNoWrap` bounds the sum and rejects the call. -/
theorem wrapWindowImage_not_noWrap :
    ¬ StepNoWrap (toModel .deposit wrapWindowImage 0) (.system false) := by decide

/-- **Canary for the finding.** The campaign boundary retains this system step;
only the optional word-exact support witness fails. -/
theorem wrapWindowImage_not_wordExact (bal : Model.Wei) :
    ¬ WordExactCall (toModel .deposit wrapWindowImage bal) (.system false) :=
  fun h => wrapWindowImage_not_noWrap h.noWrap

/-- The reviewer's instance on the user side: a `WellFormed`, enabled deposit
image with an empty queue, `SLOT_EXCESS = 2 ^ 252` and `SLOT_COUNT = 0`, so
`effectiveExcess = 2 ^ 252`. -/
def wideExcessImage : Storage :=
  storageFromList [(0, 2 ^ 252), (1, 0), (2, 0), (3, 0)]

/-- The state guard admits it and the folded excess fits the word, so a guard
reading only `effectiveExcess` would admit the zero-value fee getter. -/
theorem wideExcessImage_excess_fits :
    WellFormed .deposit wideExcessImage ∧
      effectiveExcess (toModel .deposit wideExcessImage 0) < UInt256.size :=
  ⟨by decide, by decide⟩

/-- The loop's first `MUL` is `17 * 2 ^ 252 = 2 ^ 256 + 2 ^ 252`, which is not
below the word: `FeeQuoteNoWrap` fails at the first iteration, and the image is
not inhibited, so `StepNoWrap` rejects the fee getter. -/
theorem wideExcessImage_not_noWrap :
    ¬ StepNoWrap (toModel .deposit wideExcessImage 0) (.user 0 [] 0) := by decide

 /-- **Canary for the finding.** The campaign boundary retains every user step
at this image; only the optional word-exact support witness fails. -/
theorem wideExcessImage_not_wordExact (bal : Model.Wei)
    (caller : Model.Address) (calldata : List Model.Byte) (value : Model.Wei) :
    ¬ WordExactCall (toModel .deposit wideExcessImage bal) (.user caller calldata value) :=
  fun h => wideExcessImage_not_noWrap h.noWrap

/-- **Non-vacuity of the user-side guard.** The specified deployment state and
an ordinary enabled image (`stalePointerImage`: excess `100`, count `5`, whose
fee loop runs seventeen iterations) both satisfy `FeeQuoteNoWrap`, so the guard
admits the fee getters and submissions the campaign is about. -/
theorem feeQuoteNoWrap_examples :
    FeeQuoteNoWrap Model.initialDeposit ∧
      FeeQuoteNoWrap (toModel .deposit stalePointerImage 0) :=
  ⟨by decide, by decide⟩

/-- **The fuel conjunct is load-bearing.** At a folded excess of `1607` the
loop reaches `accum = 0` within the model's `256` iterations and no word wraps;
at `1608` no word wraps either, but the fuel is spent with `accum ≠ 0`, where
`go` stops and the pinned loop does not. -/
theorem fakeExpoFitsWord_fuel_boundary :
    fakeExpoFitsWord 1607 17 256 1 0 17 = true ∧
      fakeExpoFitsWord 1608 17 256 1 0 17 = false :=
  ⟨by decide +kernel, by decide +kernel⟩

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
      PostStateAgrees c s call (Model.step s call)

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
          PostStateAgrees c s call (Model.step s call) := by
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
`hadm` supplies call binding, gas and fuel; `hend` is
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
    (hpost : PostStateAgrees c s call (Model.step s call)) :
    observe c.result = some (observeModel (Model.step s call)) ∧
      PostStateAgrees c s call (Model.step s call) :=
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
          PostStateAgrees c s call (Model.step s call)

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
