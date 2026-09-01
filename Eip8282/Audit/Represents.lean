import Eip8282.Audit.Correspondence

/-!
# R1 — `Represents`: packed EVM state ↔ abstract `Model.State`

Node R1 of the correspondence DAG. This module supplies the **state
relation** and nothing else.

`Represents kind s m` says: the EVM world `s` carries, at the pinned
predeploy address for `kind`, an account that

* runs the pinned runtime bytes (`Correspondence.runtimeCode kind`),
* whose packed storage is `WellFormed` (control slots 0–3 plus a dense
  `[QUEUE_HEAD, QUEUE_TAIL)` item window), and
* abstracts under `WellFormed.toModel` to exactly `m`, balance included.

`toModel` is already the abstraction function the three registered parents
use on a bare `Storage`. R1 lifts it to a whole `EvmYul.EVM.State`, so a
statement can now say *which* world state an abstract `Model.State` stands
for instead of quantifying over a free `Storage` variable.

## What R1 is not

R1 relates **states**, not **steps**. Nothing here says that if
`Represents kind s m` and `Ξ` carries `s` to `s'`, then
`Represents kind s' (Model.step m k)`. That ∀-transport is node R4.

Consequently `A-ABSTRACT-TX` is **not** closed and not reduced by this
module: the relation now exists and is proved functional and inhabited, but
the `Ξ` ↔ `Model.userCall`/`systemCall` step correspondence it would have to
be preserved by is still absent. See `audit/assumptions.yaml`.

No new parent IDs are introduced. The three registered parents
(`P-SUBMIT-1`, `P-DRAIN-1`, `P-CONTROL-1`) quantify over
`{σ : Storage} (_ : CallHyp kind σ)`; R1's contribution to them is
`Represents.callHyp`, which shows a `Represents` witness *supplies* that
hypothesis at the predeploy's own storage. Supplying a hypothesis is not
transporting a conclusion.
-/

namespace Eip8282.Audit.Represents

open EvmYul (UInt256 Storage AccountAddress)
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Step (isUserCaller campaignGasBound)
open Eip8282.Audit.Correspondence (targetAddr runtimeCode CallHyp campaignFuelBound)
open Eip8282.Audit.Model (Kind Wei inhibitor inhibited)

/-! ## The relation -/

/-- The pinned predeploy account for `kind`, as it appears in an EVM world. -/
def predeploy (kind : Kind) (w : EvmYul.AccountMap .EVM) :
    Option (EvmYul.Account .EVM) :=
  w.get? (targetAddr kind)

/-- **Node R1, world form.** `m` is the abstraction of the predeploy account
held by the account map `w`. -/
def RepresentsWorld (kind : Kind) (w : EvmYul.AccountMap .EVM)
    (m : Eip8282.Audit.Model.State) : Prop :=
  ∃ acc : EvmYul.Account .EVM,
    predeploy kind w = some acc ∧
      acc.code = runtimeCode kind ∧
      WellFormed kind acc.storage ∧
      m = toModel kind acc.storage acc.balance.toNat

set_option linter.dupNamespace false in
/-- **Node R1.** `Represents kind : EvmYul.EVM.State → Model.State → Prop`.

Only the predeploy account is observed: its code, its packed storage and its
balance. Every other account in the world — including the caller — is
irrelevant to the abstraction, which is what makes this relation stable
under the synthetic-world construction disclosed as `A-EVM-WORLD`. -/
def Represents (kind : Kind) (s : EvmYul.EVM.State)
    (m : Eip8282.Audit.Model.State) : Prop :=
  RepresentsWorld kind s.accountMap m

theorem represents_iff (kind : Kind) (s : EvmYul.EVM.State)
    (m : Eip8282.Audit.Model.State) :
    Represents kind s m ↔ RepresentsWorld kind s.accountMap m := Iff.rfl

/-! ## Introduction

The general introduction rule. It is deliberately weak: it holds of *any*
`EvmYul.EVM.State`, so it commits R1 to no particular world shape. The
non-vacuity content is `represents_packed_deposit` / `represents_packed_exit`
below, which exhibit worlds satisfying its hypotheses. -/

theorem represents_of_lookup {kind : Kind} {s : EvmYul.EVM.State}
    {acc : EvmYul.Account .EVM}
    (hacc : predeploy kind s.accountMap = some acc)
    (hcode : acc.code = runtimeCode kind)
    (wf : WellFormed kind acc.storage) :
    Represents kind s (toModel kind acc.storage acc.balance.toNat) :=
  ⟨acc, hacc, hcode, wf, rfl⟩

/-! ## Elimination: the fields the three parents actually read -/

namespace Represents

set_option linter.dupNamespace false

variable {kind : Kind} {s : EvmYul.EVM.State} {m : Eip8282.Audit.Model.State}
variable {acc : EvmYul.Account .EVM}

theorem exists_account (h : Represents kind s m) :
    ∃ a, predeploy kind s.accountMap = some a := by
  obtain ⟨a, ha, _⟩ := h
  exact ⟨a, ha⟩

/-- The abstraction is pinned to whichever account the world actually holds. -/
theorem model_eq (h : Represents kind s m)
    (hacc : predeploy kind s.accountMap = some acc) :
    m = toModel kind acc.storage acc.balance.toNat := by
  obtain ⟨a, ha, _, _, hm⟩ := h
  rw [hacc] at ha
  rw [hm, Option.some.inj ha]

theorem code_eq (h : Represents kind s m)
    (hacc : predeploy kind s.accountMap = some acc) :
    acc.code = runtimeCode kind := by
  obtain ⟨a, ha, hc, _, _⟩ := h
  rw [hacc] at ha
  rw [Option.some.inj ha]
  exact hc

theorem wellFormed (h : Represents kind s m)
    (hacc : predeploy kind s.accountMap = some acc) :
    WellFormed kind acc.storage := by
  obtain ⟨a, ha, _, hw, _⟩ := h
  rw [hacc] at ha
  rw [Option.some.inj ha]
  exact hw

/-- Every abstract field, read back from the packed image. These are exactly
the components `P-SUBMIT-1` (excess/count/queue), `P-DRAIN-1` (queue) and
`P-CONTROL-1` (excess/count) consume. -/
theorem fields (h : Represents kind s m)
    (hacc : predeploy kind s.accountMap = some acc) :
    m.kind = kind ∧
      m.storedExcess = slotExcess acc.storage ∧
      m.count = slotCount acc.storage ∧
      m.queue = queueOf kind acc.storage ∧
      m.balance = acc.balance.toNat := by
  rw [model_eq h hacc]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem kind_eq (h : Represents kind s m)
    (hacc : predeploy kind s.accountMap = some acc) : m.kind = kind :=
  (fields h hacc).1

theorem storedExcess_eq (h : Represents kind s m)
    (hacc : predeploy kind s.accountMap = some acc) :
    m.storedExcess = slotExcess acc.storage := (fields h hacc).2.1

theorem count_eq (h : Represents kind s m)
    (hacc : predeploy kind s.accountMap = some acc) :
    m.count = slotCount acc.storage := (fields h hacc).2.2.1

theorem queue_eq (h : Represents kind s m)
    (hacc : predeploy kind s.accountMap = some acc) :
    m.queue = queueOf kind acc.storage := (fields h hacc).2.2.2.1

theorem balance_eq (h : Represents kind s m)
    (hacc : predeploy kind s.accountMap = some acc) :
    m.balance = acc.balance.toNat := (fields h hacc).2.2.2.2

/-! ### Packed-queue invariants transported to the abstract side -/

theorem head_le_tail (h : Represents kind s m)
    (hacc : predeploy kind s.accountMap = some acc) :
    queueHead acc.storage ≤ queueTail acc.storage :=
  Eip8282.Audit.WellFormed.head_le_tail (wellFormed h hacc)

/-- The abstract queue length is the packed window width. `P-DRAIN-1` reasons
about `queue.take/drop (capOf kind)`; this is what ties those to the pointers. -/
theorem queue_length (h : Represents kind s m)
    (hacc : predeploy kind s.accountMap = some acc) :
    m.queue.length = queueTail acc.storage - queueHead acc.storage := by
  rw [queue_eq h hacc]
  exact queueOf_length (wellFormed h hacc)

theorem queue_nil_of_pointers_eq (h : Represents kind s m)
    (hacc : predeploy kind s.accountMap = some acc)
    (hp : queueHead acc.storage = queueTail acc.storage) : m.queue = [] := by
  rw [queue_eq h hacc]
  exact Eip8282.Audit.WellFormed.queueOf_empty_of_eq kind acc.storage hp

/-- The inhibitor gate `P-CONTROL-1` discriminates on, read off slot 0. -/
theorem inhibited_iff (h : Represents kind s m)
    (hacc : predeploy kind s.accountMap = some acc) :
    inhibited m = true ↔ slotExcess acc.storage = inhibitor := by
  rw [model_eq h hacc]
  exact Eip8282.Audit.WellFormed.inhibited_iff kind acc.storage acc.balance.toNat

/-! ### Functionality -/

/-- `Represents kind s` determines the abstract state uniquely: a world state
abstracts to at most one `Model.State`. Without this the relation would be
useless as a specification, since a second unrelated `m` could satisfy it. -/
theorem unique {m₁ m₂ : Eip8282.Audit.Model.State}
    (h₁ : Represents kind s m₁) (h₂ : Represents kind s m₂) : m₁ = m₂ := by
  obtain ⟨a₁, e₁, _, _, r₁⟩ := h₁
  obtain ⟨a₂, e₂, _, _, r₂⟩ := h₂
  rw [e₁] at e₂
  rw [r₁, r₂, Option.some.inj e₂]

/-! ### Bridge to the registered parents

`P-SUBMIT-1`, `P-DRAIN-1` and `P-CONTROL-1` each quantify over
`{σ : Storage} (_ : CallHyp kind σ)`. `callHyp` shows that a `Represents`
witness supplies that hypothesis at the predeploy's own storage, given the
campaign's gas/fuel bounds and a caller. This is hypothesis-supply only: it
transports no conclusion from `Ξ` to `Model`, and it strengthens the three
parents only in the sense that their `σ` can now be named as a real world's
predeploy storage rather than a free variable. -/

def callHyp (h : Represents kind s m)
    (hacc : predeploy kind s.accountMap = some acc)
    (gas fuel : Nat) (hg : gas ≥ campaignGasBound) (hf : fuel ≥ campaignFuelBound)
    (caller : UInt256) : CallHyp kind acc.storage where
  wellFormed := wellFormed h hacc
  gas := gas
  gas_ge := hg
  fuel := fuel
  fuel_ge := hf
  caller := caller
  isUser := decide (isUserCaller caller)
  caller_class := by simp

@[simp] theorem callHyp_gas (h : Represents kind s m)
    (hacc : predeploy kind s.accountMap = some acc)
    (gas fuel : Nat) (hg : gas ≥ campaignGasBound) (hf : fuel ≥ campaignFuelBound)
    (caller : UInt256) :
    (callHyp h hacc gas fuel hg hf caller).gas = gas := rfl

@[simp] theorem callHyp_caller (h : Represents kind s m)
    (hacc : predeploy kind s.accountMap = some acc)
    (gas fuel : Nat) (hg : gas ≥ campaignGasBound) (hf : fuel ≥ campaignFuelBound)
    (caller : UInt256) :
    (callHyp h hacc gas fuel hg hf caller).caller = caller := rfl

end Represents

/-! ## Non-vacuity: the campaign world satisfies `Represents`

`packedWorld` is `EvmRunner.worldWith` with the predeploy allowed a balance:
the target account holding the packed image, plus the caller. Insertion order
matches `worldWith` (target first, caller second). -/

/-- A concrete non-system caller, distinct from both predeploy addresses. -/
def campaignCaller : AccountAddress := EvmRunner.toAddress 0xcafe

def packedWorld (kind : Kind) (σ : Storage) (bal : UInt256)
    (caller : AccountAddress) (callerBal : UInt256) : EvmYul.AccountMap .EVM :=
  ((default : EvmYul.AccountMap .EVM).insert (targetAddr kind)
      (EvmRunner.mkAccount (runtimeCode kind) bal σ)).insert caller
    (EvmRunner.mkAccount ByteArray.empty callerBal)

def packedState (kind : Kind) (σ : Storage) (bal : UInt256)
    (caller : AccountAddress) (callerBal : UInt256) : EvmYul.EVM.State :=
  { (default : EvmYul.EVM.State) with
      accountMap := packedWorld kind σ bal caller callerBal }

@[simp] theorem accountMap_packedState (kind : Kind) (σ : Storage) (bal : UInt256)
    (caller : AccountAddress) (callerBal : UInt256) :
    (packedState kind σ bal caller callerBal).accountMap
      = packedWorld kind σ bal caller callerBal := rfl

theorem predeploy_packedWorld_deposit (σ : Storage) (bal callerBal : UInt256) :
    predeploy .deposit (packedWorld .deposit σ bal campaignCaller callerBal)
      = some (EvmRunner.mkAccount (runtimeCode .deposit) bal σ) := rfl

theorem predeploy_packedWorld_exit (σ : Storage) (bal callerBal : UInt256) :
    predeploy .exit (packedWorld .exit σ bal campaignCaller callerBal)
      = some (EvmRunner.mkAccount (runtimeCode .exit) bal σ) := rfl

/-- **Deliverable R1.** Every `WellFormed` packed deposit image, at any
predeploy balance, `Represents` the `Model.State` it abstracts to. This is a
`∀` over well-formed storage images, not a single ground world. -/
theorem represents_packed_deposit (σ : Storage) (bal callerBal : UInt256)
    (wf : WellFormed .deposit σ) :
    Represents .deposit (packedState .deposit σ bal campaignCaller callerBal)
      (toModel .deposit σ bal.toNat) :=
  ⟨_, predeploy_packedWorld_deposit σ bal callerBal, rfl, wf, rfl⟩

/-- Same, for the builder-exits predeploy. -/
theorem represents_packed_exit (σ : Storage) (bal callerBal : UInt256)
    (wf : WellFormed .exit σ) :
    Represents .exit (packedState .exit σ bal campaignCaller callerBal)
      (toModel .exit σ bal.toNat) :=
  ⟨_, predeploy_packedWorld_exit σ bal callerBal, rfl, wf, rfl⟩

/-! ### The campaign's own storage images

Each of these is an image the registered parents already run against, so
`Represents` is inhabited exactly where the guarantees live. -/

theorem represents_liveStorage (bal callerBal : UInt256) :
    Represents .deposit (packedState .deposit liveStorage bal campaignCaller callerBal)
      (toModel .deposit liveStorage bal.toNat) :=
  represents_packed_deposit liveStorage bal callerBal (by decide)

theorem represents_altStorage (bal callerBal : UInt256) :
    Represents .deposit (packedState .deposit altStorage bal campaignCaller callerBal)
      (toModel .deposit altStorage bal.toNat) :=
  represents_packed_deposit altStorage bal callerBal (by decide)

theorem represents_inhibitedStorage (bal callerBal : UInt256) :
    Represents .deposit
      (packedState .deposit inhibitedStorage bal campaignCaller callerBal)
      (toModel .deposit inhibitedStorage bal.toNat) :=
  represents_packed_deposit inhibitedStorage bal callerBal (by decide)

/-- The Wave-5 / P-DRAIN-1 over-cap image (`head = 0`, `tail = 65`). -/
theorem represents_depositQueue65 (bal callerBal : UInt256) :
    Represents .deposit
      (packedState .deposit depositQueue65Pointers bal campaignCaller callerBal)
      (toModel .deposit depositQueue65Pointers bal.toNat) :=
  represents_packed_deposit depositQueue65Pointers bal callerBal (by decide)

theorem represents_default_storage (kind : Kind) (bal callerBal : UInt256) :
    Represents kind (packedState kind default bal campaignCaller callerBal)
      (toModel kind default bal.toNat) := by
  cases kind
  · exact represents_packed_deposit _ bal callerBal (default_wellFormed _)
  · exact represents_packed_exit _ bal callerBal (default_wellFormed _)

/-- Honesty marker. The builder-exits predeploy is *specified* to start
inhibited (`Model.initialExit.storedExcess = inhibitor`), but an all-zero
storage image abstracts to `storedExcess = 0`. So `represents_default_storage`
at `.exit` is **not** a witness that the deployed world starts in
`Model.initialExit`; that step needs the constructor image, which is
`P-CONTROL-1`'s ctor fragment, not R1. -/
theorem default_storage_not_initialExit :
    (toModel .exit default 0).storedExcess
      ≠ Eip8282.Audit.Model.initialExit.storedExcess := by
  decide

end Eip8282.Audit.Represents
