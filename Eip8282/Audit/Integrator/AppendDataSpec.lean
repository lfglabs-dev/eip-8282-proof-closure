import Eip8282.Audit.Integrator.AppendStorage
import Eip8282.Audit.Integrator.ExitRecord

/-!
# Code-independent append data specifications

All specifications take only kind, storage reads, calldata, source/owner and
observed world/log data. No specification requires a XiCall or a bytecode pin.
The correspondence theorems instantiate those data from existing pinned calls;
they do not execute a different call or assume agreement with a desired state.

The overlay uses EVM word arithmetic even outside the fit domain. StoragePost
separately states natural count/tail successors and the independent frame.
Fits is an input bound, not an assertion that an append happened or was paid.
The record/log specification makes no signature-validation claim.
-/
namespace Eip8282.Audit.Integrator.AppendDataSpec

open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.EntryReach (slotW entrySt)
open SystemSpec (worldSlot)

set_option autoImplicit false

abbrev Read := UInt256 → UInt256

/-- Physical storage words per record, independent of executable code. -/
def stride : Kind → Nat | .deposit => 6 | .exit => 3

def count (read : Read) : UInt256 := read (UInt256.ofNat 1)
def tail (read : Read) : UInt256 := read (UInt256.ofNat 3)

def base (kind : Kind) (read : Read) : UInt256 :=
  UInt256.ofNat 4 + UInt256.ofNat (stride kind) * tail read

def recordKey (kind : Kind) (read : Read) : Nat → UInt256
  | 0 => base kind read
  | i + 1 => UInt256.ofNat 1 + recordKey kind read i

/-- Big-endian calldata words, with the final word zero padded. -/
def calldataWord (calldata : ByteArray) (offset : Nat) : UInt256 :=
  uInt256OfByteArray (calldata.readBytes offset 32)

def recordWord (kind : Kind) (calldata : ByteArray) (source : AccountAddress)
    (i : Nat) : UInt256 :=
  match kind with
  | .deposit => calldataWord calldata (32 * i)
  | .exit => if i = 0 then UInt256.ofNat source.val else calldataWord calldata (32 * (i - 1))

def put (read : Read) (key value : UInt256) : Read :=
  fun q => if q = key then value else read q

/-- Keys are based on the original read-map, never an intermediate overlay. -/
def records (kind : Kind) (read : Read) (calldata : ByteArray)
    (source : AccountAddress) : Nat → Read → Read
  | 0, acc => acc
  | i + 1, acc => put (records kind read calldata source i acc)
      (recordKey kind read i) (recordWord kind calldata source i)

def expected (kind : Kind) (read : Read) (calldata : ByteArray)
    (source : AccountAddress) : Read :=
  put (records kind read calldata source (stride kind)
    (put read (UInt256.ofNat 1) (UInt256.ofNat 1 + count read)))
    (UInt256.ofNat 3) (UInt256.ofNat 1 + tail read)

/-- Local nonalias/word-fit conditions, independent of execution and code. -/
def Fits (kind : Kind) (read : Read) : Prop :=
  4 + stride kind * (tail read).toNat + stride kind ≤ UInt256.size ∧
    (count read).toNat + 1 < UInt256.size ∧ (tail read).toNat + 1 < UInt256.size

/-- Exact read-map of one physical append. No claim of success is implicit. -/
def ExpectedPost (kind : Kind) (read : Read) (calldata : ByteArray)
    (source : AccountAddress) (post : Read) : Prop :=
  ∀ q, post q = expected kind read calldata source q

/-- Natural controls, authentic words and preservation outside the write set. -/
def StoragePost (kind : Kind) (read : Read) (calldata : ByteArray)
    (source : AccountAddress) (post : Read) : Prop :=
  post (UInt256.ofNat 0) = read (UInt256.ofNat 0) ∧
  (post (UInt256.ofNat 1)).toNat = (count read).toNat + 1 ∧
  post (UInt256.ofNat 2) = read (UInt256.ofNat 2) ∧
  (post (UInt256.ofNat 3)).toNat = (tail read).toNat + 1 ∧
  (∀ i, i < stride kind → post (recordKey kind read i) = recordWord kind calldata source i) ∧
  (∀ q, q ≠ UInt256.ofNat 1 → q ≠ UInt256.ofNat 3 →
    (∀ i, i < stride kind → q ≠ recordKey kind read i) → post q = read q)

/-- The bytes required of the anonymous receipt, without inspecting memory. -/
def record (kind : Kind) (calldata : ByteArray) (source : AccountAddress) : ByteArray :=
  match kind with
  | .deposit => calldata
  | .exit => ExitRecord.record source calldata

def AppendedLog (before : Substate) (owner : AccountAddress) (data : ByteArray)
    (after : Substate) : Prop :=
  after.logSeries = before.logSeries.push ⟨owner, #[], data⟩

def AuthenticLog (kind : Kind) (calldata : ByteArray) (source owner : AccountAddress)
    (before after : Substate) : Prop :=
  AppendedLog before owner (record kind calldata source) after

/-- The caller supplying `before` must use the transferred world for Θ frames. -/
def OtherAccountsUnchanged (before after : AccountMap .EVM) (owner : AccountAddress) : Prop :=
  ∀ addr, addr ≠ owner → after.get? addr = before.get? addr

/-! The only appearances of XiCall below are instantiation/transport theorems. -/

variable {kind : Kind}

theorem stride_eq (kind : Kind) : stride kind = AppendStorage.stride kind := by
  cases kind <;> rfl

theorem recordKey_eq (c : XiCall kind) (i : Nat) :
    recordKey kind (slotW (entrySt c)) i = AppendStorage.recordKey c i := by
  induction i with
  | zero => simp only [recordKey, base, stride_eq]; rfl
  | succ i ih => simp only [recordKey, AppendStorage.recordKey, ih]

theorem recordWord_eq (c : XiCall kind) (i : Nat) :
    recordWord kind c.env.calldata c.env.source i = AppendStorage.recordWord c i := by
  cases kind <;> rfl

theorem records_eq (c : XiCall kind) (n : Nat) (acc : Read) :
    records kind (slotW (entrySt c)) c.env.calldata c.env.source n acc =
      AppendStorage.records c n acc := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [records, AppendStorage.records, ih, recordKey_eq, recordWord_eq]
    rfl

theorem expected_eq (c : XiCall kind) :
    expected kind (slotW (entrySt c)) c.env.calldata c.env.source = AppendStorage.expected c := by
  unfold expected AppendStorage.expected
  rw [stride_eq, records_eq]
  rfl

theorem fits_iff (c : XiCall kind) :
    Fits kind (slotW (entrySt c)) ↔ AppendStorage.AppendFits c := by
  simp only [Fits, AppendStorage.AppendFits, stride_eq]
  rfl

theorem expectedPost_iff (c : XiCall kind) (world : AccountMap .EVM) :
    ExpectedPost kind (slotW (entrySt c)) c.env.calldata c.env.source
      (worldSlot world c.env.codeOwner) ↔
      (∀ q, worldSlot world c.env.codeOwner q = AppendStorage.expected c q) := by
  unfold ExpectedPost
  rw [expected_eq]

theorem storagePost_iff (c : XiCall kind) (world : AccountMap .EVM) :
    StoragePost kind (slotW (entrySt c)) c.env.calldata c.env.source
      (worldSlot world c.env.codeOwner) ↔ AppendStorage.StoragePost c world := by
  simp only [StoragePost, AppendStorage.StoragePost, stride_eq, recordKey_eq, recordWord_eq]
  rfl

theorem appendedLog_iff (c : XiCall kind) (data : ByteArray) (after : Substate) :
    AppendedLog c.substate c.env.codeOwner data after ↔ AppendSpec.AppendedLog c data after :=
  Iff.rfl

theorem authenticLog_iff (c : XiCall kind) (after : Substate) :
    AuthenticLog kind c.env.calldata c.env.source c.env.codeOwner c.substate after ↔
      AppendSpec.AppendedLog c (record kind c.env.calldata c.env.source) after := Iff.rfl

theorem otherAccountsUnchanged_iff (c : XiCall kind) (world : AccountMap .EVM) :
    OtherAccountsUnchanged c.σ world c.env.codeOwner ↔ AppendSpec.OtherAccountsUnchanged c world :=
  Iff.rfl

#print axioms expected_eq
#print axioms fits_iff
#print axioms storagePost_iff
#print axioms authenticLog_iff

end Eip8282.Audit.Integrator.AppendDataSpec
