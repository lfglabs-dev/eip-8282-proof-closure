import Eip8282.Audit.Execution.Words
import Eip8282.Audit.EntryReach.Path
import Eip8282.Audit.WellFormed

/-!
# The words the runtimes read, in terms of the call

`Machine.lean` reads the branch words off the entry state with `callerW`, `valueW`,
`cdsizeW`, `cdW` and `slotW`. This module says what those words *are* in terms of
the message call `Ξ` was handed — its `ExecutionEnv` and the predeploy account of
its entry world — and collects the 256-bit arithmetic facts the OPERANDS slice
needs: `toNat` of a sum, product, quotient or difference that does not wrap, the
`uint64` mask as a remainder, and the big-endian value of a `CALLDATALOAD`.

Nothing here runs `Ξ` or mentions the model: these are definitional readings of
EVMYulLean's `State.sload`, `State.calldataload` and `ExecutionEnv`.
-/

namespace Eip8282.Audit.EntryReach

open EvmYul EvmYul.EVM
open Eip8282.Audit.SymExec
open Eip8282.Audit.XiTransport (XiCall bytes)
open Eip8282.Audit.Model (Kind beBytes)
open Eip8282.Audit.WellFormed (loadU256 loadNat)

/-! ## Word arithmetic that does not wrap -/







theorem toNat_div (a b : UInt256) : (a / b).toNat = a.toNat / b.toNat := rfl















/-! ## The environment words -/

section Env

variable {kind : Kind} (c : XiCall kind)


theorem valueW_entry : valueW (entrySt c) = c.env.weiValue := rfl
theorem cdsizeW_entry : cdsizeW (entrySt c) = UInt256.ofNat c.env.calldata.size := rfl




/-- The value word is the wei the call carries. -/
theorem toNat_valueW : (valueW (entrySt c)).toNat = c.env.weiValue.toNat := rfl







/-- The abstract calldata has the length of the byte string. -/
theorem length_bytes_calldata : (bytes c.env.calldata).length = c.env.calldata.size :=
  Eip8282.Audit.XiTransport.bytes_length _

end Env

/-! ## Storage words -/

section Storage

variable {kind : Kind} (c : XiCall kind)

/-- `SLOAD k` at the entry reads slot `k` of the account the code runs as. -/
theorem slotW_entry {acc : Account .EVM}
    (hacc : c.entry.accountMap.get? c.env.codeOwner = some acc) (k : UInt256) :
    slotW (entrySt c) k = acc.storage.getD k ⟨0⟩ := by
  show (Option.option ⟨0⟩ (fun a => Account.lookupStorage a k)
    ((entrySt c).accountMap.get? (entrySt c).executionEnv.codeOwner)) = _
  have h : (entrySt c).accountMap.get? (entrySt c).executionEnv.codeOwner = some acc := hacc
  rw [h]
  rfl

/-- The same, read through `WellFormed.loadU256` at a small slot number. -/
theorem slotW_entry_loadU256 {acc : Account .EVM}
    (hacc : c.entry.accountMap.get? c.env.codeOwner = some acc) (n : Nat) :
    slotW (entrySt c) (UInt256.ofNat n) = loadU256 acc.storage n :=
  slotW_entry c hacc _

theorem toNat_slotW_entry {acc : Account .EVM}
    (hacc : c.entry.accountMap.get? c.env.codeOwner = some acc) (n : Nat) :
    (slotW (entrySt c) (UInt256.ofNat n)).toNat = loadNat acc.storage n := by
  rw [slotW_entry_loadU256 c hacc]; rfl

end Storage

/-! ## The value of a `CALLDATALOAD`

`State.calldataload off` is the 32 bytes of calldata at `off`, zero-padded, read
big-endian. `byteAt` is one such byte as a natural; `cdBytes b off n` the list of
`n` of them. -/



























/-- Every byte the observation lists is a byte. -/
theorem bytesOk_bytes (b : ByteArray) : Eip8282.Audit.Model.bytesOk (bytes b) = true := by
  unfold Eip8282.Audit.Model.bytesOk
  rw [List.all_eq_true]
  intro x hx
  simp only [Eip8282.Audit.XiTransport.bytes, List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  exact decide_eq_true (b.get! i).toNat_lt

end Eip8282.Audit.EntryReach
