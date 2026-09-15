import Eip8282.Audit.EntryReach.Path
import Eip8282.Audit.Integrator.ProtectedLogFrame
import Eip8282.Audit.Integrator.Topics.Protocol
import Eip8282.Audit.Integrator.ReachableCalls
import Eip8282.Audit.Integrator.ReferenceAppendOccurrences
import Eip8282.Audit.Integrator.Topics.ReferenceRuntime3
import Eip8282.Audit.Integrator.ReferenceStackOps
import Eip8282.Audit.Integrator.ReferenceStorageView
import Eip8282.Audit.Integrator.ResourceBounds

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceAcceptedStack -/

/-! Construct actual operand witnesses from accepted Z. These producers do not
assume a desired stack decomposition or any reference post-state. DUP/SWAP
witnesses use the source end-oriented shapes consumed by ReferenceStackOps.
Decode, running-PC, ownership and whole-step transport are separate layers. -/
namespace Eip8282.Audit.Integrator.ReferenceAcceptedStack
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open ReferenceStackOps ReferenceWordOps
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-- The actual underflow and overflow guards, for any admitted opcode. -/
theorem bounds {vj : Array UInt256} {op : Operation .EVM}
    {pre mid : EVM.State} {cost : Nat} (hz : Z vj op pre = .ok (mid,cost)) :
    (δ op).getD 0 ≤ pre.stack.length ∧
    pre.stack.length - (δ op).getD 0 + (α op).getD 0 ≤ 1024 := by
  refine ⟨Z_ok_stack_length hz,?_⟩
  simp only [Z,Bind.bind,Except.bind,pure,Except.pure] at hz
  iterate 7 replace hz := elim_guard hz
  exact Nat.le_of_not_lt (elim_guard_not hz)

theorem pop1 {vj : Array UInt256} {op : Operation .EVM}
    {pre mid : EVM.State} {cost : Nat} (hz : Z vj op pre = .ok (mid,cost))
    (arity : 1 ≤ (δ op).getD 0) :
    ∃ rest x, pre.stack = x::rest ∧ pre.stack.pop = some (rest,x) := by
  have hl := (bounds hz).1
  cases hs : pre.stack with
  | nil => simp only [hs,List.length_nil] at hl; omega
  | cons x rest => exact ⟨rest,x,rfl,rfl⟩

theorem pop2 {vj : Array UInt256} {op : Operation .EVM}
    {pre mid : EVM.State} {cost : Nat} (hz : Z vj op pre = .ok (mid,cost))
    (arity : 2 ≤ (δ op).getD 0) :
    ∃ rest x y, pre.stack = x::y::rest ∧ pre.stack.pop2 = some (rest,x,y) := by
  have hl := (bounds hz).1
  cases hs : pre.stack with
  | nil => simp only [hs,List.length_nil] at hl; omega
  | cons x tail =>
    cases tail with
    | nil => simp only [hs,List.length_cons,List.length_nil] at hl; omega
    | cons y rest => exact ⟨rest,x,y,rfl,rfl⟩

theorem pop3 {vj : Array UInt256} {op : Operation .EVM}
    {pre mid : EVM.State} {cost : Nat} (hz : Z vj op pre = .ok (mid,cost))
    (arity : 3 ≤ (δ op).getD 0) :
    ∃ rest x y z, pre.stack = x::y::z::rest ∧ pre.stack.pop3 = some (rest,x,y,z) := by
  have hl := (bounds hz).1
  cases hs : pre.stack with
  | nil => simp only [hs,List.length_nil] at hl; omega
  | cons x tail =>
    cases tail with
    | nil => simp only [hs,List.length_cons,List.length_nil] at hl; omega
    | cons y tail =>
      cases tail with
      | nil => simp only [hs,List.length_cons,List.length_nil] at hl; omega
      | cons z rest => exact ⟨rest,x,y,z,rfl,rfl⟩

private theorem split_at (s : Stack UInt256) (n : Nat) (hn : n < s.length) :
    ∃ above x below, above.length = n ∧ s = above ++ x::below := by
  induction n generalizing s with
  | zero =>
    cases s with
    | nil => simp at hn
    | cons x below => exact ⟨[],x,below,rfl,rfl⟩
  | succ n ih =>
    cases s with
    | nil => simp at hn
    | cons top tail =>
      obtain ⟨above,x,below,hlen,hshape⟩ := ih tail (by simpa using hn)
      exact ⟨top::above,x,below,by simp [hlen],by simp [hshape]⟩

/-- The source DUP input shape is constructed from actual accepted depth. -/
theorem dup_inputs {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    (op : Operation.DOp) (hz : Z vj (.Dup op) pre = .ok (mid,cost)) :
    ∃ base above x, above.length+1 = dupDepth op ∧
      pre.stack = fromPython (base++[x]++above) := by
  have hl := (accepted_dup_capacity op hz).1
  have hd := (dup_depth op).1
  obtain ⟨above,x,below,hlen,hshape⟩ := split_at pre.stack (dupDepth op-1) (by omega)
  refine ⟨below.reverse,above.reverse,x,?_,?_⟩
  · simp only [List.length_reverse,hlen]
    omega
  · simpa [fromPython,List.reverse_append,List.append_assoc] using hshape

/-- Source SWAP indices are selected from the actual input, including its top. -/
theorem swap_inputs {vj : Array UInt256} {pre mid : EVM.State} {cost : Nat}
    (op : Operation.ExOp) (hz : Z vj (.Exchange op) pre = .ok (mid,cost)) :
    ∃ base middle x top, middle.length+1 = swapDepth op ∧
      pre.stack = fromPython (base++[x]++middle++[top]) := by
  have hl := (accepted_swap_capacity op hz).1
  have hd := (swap_depth op).1
  cases hs : pre.stack with
  | nil => simp only [hs,List.length_nil] at hl; omega
  | cons top tail =>
    have ht : swapDepth op-1 < tail.length := by
      simp only [hs,List.length_cons] at hl
      omega
    obtain ⟨middle,x,below,hlen,hshape⟩ := split_at tail (swapDepth op-1) ht
    refine ⟨below.reverse,middle.reverse,x,top,?_,?_⟩
    · simp only [List.length_reverse,hlen]
      omega
    · simp [fromPython,List.reverse_append,List.append_assoc,hshape]

#print axioms bounds
#print axioms pop1
#print axioms pop2
#print axioms pop3
#print axioms dup_inputs
#print axioms swap_inputs
end Eip8282.Audit.Integrator.ReferenceAcceptedStack

end

section

/-! ## ReferenceAccountLookup -/

/-! Literal optional-account read chain from the pinned Amsterdam
state_tracker.py: transaction writes, then block writes, then PreState.
An explicit deletion (some none) masks older accounts; an empty account is
still present. Reads are recorded even when lookup returns none and survive
rollback. Payload is generic: no account-field or whole-world correspondence
is assumed by this lookup projection. Initial deployment/presence and concrete
source dictionary bindings remain source-context producers.
-/
namespace Eip8282.Audit.Integrator.ReferenceAccountLookup
open EvmYul
set_option autoImplicit false

abbrev Overlay (Account : Type) := AccountAddress → Option (Option Account)

structure Parent (Account : Type) where
  writes : Overlay Account
  pre : AccountAddress → Option Account

structure Tx (Account : Type) where
  writes : Overlay Account
  reads : Set AccountAddress

def parentRead {Account : Type} (p : Parent Account) (a : AccountAddress) : Option Account :=
  (p.writes a).getD (p.pre a)

/-- Pure observation of the chain; getOptional below records the source read. -/
def peek {Account : Type} (p : Parent Account) (tx : Tx Account) (a : AccountAddress) : Option Account :=
  (tx.writes a).getD (parentRead p a)

def tracked {Account : Type} (tx : Tx Account) (a : AccountAddress) : Tx Account :=
  {tx with reads := insert a tx.reads}

def getOptional {Account : Type} (p : Parent Account) (tx : Tx Account) (a : AccountAddress) :
    Option Account × Tx Account := (peek p tx a,tracked tx a)

/-- Actual restore_tx_state resets the write dictionary, retaining shared reads. -/
def rollback {Account : Type} (tx snapshot : Tx Account) : Tx Account :=
  {tx with writes := snapshot.writes}

theorem tracked_peek {Account : Type} (p : Parent Account) (tx : Tx Account) (a b : AccountAddress) :
    peek p (tracked tx a) b = peek p tx b := rfl

theorem deletion_masks {Account : Type} (p : Parent Account) (tx : Tx Account) (a : AccountAddress)
    (deleted : tx.writes a = some none) : peek p tx a = none := by
  simp only [peek,deleted,Option.getD_some]

theorem read_recorded {Account : Type} (p : Parent Account) (tx : Tx Account) (a : AccountAddress) :
    a ∈ (getOptional p tx a).2.reads := Set.mem_insert a _

theorem rollback_lookup {Account : Type} (p : Parent Account) (tx snapshot : Tx Account) (a : AccountAddress) :
    peek p (rollback tx snapshot) a = peek p snapshot a ∧
    (rollback tx snapshot).reads = tx.reads := ⟨rfl,rfl⟩

#print axioms tracked_peek
#print axioms deletion_masks
#print axioms read_recorded
#print axioms rollback_lookup
end Eip8282.Audit.Integrator.ReferenceAccountLookup

end

section

/-! ## ReferenceDecodeShape -/

/-! Immediate shape follows from the actual decoder, including its EOF/invalid
STOP default. No independently supplied well-shaped instruction is assumed. -/
namespace Eip8282.Audit.Integrator.ReferenceDecodeShape
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem no_argument (pre : EVM.State) (hw : argOnNBytesOfInstr (decodeAt pre).1 = 0) :
    decodeAt pre = ((decodeAt pre).1,none) := by
  unfold decodeAt decode at hw ⊢
  cases h : pre.toState.executionEnv.code.get? pre.pc.toNat >>= parseInstr with
  | none => rfl
  | some op =>
    rw [h] at hw
    dsimp only [Bind.bind,Option.bind,Option.getD] at hw ⊢
    simp [hw]

theorem argument_width (pre : EVM.State) (value : UInt256) (width : Nat)
    (ha : (decodeAt pre).2 = some (value,width)) :
    width = argOnNBytesOfInstr (decodeAt pre).1 := by
  unfold decodeAt decode at ha ⊢
  cases h : pre.toState.executionEnv.code.get? pre.pc.toNat >>= parseInstr with
  | none => rw [h] at ha; cases ha
  | some op =>
    rw [h] at ha
    dsimp only [Bind.bind,Option.bind,Option.getD] at ha ⊢
    split at ha
    · cases ha
    · exact (Prod.mk.inj (Option.some.inj ha)).2.symm

theorem fixed (pre : EVM.State) (op : Operation .EVM)
    (hop : (decodeAt pre).1 = op) (hw : argOnNBytesOfInstr op = 0) :
    decodeAt pre = (op,none) := by
  have hn := no_argument pre (by rw [hop]; exact hw)
  simpa only [hop] using hn

#print axioms no_argument
#print axioms argument_width
#print axioms fixed
end Eip8282.Audit.Integrator.ReferenceDecodeShape

end

section

/-! ## ReferenceTerminalDecode -/

/-! Actual non-STOP instructions cannot be the pinned EOF default. This gives
terminal RETURN the same exact checked source-decoder binding as running sites,
without an impossible nonhalting-H premise. No execution or source agreement
is assumed beyond the actual pinned site invariant and actual decoded opcode. -/
namespace Eip8282.Audit.Integrator.ReferenceTerminalDecode
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeSites
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem roundtrip (u : UInt256) : UInt256.ofNat u.toNat = u := by
  cases u with | mk u =>
    apply congrArg UInt256.mk
    apply Fin.ext
    exact Nat.mod_eq_of_lt u.isLt

private theorem decode_at (pre : EVM.State) :
    decodeAt pre = (decode pre.executionEnv.code (UInt256.ofNat pre.pc.toNat)).getD (.STOP,none) := by
  rw [roundtrip]
  rfl

theorem nonstop_site {kind : Kind} {pre : EVM.State}
    (hat : RuntimeExecutionScope.At (runtime kind) pre)
    (hn : (decodeAt pre).1 ≠ .STOP) :
    pre.pc.toNat ∈ ReferenceDecodeSites.sites (reference kind) := by
  rcases site_or_eof hat with hp | he
  · exact hp
  · apply False.elim
    apply hn
    rw [decode_at,hat.1,code_eq,he]
    have hf := (runtime kind).eof
    change decode (runtime kind).code (UInt256.ofNat (runtime kind).code.size) = none at hf
    rw [code_eq] at hf
    rw [hf]
    rfl

theorem decode_matches {kind : Kind} {pre : EVM.State}
    (hat : RuntimeExecutionScope.At (runtime kind) pre)
    (hn : (decodeAt pre).1 ≠ .STOP) :
    decodeAt pre = (ReferenceDecodeSites.referenceDecode
      (ReferenceDecodeSites.code (reference kind)) pre.pc.toNat).getD (.STOP,none) := by
  rw [decode_at,hat.1,code_eq,ReferenceDecodeSites.decode_eq (nonstop_site hat hn)]

/-- The source decoder really succeeds; its fallback is not being equated. -/
theorem decode_some {kind : Kind} {pre : EVM.State}
    (hat : RuntimeExecutionScope.At (runtime kind) pre)
    (hn : (decodeAt pre).1 ≠ .STOP) :
    ReferenceDecodeSites.referenceDecode
      (ReferenceDecodeSites.code (reference kind)) pre.pc.toNat = some (decodeAt pre) := by
  have hm := decode_matches hat hn
  cases hd : ReferenceDecodeSites.referenceDecode
      (ReferenceDecodeSites.code (reference kind)) pre.pc.toNat with
  | none =>
    simp only [hd,Option.getD_none] at hm
    exact False.elim (hn (congrArg Prod.fst hm))
  | some instr =>
    simp only [hd,Option.getD_some] at hm
    exact congrArg some hm.symm

/-- RETURN's null immediate and successful source decode are both derived. -/
theorem return_decode {kind : Kind} {pre : EVM.State}
    (hat : RuntimeExecutionScope.At (runtime kind) pre)
    (hr : (decodeAt pre).1 = .RETURN) :
    ReferenceDecodeSites.referenceDecode
      (ReferenceDecodeSites.code (reference kind)) pre.pc.toNat = some (.RETURN,none) := by
  have hn : (decodeAt pre).1 ≠ .STOP := by rw [hr]; decide
  rw [decode_some hat hn,ReferenceDecodeShape.fixed pre .RETURN hr rfl]

#print axioms nonstop_site
#print axioms decode_matches
#print axioms decode_some
#print axioms return_decode
end Eip8282.Audit.Integrator.ReferenceTerminalDecode

end

section

/-! ## ReferenceAllDecode -/

/-! Decoder agreement also includes STOP and the checked runtime EOF fallback.
This remains restricted to actual sites of the two pinned protected images;
generic foreign-code decoder agreement is not asserted. -/
namespace Eip8282.Audit.Integrator.ReferenceAllDecode
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeSites
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private theorem roundtrip (u : UInt256) : UInt256.ofNat u.toNat = u := by
  cases u with | mk u =>
    apply congrArg UInt256.mk
    apply Fin.ext
    exact Nat.mod_eq_of_lt u.isLt

theorem decode_matches {kind : Kind} {pre : EVM.State}
    (hat : RuntimeExecutionScope.At (runtime kind) pre) :
    decodeAt pre = (ReferenceDecodeSites.referenceDecode
      (ReferenceDecodeSites.code (reference kind)) pre.pc.toNat).getD (.STOP,none) := by
  have hd : decodeAt pre = (decode pre.executionEnv.code (UInt256.ofNat pre.pc.toNat)).getD (.STOP,none) := by
    rw [roundtrip]
    rfl
  rw [hd,hat.1,code_eq]
  rcases site_or_eof hat with hsite | heof
  · rw [ReferenceDecodeSites.decode_eq hsite]
  · rw [heof]
    have hf := (runtime kind).eof
    change decode (runtime kind).code (UInt256.ofNat (runtime kind).code.size) = none at hf
    rw [code_eq] at hf
    rw [hf]
    cases kind <;> decide +kernel

#print axioms decode_matches
end Eip8282.Audit.Integrator.ReferenceAllDecode

end

section

/-! ## ReferenceAppendEntry -/

/-! Actual successful user entry and arbitrary finite fee execution produce the
ordered append markers. No fee iteration bound, noWrap, queue invariant or
resource sufficiency is assumed. Source pricing is attached at the consumer. -/
namespace Eip8282.Audit.Integrator.ReferenceAppendEntry
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall)
open SuccessInversion ActualAppendGas AppendGasPath ReferenceAppendOccurrences
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem exit_entry (c : XiCall .exit)
    {fuel : Nat} {final : EVM.State} {out : ByteArray}
    (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hsize : c.env.calldata.size = 48)
    (hx : X fuel exitJumpdests c.entry = .ok (.success final out)) :
    ∃ rest finish, Marked exitJumpdests fuel c.entry rest finish exitMarkers ∧
      decodeAt finish = (.STOP,none) ∧ X rest exitJumpdests finish = .ok (.success final out) := by
  have hu : Exit.callerWord c ≠ sysW := by
    intro he
    exact huser ((callerW_eq_sysW_iff c).mp he)
  obtain ⟨_, _, _, _, hhead, phead⟩ := traced_exit_entry c hu hx
  obtain ⟨n, output, counter, remaining, gas, count, hloop, htail, ptail⟩ := traced_exit_fee c rfl hhead
  have hc := Exit.hcode_of_env c (st := Exit.st₂ c) rfl
  obtain ⟨f1, g1, e1, _, hx1, hp1⟩ := traced_symBlock (h := htail) exit_b126 exit_b126_ok
    (by exact hc) rfl (exit_b126_shape c _ _ _ _ _ _ _ _ _ _ [])
  rw [withGE_at] at hx1 hp1
  have hs : Exit.cdsizeWord c = UInt256.ofNat 48 := by
    change UInt256.ofNat c.env.calldata.size = _
    rw [hsize]
  obtain ⟨f2, cost2, _, _, hx2, hp2⟩ := traced_jumpi_taken
    (decodeAt_of_code_pc (st := at_ c (Exit.st₂ c) c.entry.memory c.entry.activeWords g1 141 _ e1)
      (by exact hc) rfl exit_s141) rfl ((eq_ne_zero_iff _ _).mpr hs.symm) hx1
  rw [jumpi_taken_at, withGE_at] at hx2 hp2
  obtain ⟨f3, g3, e3, _, hx3, hp3⟩ := traced_symBlock (h := hx2) exit_b158 exit_b158_ok
    (by exact hc) rfl (exit_b158_shape c _ _ _ _ _ _ _)
  rw [withGE_at] at hx3 hp3
  obtain ⟨_, _, _, _, hwrite, pwrite⟩ := traced_exit_guard c rfl exit_s164 hx3
  obtain ⟨rest,finish,marked,stopped,actual⟩ := exit_suffix c hwrite
  refine ⟨rest,finish,?_,stopped,actual⟩
  have hp := (phead.trans (ptail.trans (hp1.trans (hp2.trans (hp3.trans pwrite)))))
  exact (Marked.skip hp).trans marked

theorem deposit_entry (c : XiCall .deposit)
    {fuel : Nat} {final : EVM.State} {out : ByteArray}
    (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hsize : c.env.calldata.size = 184)
    (hx : X fuel depositJumpdests c.entry = .ok (.success final out)) :
    ∃ rest finish, Marked depositJumpdests fuel c.entry rest finish depositMarkers ∧
      decodeAt finish = (.STOP,none) ∧ X rest depositJumpdests finish = .ok (.success final out) := by
  have hu : Deposit.callerWord c ≠ sysW := by
    intro he
    exact huser ((callerW_eq_sysW_iff c).mp he)
  obtain ⟨_, _, _, _, hhead, phead⟩ := traced_deposit_entry c hu hx
  obtain ⟨n, output, counter, remaining, gas, count, hloop, htail, ptail⟩ := traced_deposit_fee c rfl hhead
  have hc := Deposit.hcode_of_env c (st := Deposit.st₂ c) rfl
  obtain ⟨f1, g1, e1, _, hx1, hp1⟩ := traced_symBlock (h := htail) deposit_b127 deposit_b127_ok
    (by exact hc) rfl (deposit_b127_shape c _ _ _ _ _ _ _ _ _ _ [])
  rw [withGE_at] at hx1 hp1
  have hs : Deposit.cdsizeWord c = UInt256.ofNat 184 := by
    change UInt256.ofNat c.env.calldata.size = _
    rw [hsize]
  obtain ⟨f2, cost2, _, _, hx2, hp2⟩ := traced_jumpi_taken
    (decodeAt_of_code_pc (st := at_ c (Deposit.st₂ c) c.entry.memory c.entry.activeWords g1 142 _ e1)
      (by exact hc) rfl deposit_s142) rfl ((eq_ne_zero_iff _ _).mpr hs.symm) hx1
  rw [jumpi_taken_at, withGE_at] at hx2 hp2
  obtain ⟨f3, g3, e3, _, hx3, hp3⟩ := traced_symBlock (h := hx2) deposit_b159 deposit_b159_ok
    (by exact hc) rfl (deposit_b159_shape c _ _ _ _ _ _ _)
  rw [withGE_at] at hx3 hp3
  obtain ⟨_, f4, g4, e4, hx4, hp4⟩ := traced_deposit_guard c rfl deposit_s166 hx3
  obtain ⟨f5, g5, e5, _, hx5, hp5⟩ := traced_symBlock (h := hx4) deposit_b167 deposit_b167_ok
    (by exact hc) rfl (deposit_b167_shape c _ _ _ _ _ _)
  rw [withGE_at] at hx5 hp5
  obtain ⟨_, f6, g6, e6, hx6, hp6⟩ := traced_deposit_guard c rfl deposit_s190 hx5
  obtain ⟨f7, g7, e7, _, hx7, hp7⟩ := traced_symBlock (h := hx6) deposit_b191 deposit_b191_ok
    (by exact hc) rfl (deposit_b191_shape c _ _ _ _ _ _ _ _)
  rw [withGE_at] at hx7 hp7
  obtain ⟨_, _, _, _, hwrite, pwrite⟩ := traced_deposit_guard c rfl deposit_s204 hx7
  obtain ⟨rest,finish,marked,stopped,actual⟩ := deposit_suffix c hwrite
  refine ⟨rest,finish,?_,stopped,actual⟩
  have hp := (phead.trans (ptail.trans (hp1.trans (hp2.trans (hp3.trans
      (hp4.trans (hp5.trans (hp6.trans (hp7.trans pwrite)))))))))
  exact (Marked.skip hp).trans marked

#print axioms exit_entry
#print axioms deposit_entry
end Eip8282.Audit.Integrator.ReferenceAppendEntry

end

section

/-! ## ReferenceBlockGasCapacity -/

/-! Aggregate block-gas envelope, complementing `ResourceBounds`.

`ResourceBounds.totalAppends` bounds the total *append count* across all
blocks by `2^128` under the reference protocol's typed 64-bit slot and gas
inputs. This module states and proves the analogous bound on the total
*gas capacity* itself — `totalGas` — so downstream consumers can quote a
uniform 2^128 envelope regardless of which resource they are tracking, and
so the pointwise inequality `totalAppends blocks ≤ totalGas blocks`
becomes a named lemma.

The bound is a corollary of `BlockUsage` typing (`gas : Fin (2^64)`) and
slot uniqueness. It does NOT assert that arbitrary Θ histories actually
satisfy these envelopes: as noted in `ResourceBounds`, `charged` must still
be produced from actual transaction gas accounting, including nested calls
and refunds. See `audit/PROTOCOL-BOUNDARY.md`. -/
namespace Eip8282.Audit.Integrator.ReferenceBlockGasCapacity

open EvmYul
open Eip8282.Audit.Integrator.ResourceBounds
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Natural sum of block gas capacities. -/
def totalGas (blocks : List BlockUsage) : Nat := (blocks.map (fun b => b.gas.val)).sum

/-- Sum of gas capacities is at most `length * (2^64 - 1)`. Mirrors
`ResourceBounds.total_le` on the gas dimension. -/
theorem totalGas_le (blocks : List BlockUsage) :
    totalGas blocks ≤ blocks.length * (2^64-1) := by
  induction blocks with
  | nil => simp [totalGas]
  | cons b bs ih =>
    have hb := b.gas.isLt
    simp only [totalGas, List.map_cons, List.sum_cons, List.length_cons]
    change b.gas.val + totalGas bs ≤ (bs.length+1)*(2^64-1)
    rw [Nat.add_mul]
    omega

/-- Fewer than 2^128 gas across a finite canonical history with distinct
slots. Slot uniqueness bounds `blocks.length ≤ 2^64` via `Fintype.card`. -/
theorem totalGas_lt (blocks : List BlockUsage) (hs : (blocks.map (·.slot)).Nodup) :
    totalGas blocks < 2^128 := by
  have hl := hs.length_le_card
  simp only [List.length_map, Fintype.card_fin] at hl
  have ht := totalGas_le blocks
  have hm := Nat.mul_le_mul_right (2^64-1) hl
  have hc : 2^64*(2^64-1) < 2^128 := by decide
  exact lt_of_le_of_lt (ht.trans hm) hc

/-- The block-level `charged` field constrains appends by gas per block, so
the aggregate append count is bounded by the aggregate gas capacity. -/
theorem totalAppends_le_totalGas (blocks : List BlockUsage) :
    totalAppends blocks ≤ totalGas blocks := by
  induction blocks with
  | nil => simp [totalAppends, totalGas]
  | cons b bs ih =>
    simp only [totalAppends, totalGas, List.map_cons, List.sum_cons]
    change b.appends + totalAppends bs ≤ b.gas.val + totalGas bs
    have hc := b.charged
    omega

/-- Combined uniform envelope: total appends and total gas both fit inside
2^128. Consumers that need one bound on both resources can quote this. -/
theorem uniform_envelope (blocks : List BlockUsage)
    (hs : (blocks.map (·.slot)).Nodup) :
    totalAppends blocks < 2^128 ∧ totalGas blocks < 2^128 :=
  ⟨total_lt blocks hs, totalGas_lt blocks hs⟩

#print axioms totalGas_le
#print axioms totalGas_lt
#print axioms totalAppends_le_totalGas
#print axioms uniform_envelope

end Eip8282.Audit.Integrator.ReferenceBlockGasCapacity

end

section

/-! ## ReferenceCodeAccountPresence -/

/-! Literal account-default and code-hash read chain from pinned Amsterdam
state_tracker.py. EMPTY_CODE_HASH is tested before any code overlay; an absent
account defaults to EMPTY_ACCOUNT and therefore loads empty code. A completed
nonempty fetch consequently witnesses a present account. The PreState callback
retains its possible error; neither code availability nor a successful fetch
is invented. Code addresses and current_target must be related by actual frame
construction (SYSTEM uses the same target; delegation/CALLCODE need care).
-/
namespace Eip8282.Audit.Integrator.ReferenceCodeAccountPresence
open EvmYul
set_option autoImplicit false

structure CodeParent (Hash Error : Type) where
  writes : Hash → Option ByteArray
  pre : Hash → Except Error ByteArray

/-- Source get_code special-cases the empty hash before the tx/block layers. -/
noncomputable def getCode {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash)
    (p : CodeParent Hash Error) (writes : Hash → Option ByteArray) (hash : Hash) : Except Error ByteArray :=
  if hash = emptyHash then .ok ByteArray.empty
  else match writes hash with
    | some code => .ok code
    | none => match p.writes hash with
      | some code => .ok code
      | none => p.pre hash

/-- get_account records the optional read, defaults absent accounts to
EMPTY_ACCOUNT, then passes its code_hash to get_code. Reads survive errors. -/
noncomputable def load {Account Hash Error : Type} [DecidableEq Hash]
    (codeHash : Account → Hash) (emptyHash : Hash)
    (accountsParent : ReferenceAccountLookup.Parent Account) (accounts : ReferenceAccountLookup.Tx Account)
    (codeParent : CodeParent Hash Error) (codeWrites : Hash → Option ByteArray) (address : AccountAddress) :
    Except Error ByteArray × ReferenceAccountLookup.Tx Account :=
  (getCode emptyHash codeParent codeWrites
    ((ReferenceAccountLookup.peek accountsParent accounts address).map codeHash |>.getD emptyHash),
   ReferenceAccountLookup.tracked accounts address)

theorem absent_empty {Account Hash Error : Type} [DecidableEq Hash]
    (codeHash : Account → Hash) (emptyHash : Hash)
    (accountsParent : ReferenceAccountLookup.Parent Account) (accounts : ReferenceAccountLookup.Tx Account)
    (codeParent : CodeParent Hash Error) (codeWrites : Hash → Option ByteArray) (address : AccountAddress)
    (absent : ReferenceAccountLookup.peek accountsParent accounts address = none) :
    (load codeHash emptyHash accountsParent accounts codeParent codeWrites address).1 = .ok ByteArray.empty := by
  simp only [load,absent,Option.map_none,Option.getD_none,getCode,if_true]

/-- Nonempty code proves presence at the *code address*. This does not equate
that address with a delegated or CALLCODE frame's storage owner by definition. -/
theorem nonempty_present {Account Hash Error : Type} [DecidableEq Hash]
    (codeHash : Account → Hash) (emptyHash : Hash)
    (accountsParent : ReferenceAccountLookup.Parent Account) (accounts : ReferenceAccountLookup.Tx Account)
    (codeParent : CodeParent Hash Error) (codeWrites : Hash → Option ByteArray) (address : AccountAddress)
    {code : ByteArray}
    (loaded : (load codeHash emptyHash accountsParent accounts codeParent codeWrites address).1 = .ok code)
    (nonempty : code ≠ ByteArray.empty) :
    ∃ account, ReferenceAccountLookup.peek accountsParent accounts address = some account := by
  cases found : ReferenceAccountLookup.peek accountsParent accounts address with
  | some account => exact ⟨account,rfl⟩
  | none =>
    have empty := absent_empty codeHash emptyHash accountsParent accounts codeParent codeWrites address found
    have same : code = ByteArray.empty := Except.ok.inj (loaded.symm.trans empty)
    exact False.elim (nonempty same)

/-- SYSTEM's code-probe transaction and execution transaction are fresh
siblings with the same block parent. Only their empty account write overlays
matter; the probe's read bookkeeping is not imported into the execution. -/
theorem fresh_system_owner {Account Hash Error : Type} [DecidableEq Hash]
    (codeHash : Account → Hash) (emptyHash : Hash)
    (accountsParent : ReferenceAccountLookup.Parent Account)
    (probe execution : ReferenceAccountLookup.Tx Account)
    (probeEmpty : ∀ a, probe.writes a = none) (executionEmpty : ∀ a, execution.writes a = none)
    (codeParent : CodeParent Hash Error) (codeWrites : Hash → Option ByteArray) (target : AccountAddress)
    {code : ByteArray}
    (loaded : (load codeHash emptyHash accountsParent probe codeParent codeWrites target).1 = .ok code)
    (nonempty : code ≠ ByteArray.empty) :
    (ReferenceAccountLookup.peek accountsParent execution target).isSome = true := by
  obtain ⟨account,present⟩ := nonempty_present codeHash emptyHash accountsParent probe codeParent codeWrites target loaded nonempty
  have same : ReferenceAccountLookup.peek accountsParent execution target =
      ReferenceAccountLookup.peek accountsParent probe target := by
    simp only [ReferenceAccountLookup.peek,probeEmpty,executionEmpty]
  rw [same,present]
  rfl

#print axioms absent_empty
#print axioms nonempty_present
#print axioms fresh_system_owner
end Eip8282.Audit.Integrator.ReferenceCodeAccountPresence

end

section

/-! ## ReferenceCreditBatchKillLines -/

/-! Kill-line mutations exercising the aggregate accounting inside
`ProtocolCreditEnvelope.CreditBatch`, `envelope`, `powMaximum` and
`withdrawalMaximum`.

Each theorem below is a small concrete equality or bound the constructor
must satisfy; a mutation that swaps operand order, replaces `+` with `*`,
or drops a factor would flip the statement. The theorems do not require
instantiating a `Ledger` or a `History` — they exercise the arithmetic in
isolation, so downstream `native_decide` fixtures are unnecessary.

No new premise; no new axiom. -/
namespace Eip8282.Audit.Integrator.ReferenceCreditBatchKillLines

open EvmYul EvmYul.EVM
open ProtocolCreditEnvelope
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- `powMaximum` is exactly the reference-EL Frontier miner batch bound. A
mutation dropping a digit or reordering the literal breaks this equality. -/
theorem powMaximum_value : powMaximum = 14062500000000000000 := rfl

/-- `withdrawalMaximum` is exactly `(2^64 - 1) * 10^9`. A mutation replacing
`*` with `+` or `10^9` with `10^8` breaks this equality. -/
theorem withdrawalMaximum_value : withdrawalMaximum = (2^64 - 1) * 10^9 := rfl

/-- `envelope` is exactly the sum of the three protocol credit sources plus
the genesis constant. Mutations swapping the factor order or dropping a
term break this equality. -/
theorem envelope_expansion (pow withdrawals migrations : Nat) :
    envelope pow withdrawals migrations =
      GenesisFundingInput.totalCredit + powMaximum * pow + withdrawalMaximum * withdrawals + migrations := rfl

/-- Zero pow/withdrawal/migration inputs give the genesis total exactly. -/
theorem envelope_zero : envelope 0 0 0 = GenesisFundingInput.totalCredit := by
  simp [envelope]

/-- One PoW batch contributes `powMaximum` on top of the base. -/
theorem envelope_one_pow :
    envelope 1 0 0 = GenesisFundingInput.totalCredit + powMaximum := by
  simp [envelope]

/-- One withdrawal contributes `withdrawalMaximum` on top of the base. -/
theorem envelope_one_withdrawal :
    envelope 0 1 0 = GenesisFundingInput.totalCredit + withdrawalMaximum := by
  simp [envelope]

/-- `nil` batch: source world unchanged, aggregate credit zero. This is
the identity kill-line — dropping the `world = world` requirement would
allow a mutated `nil` to pretend to teleport between worlds. -/
theorem nil_credit_zero (world : AccountMap .EVM) :
    CreditBatch world 0 world := CreditBatch.nil world

/-- A one-element batch aggregates a single `amount`. Mutations replacing
the amount with a fixed constant would fail this general form. -/
theorem cons_singleton (world : AccountMap .EVM)
    (recipient : AccountAddress) (amount : UInt256) :
    CreditBatch world (amount.toNat + 0)
      (world.increaseBalance .EVM recipient amount) :=
  CreditBatch.cons recipient amount (CreditBatch.nil _)

/-- Concrete numeric kill-line: a two-step batch aggregates exactly the sum
of its two amounts (specialised at `⟨0⟩` and `⟨0⟩`). Two zero-value
credits still walk through the batch even if `increaseBalance` yields
the same world. -/
theorem cons_two_zero_amounts (world : AccountMap .EVM)
    (r1 r2 : AccountAddress) :
    CreditBatch world ((⟨0⟩ : UInt256).toNat + ((⟨0⟩ : UInt256).toNat + 0))
      (((world.increaseBalance .EVM r1 ⟨0⟩).increaseBalance .EVM r2 ⟨0⟩)) :=
  CreditBatch.cons r1 ⟨0⟩
    (CreditBatch.cons r2 ⟨0⟩ (CreditBatch.nil _))

#print axioms powMaximum_value
#print axioms withdrawalMaximum_value
#print axioms envelope_expansion
#print axioms envelope_zero
#print axioms envelope_one_pow
#print axioms envelope_one_withdrawal
#print axioms nil_credit_zero
#print axioms cons_singleton
#print axioms cons_two_zero_amounts

end Eip8282.Audit.Integrator.ReferenceCreditBatchKillLines

end

section

/-! ## ReferenceStopView -/

/-! Actual STOP terminal observations. The source control_flow.stop only clears
running and leaves the view unchanged. Actual output is empty; identification
with the source frame's initially empty output belongs to frame initialization.
No running-PC increment, memory growth, write permission or stack shape occurs. -/
namespace Eip8282.Audit.Integrator.ReferenceStopView
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open ReferenceRuntimeView
set_option autoImplicit false

theorem terminal {parent : ReferenceStorageView.Parent} {v : View}
    {vj : Array UInt256} {pre mid post : EVM.State} {fuel gasCost : Nat}
    (hz : Z vj .STOP pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (.STOP,none) mid post)
    (related : Related parent v pre) :
    Related parent v post ∧ H post.toMachineState .STOP = some ByteArray.empty := by
  obtain rfl := Z_ok_state hz
  change EVM.step (fuel+1) gasCost (some (.STOP,none)) (zMid pre .STOP) = .ok post at hs
  rw [OrdinaryGas.dispatch (by decide)] at hs
  have known := Eip8282.Audit.SymExec.step_STOP (stepPre gasCost (zMid pre .STOP))
  have same := Except.ok.inj (hs.symm.trans known)
  subst post
  exact ⟨⟨related.env,related.pc,related.stack,
    ⟨related.memory.coherent,related.memory.size,related.memory.bytes⟩,
    related.storage,related.logs,related.owner⟩,rfl⟩

#print axioms terminal
end Eip8282.Audit.Integrator.ReferenceStopView

end

section

/-! ## ReferenceTransferLogs -/

/-! Source-shaped EIP-7708 log projection, not reference execution equivalence.
Proposed EL 0cc100eb190b64b23baba72dac0165652eaec252:
vm/__init__.py:40-43,252-288, SHA256
664702bc483736fca3c4ac4bb9e459a24c83f5365b495485c4674d5c41fbe993.
Emitter is SYSTEM; topics are signature hash, padded sender, padded recipient;
data is the big-endian amount. The signature hash is an explicit argument:
its Keccak/source binding and byte-representation transport are external,
and no cryptographic axiom is needed for address-only projection.
Actual process_call placement/guards and success-only child incorporation
remain reference adapters. Nothing filters LOG0 or changes the public clause.
-/
namespace Eip8282.Audit.Integrator.ReferenceTransferLogs
open EvmYul EvmYul.EVM
open ReachableCalls (Contract address)
set_option autoImplicit false

/-- UInt256 representation of the source's 32-byte padded address topic. -/
def addressTopic (a : AccountAddress) : UInt256 := UInt256.ofNat a.val

/-- Instantiate signature with keccak256("Transfer(address,address,uint256)").
Projection below holds for every signature, without trusting a hash evaluator. -/
def entry (signature : UInt256) (sender recipient : AccountAddress)
    (amount : UInt256) : LogEntry :=
  { address := Eip8282.Audit.EvmRunner.sysAddr,
    topics := #[signature, addressTopic sender, addressTopic recipient],
    data := amount.toByteArray }

/-- The actual helper emits nothing for a zero transfer. -/
def emitted (signature : UInt256) (sender recipient : AccountAddress)
    (amount : UInt256) : List LogEntry :=
  if amount = UInt256.ofNat 0 then [] else [entry signature sender recipient amount]

/-- Ordered all-topics address projection, shared with ProtectedLogFrame. -/
def project (a : AccountAddress) (logs : List LogEntry) : List LogEntry :=
  logs.filter (fun e => decide (e.address = a))

theorem project_substate (a : AccountAddress) (ss : Substate) :
    project a ss.logSeries.toList = ProtectedLogFrame.project a ss := rfl

theorem address_ne_system (kind : Contract) :
    address kind ≠ Eip8282.Audit.EvmRunner.sysAddr := by
  cases kind <;> decide +kernel

theorem project_append (a : AccountAddress) (left right : List LogEntry) :
    project a (left ++ right) = project a left ++ project a right := by
  simp [project,List.filter_append]

theorem project_entry (kind : Contract) (signature : UInt256)
    (sender recipient : AccountAddress) (amount : UInt256) :
    project (address kind) [entry signature sender recipient amount] = [] := by
  simp [project,entry,Ne.symm (address_ne_system kind)]

theorem project_emitted (kind : Contract) (signature : UInt256)
    (sender recipient : AccountAddress) (amount : UInt256) :
    project (address kind) (emitted signature sender recipient amount) = [] := by
  unfold emitted
  split
  · rfl
  · exact project_entry kind signature sender recipient amount

/-- The guarded process_call transfer prefix is invisible at either runtime.
The source producer must establish the actual should-transfer/nonalias guard. -/
theorem frame (kind : Contract) (signature : UInt256)
    (sender recipient : AccountAddress) (amount : UInt256)
    (enabled : Bool) (before after : List LogEntry) :
    project (address kind)
      (before ++ (if enabled then emitted signature sender recipient amount else []) ++ after) =
    project (address kind) before ++ project (address kind) after := by
  cases enabled with
  | false => simp [project]
  | true =>
    simp only [ite_true,project_append,project_emitted,List.append_nil]

/-- Source settlement chooses child logs only on success. This is a list
identity; actual reference error/success selection must be supplied separately. -/
theorem settle (a : AccountAddress) (success : Bool) (parent child : List LogEntry) :
    project a (parent ++ (if success then child else [])) =
    project a parent ++ (if success then project a child else []) := by
  cases success <;> simp [project]

/-- Ordered composition across any supplied frame list; no occurrence loss or
reordering is introduced by the address projection. -/
theorem project_flatMap (a : AccountAddress) (frames : List (List LogEntry)) :
    project a frames.flatten = frames.flatMap (project a) := by
  induction frames with
  | nil => rfl
  | cons head tail ih => simp only [List.flatten_cons,List.flatMap_cons,project_append,ih]

#print axioms project_substate
#print axioms address_ne_system
#print axioms project_append
#print axioms project_entry
#print axioms project_emitted
#print axioms frame
#print axioms settle
#print axioms project_flatMap
end Eip8282.Audit.Integrator.ReferenceTransferLogs

end
