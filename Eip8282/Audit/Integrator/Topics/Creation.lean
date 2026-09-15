import Eip8282.Audit.Integrator.CodeStorageFrame
import Eip8282.Audit.Integrator.CreationWorld
import Eip8282.Audit.Integrator.JournalInvariant
import Eip8282.Audit.Integrator.NestedEventArgs
import Eip8282.Audit.Integrator.RuntimeThetaExclusion

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## CreationCollisionScope -/

/-! Actual creation at an installed protected runtime selects collision INVALID.
The computed address remains explicit; neither preimage validity nor sufficient
fuel is needed for the code-selection or exclusion conclusions. -/
namespace Eip8282.Audit.Integrator.CreationCollisionScope
open EvmYul EvmYul.EVM
open NestedEvents
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem runtime_size_positive (kind : ReachableCalls.Contract) :
    0 < (ReachableCalls.runtime kind).size := by
  cases kind <;> decide +kernel

theorem context_collision {kind : ReachableCalls.Contract} (c : CreationSettlement.Context)
    (bytes : ByteArray) (hc : JournalInvariant.CodeAt kind c.world)
    (ha : CreationSettlement.address bytes = ReachableCalls.address kind) :
    c.collision (CreationSettlement.address bytes) = true := by
  obtain ⟨old,ho,hcode⟩ := hc
  have he : c.existing (CreationSettlement.address bytes) = old := by
    unfold CreationSettlement.Context.existing
    rw [Std.TreeMap.getD_eq_getD_getElem?]
    change (c.world.get? (CreationSettlement.address bytes)).getD default = old
    rw [ha,ho]
    rfl
  have hn : old.code.size ≠ 0 := by
    rw [hcode]
    exact Nat.ne_of_gt (runtime_size_positive kind)
  have hd : decide (old.code.size ≠ 0) = true := decide_eq_true hn
  simp only [CreationSettlement.Context.collision, he, hd, Bool.or_true, Bool.true_or]

theorem selected_invalid {kind : ReachableCalls.Contract} (a : LambdaArgs)
    (bytes : ByteArray) (hc : JournalInvariant.CodeAt kind a.world)
    (ha : CreationSettlement.address bytes = ReachableCalls.address kind) :
    (a.xiArgs bytes).env.code = ⟨#[0xfe]⟩ := by
  have hcollision := context_collision (a.context 0) bytes hc ha
  change (a.context 0).selectedCode (CreationSettlement.address bytes) = _
  simp only [CreationSettlement.Context.selectedCode, hcollision, ↓reduceIte]

theorem no_theta {kind : ReachableCalls.Contract} {a : LambdaArgs} {bytes : ByteArray}
    (hc : JournalInvariant.CodeAt kind a.world)
    (ha : CreationSettlement.address bytes = ReachableCalls.address kind)
    {fuel f : Nat} {result : XiResult} {tree : EventTree} {path : EventTree.Address}
    {child : ThetaArgs} {r : ThetaResult}
    (loc : ThetaAt (.xi fuel (a.xiArgs bytes)) result tree path f child r) : False :=
  RuntimeThetaExclusion.invalid_no_theta (selected_invalid a bytes hc ha) loc

theorem no_success {kind : ReachableCalls.Contract} {a : LambdaArgs} {bytes : ByteArray}
    (hc : JournalInvariant.CodeAt kind a.world)
    (ha : CreationSettlement.address bytes = ReachableCalls.address kind)
    {fuel : Nat} {published : Created × World × UInt256 × Substate} {out : ByteArray}
    (hr : (Request.xi fuel (a.xiArgs bytes)).eval = .ok (.success published out)) : False :=
  RuntimeThetaExclusion.invalid_no_success (selected_invalid a bytes hc ha) hr

#print axioms context_collision
#print axioms selected_invalid
#print axioms no_theta
#print axioms no_success
end Eip8282.Audit.Integrator.CreationCollisionScope

end

section

/-! ## CreationPreimageTotal -/

/-!
The pinned CREATE address encoder is total on its typed inputs. This proves
Option nonfailure, not cryptographic address correctness. CREATE2's encoder
returns Some directly; no length property of the opaque KEC output is used.
-/
namespace Eip8282.Audit.Integrator.CreationPreimageTotal
open EvmYul EvmYul.EVM
open NestedEvents
open private s from EvmYul.Wheels
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- A word's minimal big-endian representation fits the RLP short-string case. -/
theorem nonce_bytes_le (nonce : UInt256) : (BE nonce.toNat).size ≤ 32 := by
  simpa [BE] using EvmYul.length_toBytesBigEndian_le (n := nonce.toNat) nonce.val.isLt

/-- The actual address serializer has precisely its typed 160-bit width. -/
theorem sender_bytes_size (sender : AccountAddress) : sender.toByteArray.size = 20 := by
  have hfit : sender.val < 256^20 := sender.isLt
  have hlen := congrArg List.length (EvmYul.toBeBytesFixed_eq_zeroPad sender.val 20 hfit)
  simp only [EvmYul.length_toBeBytesFixed, List.length_append, List.length_replicate] at hlen
  have hb : (BE sender.val).size ≤ 20 := by
    simpa [BE] using (show (EvmYul.toBytesBigEndian sender.val).length ≤ 20 by omega)
  unfold AccountAddress.toByteArray
  rw [ByteArray.size_append, ffi.ByteArray.size_zeroes]
  have hw : 20 < 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  have hn : (BE sender.val).size < 2 ^ System.Platform.numBits := by omega
  have h20 : (20 : BitVec System.Platform.numBits).toNat = 20 := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
  simp only [USize.toNat, BitVec.toNat_sub, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, h20]
  rw [show 2 ^ System.Platform.numBits - (BE sender.val).size + 20 =
      2 ^ System.Platform.numBits + (20 - (BE sender.val).size) by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem rlp_bytes_short {bytes : ByteArray} (hb : bytes.size ≤ 32) :
    ∃ encoded, RLP (.𝔹 bytes) = some encoded ∧ encoded.size ≤ 33 := by
  unfold RLP
  change ∃ encoded, (if bytes.size = 1 ∧ bytes.get! 0 < 128 then some bytes
    else if bytes.size < 56 then some ([⟨128 + bytes.size⟩].toByteArray ++ bytes)
    else if bytes.size < 2^64 then
      some ([⟨183 + (BE bytes.size).size⟩].toByteArray ++ BE bytes.size ++ bytes)
    else none) = some encoded ∧ encoded.size ≤ 33
  split
  · exact ⟨bytes, rfl, by omega⟩
  · split
    · refine ⟨_, rfl, ?_⟩
      simp only [ByteArray.size_append, List.size_toByteArray, List.length_cons, List.length_nil]
      omega
    · omega

private theorem rlp_pair_total {left right : ByteArray} (hl : left.size ≤ 32)
    (hr : right.size ≤ 32) : ∃ encoded, RLP (.𝕃 [.𝔹 left, .𝔹 right]) = some encoded := by
  obtain ⟨l, hel, hll⟩ := rlp_bytes_short hl
  obtain ⟨r, her, hrl⟩ := rlp_bytes_short hr
  rw [RLP.eq_2, R_l.eq_1]
  simp only [s, hel, her]
  have hb : (l ++ (r ++ ByteArray.empty)).size < 2^64 := by
    simp only [ByteArray.size_append, ByteArray.size_empty]
    omega
  split
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩

/-- No nonce-admission premise is required: even a full 256-bit nonce encodes. -/
theorem create_total (sender : AccountAddress) (nonce : UInt256) (init : ByteArray) :
    ∃ bytes, Lambda.L_A sender nonce none init = some bytes := by
  exact rlp_pair_total (by rw [sender_bytes_size]; omega) (nonce_bytes_le nonce)

/-- Syntactic Option totality for CREATE2, without asserting that arbitrary
salt/hash bytes have the protocol widths. -/
theorem create2_total (sender : AccountAddress) (nonce : UInt256)
    (salt init : ByteArray) : ∃ bytes, Lambda.L_A sender nonce (some salt) init = some bytes :=
  ⟨_,rfl⟩

theorem context_total (c : CreationSettlement.Context) : ∃ bytes, c.preimage = some bytes := by
  unfold CreationSettlement.Context.preimage
  cases c.salt with
  | none => exact create_total _ _ _
  | some salt => exact create2_total _ _ _ _

theorem lambdaArgs_total (a : LambdaArgs) : ∃ bytes, a.preimage = some bytes :=
  context_total (a.context 0)

/-- The actual selected CREATE/CREATE2 request, with all nonce updates and gas
charging retained, has a successfully encoded address preimage. -/
theorem creationArgs_total (kind : CreationGas.Variant) (cost : Nat) (pre : EVM.State)
    (value off len salt : UInt256) :
    ∃ bytes, (creationArgs kind cost pre value off len salt).preimage = some bytes :=
  lambdaArgs_total _

/-- The actual CREATE2 salt adapter is exactly the 32-byte word encoding. This
is separate from the opaque init hash, whose width is not needed above. -/
theorem create2_salt_width (salt : UInt256) :
    ∃ bytes, CreationGas.saltBytes .create2 salt = some bytes ∧ bytes.size = 32 :=
  ⟨salt.toByteArray,rfl,UInt256.size_toByteArray salt⟩

#print axioms context_total
#print axioms lambdaArgs_total
#print axioms creationArgs_total
#print axioms create2_salt_width
end Eip8282.Audit.Integrator.CreationPreimageTotal

end

section

/-! ## CreationErrorScope -/

/-!
After actual address-encoding totality, Lambda's only returned exception is
OutOfFuel. Ordinary init exceptions are returned failed creations. This is an
error classification, not evaluator-fuel adequacy or a rollback assertion for
CREATE's catch of a Lambda error.
-/
namespace Eip8282.Audit.Integrator.CreationErrorScope
open EvmYul EvmYul.EVM
open NestedEvents
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem context_error (c : CreationSettlement.Context) {err : ExecutionException}
    (h : c.result = .error err) : err = .OutOfFuel := by
  obtain ⟨bytes,hp⟩ := CreationPreimageTotal.context_total c
  rw [CreationSettlement.result_eq_settle c hp] at h
  cases he : c.execution (CreationSettlement.address bytes) with
  | error childError =>
      simp only [CreationSettlement.Context.settle, he] at h
      split at h
      · cases h; rfl
      · cases h
  | ok result =>
      cases result with
      | revert gas out =>
          simp only [CreationSettlement.Context.settle, he] at h
          cases h
      | success state out =>
          obtain ⟨created,world,gas,substate⟩ := state
          simp only [CreationSettlement.Context.settle, he] at h
          cases h

/-- The same classification for the actual raw Lambda request, including its
zero-fuel branch. No success or per-child admission premise is needed. -/
theorem lambda_error {fuel : Nat} {a : LambdaArgs} {err : ExecutionException}
    (h : (Request.lambda fuel a).eval = .error err) : err = .OutOfFuel := by
  cases fuel with
  | zero => cases h; rfl
  | succ fuel => exact context_error (a.context fuel) h

#print axioms context_error
#print axioms lambda_error
end Eip8282.Audit.Integrator.CreationErrorScope

end

section

/-! ## CreationStorageFrame -/

/-! Creation entry preserves existing code and persistent storage, including
sender/target aliasing. Installation is framed only away from its target.
Occupied-target rejection concerns completed Lambda results, not caught errors. -/
namespace Eip8282.Audit.Integrator.CreationStorageFrame
open EvmYul EvmYul.EVM
open CreationSettlement CodeStorageFrame
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private theorem lookup_insert (world : AccountMap .EVM) (key addr : AccountAddress)
    (account : Account .EVM) :
    (world.insert key account).get? addr = if key = addr then some account else world.get? addr := by
  exact (Std.TreeMap.getElem?_insert (t := world) (k := key) (a := addr) (v := account)).trans
    (by simp only [Std.LawfulEqOrd.compare_eq_iff_eq]; rfl)

/-- Literal debit and fresh-account insertion preserve code, including aliases. -/
theorem entry_frame (c : Context) (target protectedAddr : AccountAddress) :
    Frame c.world (c.entryWorld target) protectedAddr := by
  constructor
  · intro old hold
    unfold Context.entryWorld
    cases hs : c.world.get? c.sender with
    | none => exact ⟨old,hold,rfl⟩
    | some sender =>
      dsimp only
      by_cases ht : target = protectedAddr
      · subst target
        refine ⟨{ (c.existing protectedAddr) with nonce := (c.existing protectedAddr).nonce + ⟨1⟩, balance := c.value + (c.existing protectedAddr).balance }, ?_, ?_⟩
        · exact Std.TreeMap.getElem?_insert_self
        · change (c.existing protectedAddr).code = old.code
          unfold Context.existing
          rw [Std.TreeMap.getD_eq_getD_getElem?]
          change ((c.world.get? protectedAddr).getD default).code = old.code
          rw [hold]
          rfl
      · rw [lookup_insert, if_neg ht]
        by_cases ha : c.sender = protectedAddr
        · rw [lookup_insert, if_pos ha]
          refine ⟨_,rfl,?_⟩
          have he : sender = old := Option.some.inj ((ha ▸ hs).symm.trans hold)
          change sender.code = old.code
          exact congrArg (fun a : Account .EVM => a.code) he
        · rw [lookup_insert, if_neg ha]
          exact ⟨old,hold,rfl⟩
  · exact CreationSettlement.entry_storage c target protectedAddr

theorem install_away_frame (world : AccountMap .EVM) (target protectedAddr : AccountAddress)
    (code : ByteArray) (hne : target ≠ protectedAddr) :
    Frame world (install world target code) protectedAddr := by
  constructor
  · intro old hold
    refine ⟨old,?_,rfl⟩
    unfold install
    rw [lookup_insert, if_neg hne]
    exact hold
  · exact CreationSettlement.install_storage world target protectedAddr code

/-- The occupied guard rejects even a hypothetical successful initializer;
ordinary init errors and reverts also return the exact input world. -/
theorem occupied_creation_fails (c : Context) {bytes : ByteArray}
    {old : Account .EVM} {target : AccountAddress}
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {ss : Substate} {status : Bool} {out : ByteArray}
    (hp : c.preimage = some bytes)
    (hold : c.world.get? (address bytes) = some old) (hcode : old.code ≠ .empty)
    (hr : c.result = .ok (target,created,world,gas,ss,status,out)) :
    status = false ∧ world = c.world := by
  have hf (gas : UInt256) (code : ByteArray) : c.depositFailure (address bytes) gas code = true := by
    unfold Context.depositFailure
    simp only [hold]
    simp [hcode]
  rw [result_eq_settle c hp] at hr
  cases he : c.execution (address bytes) with
  | error err =>
    simp only [Context.settle, he] at hr
    split at hr
    · cases hr
    · cases hr; exact ⟨rfl,rfl⟩
  | ok result =>
    cases result with
    | revert remaining output =>
      simp only [Context.settle, he] at hr
      cases hr; exact ⟨rfl,rfl⟩
    | success state code =>
      obtain ⟨cr,w,g,sub⟩ := state
      simp only [Context.settle, he, hf, ↓reduceIte, Bool.not_true] at hr
      cases hr; exact ⟨rfl,rfl⟩

#print axioms entry_frame
#print axioms install_away_frame
#print axioms occupied_creation_fails
end Eip8282.Audit.Integrator.CreationStorageFrame

end
