import Eip8282.Audit.Integrator.Topics.Reference2

/-! # Source admission extraction for the actual history consumers

Consumers (unchanged): `ReferenceAdmissionHistory.append` / `receipt_effects`,
which take `TransactionFunding.Admission` and a `ReferenceCalldataAdmission.Gate`.

This module transcribes the admission clauses of the archived EL pin
`0cc100eb190b64b23baba72dac0165652eaec252` (bundle receipt
`audit/receipts/direct-reference-admission-sources-20260910.json`, SHA256 of the
three archived bodies verified against that receipt):

* `transactions.py` (SHA256 `1fb6202062805d892a2a0100f46220d7a762e88a049ab9871b53f5159f6e0b25`)
  `validate_transaction` 586-670, `calculate_intrinsic_cost` 672-777,
  `calculate_effective_gas_price` 791-817, `calculate_max_gas_fee` 820-827,
  `check_nonce` 830-838, constants 56/68/76;
* `vm/gas.py` (SHA256 `41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c`)
  constants 86-87, 95, 101, 154-158;
* `fork.py` (SHA256 `dd0d069cbd0ba3e60e3f927c0e2d41be40958c6415be039ee29d6074eb2950da`)
  `check_transaction` 488-632 (sender lookup 551, effective price 553-555,
  max fee 556, blob fee 559-567, nonce 572, balance 574-575).

`SourceChecks` is an explicitly incomplete subset of those checks over
represented `RefundAccounting.Context` fields. It is NOT a certificate of
`validate_transaction` or `check_transaction` success. `admission` constructs
the old `TransactionFunding.Admission` from these source checks AND separate
`OldConsumerCompatibility`: a present pinned sender account and sufficient
coverage of the OLD blob tariff. `gate` only needs the source floor subset.

The source blob-price check is the distinct OPEN obligation
`source_blob_validation`: `calculate_blob_gas_price` at this Amsterdam pin uses
update fraction11684671, whereas pinned `header.getBlobGasprice` uses3338477.
These prices are not identified. `OldBlobFeeCovered` is a compatibility input,
not a transcribed source check or a derived consequence of source admission.
The exact numerical difference is retained in the independent review receipt;
no equality of tariffs or universal source-to-old funding implication is claimed.

Other OPEN bindings/checks: source gas and fee fields are unbounded Uint,
whereas pinned fields are UInt256; exact field correspondence and required
nontruncating conversions are NOT constructed here. Source `get_account` may
return a default empty account, so pinned presence is separately required.
Type4/set-code and authorization semantics are absent from the pinned transaction
type, not excluded from an accepted protocol domain by this adapter. Signature
recovery, source intrinsic.execution affordability/MAX, init-code size, blob
count/version/recipient constraints, block execution/state/blob capacity and
sender-code checks remain outside SourceChecks. No source-to-old intrinsicGas
implication, Python refinement or canonical history extraction is asserted. -/
namespace Eip8282.Audit.Integrator.ReferenceAdmissionExtraction
open EvmYul EvmYul.EVM
open NestedEvents
open TransactionAppendBudget (Receipt)
open ReachableCalls (Contract address)
open JournalInvariant (Invariant modelKind)
open RefundAccounting (Context)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-! ## Source constants -/

/-- transactions.py:56. -/
def TX_MAX_GAS_LIMIT : Nat := 16777216
/-- transactions.py:68. -/
def ACCESS_LIST_ADDRESS_FLOOR_TOKENS : Nat := 80
/-- transactions.py:76. -/
def ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS : Nat := 128
/-- gas.py:87. -/
def COLD_ACCOUNT_ACCESS : Nat := 3000
/-- gas.py:95. -/
def ACCOUNT_WRITE : Nat := 9000
/-- gas.py:101. -/
def CREATE_ACCESS : Nat := ACCOUNT_WRITE + COLD_ACCOUNT_ACCESS
/-- gas.py:154. -/
def TX_BASE : Nat := 12000
/-- gas.py:156. -/
def TX_VALUE_COST : Nat := 6000
/-- gas.py:157. -/
def TX_DATA_TOKEN_STANDARD : Nat := 4
/-- gas.py:158. -/
def TX_DATA_TOKEN_FLOOR : Nat := 16

/-! ## Calldata floor (`calculate_intrinsic_cost`) -/

/-- `recipient_execution_gas`, transactions.py:718-728: creation pays
`CREATE_ACCESS`; a non-self call pays `COLD_ACCOUNT_ACCESS` plus
`TX_VALUE_COST` when `tx.value > 0`; a self-transfer pays nothing. -/
def recipientExecution (tx : Transaction) (sender : AccountAddress) : Nat :=
  match tx.base.recipient with
  | none => CREATE_ACCESS
  | some recipient =>
    if recipient = sender then 0
    else COLD_ACCOUNT_ACCESS + (if 0 < tx.base.value.toNat then TX_VALUE_COST else 0)

/-- `tokens_in_access_list`, transactions.py:731-741: per entry the address
floor tokens plus storage-key floor tokens per slot (`[]` without a list). -/
def accessListFloorTokens (tx : Transaction) : Nat :=
  tx.getAccessList.foldl
    (fun tokens entry =>
      tokens + ACCESS_LIST_ADDRESS_FLOOR_TOKENS +
        entry.2.size * ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS) 0

/-- `data_floor_gas_cost`, transactions.py:753-765, in source order. -/
def calldataFloor (tx : Transaction) (sender : AccountAddress) : Nat :=
  let floorTokensInCalldata := tx.base.data.size * TX_DATA_TOKEN_STANDARD
  let totalFloorTokens := floorTokensInCalldata + accessListFloorTokens tx
  let baseExecutionGas := TX_BASE + recipientExecution tx sender
  totalFloorTokens * TX_DATA_TOKEN_FLOOR + baseExecutionGas

/-- The source floor is the already-reviewed transcription with the recipient
and access-token parameters now bound to their source computations. -/
theorem calldataFloor_eq (tx : Transaction) (sender : AccountAddress) :
    calldataFloor tx sender =
      ReferenceCalldataAdmission.floor tx.base.data.size (recipientExecution tx sender)
        (accessListFloorTokens tx) := rfl

/-! ## Fees (`calculate_effective_gas_price`, `calculate_max_gas_fee`) -/

/-- The per-gas cap used by `calculate_max_gas_fee`, transactions.py:826-827:
`max_fee_per_gas` for fee-market transactions, otherwise `gas_price`. -/
def feeCap (tx : Transaction) : Nat :=
  match tx with
  | .legacy t | .access t => t.gasPrice.toNat
  | .dynamic t | .blob t => t.maxFeePerGas.toNat

/-- The blob term added to `max_gas_fee` in fork.py:565-567 (blob transactions only). -/
def blobFeeCap (tx : Transaction) : Nat :=
  match tx with
  | .blob t => getTotalBlobGas tx * t.maxFeePerBlobGas.toNat
  | _ => 0

/-- `max_gas_fee` as compared against the balance in fork.py:556-575. -/
def maxGasFee (tx : Transaction) : Nat :=
  tx.base.gasLimit.toNat * feeCap tx + blobFeeCap tx

/-- transactions.py:627-630: fee-market priority cap not above the fee cap. -/
def PriorityCapped (tx : Transaction) : Prop :=
  match tx with
  | .legacy _ | .access _ => True
  | .dynamic t | .blob t => t.maxPriorityFeePerGas.toNat ≤ t.maxFeePerGas.toNat

/-- Separate OLD-consumer compatibility. This is not fork.py:559-563's
source blob check: the old and Amsterdam update fractions differ. -/
def OldBlobFeeCovered (header : BlockHeader) (tx : Transaction) : Prop :=
  match tx with
  | .blob t => header.getBlobGasprice ≤ t.maxFeePerBlobGas.toNat
  | _ => True

/-! ## The source admission record -/

/-- Selected source nonce, fee-cap, balance and calldata-floor clauses over
represented inputs. Incomplete: source blob validation and the other source
checks/bindings listed above remain OPEN; this is not validator success. -/
structure SourceChecks (c : Context) (account : Account .EVM) : Prop where
  /-- transactions.py:620-621: `U256(tx.nonce) >= U256(U64.MAX_VALUE)` raises. -/
  nonceOverflow : c.transaction.base.nonce.toNat < 2^64 - 1
  /-- transactions.py:830-838 via fork.py:572: sender nonce equals `tx.nonce`. -/
  nonceMatch : account.nonce.toNat = c.transaction.base.nonce.toNat
  /-- transactions.py:627-630. -/
  priorityCapped : PriorityCapped c.transaction
  /-- transactions.py:804-807 / 815-816: the fee cap covers `base_fee_per_gas`. -/
  baseCovered : c.baseFee ≤ feeCap c.transaction
  /-- fork.py:574-575: `balance < max_gas_fee + value` raises. -/
  balance : maxGasFee c.transaction + c.transaction.base.value.toNat ≤ account.balance.toNat
  /-- transactions.py:658-659: `calldata_floor > tx.gas` raises. -/
  floorGas : calldataFloor c.transaction c.sender ≤ c.transaction.base.gasLimit.toNat
  /-- transactions.py:664-667: `calldata_floor > TX_MAX_GAS_LIMIT` raises. -/
  floorMax : calldataFloor c.transaction c.sender ≤ TX_MAX_GAS_LIMIT

/-- Compatibility with the unchanged old evaluator consumers, not additional
source validation. Neither presence nor old blob coverage follows here from
SourceChecks or from an asserted equality of source and old tariffs. -/
structure OldConsumerCompatibility (c : Context) (account : Account .EVM) : Prop where
  /-- Source default-account lookup requires a separate representation adapter. -/
  sender : c.world.get? c.sender = some account
  /-- Old blob prepayment must fit the represented source maximum-fee budget. -/
  blobFeeCovered : OldBlobFeeCovered c.header c.transaction

/-! ## Pinned word arithmetic used by the price formulas -/

private theorem toNat_lt_size (a : UInt256) : a.toNat < UInt256.size := a.val.isLt

private theorem toNat_ofNat_of_lt {n : Nat} (h : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  show n % UInt256.size = n
  exact Nat.mod_eq_of_lt h

private theorem toNat_add_of_lt (a b : UInt256) (h : a.toNat + b.toNat < UInt256.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  show (a.toNat + b.toNat) % UInt256.size = _
  exact Nat.mod_eq_of_lt h

private theorem toNat_sub_of_le (a b : UInt256) (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  show (a.val - b.val).val = a.val.val - b.val.val
  exact Fin.coe_sub_iff_le.mpr h

private theorem toNat_min (a b : UInt256) : (min a b).toNat = min a.toNat b.toNat := by
  show (if a ≤ b then a else b).toNat = _
  split
  · next h =>
    have h' : a.toNat ≤ b.toNat := h
    exact (Nat.min_eq_left h').symm
  · next h =>
    have h' : ¬ a.toNat ≤ b.toNat := h
    exact (Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h'))).symm

/-! ## Price/priority derived from the source formulas -/

/-- Legacy/access priority `gas_price - base_fee` never exceeds `gas_price`
once `gas_price >= base_fee` (transactions.py:815-817). -/
theorem legacy_priority_le (gasPrice : UInt256) (baseFee : Nat)
    (base : baseFee ≤ gasPrice.toNat) :
    (gasPrice - UInt256.ofNat baseFee).toNat ≤ gasPrice.toNat := by
  have hb := toNat_ofNat_of_lt (Nat.lt_of_le_of_lt base (toNat_lt_size gasPrice))
  rw [toNat_sub_of_le _ _ (by rw [hb]; exact base)]
  omega

/-- Fee-market pricing (transactions.py:804-813): with `max_fee >= base_fee`
the pinned `min` priority is at most `max_fee - base_fee`, so adding the
base fee neither wraps nor exceeds `max_fee`. -/
theorem dynamic_price_bounds (maxFee maxPriority : UInt256) (baseFee : Nat)
    (base : baseFee ≤ maxFee.toNat) :
    (min maxPriority (maxFee - UInt256.ofNat baseFee)).toNat ≤
        (min maxPriority (maxFee - UInt256.ofNat baseFee) + UInt256.ofNat baseFee).toNat ∧
      (min maxPriority (maxFee - UInt256.ofNat baseFee) + UInt256.ofNat baseFee).toNat ≤
        maxFee.toNat := by
  have hlt := toNat_lt_size maxFee
  have hb := toNat_ofNat_of_lt (Nat.lt_of_le_of_lt base hlt)
  have hsub : (maxFee - UInt256.ofNat baseFee).toNat = maxFee.toNat - baseFee := by
    rw [toNat_sub_of_le _ _ (by rw [hb]; exact base), hb]
  have hmin : (min maxPriority (maxFee - UInt256.ofNat baseFee)).toNat ≤ maxFee.toNat - baseFee := by
    rw [toNat_min, hsub]
    exact Nat.min_le_right _ _
  rw [toNat_add_of_lt _ _ (by rw [hb]; omega), hb]
  omega

theorem effectivePrice_le_feeCap (c : Context) (base : c.baseFee ≤ feeCap c.transaction) :
    c.effectivePrice.toNat ≤ feeCap c.transaction := by
  obtain ⟨fuel, world, baseFee, header, genesis, blocks, tx, sender⟩ := c
  cases tx with
  | legacy t => exact Nat.le_refl t.gasPrice.toNat
  | access t => exact Nat.le_refl t.gasPrice.toNat
  | dynamic t => exact (dynamic_price_bounds t.maxFeePerGas t.maxPriorityFeePerGas baseFee base).2
  | blob t => exact (dynamic_price_bounds t.maxFeePerGas t.maxPriorityFeePerGas baseFee base).2

theorem priorityFee_le_effectivePrice (c : Context) (base : c.baseFee ≤ feeCap c.transaction) :
    c.priorityFee.toNat ≤ c.effectivePrice.toNat := by
  obtain ⟨fuel, world, baseFee, header, genesis, blocks, tx, sender⟩ := c
  cases tx with
  | legacy t => exact legacy_priority_le t.gasPrice baseFee base
  | access t => exact legacy_priority_le t.gasPrice baseFee base
  | dynamic t => exact (dynamic_price_bounds t.maxFeePerGas t.maxPriorityFeePerGas baseFee base).1
  | blob t => exact (dynamic_price_bounds t.maxFeePerGas t.maxPriorityFeePerGas baseFee base).1

/-! ## Funding derived from the source balance check -/

/-- Old blob fee bounded by the represented maximum-fee term, conditional
on separate old-tariff compatibility; source blob admission alone is insufficient. -/
theorem blobFee_le (header : BlockHeader) (tx : Transaction)
    (covered : OldBlobFeeCovered header tx) : calcBlobFee header tx ≤ blobFeeCap tx := by
  cases tx with
  | blob t => exact Nat.mul_le_mul_left _ covered
  | legacy t => exact Nat.le_of_eq (Nat.zero_mul _)
  | access t => exact Nat.le_of_eq (Nat.zero_mul _)
  | dynamic t => exact Nat.le_of_eq (Nat.zero_mul _)

/-- The pinned prepayment is at most the source `max_gas_fee`. -/
theorem upfront_le (c : Context) (base : c.baseFee ≤ feeCap c.transaction)
    (blobs : OldBlobFeeCovered c.header c.transaction) :
    TransactionFunding.upfront c ≤ maxGasFee c.transaction :=
  Nat.add_le_add
    (Nat.mul_le_mul_left c.transaction.base.gasLimit.toNat (effectivePrice_le_feeCap c base))
    (blobFee_le c.header c.transaction blobs)

/-! ## Constructing the consumer inputs -/

/-- Construct the old consumer input from both independent records. -/
theorem admission {c : Context} {account : Account .EVM}
    (v : SourceChecks c account) (compat : OldConsumerCompatibility c account) :
    TransactionFunding.Admission c account :=
  { sender := compat.sender
    funded := by
      have hupfront := upfront_le c v.baseCovered compat.blobFeeCovered
      have hbalance := v.balance
      omega
    nonce := by
      rw [v.nonceMatch]
      exact v.nonceOverflow
    priority := priorityFee_le_effectivePrice c v.baseCovered }

/-- The calldata-floor gate with its parameters bound to the source values. -/
theorem gate {c : Context} {account : Account .EVM} (v : SourceChecks c account) :
    ReferenceCalldataAdmission.Gate c.transaction.base.data.size
      (recipientExecution c.transaction c.sender) (accessListFloorTokens c.transaction) := by
  unfold ReferenceCalldataAdmission.Gate
  rw [← calldataFloor_eq]
  exact v.floorMax

/-! ## Applying the current consumers -/

theorem append {initial before : World} {receipts : List Receipt} {credits : Nat}
    (history : ActualJournalHistory.Trace initial receipts credits before)
    (r : Receipt) (linked : r.call.world = before) (account : Account .EVM)
    (validated : SourceChecks r.call account)
    (compat : OldConsumerCompatibility r.call account)
    (resources : 5*(r.call.entryGas.toNat+1) ≤ r.call.fuel) :
    ActualJournalHistory.Trace initial (receipts++[r]) credits r.world :=
  ReferenceAdmissionHistory.append history r linked account (admission validated compat)
    (gate validated) resources

theorem receipt_effects {kind : Contract} {genesis : World} {credits budget : Nat}
    (r : Receipt) {account : Account .EVM}
    (history : FundingHistory.Trace genesis credits r.call.world)
    (validated : SourceChecks r.call account)
    (compat : OldConsumerCompatibility r.call account)
    (funds : TransferFunding.worldFunds genesis+credits < FundedDomain.fundingCeiling)
    (resources : 5*(r.call.entryGas.toNat+1) ≤ r.call.fuel)
    (invariant : Invariant kind budget r.call.world)
    (bound : budget+NestedJournalBudget.events r < 2^128)
    (queue : JournalPathQueues.Queue kind)
    (represented : QueueInvariant.Represents (modelKind kind)
      (SystemSpec.worldSlot r.call.world (address kind)) queue) :
    TransactionCommittedEffects.Effects kind r queue :=
  ReferenceAdmissionHistory.receipt_effects r history (admission validated compat) (gate validated)
    funds resources invariant bound queue represented

/-! ## AdmissionExtraction tests

Kernel-checked concrete values of the transcribed source functions. Each is a
kill-line for a one-constant mutation of the corresponding definition. -/
namespace AdmissionExtractionTest

def alice : AccountAddress := ⟨1, by decide⟩
def bob : AccountAddress := ⟨2, by decide⟩

def legacy (recipient : Option AccountAddress) (value : UInt256) (data : ByteArray)
    (gasPrice : UInt256) : Transaction :=
  .legacy
    { nonce := ⟨0⟩, gasLimit := ⟨30000⟩, recipient := recipient, value := value,
      r := .empty, s := .empty, data := data, gasPrice := gasPrice, w := ⟨27⟩ }

def dynamic (maxFeePerGas maxPriorityFeePerGas : UInt256)
    (accessList : List (AccountAddress × Array UInt256)) : Transaction :=
  .dynamic
    { nonce := ⟨0⟩, gasLimit := ⟨21000⟩, recipient := some bob, value := ⟨0⟩,
      r := .empty, s := .empty, data := .empty, chainId := ⟨1⟩, accessList := accessList,
      yParity := ⟨0⟩, maxFeePerGas := maxFeePerGas, maxPriorityFeePerGas := maxPriorityFeePerGas }

def blob (maxFeePerBlobGas : UInt256) (hashes : List ByteArray) : Transaction :=
  .blob
    { nonce := ⟨0⟩, gasLimit := ⟨21000⟩, recipient := some bob, value := ⟨0⟩,
      r := .empty, s := .empty, data := .empty, chainId := ⟨1⟩, accessList := [],
      yParity := ⟨0⟩, maxFeePerGas := ⟨100⟩, maxPriorityFeePerGas := ⟨10⟩,
      maxFeePerBlobGas := maxFeePerBlobGas, blobVersionedHashes := hashes }

def context (tx : Transaction) (baseFee : Nat) : Context :=
  { fuel := 0, world := ∅, baseFee, header := default, genesis := default, blocks := #[],
    transaction := tx, sender := alice }

/-- transactions.py:718-720 self-transfer branch: floor is `TX_BASE` only. -/
theorem selfTransfer_floor :
    calldataFloor (legacy (some alice) ⟨0⟩ .empty ⟨0⟩) alice = 12000 := by decide +kernel

/-- Non-self call with value: `12000 + 3000 + 6000`; without value `15000`. -/
theorem valueCall_floor :
    calldataFloor (legacy (some bob) ⟨1⟩ .empty ⟨0⟩) alice = 21000 ∧
      calldataFloor (legacy (some bob) ⟨0⟩ .empty ⟨0⟩) alice = 15000 := by decide +kernel

/-- Creation with two calldata bytes: `2*4*16 + 12000 + 12000`. -/
theorem create_floor :
    calldataFloor (legacy none ⟨0⟩ (ByteArray.mk #[1, 0]) ⟨0⟩) alice = 24128 := by decide +kernel

/-- One access-list entry with two slots: `80 + 2*128` floor tokens, times 16. -/
theorem accessList_floor :
    accessListFloorTokens (dynamic ⟨100⟩ ⟨10⟩ [(bob, #[⟨1⟩, ⟨2⟩])]) = 336 ∧
      calldataFloor (dynamic ⟨100⟩ ⟨10⟩ [(bob, #[⟨1⟩, ⟨2⟩])]) alice = 336*16 + 15000 := by
  decide +kernel

/-- `max_gas_fee` uses the fee cap, and the blob term is added for blob transactions. -/
theorem maxGasFee_values :
    maxGasFee (dynamic ⟨100⟩ ⟨10⟩ []) = 2100000 ∧
      maxGasFee (blob ⟨3⟩ [ByteArray.mk #[1]]) = 2100000 + 131072*3 ∧
      maxGasFee (legacy (some bob) ⟨0⟩ .empty ⟨7⟩) = 30000*7 := by
  decide +kernel

/-- Pinned pricing on the source fee-market formula: priority capped by
`max_fee - base_fee` (5) and effective price `base + priority` (100). -/
theorem dynamic_pricing :
    (context (dynamic ⟨100⟩ ⟨10⟩ []) 95).priorityFee.toNat = 5 ∧
      (context (dynamic ⟨100⟩ ⟨10⟩ []) 95).effectivePrice.toNat = 100 ∧
      (context (dynamic ⟨100⟩ ⟨10⟩ []) 80).priorityFee.toNat = 10 ∧
      (context (dynamic ⟨100⟩ ⟨10⟩ []) 80).effectivePrice.toNat = 90 := by
  decide +kernel

/-- Pinned legacy pricing: priority `gas_price - base_fee`, effective `gas_price`. -/
theorem legacy_pricing :
    (context (legacy (some bob) ⟨0⟩ .empty ⟨7⟩) 5).priorityFee.toNat = 2 ∧
      (context (legacy (some bob) ⟨0⟩ .empty ⟨7⟩) 5).effectivePrice.toNat = 7 := by
  decide +kernel

/-- The source floor gate on the pinned sample does not reach the different
old intrinsic base; `ReferenceIntrinsicGap` states the non-implication. -/
theorem floor_ne_old_intrinsic :
    calldataFloor (legacy (some alice) ⟨0⟩ .empty ⟨0⟩) alice ≠
      intrinsicGas (legacy (some alice) ⟨0⟩ .empty ⟨0⟩) := by decide +kernel

end AdmissionExtractionTest

#print axioms calldataFloor_eq
#print axioms effectivePrice_le_feeCap
#print axioms priorityFee_le_effectivePrice
#print axioms upfront_le
#print axioms admission
#print axioms gate
#print axioms append
#print axioms receipt_effects
#print axioms AdmissionExtractionTest.dynamic_pricing
#print axioms AdmissionExtractionTest.floor_ne_old_intrinsic
end Eip8282.Audit.Integrator.ReferenceAdmissionExtraction
