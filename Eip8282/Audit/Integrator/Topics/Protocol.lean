import Eip8282.Audit.Integrator.ActualJournalHistory
import Eip8282.Audit.Integrator.FundingHistory
import Eip8282.Audit.Integrator.Topics.Genesis
import Eip8282.Audit.Integrator.NestedProtectedJournal
import Eip8282.Audit.Integrator.SystemJournal

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ProtocolCreditEnvelope -/

/-! Conditional arithmetic over actual explicit credit operations.
Reference EL 0cc100eb190b64b23baba72dac0165652eaec252, CL
ad0058fd0d34c5dcf504fa51ea2f4f11077b9996; source hashes and exact lines:
audit/receipts/direct-protocol-credit-envelope-audit-20260910.md. No reference is adopted here.
Frontier fork.py:581-589 gives the miner/ommer batch bound (max two, age>=1).
Amsterdam blocks.py:62 and fork.py:1118 give uint64 Gwei withdrawal amounts.
Capella beacon-chain.md:138 gives cap16; phase0:473,1788 give uint64 slots.
OPEN producers: actual canonical PoW batch extraction, all-fork coverage,
withdrawal payload/cardinality/slot linkage, migration conservation, genesis
world correspondence. EL number is Uint: the PoW count bound is NOT its width.
-/
namespace Eip8282.Audit.Integrator.ProtocolCreditEnvelope
open EvmYul EvmYul.EVM
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def powMaximum : Nat := 14062500000000000000

def withdrawalMaximum : Nat := (2^64-1)*10^9

def envelope (pow withdrawals migrations : Nat) : Nat :=
  GenesisFundingInput.totalCredit + powMaximum*pow + withdrawalMaximum*withdrawals + migrations

/-- A batch retains every literal credited world, recipient and amount. -/
inductive CreditBatch : (AccountMap .EVM) → Nat → (AccountMap .EVM) → Prop where
  | nil (world : (AccountMap .EVM)) : CreditBatch world 0 world
  | cons {before after : (AccountMap .EVM)} {total : Nat}
      (recipient : AccountAddress) (amount : UInt256)
      (tail : CreditBatch (before.increaseBalance .EVM recipient amount) total after)
      :
      CreditBatch before (amount.toNat+total) after

private theorem batch_extend {initial before after : (AccountMap .EVM)} {credits total : Nat}
    (prior : FundingHistory.Trace initial credits before) (batch : CreditBatch before total after) :
    FundingHistory.Trace initial (credits+total) after := by
  induction batch generalizing credits with
  | nil => simpa using prior
  | cons recipient amount tail ih =>
    have h := ih (FundingHistory.Trace.next prior (.credit _ recipient amount))
    simpa only [Nat.add_assoc] using h

/-- Classifications and numeric bounds are inputs to be extracted from protocol
operations, never bounds on the resulting world's wealth. -/
inductive Ledger (initial : (AccountMap .EVM)) : Nat → Nat → Nat → Nat → (AccountMap .EVM) → Prop where
  | initial : Ledger initial 0 0 0 0 initial
  | conserving {p w s c : Nat} {before after : (AccountMap .EVM)}
      (prior : Ledger initial p w s c before) (step : FundingHistory.Step before 0 after) :
      Ledger initial p w s c after
  | pow {p w s c amount : Nat} {before after : (AccountMap .EVM)}
      (prior : Ledger initial p w s c before) (batch : CreditBatch before amount after)
      (bounded : amount ≤ powMaximum) : Ledger initial (p+1) w s (c+amount) after
  | withdrawal {p w s c : Nat} {before : (AccountMap .EVM)}
      (prior : Ledger initial p w s c before) (recipient : AccountAddress) (amount : UInt256)
      (bounded : amount.toNat ≤ withdrawalMaximum) :
      Ledger initial p (w+1) s (c+amount.toNat) (before.increaseBalance .EVM recipient amount)
  | migration {p w s c amount : Nat} {before after : (AccountMap .EVM)}
      (prior : Ledger initial p w s c before) (batch : CreditBatch before amount after) :
      Ledger initial p w (s+amount) (c+amount) after

theorem ledger_bound {initial world : (AccountMap .EVM)} {p w s c : Nat}
    (h : Ledger initial p w s c world) :
    FundingHistory.Trace initial c world ∧ c ≤ powMaximum*p + withdrawalMaximum*w + s := by
  induction h with
  | initial => exact ⟨.initial,by omega⟩
  | conserving prior step ih => exact ⟨by simpa using FundingHistory.Trace.next ih.1 step,ih.2⟩
  | pow prior batch bounded ih =>
    exact ⟨batch_extend ih.1 batch,by simp only [Nat.mul_add,Nat.mul_one]; omega⟩
  | withdrawal prior recipient amount bounded ih =>
    exact ⟨FundingHistory.Trace.next ih.1 (.credit _ recipient amount),by
      simp only [Nat.mul_add,Nat.mul_one]; omega⟩
  | migration prior batch ih => exact ⟨batch_extend ih.1 batch,by omega⟩

/-- Explicit count and migration obligations, not asserted protocol facts. -/
structure Counts (pow withdrawals migrations : Nat) : Prop where
  pow_count : pow ≤ 2^64
  withdrawal_count : withdrawals ≤ 16*2^64
  migration_conserving : migrations = 0

theorem numeric_envelope {p w s : Nat} (h : Counts p w s) : envelope p w s < 2^163 := by
  have hp := Nat.mul_le_mul_left powMaximum h.pow_count
  have hw := Nat.mul_le_mul_left withdrawalMaximum h.withdrawal_count
  have hn : GenesisFundingInput.totalCredit + powMaximum*2^64 + withdrawalMaximum*(16*2^64) < 2^163 := by
    rw [GenesisFundingInput.total_credit_exact]
    decide +kernel
  unfold envelope
  rw [GenesisFundingInput.total_credit_exact] at hn ⊢
  rw [h.migration_conserving, Nat.add_zero]
  exact lt_of_le_of_lt (Nat.add_le_add (Nat.add_le_add_left hp _) hw) hn

theorem below_ceiling : 2^163 < FundedDomain.fundingCeiling := by decide +kernel

theorem funding_budget {initial world : (AccountMap .EVM)} {p w s c : Nat}
    (ledger : Ledger initial p w s c world)
    (genesis : TransferFunding.worldFunds initial ≤ GenesisFundingInput.totalCredit)
    (counts : Counts p w s) :
    FundingHistory.Trace initial c world ∧
      TransferFunding.worldFunds initial+c < FundedDomain.fundingCeiling := by
  obtain ⟨trace,bound⟩ := ledger_bound ledger
  have hn := numeric_envelope counts
  have hb := below_ceiling
  unfold envelope at hn
  exact ⟨trace,by omega⟩

#print axioms ledger_bound
#print axioms numeric_envelope
#print axioms below_ceiling
#print axioms funding_budget
end Eip8282.Audit.Integrator.ProtocolCreditEnvelope

end

section

/-! ## ProtocolMigrationLedger -/

/-! A literal full-balance migration sweep creates no external credit.
Reference: audit/receipts/direct-reference-migration-deployment-sources-20260910.json,
DAO apply_dao and sequential move_ether. Every source balance is read from the
current world. Duplicate sources, recovery aliases and absent accounts are
allowed. Python state-diff and canonical DAO-list correspondence remain OPEN.
The optional checked-addition bound is derived from the pre-world sum, which
must itself be supplied by the independently justified funding ledger. -/
namespace Eip8282.Audit.Integrator.ProtocolMigrationLedger
open EvmYul EvmYul.EVM
open TransferFunding ProtocolCreditEnvelope
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def currentBalance (world : AccountMap .EVM) (source : AccountAddress) : UInt256 :=
  ((world.get? source).getD (default : Account .EVM)).balance

theorem current_balance (world : AccountMap .EVM) (source : AccountAddress) :
    (currentBalance world source).toNat = worldBalance world source := by
  unfold currentBalance worldBalance
  cases world.get? source <;> rfl

def sweep (recovery : AccountAddress) : List AccountAddress → AccountMap .EVM → AccountMap .EVM
  | [], world => world
  | source::rest, world => sweep recovery rest
      (ProtocolTransfer.transfer world source recovery (currentBalance world source))

theorem ledger {initial world : AccountMap .EVM} {p w s c : Nat}
    (prior : Ledger initial p w s c world) (sources : List AccountAddress) (recovery : AccountAddress) :
    Ledger initial p w s c (sweep recovery sources world) := by
  induction sources generalizing world with
  | nil => exact prior
  | cons source rest ih =>
    apply ih
    exact Ledger.conserving prior (.transfer world source recovery (currentBalance world source)
      (by rw [current_balance]))

theorem funding {initial world : AccountMap .EVM} {credits : Nat}
    (prior : FundingHistory.Trace initial credits world)
    (sources : List AccountAddress) (recovery : AccountAddress) :
    FundingHistory.Trace initial credits (sweep recovery sources world) := by
  induction sources generalizing world with
  | nil => exact prior
  | cons source rest ih =>
    apply ih
    simpa only [Nat.add_zero] using FundingHistory.Trace.next prior
      (.transfer world source recovery (currentBalance world source) (by rw [current_balance]))

theorem frame (world : AccountMap .EVM) (sources : List AccountAddress)
    (recovery protectedAddr : AccountAddress) :
    CodeStorageFrame.Frame world (sweep recovery sources world) protectedAddr := by
  induction sources generalizing world with
  | nil => exact CodeStorageFrame.refl _ _
  | cons source rest ih =>
    exact CodeStorageFrame.trans (ProtocolTransfer.frame world source recovery protectedAddr _)
      (ih _)

/-- The recipient is read after debit. Thus aliases satisfy the same bound. -/
theorem recipient_add_bound (world : AccountMap .EVM) (source recipient : AccountAddress)
    (amount : UInt256) (funded : amount.toNat ≤ worldBalance world source) :
    worldBalance (ProtocolTransfer.debit world source amount) recipient + amount.toNat ≤
      worldFunds world := by
  have hd := ProtocolTransfer.debit_funds world source amount funded
  have hr := balance_le_funds (ProtocolTransfer.debit world source amount) recipient
  omega

theorem checked_add_fits (world : AccountMap .EVM) (source recipient : AccountAddress)
    (amount : UInt256) (funded : amount.toNat ≤ worldBalance world source)
    (total : worldFunds world < UInt256.size) :
    (currentBalance (ProtocolTransfer.debit world source amount) recipient).toNat + amount.toNat < UInt256.size := by
  rw [current_balance]
  exact lt_of_le_of_lt (recipient_add_bound world source recipient amount funded) total

#print axioms ledger
#print axioms funding
#print axioms frame
#print axioms recipient_add_bound
#print axioms checked_add_fits
end Eip8282.Audit.Integrator.ProtocolMigrationLedger

end

section

/-! ## ProtocolPowCount -/

/-! Owner: Dewey, protocol input arithmetic. Proposed mainnet policy only.
Reference EL 0cc100eb190b64b23baba72dac0165652eaec252 and CL
ad0058fd0d34c5dcf504fa51ea2f4f11077b9996; source audit planned at
audit/receipts/direct-pow-count-producer-dewey-20260910.md.
The natural cumulative-difficulty linkage and canonical reward-batch linkage
are explicit inputs. No block-number width, terminal-TD upper bound, fork
selection, hash lookup correctness or protocol adoption is asserted here. -/
namespace Eip8282.Audit.Integrator.ProtocolPowCount
set_option autoImplicit false

def minimumDifficulty : Nat := 131072
def mainnetTTD : Nat := 58750000000000000000000
def maximumCount : Nat := 448226928710937500

/-- External selection of the proposed default policy, not a proved config loader.
The natural hash encoding is zero precisely for the disabled override input. -/
structure MainnetZeroOverride (configuredTTD configuredHash : Nat) : Prop where
  threshold : configuredTTD = mainnetTTD
  no_override : configuredHash = 0

/-- The list excludes genesis and the one terminal crossing block. -/
theorem difficulty_sum_lower (difficulties : List Nat)
    (valid : ∀ d ∈ difficulties, minimumDifficulty ≤ d) :
    minimumDifficulty * difficulties.length ≤ difficulties.sum := by
  induction difficulties with
  | nil => simp
  | cons d ds ih =>
    have hd := valid d (by simp)
    have hs := ih (fun x hx => valid x (by simp [hx]))
    simp only [List.length_cons, List.sum_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- Genesis contributes to TD but is not a reward batch. Only the parent's TD
is bounded: the terminal block may overshoot the threshold arbitrarily. -/
theorem count_of_terminal_parent (difficulties : List Nat)
    (genesisDifficulty parentTD : Nat)
    (valid : ∀ d ∈ difficulties, minimumDifficulty ≤ d)
    (linked : parentTD = genesisDifficulty + difficulties.sum)
    (below : parentTD < mainnetTTD) :
    difficulties.length + 1 ≤ maximumCount := by
  have hs := difficulty_sum_lower difficulties valid
  unfold minimumDifficulty at hs
  unfold mainnetTTD at below
  unfold maximumCount
  omega

theorem maximum_lt_uint64 : maximumCount < 2^64 := by decide +kernel

/-- A ledger prefix may contain fewer batches than the complete terminal
ancestry. The link is to canonical non-genesis batches, not ommer count. -/
theorem reward_count (difficulties : List Nat)
    (genesisDifficulty parentTD configuredTTD configuredHash batches : Nat)
    (policy : MainnetZeroOverride configuredTTD configuredHash)
    (valid : ∀ d ∈ difficulties, minimumDifficulty ≤ d)
    (linked : parentTD = genesisDifficulty + difficulties.sum)
    (below : parentTD < configuredTTD)
    (batchLink : batches ≤ difficulties.length + 1) : batches ≤ 2^64 := by
  have hb := count_of_terminal_parent difficulties genesisDifficulty parentTD valid linked
    (by simpa only [policy.threshold] using below)
  exact Nat.le_trans (Nat.le_trans batchLink hb) (Nat.le_of_lt maximum_lt_uint64)

/-- Populate the count interface while leaving withdrawal and migration
producers independent. `batches` must be the same index used by the ledger. -/
theorem counts (difficulties : List Nat)
    (genesisDifficulty parentTD configuredTTD configuredHash batches withdrawals migrations : Nat)
    (policy : MainnetZeroOverride configuredTTD configuredHash)
    (valid : ∀ d ∈ difficulties, minimumDifficulty ≤ d)
    (linked : parentTD = genesisDifficulty + difficulties.sum)
    (below : parentTD < configuredTTD)
    (batchLink : batches ≤ difficulties.length + 1)
    (withdrawalBound : withdrawals ≤ 16*2^64) (migrationConserving : migrations = 0) :
    ProtocolCreditEnvelope.Counts batches withdrawals migrations :=
  ⟨reward_count difficulties genesisDifficulty parentTD configuredTTD configuredHash batches
    policy valid linked below batchLink, withdrawalBound, migrationConserving⟩

#print axioms difficulty_sum_lower
#print axioms count_of_terminal_parent
#print axioms maximum_lt_uint64
#print axioms reward_count
#print axioms counts
end Eip8282.Audit.Integrator.ProtocolPowCount

end

section

/-! ## ProtocolPowRewards -/

/-! Literal PoW reward batches at proposed EL reference
0cc100eb190b64b23baba72dac0165652eaec252. Archived full bodies/hashes:
audit/receipts/direct-reference-migration-deployment-sources-20260910.json.
Frontier fork.py:58,516,545-547,581-589; Byzantium/Constantinople:62,597-604.
OPEN adapters: selected fork era, canonical miner and ommer beneficiaries,
validated cardinality/ages, checked recipient addition and EL world transport.
No aggregate reward bound or canonical occurrence is assumed. -/
namespace Eip8282.Audit.Integrator.ProtocolPowRewards
open EvmYul EvmYul.EVM
open ProtocolCreditEnvelope
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

inductive Era where | frontier | byzantium | constantinople

def base : Era → Nat
  | .frontier => 5000000000000000000
  | .byzantium => 3000000000000000000
  | .constantinople => 2000000000000000000

structure Ommer where
  beneficiary : AccountAddress
  age : Nat

structure Admission (ommers : List Ommer) : Prop where
  cardinality : ommers.length ≤ 2
  ages : ∀ o ∈ ommers, 1 ≤ o.age ∧ o.age ≤ 6

def minerReward (era : Era) (ommers : List Ommer) : Nat :=
  base era + ommers.length*(base era/32)

def ommerReward (era : Era) (o : Ommer) : Nat := ((8-o.age)*base era)/8

def payments (era : Era) (miner : AccountAddress) (ommers : List Ommer) : List (AccountAddress × Nat) :=
  (miner,minerReward era ommers)::ommers.map (fun o => (o.beneficiary,ommerReward era o))

private theorem ommer_bound (era : Era) (o : Ommer) (age : 1 ≤ o.age) :
    ommerReward era o ≤ 7*base era/8 := by
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul_right _ (by omega)

private theorem ommer_sum (era : Era) (ommers : List Ommer)
    (ages : ∀ o ∈ ommers, 1 ≤ o.age) :
    (ommers.map (ommerReward era)).sum ≤ ommers.length*(7*base era/8) := by
  induction ommers with
  | nil => simp
  | cons o rest ih =>
    have ho := ommer_bound era o (ages o (by simp))
    have hr := ih (fun a ha => ages a (by simp [ha]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem reward_bound (era : Era) (miner : AccountAddress) (ommers : List Ommer)
    (admitted : Admission ommers) :
    ((payments era miner ommers).map Prod.snd).sum ≤ powMaximum := by
  have hs := ommer_sum era ommers (fun o ho => (admitted.ages o ho).1)
  have hn := admitted.cardinality
  have hminer := Nat.mul_le_mul_right (base era/32) hn
  have hommer := Nat.mul_le_mul_right (7*base era/8) hn
  simp only [payments,List.map_cons,List.map_map,List.sum_cons,Function.comp_def]
  change minerReward era ommers + (ommers.map (ommerReward era)).sum ≤ powMaximum
  unfold minerReward
  have hb : base era + 2*(base era/32) + 2*(7*base era/8) ≤ powMaximum := by
    cases era <;> decide +kernel
  omega

/-- Execute every listed payment in order; collisions do not drop payments. -/
def pay : List (AccountAddress × Nat) → AccountMap .EVM → AccountMap .EVM
  | [], world => world
  | (recipient,amount)::rest, world =>
    pay rest (world.increaseBalance .EVM recipient (UInt256.ofNat amount))

private theorem pay_batch (items : List (AccountAddress × Nat)) (world : AccountMap .EVM)
    (fit : ∀ item ∈ items, item.2 < UInt256.size) :
    CreditBatch world (items.map Prod.snd).sum (pay items world) := by
  induction items generalizing world with
  | nil => exact .nil world
  | cons item rest ih =>
    obtain ⟨recipient,amount⟩ := item
    have hfit := fit (recipient,amount) (by simp)
    have he : (UInt256.ofNat amount).toNat = amount := Nat.mod_eq_of_lt hfit
    have batch := CreditBatch.cons (before := world) recipient (UInt256.ofNat amount)
      (ih _ (fun x hx => fit x (by simp [hx])))
    simpa only [pay,List.map_cons,List.sum_cons,he] using batch

theorem batch (era : Era) (miner : AccountAddress) (ommers : List Ommer)
    (admitted : Admission ommers) (world : AccountMap .EVM) :
    CreditBatch world ((payments era miner ommers).map Prod.snd).sum
      (pay (payments era miner ommers) world) := by
  apply pay_batch
  intro item hi
  have hm : item.2 ∈ (payments era miner ommers).map Prod.snd := List.mem_map.mpr ⟨item,hi,rfl⟩
  have hb := reward_bound era miner ommers admitted
  have hs := List.le_sum_of_mem hm
  have hf : powMaximum < UInt256.size := by decide +kernel
  omega

theorem ledger {initial world : AccountMap .EVM} {p w s c : Nat}
    (prior : Ledger initial p w s c world) (era : Era) (miner : AccountAddress)
    (ommers : List Ommer) (admitted : Admission ommers) :
    Ledger initial (p+1) w s (c+((payments era miner ommers).map Prod.snd).sum)
      (pay (payments era miner ommers) world) :=
  Ledger.pow prior (batch era miner ommers admitted world) (reward_bound era miner ommers admitted)

#print axioms reward_bound
#print axioms batch
#print axioms ledger
end Eip8282.Audit.Integrator.ProtocolPowRewards

end

section

/-! ## ProtocolSystemCalls -/

/-! Actual pinned-EVM SYSTEM progress and safety, with explicit counterpart
inputs for proposed Amsterdam. Reference dispatcher: EL
0cc100eb190b64b23baba72dac0165652eaec252, fork.py:729-786,904-923;
audit/receipts/direct-reference-migration-deployment-sources-20260910.json.
OPEN: canonical scheduling/adoption, base-fee word conversion, empty substate
and original-world mapping, installed code/history, and Amsterdam dual-pool
execution/state-gas correspondence. A 30M numeric grant is not that transport.
-/
namespace Eip8282.Audit.Integrator.ProtocolSystemCalls
open EvmYul EvmYul.EVM
open ReachableCalls (Contract Transition address runtime)
open JournalInvariant (modelKind)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def call (kind : Contract) (world : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (gasPrice : UInt256)
    (fuel : Nat) (data : ByteArray) : MessageCall.Context :=
  { fuel := fuel, created := ∅, genesis := genesis, blocks := blocks,
    world := world, originalWorld := world, substate := default,
    caller := Eip8282.Audit.EvmRunner.sysAddr, origin := Eip8282.Audit.EvmRunner.sysAddr,
    target := address kind, code := runtime kind, gas := ⟨30000000⟩,
    gasPrice := gasPrice, value := ⟨0⟩, apparentValue := ⟨0⟩,
    calldata := data, depth := 0, header := header, permission := true, blobHashes := [] }

theorem completes (kind : Contract) (world : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (gasPrice : UInt256)
    (fuel : Nat) (data : ByteArray) (installed : JournalInvariant.CodeAt kind world)
    (resources : 8503 ≤ fuel) :
    ∃ after, ∃ t : Transition kind world after,
      t.call = call kind world genesis blocks header gasPrice fuel data ∧ t.success = true := by
  let c := call kind world genesis blocks header gasPrice fuel data
  have hc : c.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
    cases kind <;> rfl
  obtain ⟨old,ho,hcode⟩ := installed
  obtain ⟨created,after,gas,ss,out,hr⟩ := SystemProgress.pinned (modelKind kind) c hc rfl
    ⟨old,ho⟩ rfl (by change 2500000 ≤ 30000000; decide +kernel) resources
  let t : Transition kind world after :=
    { call := c, pinned := ⟨rfl,rfl,⟨old,ho,hcode⟩,rfl⟩,
      pre := rfl, created := created, gas := gas, substate := ss,
      success := true, output := out, executed := hr }
  exact ⟨after,t,rfl,rfl⟩

theorem guarantees (kind : Contract) (world : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (gasPrice : UInt256)
    (fuel : Nat) (data : ByteArray) {budget : Nat}
    (initial : JournalInvariant.Invariant kind budget world) (bound : budget < 2^128)
    (fit : data.size < UInt256.size) (resources : 8503 ≤ fuel) :
    ∃ after, ∃ t : Transition kind world after,
      t.call = call kind world genesis blocks header gasPrice fuel data ∧ t.success = true ∧
      JournalInvariant.Invariant kind budget after ∧
      NestedProtectedJournal.Observed kind t.call t.created after t.substate t.success t.output := by
  obtain ⟨after,t,hc,hs⟩ := completes kind world genesis blocks header gasPrice fuel data initial.1 resources
  have hcaller : t.call.caller = Eip8282.Audit.EvmRunner.sysAddr := by rw [hc]; rfl
  have hvalue : t.call.value = ⟨0⟩ := by rw [hc]; rfl
  have hfit : t.call.calldata.size < UInt256.size := by rw [hc]; exact fit
  exact ⟨after,t,hc,hs,SystemJournal.preserves t hcaller hvalue hfit bound initial,
    JournalGuarantees.completed t initial bound hfit⟩

/-- Empty calldata covers the normal dispatch/activation shape; actual fork
scheduling and state-gas resources are still separate adapter obligations. -/
theorem empty_guarantees (kind : Contract) (world : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (gasPrice : UInt256)
    (fuel : Nat) {budget : Nat}
    (initial : JournalInvariant.Invariant kind budget world) (bound : budget < 2^128)
    (resources : 8503 ≤ fuel) :
    ∃ after, ∃ t : Transition kind world after,
      t.call = call kind world genesis blocks header gasPrice fuel ByteArray.empty ∧ t.success = true ∧
      JournalInvariant.Invariant kind budget after ∧
      NestedProtectedJournal.Observed kind t.call t.created after t.substate t.success t.output :=
  guarantees kind world genesis blocks header gasPrice fuel ByteArray.empty initial bound
    (by decide +kernel) resources

#print axioms completes
#print axioms guarantees
#print axioms empty_guarantees
end Eip8282.Audit.Integrator.ProtocolSystemCalls

end

section

/-! ## ProtocolSystemSequence -/

/-! The proposed empty Deposit-then-Exit SYSTEM sequence runs in one actual
world history. The first call supplies the second call's pre-world and preserves
the other journal. This is a named conditional schedule, not protocol adoption
or an equation with the canonical block processor. -/
namespace Eip8282.Audit.Integrator.ProtocolSystemSequence
open EvmYul EvmYul.EVM
open ReachableCalls (Contract Transition)
open JournalInvariant (Invariant)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

structure EmptyPair (before after : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (gasPrice : UInt256) (fuel : Nat) where
  middle : AccountMap .EVM
  deposit : Transition .deposit before middle
  exit : Transition .exit middle after
  depositCall : deposit.call = ProtocolSystemCalls.call .deposit before genesis blocks header gasPrice fuel ByteArray.empty
  exitCall : exit.call = ProtocolSystemCalls.call .exit middle genesis blocks header gasPrice fuel ByteArray.empty
  depositSuccess : deposit.success = true
  exitSuccess : exit.success = true

/-- The two successful calls are constructed in order, not supplied as desired
endpoints. Both protected invariants are retained after both calls. -/
theorem completes (before : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (gasPrice : UInt256) (fuel : Nat)
    (budgets : Contract → Nat) (initial : ∀ kind, Invariant kind (budgets kind) before)
    (bounds : ∀ kind, budgets kind < 2^128) (resources : 8503 ≤ fuel) :
    ∃ after, ∃ pair : EmptyPair before after genesis blocks header gasPrice fuel,
      (∀ kind, Invariant kind (budgets kind) after) ∧
      NestedProtectedJournal.Observed .deposit pair.deposit.call pair.deposit.created pair.middle
        pair.deposit.substate pair.deposit.success pair.deposit.output ∧
      NestedProtectedJournal.Observed .exit pair.exit.call pair.exit.created after
        pair.exit.substate pair.exit.success pair.exit.output := by
  obtain ⟨middle,dep,depCall,depSuccess,depInv,depGuards⟩ :=
    ProtocolSystemCalls.empty_guarantees .deposit before genesis blocks header gasPrice fuel
      (initial .deposit) (bounds .deposit) resources
  have depSender : dep.call.caller = Eip8282.Audit.EvmRunner.sysAddr := by rw [depCall]; rfl
  have depValue : dep.call.value = ⟨0⟩ := by rw [depCall]; rfl
  have depFit : dep.call.calldata.size < UInt256.size := by rw [depCall]; change 0 < UInt256.size; decide +kernel
  have midInv : ∀ kind, Invariant kind (budgets kind) middle :=
    fun kind => SystemJournal.preserves dep depSender depValue depFit (bounds kind) (initial kind)
  obtain ⟨after,ext,extCall,extSuccess,extInv,extGuards⟩ :=
    ProtocolSystemCalls.empty_guarantees .exit middle genesis blocks header gasPrice fuel
      (midInv .exit) (bounds .exit) resources
  have extSender : ext.call.caller = Eip8282.Audit.EvmRunner.sysAddr := by rw [extCall]; rfl
  have extValue : ext.call.value = ⟨0⟩ := by rw [extCall]; rfl
  have extFit : ext.call.calldata.size < UInt256.size := by rw [extCall]; change 0 < UInt256.size; decide +kernel
  let pair : EmptyPair before after genesis blocks header gasPrice fuel :=
    ⟨middle,dep,ext,depCall,extCall,depSuccess,extSuccess⟩
  exact ⟨after,pair,fun kind => SystemJournal.preserves ext extSender extValue extFit
    (bounds kind) (midInv kind),depGuards,extGuards⟩

/-- Extend the same actual journal history by the ordered pair. SYSTEM does
not add a transaction receipt, external credit or append-work budget. -/
theorem append {before after initial : AccountMap .EVM} {genesis : BlockHeader}
    {blocks : ProcessedBlocks} {header : BlockHeader} {gasPrice : UInt256} {fuel : Nat}
    (pair : EmptyPair before after genesis blocks header gasPrice fuel)
    {receipts : List TransactionAppendBudget.Receipt} {credits : Nat}
    (history : ActualJournalHistory.Trace initial receipts credits before) :
    ActualJournalHistory.Trace initial receipts credits after := by
  have hd := ActualJournalHistory.Trace.system history pair.deposit
    (by rw [pair.depositCall]; rfl) (by rw [pair.depositCall]; rfl)
    (by rw [pair.depositCall]; change 0 < UInt256.size; decide +kernel)
  exact ActualJournalHistory.Trace.system hd pair.exit
    (by rw [pair.exitCall]; rfl) (by rw [pair.exitCall]; rfl)
    (by rw [pair.exitCall]; change 0 < UInt256.size; decide +kernel)

/-- An actual initialized prefix and the constructed ordered SYSTEM calls
remain one history, with the same credits and receipt list. Canonical dispatch
extraction and policy acceptance are still external producers. -/
theorem extends_history {before initial : AccountMap .EVM} (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (gasPrice : UInt256) (fuel : Nat)
    {receipts : List TransactionAppendBudget.Receipt} {credits : Nat}
    (history : ActualJournalHistory.Trace initial receipts credits before)
    (budgets : Contract → Nat) (invariants : ∀ kind, Invariant kind (budgets kind) before)
    (bounds : ∀ kind, budgets kind < 2^128) (resources : 8503 ≤ fuel) :
    ∃ after, ∃ pair : EmptyPair before after genesis blocks header gasPrice fuel,
      ActualJournalHistory.Trace initial receipts credits after ∧
      (∀ kind, Invariant kind (budgets kind) after) ∧
      NestedProtectedJournal.Observed .deposit pair.deposit.call pair.deposit.created pair.middle
        pair.deposit.substate pair.deposit.success pair.deposit.output ∧
      NestedProtectedJournal.Observed .exit pair.exit.call pair.exit.created after
        pair.exit.substate pair.exit.success pair.exit.output := by
  obtain ⟨after,pair,finalInv,dep,ext⟩ := completes before genesis blocks header gasPrice fuel
    budgets invariants bounds resources
  exact ⟨after,pair,append pair history,finalInv,dep,ext⟩

#print axioms completes
#print axioms append
#print axioms extends_history
end Eip8282.Audit.Integrator.ProtocolSystemSequence

end
