import Eip8282.Audit.Integrator.Topics.Protocol
import Eip8282.Audit.Integrator.Topics.ReferenceSystem2

/-! # Pinned source SYSTEM dispatch, extracted into the three consumers

Reference dispatcher: EL 0cc100eb190b64b23baba72dac0165652eaec252,
src/ethereum/forks/amsterdam/fork.py SHA256
dd0d069cbd0ba3e60e3f927c0e2d41be40958c6415be039ee29d6074eb2950da
(audit/receipts/direct-reference-migration-deployment-sources-20260910.json).
Lines 110-133 fix SYSTEM_ADDRESS, SYSTEM_TRANSACTION_GAS = 30000000,
SYSTEM_MAX_SSTORES_PER_CALL = 16 and both builder addresses. Lines 753-777
(`process_unchecked_system_transaction`) construct one fresh transaction
state and one transaction environment: origin SYSTEM, recipient = target,
no create, value 0, the data argument, gas limit and execution grant
30000000, state reservoir STORAGE_SET*16 (vm/gas.py:49-69, 64*1530 = 97920),
calldata floor 0, empty access lists, no paid writes, empty blob hashes and
authorizations. Lines 904-926 (`apply_body`) dispatch the checked builder
Deposit call and then the checked builder Exit call, both with empty data.

`SystemTransaction` transcribes that environment; `unchecked` is the
constructor of lines 753-777 and `mandatoryDeposit`/`mandatoryExit` are the
two call sites of lines 904-920. `frame` maps the source environment to the
actual message-call context, reading the installed code by account lookup
exactly as lines 703-706 do. `blockParent` is the storage projection of the
block state the fresh transaction state is parented on, and `freshTx` is that
fresh state. Nothing below assumes the extracted context equals the consumer
context: `frame_call` derives that identity from installed code alone, and
every consumer premise (SYSTEM caller word, permission, dual-pool grant,
empty calldata, storage relation, warm set, owner, created set) is derived
from the transcribed fields. Fork scheduling, adoption, base-fee word
conversion and the Python evaluator itself remain outside this module. -/
namespace Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction
open EvmYul EvmYul.EVM
open ReachableCalls (Contract Transition PinnedCall address runtime)
open JournalInvariant (Invariant CodeAt modelKind)
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Correspondence (runtimeCode)
open ReferenceRuntimeView ReferenceSourceReadings SystemExecutionResources SystemMeterResources
open ReferenceSystemSourcePayment
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

/-! ## Source constants (fork.py:110-133, vm/gas.py:49-69) -/

/-- `SYSTEM_TRANSACTION_GAS`, fork.py:114. -/
def systemTransactionGas : Nat := 30000000

/-- `SYSTEM_MAX_SSTORES_PER_CALL`, fork.py:115. -/
def systemMaxSstoresPerCall : Nat := 16

/-- `StateGasCosts.STORAGE_SET`, vm/gas.py:49-69. -/
def storageSet : Nat := 97920

/-! ## Transcribed transaction environment (fork.py:753-777) -/

/-- The fields of `vm.TransactionEnvironment` that the SYSTEM frame reads,
plus the fresh `TransactionState` projection. Authorizations, index and hash
are `()`/`None` in the source and have no frame effect here. -/
structure SystemTransaction where
  origin : AccountAddress
  recipient : AccountAddress
  isCreate : Bool
  data : ByteArray
  value : UInt256
  gasLimit : Nat
  effectiveGasPrice : UInt256
  executionGasGrant : Nat
  stateGasReservoir : Nat
  calldataFloor : Nat
  accessListAddresses : Set AccountAddress
  accessListStorageKeys : Warm
  blobVersionedHashes : List ByteArray
  state : ReferenceStorageView.Tx

/-- `TransactionState(parent=block_env.state)`: no writes, no created
accounts, no tracked reads yet. -/
def freshTx : ReferenceStorageView.Tx :=
  { writes := fun _ _ => none, created := ∅, reads := ∅ }

/-- `process_unchecked_system_transaction`, fork.py:753-777. Only the target
and data are call-site inputs; the base fee is the block environment's. -/
def unchecked (target : AccountAddress) (data : ByteArray) (baseFee : UInt256) :
    SystemTransaction :=
  { origin := Eip8282.Audit.EvmRunner.sysAddr, recipient := target, isCreate := false,
    data := data, value := ⟨0⟩, gasLimit := systemTransactionGas,
    effectiveGasPrice := baseFee, executionGasGrant := systemTransactionGas,
    stateGasReservoir := storageSet*systemMaxSstoresPerCall, calldataFloor := 0,
    accessListAddresses := ∅, accessListStorageKeys := ∅, blobVersionedHashes := [],
    state := freshTx }

/-- fork.py:904-908: the checked builder Deposit call with `data=b""`. -/
def mandatoryDeposit (baseFee : UInt256) : SystemTransaction :=
  unchecked (address .deposit) ByteArray.empty baseFee

/-- fork.py:916-920: the checked builder Exit call with `data=b""`. -/
def mandatoryExit (baseFee : UInt256) : SystemTransaction :=
  unchecked (address .exit) ByteArray.empty baseFee

/-- The two call sites in dispatch order. -/
def mandatory (kind : Contract) (baseFee : UInt256) : SystemTransaction :=
  unchecked (address kind) ByteArray.empty baseFee

/-- The dual-pool meter the frame starts with: execution grant and state
reservoir, no spill and no refund (fork.py:761-766). -/
def meter (t : SystemTransaction) : ReferenceStorageGas.Meter :=
  { execution := t.executionGasGrant, reservoir := t.stateGasReservoir, spill := 0, refund := 0 }

/-- The source dual pool is the meter the source-payment producers use.
Both numbers are computed from the transcribed fields, not copied. -/
theorem meter_unchecked (target : AccountAddress) (data : ByteArray) (baseFee : UInt256) :
    meter (unchecked target data baseFee) = systemMeter := rfl

/-! ## Block-state storage projection and the actual message frame -/

/-- Decode a 32-byte big-endian storage key. -/
def keyOf (bytes : ByteArray) : UInt256 := UInt256.ofNat (fromBytes' bytes.data.toList.reverse)

private theorem decode_fixed (n w : Nat) (h : n < 256^w) :
    fromBytes' (toLeBytesFixed n w) = n := by
  induction w generalizing n with
  | zero =>
    have hn : n = 0 := Nat.lt_one_iff.mp h
    subst n
    rfl
  | succ w ih =>
    have hd : n/256 < 256^w := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]
      simpa [Nat.pow_succ, Nat.mul_comm] using h
    simp only [toLeBytesFixed,fromBytes']
    rw [ih _ hd]
    change n % 256 % 256 + 256 * (n/256) = n
    rw [Nat.mod_mod]
    exact Nat.mod_add_div n 256

theorem keyOf_toByteArray (k : UInt256) : keyOf k.toByteArray = k := by
  unfold keyOf
  rw [UInt256.toList_data_toByteArray]
  simp only [toBeBytesFixed,List.reverse_reverse]
  rw [decode_fixed k.toNat 32 (by exact k.val.isLt)]
  exact ofNat_toNat' k

/-- `block_env.state` as a storage parent: no pending block-level writes in
this projection, and every slot read is the actual world's storage read. -/
def blockParent (world : AccountMap .EVM) : ReferenceStorageView.Parent :=
  { writes := fun _ _ => none,
    pre := fun a bytes => SystemSpec.worldSlot world a (keyOf bytes) }

/-- `worldCode`: the installed code by account lookup (fork.py:703-706). -/
def installedCode (world : AccountMap .EVM) (addr : AccountAddress) : ByteArray :=
  TransferFrame.worldCode world addr

/-- The actual Θ frame the source environment induces: caller and origin are
the transaction origin, value and apparent value are the transaction value,
gas is the execution pool, code is the installed lookup, the substate and
created set are fresh, permission is write (not static), depth 0. -/
def frame (t : SystemTransaction) (world : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (fuel : Nat) : MessageCall.Context :=
  { fuel := fuel, created := ∅, genesis := genesis, blocks := blocks,
    world := world, originalWorld := world, substate := default,
    caller := t.origin, origin := t.origin, target := t.recipient,
    code := installedCode world t.recipient, gas := UInt256.ofNat t.executionGasGrant,
    gasPrice := t.effectiveGasPrice, value := t.value, apparentValue := t.value,
    calldata := t.data, depth := 0, header := header, permission := true,
    blobHashes := t.blobVersionedHashes }

theorem installedCode_eq {kind : Contract} {world : AccountMap .EVM} (installed : CodeAt kind world) :
    installedCode world (address kind) = runtime kind := by
  obtain ⟨account,ha,hc⟩ := installed
  simp only [installedCode,TransferFrame.worldCode,ha,Option.map_some,Option.getD_some,hc]

theorem runtime_eq (kind : Contract) : runtime kind = runtimeCode (modelKind kind) := by
  cases kind <;> rfl

/-! ## Consumer 1: `ProtocolSystemCalls.call` is the extracted frame -/

/-- Installed code is the only fact needed: every other field of the
consumer context is the transcribed dispatcher field. -/
theorem frame_call (kind : Contract) (world : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (baseFee : UInt256) (fuel : Nat)
    (data : ByteArray) (installed : CodeAt kind world) :
    frame (unchecked (address kind) data baseFee) world genesis blocks header fuel =
      ProtocolSystemCalls.call kind world genesis blocks header baseFee fuel data := by
  unfold frame unchecked ProtocolSystemCalls.call
  simp only [installedCode_eq installed]
  rfl

theorem mandatory_call (kind : Contract) (world : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (baseFee : UInt256) (fuel : Nat)
    (installed : CodeAt kind world) :
    frame (mandatory kind baseFee) world genesis blocks header fuel =
      ProtocolSystemCalls.call kind world genesis blocks header baseFee fuel ByteArray.empty :=
  frame_call kind world genesis blocks header baseFee fuel ByteArray.empty installed

/-! ## Derived frame facts -/

section Frame
variable (t : SystemTransaction) (world : AccountMap .EVM) (genesis : BlockHeader)
  (blocks : ProcessedBlocks) (header : BlockHeader) (fuel : Nat)

theorem frame_caller : (frame t world genesis blocks header fuel).caller = t.origin := rfl
theorem frame_value : (frame t world genesis blocks header fuel).value = t.value := rfl
theorem frame_calldata : (frame t world genesis blocks header fuel).calldata = t.data := rfl
theorem frame_gas : (frame t world genesis blocks header fuel).gas = UInt256.ofNat t.executionGasGrant := rfl
theorem frame_permission : (frame t world genesis blocks header fuel).permission = true := rfl
theorem frame_substate : (frame t world genesis blocks header fuel).substate = default := rfl
end Frame

/-- The extracted frame is a pinned call once the target code is installed. -/
theorem frame_pinned (kind : Contract) (world : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (baseFee : UInt256) (fuel : Nat)
    (data : ByteArray) (installed : CodeAt kind world) :
    PinnedCall kind (frame (unchecked (address kind) data baseFee) world genesis blocks header fuel) := by
  obtain ⟨account,ha,hc⟩ := installed
  refine ⟨rfl,installedCode_eq ⟨account,ha,hc⟩,⟨account,ha,?_⟩,rfl⟩
  rw [hc]
  exact (installedCode_eq ⟨account,ha,hc⟩).symm

theorem frame_code (kind : Contract) (world : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (baseFee : UInt256) (fuel : Nat)
    (data : ByteArray) (installed : CodeAt kind world) :
    (frame (unchecked (address kind) data baseFee) world genesis blocks header fuel).code =
      runtimeCode (modelKind kind) :=
  (installedCode_eq installed).trans (runtime_eq kind)

/-- The Ξ code frame of the extracted context, with the Θ fuel wrapper consumed. -/
def xi (kind : Contract) (world : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (baseFee : UInt256) (evalFuel : Nat)
    (data : ByteArray) (installed : CodeAt kind world) : XiCall (modelKind kind) :=
  CallBridge.codeCall (frame (unchecked (address kind) data baseFee) world genesis blocks header (evalFuel+1))
    (frame_code kind world genesis blocks header baseFee (evalFuel+1) data installed) evalFuel

section Xi
variable (kind : Contract) (world : AccountMap .EVM) (genesis : BlockHeader)
  (blocks : ProcessedBlocks) (header : BlockHeader) (baseFee : UInt256) (evalFuel : Nat)
  (data : ByteArray) (installed : CodeAt kind world)

/-- `CALLER` reads the transcribed origin: the SYSTEM word, derived through
the source-address equivalence rather than restated. -/
theorem xi_callerW :
    callerW (entrySt (xi kind world genesis blocks header baseFee evalFuel data installed)) = sysW :=
  (callerW_eq_sysW_iff _).mpr rfl

theorem xi_perm : (xi kind world genesis blocks header baseFee evalFuel data installed).env.perm = true := rfl

/-- The execution pool of the dual-pool grant is the frame gas. -/
theorem xi_gas : (xi kind world genesis blocks header baseFee evalFuel data installed).gas =
    UInt256.ofNat (unchecked (address kind) data baseFee).executionGasGrant := rfl

theorem xi_gas_grant :
    (xi kind world genesis blocks header baseFee evalFuel data installed).gas = UInt256.ofNat 30000000 := rfl

theorem xi_fuel : (xi kind world genesis blocks header baseFee evalFuel data installed).fuel = evalFuel := rfl

theorem xi_calldata :
    (xi kind world genesis blocks header baseFee evalFuel data installed).env.calldata = data := rfl

/-- The fresh transaction state over the block parent is related to the
entry machine: every visible owner slot is the actual world storage read. -/
theorem xi_slots : ReferenceStorageView.Related (blockParent world) freshTx
    (entrySt (xi kind world genesis blocks header baseFee evalFuel data installed)) := by
  intro k
  unfold xi
  change SystemSpec.worldSlot world (address kind) (keyOf k.toByteArray) = _
  rw [keyOf_toByteArray]
  exact (TransferFrame.codeCall_storage
    (frame (unchecked (address kind) data baseFee) world genesis blocks header (evalFuel+1))
    (frame_code kind world genesis blocks header baseFee (evalFuel+1) data installed) evalFuel k).symm

/-- Installed code supplies the owner at entry through the actual zero-value transfer. -/
theorem xi_owner : SystemSpec.HasOwner
    (entrySt (xi kind world genesis blocks header baseFee evalFuel data installed)) := by
  unfold xi
  exact TransferFrame.codeCall_hasOwner _ _ evalFuel
    (by obtain ⟨account,ha,_⟩ := installed; exact ⟨account,ha⟩)

/-- The empty `access_list_storage_keys` set is the entry warm set: the fresh
substate has no accessed storage key. -/
theorem xi_warm : WarmRelated (unchecked (address kind) data baseFee).accessListStorageKeys
    (xi kind world genesis blocks header baseFee evalFuel data installed).entry := by
  intro a k
  change (a,k.toByteArray) ∈ (∅ : Warm) ↔ (∅ : Std.TreeSet _ _).contains (a,k) = true
  simp
end Xi

/-! ## Consumer 2: the source-view payment for the extracted frame -/

/-- Per-kind trace envelope constants already produced by the source-entry module. -/
def steps : Contract → Nat
  | .deposit => 8500
  | .exit => 800

def cap : Contract → Nat
  | .deposit => 400
  | .exit => 40

def outputBytes : Contract → Nat
  | .deposit => 11776
  | .exit => 1088

/-- The mandatory (empty-data) dispatch of either builder contract completes
with a whole source-formula payment out of the transcribed dual pool. The
storage relation, warm set, owner, caller word, permission and gas are all
derived above; none is a premise. -/
theorem source_whole (kind : Contract) (world : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (baseFee : UInt256) (evalFuel : Nat)
    (fuel : 8502 ≤ evalFuel) (installed : CodeAt kind world) :
    ∃ h : Completed (ReferenceRuntimeSites.runtime (modelKind kind)) (steps kind) (cap kind)
        (outputBytes kind) evalFuel
        (xi kind world genesis blocks header baseFee evalFuel ByteArray.empty installed).entry,
      Whole (blockParent world) (mandatory kind baseFee).state.created h
        (initial (xi kind world genesis blocks header baseFee evalFuel ByteArray.empty installed)
          (mandatory kind baseFee).state)
        (mandatory kind baseFee).accessListStorageKeys (meter (mandatory kind baseFee)) := by
  rw [show meter (mandatory kind baseFee) = systemMeter from meter_unchecked _ _ _]
  cases kind with
  | deposit =>
    exact ReferenceSystemSourceEntry.deposit
      (xi .deposit world genesis blocks header baseFee evalFuel ByteArray.empty installed)
      (xi_callerW .deposit world genesis blocks header baseFee evalFuel ByteArray.empty installed)
      rfl rfl fuel rfl (blockParent world) freshTx ∅
      (xi_slots .deposit world genesis blocks header baseFee evalFuel ByteArray.empty installed)
      (xi_owner .deposit world genesis blocks header baseFee evalFuel ByteArray.empty installed)
      (xi_warm .deposit world genesis blocks header baseFee evalFuel ByteArray.empty installed)
  | exit =>
    exact ReferenceSystemSourceEntry.exit
      (xi .exit world genesis blocks header baseFee evalFuel ByteArray.empty installed)
      (xi_callerW .exit world genesis blocks header baseFee evalFuel ByteArray.empty installed)
      rfl rfl (Nat.le_trans (by decide) fuel) rfl (blockParent world) freshTx ∅
      (xi_slots .exit world genesis blocks header baseFee evalFuel ByteArray.empty installed)
      (xi_owner .exit world genesis blocks header baseFee evalFuel ByteArray.empty installed)
      (xi_warm .exit world genesis blocks header baseFee evalFuel ByteArray.empty installed)

/-- The extracted frame's actual receipt, three guarantees, preserved
invariant and source payment, from the transcribed environment. -/
theorem source_guarantees (kind : Contract) (world : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (baseFee : UInt256) (evalFuel : Nat)
    (fuel : 8502 ≤ evalFuel) {budget : Nat} (invariant : Invariant kind budget world)
    (bound : budget < 2^128) :
    ∃ h : Completed (ReferenceRuntimeSites.runtime (modelKind kind)) (steps kind) (cap kind)
        (outputBytes kind) evalFuel
        (xi kind world genesis blocks header baseFee evalFuel ByteArray.empty invariant.1).entry,
      (frame (mandatory kind baseFee) world genesis blocks header (evalFuel+1)).result =
        .ok (h.finalState.createdAccounts,h.finalState.accountMap,
          h.finalState.gasAvailable,h.finalState.substate,true,h.output) ∧
      NestedProtectedJournal.Observed kind (frame (mandatory kind baseFee) world genesis blocks header (evalFuel+1))
        h.finalState.createdAccounts h.finalState.accountMap h.finalState.substate true h.output ∧
      Invariant kind budget h.finalState.accountMap ∧
      Whole (blockParent world) (mandatory kind baseFee).state.created h
        (initial (xi kind world genesis blocks header baseFee evalFuel ByteArray.empty invariant.1)
          (mandatory kind baseFee).state)
        (mandatory kind baseFee).accessListStorageKeys (meter (mandatory kind baseFee)) := by
  obtain ⟨h,whole⟩ := source_whole kind world genesis blocks header baseFee evalFuel fuel invariant.1
  refine ⟨h,?_⟩
  rw [show meter (mandatory kind baseFee) = systemMeter from meter_unchecked _ _ _] at whole ⊢
  exact ReferenceSystemSourceEntry.guarantees kind _
    (frame_pinned kind world genesis blocks header baseFee (evalFuel+1) ByteArray.empty invariant.1)
    (frame_code kind world genesis blocks header baseFee (evalFuel+1) ByteArray.empty invariant.1)
    evalFuel rfl h whole rfl rfl invariant bound (by change 0 < UInt256.size; decide +kernel)

/-! ## Consumer 3: the ordered mandatory pair (fork.py:904-926) -/

/-- The proposed ordered Deposit-then-Exit schedule, with each call identified
as the extracted mandatory frame over its own pre-world. The Exit frame's code
identity comes from the constructed transition's pinned witness. -/
theorem mandatory_pair (before : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (baseFee : UInt256) (fuel : Nat)
    (budgets : Contract → Nat) (initial : ∀ kind, Invariant kind (budgets kind) before)
    (bounds : ∀ kind, budgets kind < 2^128) (resources : 8503 ≤ fuel) :
    ∃ after, ∃ pair : ProtocolSystemSequence.EmptyPair before after genesis blocks header baseFee fuel,
      pair.deposit.call = frame (mandatoryDeposit baseFee) before genesis blocks header fuel ∧
      pair.exit.call = frame (mandatoryExit baseFee) pair.middle genesis blocks header fuel ∧
      (∀ kind, Invariant kind (budgets kind) after) ∧
      NestedProtectedJournal.Observed .deposit pair.deposit.call pair.deposit.created pair.middle
        pair.deposit.substate pair.deposit.success pair.deposit.output ∧
      NestedProtectedJournal.Observed .exit pair.exit.call pair.exit.created after
        pair.exit.substate pair.exit.success pair.exit.output := by
  obtain ⟨after,pair,inv,dep,ext⟩ := ProtocolSystemSequence.completes before genesis blocks header
    baseFee fuel budgets initial bounds resources
  have hmid : CodeAt .exit pair.middle := by
    obtain ⟨account,ha,hc⟩ := pair.exit.pinned.installed
    rw [pair.exit.pre,pair.exit.pinned.target] at ha
    exact ⟨account,ha,hc.trans pair.exit.pinned.code⟩
  refine ⟨after,pair,?_,?_,inv,dep,ext⟩
  · rw [pair.depositCall]
    exact (mandatory_call .deposit before genesis blocks header baseFee fuel (initial .deposit).1).symm
  · rw [pair.exitCall]
    exact (mandatory_call .exit pair.middle genesis blocks header baseFee fuel hmid).symm

/-- The same ordered pair, constructed from the two source-view executions
rather than from pinned progress: each call is the extracted mandatory frame,
each carries its whole source payment out of the transcribed dual pool, and
the Deposit poststate is the Exit pre-world. -/
theorem source_pair (before : AccountMap .EVM) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (header : BlockHeader) (baseFee : UInt256) (evalFuel : Nat)
    (fuel : 8502 ≤ evalFuel)
    (budgets : Contract → Nat) (invariants : ∀ kind, Invariant kind (budgets kind) before)
    (bounds : ∀ kind, budgets kind < 2^128) :
    ∃ after, ∃ pair : ProtocolSystemSequence.EmptyPair before after genesis blocks header baseFee (evalFuel+1),
      pair.deposit.call = frame (mandatoryDeposit baseFee) before genesis blocks header (evalFuel+1) ∧
      pair.exit.call = frame (mandatoryExit baseFee) pair.middle genesis blocks header (evalFuel+1) ∧
      (∀ kind, Invariant kind (budgets kind) after) ∧
      (∃ h : Completed (ReferenceRuntimeSites.runtime .deposit) 8500 400 11776 evalFuel
          (xi .deposit before genesis blocks header baseFee evalFuel ByteArray.empty (invariants .deposit).1).entry,
        pair.middle = h.finalState.accountMap ∧
        Whole (blockParent before) (mandatoryDeposit baseFee).state.created h
          (initial (xi .deposit before genesis blocks header baseFee evalFuel ByteArray.empty (invariants .deposit).1)
            (mandatoryDeposit baseFee).state)
          (mandatoryDeposit baseFee).accessListStorageKeys (meter (mandatoryDeposit baseFee))) ∧
      (∃ installed : CodeAt .exit pair.middle,
        ∃ h : Completed (ReferenceRuntimeSites.runtime .exit) 800 40 1088 evalFuel
          (xi .exit pair.middle genesis blocks header baseFee evalFuel ByteArray.empty installed).entry,
        after = h.finalState.accountMap ∧
        Whole (blockParent pair.middle) (mandatoryExit baseFee).state.created h
          (initial (xi .exit pair.middle genesis blocks header baseFee evalFuel ByteArray.empty installed)
            (mandatoryExit baseFee).state)
          (mandatoryExit baseFee).accessListStorageKeys (meter (mandatoryExit baseFee))) := by
  obtain ⟨hd,depResult,_,_,depWhole⟩ := source_guarantees .deposit before genesis blocks header
    baseFee evalFuel fuel (invariants .deposit) (bounds .deposit)
  let dep : Transition .deposit before hd.finalState.accountMap :=
    { call := frame (mandatoryDeposit baseFee) before genesis blocks header (evalFuel+1),
      pinned := frame_pinned .deposit before genesis blocks header baseFee (evalFuel+1) ByteArray.empty (invariants .deposit).1,
      pre := rfl, created := hd.finalState.createdAccounts, gas := hd.finalState.gasAvailable,
      substate := hd.finalState.substate, success := true, output := hd.output, executed := depResult }
  have midInv : ∀ kind, Invariant kind (budgets kind) hd.finalState.accountMap :=
    fun kind => SystemJournal.preserves dep rfl rfl (by change 0 < UInt256.size; decide +kernel) (bounds kind) (invariants kind)
  obtain ⟨he,extResult,_,_,extWhole⟩ := source_guarantees .exit hd.finalState.accountMap genesis blocks header
    baseFee evalFuel fuel (midInv .exit) (bounds .exit)
  let ext : Transition .exit hd.finalState.accountMap he.finalState.accountMap :=
    { call := frame (mandatoryExit baseFee) hd.finalState.accountMap genesis blocks header (evalFuel+1),
      pinned := frame_pinned .exit hd.finalState.accountMap genesis blocks header baseFee (evalFuel+1) ByteArray.empty (midInv .exit).1,
      pre := rfl, created := he.finalState.createdAccounts, gas := he.finalState.gasAvailable,
      substate := he.finalState.substate, success := true, output := he.output, executed := extResult }
  have afterInv : ∀ kind, Invariant kind (budgets kind) he.finalState.accountMap :=
    fun kind => SystemJournal.preserves ext rfl rfl (by change 0 < UInt256.size; decide +kernel) (bounds kind) (midInv kind)
  refine ⟨he.finalState.accountMap,
    ⟨hd.finalState.accountMap,dep,ext,
      mandatory_call .deposit before genesis blocks header baseFee (evalFuel+1) (invariants .deposit).1,
      mandatory_call .exit hd.finalState.accountMap genesis blocks header baseFee (evalFuel+1) (midInv .exit).1,
      rfl,rfl⟩,
    rfl,rfl,afterInv,⟨hd,rfl,depWhole⟩,⟨(midInv .exit).1,he,rfl,extWhole⟩⟩

#print axioms meter_unchecked
#print axioms keyOf_toByteArray
#print axioms frame_call
#print axioms mandatory_call
#print axioms frame_pinned
#print axioms xi_callerW
#print axioms xi_slots
#print axioms xi_owner
#print axioms xi_warm
#print axioms source_whole
#print axioms source_guarantees
#print axioms mandatory_pair
#print axioms source_pair
end Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction
