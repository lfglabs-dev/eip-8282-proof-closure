import Eip8282.Audit.Integrator.SuccessfulUser
import Eip8282.Audit.Integrator.UniversalGate

/-!
# Invalid user inputs cannot commit at arbitrary resources

Concrete predicates observe calldata, actual call value, amount and pre-transfer
storage. Underpayment uses any completed operational quote of that same input;
its budget is independent of the actual execution. No gas lower bound, execution
quote-completion premise or mathematical-fee domain restriction is required.

The conclusion concerns a completed Θ result. Interpreter OutOfFuel is an error,
not such a result. Failure restores the full pre-call journal; gas and returned
bytes are intentionally unconstrained. Actual and apparent value are explicitly
bound as for an ordinary call, and calldata length must fit the EVM size word.
-/
namespace Eip8282.Audit.Integrator.UniversalRejection

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open MessageCall CallBridge UniversalGate
open Eip8282.Audit.Correspondence (runtimeCode)

/-- Operational tariff input calculated from the pre-transfer target storage. -/
def feeInput (c : Context) (target : Nat) : UInt256 :=
  ControlSpec.feeInput (UInt256.ofNat target)
    (SystemSpec.worldSlot c.world c.target (UInt256.ofNat 0))
    (SystemSpec.worldSlot c.world c.target (UInt256.ofNat 1))

/-- A completed quote at any finite budget, without a semantic cutoff. -/
def KnownPrice (c : Context) (target : Nat) (price : UInt256) : Prop :=
  ∃ n, quoteWithin (feeInput c target) n = some price

def DepositInvalid (c : Context) : Prop :=
  (c.calldata.size ≠ 0 ∧ c.calldata.size ≠ 184) ∨
  (c.calldata.size = 0 ∧ c.value ≠ ⟨0⟩) ∨
  (c.calldata.size = 184 ∧ SubmissionCall.amount c.calldata < 1000000000) ∨
  (c.calldata.size = 184 ∧ ∃ price, KnownPrice c 8 price ∧
    (c.value.toNat < price.toNat ∨
     c.value.toNat < price.toNat + 1000000000 * SubmissionCall.amount c.calldata))

def ExitInvalid (c : Context) : Prop :=
  (c.calldata.size ≠ 0 ∧ c.calldata.size ≠ 48) ∨
  (c.calldata.size = 0 ∧ c.value ≠ ⟨0⟩) ∨
  (c.calldata.size = 48 ∧ ∃ price, KnownPrice c 2 price ∧ c.value.toNat < price.toNat)

theorem deposit_feeInput (c : Context) (hcode : c.code = runtimeCode .deposit) (steps : Nat) :
    Deposit.effExcess (codeCall c hcode steps) = feeInput c 8 := by
  rw [← ControlSpec.deposit_feeInput]
  change ControlSpec.feeInput _ (slotW (entrySt (codeCall c hcode steps)) _)
    (slotW (entrySt (codeCall c hcode steps)) _) = _
  rw [TransferFrame.codeCall_storage, TransferFrame.codeCall_storage]
  rfl

theorem exit_feeInput (c : Context) (hcode : c.code = runtimeCode .exit) (steps : Nat) :
    Exit.effExcess (codeCall c hcode steps) = feeInput c 2 := by
  rw [← ControlSpec.exit_feeInput]
  change ControlSpec.feeInput _ (slotW (entrySt (codeCall c hcode steps)) _)
    (slotW (entrySt (codeCall c hcode steps)) _) = _
  rw [TransferFrame.codeCall_storage, TransferFrame.codeCall_storage]
  rfl

/-- Concrete invalid deposit inputs force a failed status and full rollback for
any completed actual message call, including resource-related failure. -/
theorem deposit_invalid (c : Context) (hcode : c.code = runtimeCode .deposit)
    (huser : c.caller ≠ EvmRunner.sysAddr) (hactual : c.apparentValue = c.value)
    (hdata : c.calldata.size < UInt256.size) (hinvalid : DepositInvalid c)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, success, out)) :
    FailedJournal c created world substate success := by
  cases success with
  | false =>
    obtain ⟨hw, hs, hc⟩ := failure_restores_journal c created world gas substate out h
    exact ⟨rfl, hc, hw, hs⟩
  | true =>
    obtain ⟨_, n, price, hq, hc⟩ := SuccessfulUser.deposit_admission c hcode huser hactual hdata h
    rw [deposit_feeInput] at hq
    exfalso
    rcases hinvalid with hsize | hgetter | hamount | hpay
    · rcases hc with ⟨hz, _⟩ | ⟨hz, _⟩ <;> omega
    · rcases hc with ⟨_, hv, _⟩ | ⟨hz, _⟩
      · exact hgetter.2 hv
      · omega
    · rcases hc with ⟨hz, _⟩ | ⟨_, ha, _⟩ <;> omega
    · obtain ⟨hsize, other, ⟨m, hm⟩, hp⟩ := hpay
      have he : other = price := quoteWithin_unique hm hq
      subst other
      rcases hc with ⟨hz, _⟩ | ⟨_, _, hpaid⟩
      · omega
      · rcases hp with hp | hp <;> omega

/-- Concrete invalid exit inputs force the same full journal rollback. -/
theorem exit_invalid (c : Context) (hcode : c.code = runtimeCode .exit)
    (huser : c.caller ≠ EvmRunner.sysAddr) (hactual : c.apparentValue = c.value)
    (hdata : c.calldata.size < UInt256.size) (hinvalid : ExitInvalid c)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, success, out)) :
    FailedJournal c created world substate success := by
  cases success with
  | false =>
    obtain ⟨hw, hs, hc⟩ := failure_restores_journal c created world gas substate out h
    exact ⟨rfl, hc, hw, hs⟩
  | true =>
    obtain ⟨_, n, price, hq, hc⟩ := SuccessfulUser.exit_admission c hcode huser hactual hdata h
    rw [exit_feeInput] at hq
    exfalso
    rcases hinvalid with hsize | hgetter | hpay
    · rcases hc with ⟨hz, _⟩ | ⟨hz, _⟩ <;> omega
    · rcases hc with ⟨_, hv, _⟩ | ⟨hz, _⟩
      · exact hgetter.2 hv
      · omega
    · obtain ⟨hsize, other, ⟨m, hm⟩, hp⟩ := hpay
      have he : other = price := quoteWithin_unique hm hq
      subst other
      rcases hc with ⟨hz, _⟩ | ⟨_, hpaid⟩ <;> omega

/-- The requested amount-below-one case is included in the stronger bytecode
floor of one billion gwei. -/
theorem deposit_amount_lt_one (c : Context) (hs : c.calldata.size = 184)
    (ha : SubmissionCall.amount c.calldata < 1) : DepositInvalid c := by
  exact Or.inr (Or.inr (Or.inl ⟨hs, by omega⟩))

#print axioms deposit_feeInput
#print axioms exit_feeInput
#print axioms deposit_invalid
#print axioms exit_invalid
#print axioms deposit_amount_lt_one

end Eip8282.Audit.Integrator.UniversalRejection
