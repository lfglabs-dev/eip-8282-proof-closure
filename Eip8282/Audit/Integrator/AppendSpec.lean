import Eip8282.Audit.Integrator.EndpointState

/-!
# Independent append postconditions

This module begins the interpretation of the concrete append endpoints. The
receipt specification is one anonymous log emitted by the executing account;
for deposits its payload is exactly the supplied calldata. The world-frame
specification preserves every other account. These conclusions need no queue
address non-alias assumption: that assumption will be needed for the separate
control-slot and FIFO-storage postconditions, which are not asserted here.
-/

namespace Eip8282.Audit.Integrator.AppendSpec

open EvmYul EvmYul.EVM
open Eip8282.Audit.XiTransport
open Eip8282.Audit.EntryReach
open Eip8282.Audit.SymExec

set_option maxHeartbeats 1600000

/-- The complete receipt sequence expected from one authentic anonymous log. -/
def AppendedLog (c : XiCall kind) (record : ByteArray) (substate : Substate) : Prop :=
  substate.logSeries = c.substate.logSeries.push ⟨c.env.codeOwner, #[], record⟩

/-- A submission may modify its executing account, but no other account. -/
def OtherAccountsUnchanged (c : XiCall kind) (world : AccountMap .EVM) : Prop :=
  ∀ addr, addr ≠ c.env.codeOwner → world.get? addr = c.σ.get? addr

theorem logs_sstore (st : EvmYul.State .EVM) (k v : UInt256) :
    (st.sstore k v).substate.logSeries = st.substate.logSeries := by
  unfold EvmYul.State.sstore
  dsimp only
  rcases hacc : Std.TreeMap.get! st.accountMap st.executionEnv.codeOwner with
    ⟨⟨nonce, bal, sto, code⟩, tst⟩
  cases st.lookupAccount st.executionEnv.codeOwner <;> rfl

theorem other_account_sstore (st : EvmYul.State .EVM) (k v : UInt256)
    (addr : AccountAddress) (hne : addr ≠ st.executionEnv.codeOwner) :
    (st.sstore k v).accountMap.get? addr = st.accountMap.get? addr := by
  unfold EvmYul.State.sstore
  dsimp only
  rcases hacc : Std.TreeMap.get! st.accountMap st.executionEnv.codeOwner with
    ⟨⟨nonce, bal, sto, code⟩, tst⟩
  cases st.lookupAccount st.executionEnv.codeOwner with
  | none => rfl
  | some acc =>
    change (st.accountMap.insert st.executionEnv.codeOwner (acc.updateStorage k v)).get? addr = _
    simp [Std.TreeMap.getElem?_insert, Ne.symm hne]

theorem deposit_item_environment (c : XiCall .deposit) :
    (Deposit.itemStored c).executionEnv = c.env := by
  simp only [Deposit.itemStored, Deposit.countStore, Deposit.st₂,
    executionEnv_sstore, executionEnv_touch, executionEnv_entrySt]

theorem exit_item_environment (c : XiCall .exit) :
    (Exit.itemStored c).executionEnv = c.env := by
  simp only [Exit.itemStored, Exit.countStore, Exit.st₂,
    executionEnv_sstore, executionEnv_touch, executionEnv_entrySt]

/-- Receipt count, emitter and anonymity are fixed for the concrete deposit
append state. The next lemma identifies this staged payload with raw calldata. -/
theorem deposit_append_log (c : XiCall .deposit) :
    AppendedLog c ((Deposit.stagedMem c).readWithPadding 0 184)
      (EndpointState.depositAppendState c).substate := by
  unfold AppendedLog EndpointState.depositAppendState Deposit.appendedSt
  rw [logs_sstore]
  change (Deposit.itemStored c).substate.logSeries.push
    ⟨(Deposit.itemStored c).executionEnv.codeOwner, #[], _⟩ = _
  rw [deposit_item_environment]
  simp only [Deposit.itemStored, Deposit.countStore, Deposit.st₂,
    logs_sstore, logSeries_touch]
  rfl

/-- Deposit staging copies exactly the provided 184 bytes. No signature
validity premise is used or supplied by the contract. -/
theorem deposit_staged_record (c : XiCall .deposit) (hsize : c.env.calldata.size = 184) :
    (Deposit.stagedMem c).readWithPadding 0 184 = c.env.calldata := by
  unfold Deposit.stagedMem cdcopyMem
  rw [deposit_item_environment]
  change (ByteArray.write c.env.calldata 0 (Deposit.mem₀ c) 0 184).readWithPadding 0 184 = _
  exact ByteArray.readWithPadding_write_self_of_pad _ _ _ _
    (by decide) (by decide) hsize (by simp)

theorem deposit_authentic_log (c : XiCall .deposit) (hsize : c.env.calldata.size = 184) :
    AppendedLog c c.env.calldata (EndpointState.depositAppendState c).substate := by
  have h := deposit_append_log c
  rwa [deposit_staged_record c hsize] at h

/-- The exit endpoint appends exactly one anonymous log of its staged bytes.
Identification of those bytes with address concatenated with pubkey is separate. -/
theorem exit_append_log (c : XiCall .exit) :
    AppendedLog c ((Exit.stagedMem c).readWithPadding 0 68)
      (EndpointState.exitAppendState c).substate := by
  unfold AppendedLog EndpointState.exitAppendState Exit.appendedSt
  rw [logs_sstore]
  change (Exit.itemStored c).substate.logSeries.push
    ⟨(Exit.itemStored c).executionEnv.codeOwner, #[], _⟩ = _
  rw [exit_item_environment]
  simp only [Exit.itemStored, Exit.countStore, Exit.st₂, logs_sstore, logSeries_touch]
  rfl

/-- A compositional frame predicate keeps large storage expressions underneath
the predicate while each write is checked, avoiding eager map evaluation. -/
def AccountFrame (c : XiCall kind) (st : EvmYul.State .EVM) : Prop :=
  st.executionEnv = c.env ∧ OtherAccountsUnchanged c st.accountMap

theorem frame_entry (c : XiCall kind) : AccountFrame c (entrySt c) :=
  ⟨rfl, fun _ _ => rfl⟩

theorem frame_touch {c : XiCall kind} {st : EvmYul.State .EVM} {k : UInt256}
    (h : AccountFrame c st) : AccountFrame c (touch st k) := h

theorem frame_logged {c : XiCall kind} {st : EvmYul.State .EVM} {data : ByteArray}
    (h : AccountFrame c st) : AccountFrame c (logged st data) := h

theorem frame_sstore {c : XiCall kind} {st : EvmYul.State .EVM} {k v : UInt256}
    (h : AccountFrame c st) : AccountFrame c (st.sstore k v) := by
  refine ⟨(executionEnv_sstore st k v).trans h.1, ?_⟩
  intro addr hne
  rw [other_account_sstore st k v addr (by rw [h.1]; exact hne)]
  exact h.2 addr hne

theorem deposit_append_frame (c : XiCall .deposit) :
    AccountFrame c (EndpointState.depositAppendState c) := by
  unfold EndpointState.depositAppendState Deposit.appendedSt
  apply frame_sstore
  apply frame_logged
  unfold Deposit.itemStored Deposit.countStore Deposit.st₂
  repeat (first | apply frame_sstore | apply frame_touch)
  exact frame_entry c

theorem exit_append_frame (c : XiCall .exit) :
    AccountFrame c (EndpointState.exitAppendState c) := by
  unfold EndpointState.exitAppendState Exit.appendedSt
  apply frame_sstore
  apply frame_logged
  unfold Exit.itemStored Exit.countStore Exit.st₂
  repeat (first | apply frame_sstore | apply frame_touch)
  exact frame_entry c

theorem deposit_other_accounts (c : XiCall .deposit) :
    OtherAccountsUnchanged c (EndpointState.depositAppendState c).accountMap :=
  (deposit_append_frame c).2

theorem exit_other_accounts (c : XiCall .exit) :
    OtherAccountsUnchanged c (EndpointState.exitAppendState c).accountMap :=
  (exit_append_frame c).2

/-- An actual successful deposit result satisfies the independent receipt and
other-account frame specifications. The loop completion and gas/fuel conditions
are explicit; this is not a success-inversion theorem at arbitrary resources. -/
theorem deposit_submission_receipt (c : XiCall .deposit)
    (huser : Deposit.callerWord c ≠ sysW) (hen : Deposit.excessWord c ≠ INH)
    (hperm : c.env.perm = true) {n : Nat} {o i : UInt256}
    (hfee : Deposit.FeeLoopEnds c n o i)
    (hsize : c.env.calldata.size = 184)
    (hpaid : ¬ Deposit.valueWord c < Deposit.feeWord o)
    (hfloor : ¬ Deposit.amountWord c < UInt256.ofNat 1000000000)
    (hstake : ¬ (Deposit.valueWord c - Deposit.feeWord o) <
      UInt256.ofNat 1000000000 * Deposit.amountWord c)
    (hg : 87 * n + 190000 ≤ c.gas.toNat) (hf : 24 * n + 152 ≤ c.fuel) :
    ∃ created world gas substate,
      c.result = .ok (.success (created, world, gas, substate) .empty) ∧
      AppendedLog c c.env.calldata substate ∧ OtherAccountsUnchanged c world := by
  have hword : Deposit.cdsizeWord c = UInt256.ofNat 184 := by
    change UInt256.ofNat c.env.calldata.size = _
    rw [hsize]
  obtain ⟨gas, hres⟩ := EndpointState.deposit_append_result c huser hen hperm hfee
    hword hpaid hfloor hstake hg hf
  exact ⟨_, _, gas, _, hres, deposit_authentic_log c hsize, deposit_other_accounts c⟩

#print axioms deposit_authentic_log
#print axioms deposit_other_accounts
#print axioms exit_other_accounts
#print axioms deposit_submission_receipt

end Eip8282.Audit.Integrator.AppendSpec
