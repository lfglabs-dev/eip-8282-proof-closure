import Eip8282.Audit.Correspondence

/-!
P-CONTROL-1 caller gate, `∀` callers / storage / gas.

C1: after the opening `CALLER; PUSH20 SYSTEM_ADDR; EQ; PUSH dest; JUMPI`,
PC is `read_requests` iff `CALLER = SYSTEM_ADDR`, for both pinned
predeploys, under `WellFormed` + `CallHyp` (gas ≥ 30M). Storage is not
read by the gate; the queue may be nonempty (excess fold is C2).

F3/F4 already closed the CFG prefix (`deposit_caller_gate` /
`exit_caller_gate`, `caller_gate`, `system_iff_read_requests`,
`callHyp_dispatch`). This module packages those lemmas as the claim
the integrator IC registers. It does not `native_decide` `controlFacts`
and does not re-scan `D_J_aux`.

Load-bearing on the `EQ` at offset 22 (`0x14`): `cfgStep` takes the
identity comparison `UInt256.eq`, then `JUMPI`s to `read_requests` iff
that word is nonzero. Replacing the byte with `LT` (`0x10`) makes
`opcodeAt _ gateEqPc = some (.EQ, none)` false and `runGatePrefix` fail
(`unexpectedOpcode`). The statement is therefore not a tautology.
-/

namespace Eip8282.Audit.Guarantees.PControl1

open EvmYul (UInt256 Storage)
open EvmYul.Operation
open Eip8282.Audit.Bytecode
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Step
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Correspondence
open Eip8282.Audit.Model (Kind)
open GasConstants

/-! ## Kind-indexed gate PCs -/

/-- `JUMPI` of the caller gate. Deposit pushes a 2-byte dest (`PC = 26`);
exit pushes a 1-byte dest (`PC = 25`). -/
def gateJumpiPc : Kind → Nat
  | .deposit => depositJumpiPc
  | .exit => exitJumpiPc

/-- User fee-quote JUMPDEST (`compute_user_fee`), reached only on the
fall-through path after a failed gate. -/
def feeQuotePc : Kind → Nat
  | .deposit => Deposit.compute_user_fee
  | .exit => Exit.compute_user_fee

/-- System FIFO drain JUMPDEST (`accum_loop`), reached only after
`read_requests`. -/
def accumLoopPc : Kind → Nat
  | .deposit => Deposit.accum_loop
  | .exit => Exit.accum_loop

theorem readRequestsPc_ne_userPathPc (kind : Kind) :
    readRequestsPc kind ≠ userPathPc kind := by
  cases kind with
  | deposit => exact depositUserPc_ne_read_requests.symm
  | exit => exact exitUserPc_ne_read_requests.symm

theorem readRequestsPc_ne_feeQuotePc (kind : Kind) :
    readRequestsPc kind ≠ feeQuotePc kind := by
  cases kind <;> decide

theorem userPathPc_ne_accumLoopPc (kind : Kind) :
    userPathPc kind ≠ accumLoopPc kind := by
  cases kind <;> decide

theorem readRequestsPc_ne_accumLoopPc (kind : Kind) :
    readRequestsPc kind ≠ accumLoopPc kind := by
  cases kind <;> decide

/-! ## Opening `EQ` / `JUMPI` (kill-line bytes) -/

/-- Both runtimes open `CALLER; PUSH20 SYSTEM_ADDR; EQ; …; JUMPI`.
The `EQ` is at offset 22 in each image. -/
theorem pcontrol1_opening_eq_jumpi (kind : Kind) :
    opcodeAt (openingCode kind) 0 = some (.CALLER, none) ∧
      opcodeAt (openingCode kind) 1 =
        some (.PUSH20, some (UInt256.ofNat systemAddress, 20)) ∧
      opcodeAt (openingCode kind) gateEqPc = some (.EQ, none) ∧
      opcodeAt (openingCode kind) (gateJumpiPc kind) = some (.JUMPI, none) := by
  cases kind with
  | deposit =>
      exact ⟨deposit_opcode_CALLER, deposit_opcode_PUSH20,
        deposit_opcode_EQ, deposit_opcode_JUMPI⟩
  | exit =>
      exact ⟨exit_opcode_CALLER, exit_opcode_PUSH20,
        exit_opcode_EQ, exit_opcode_JUMPI⟩

/-- The `JUMPI` dest immediate is `read_requests` (284 deposit / 225 exit). -/
theorem pcontrol1_opening_push_read_requests (kind : Kind) :
    opcodeAt (openingCode kind) 23 =
      some (match kind with
        | .deposit => (.PUSH2, some (UInt256.ofNat Deposit.read_requests, 2))
        | .exit => (.PUSH1, some (UInt256.ofNat Exit.read_requests, 1))) := by
  cases kind with
  | deposit => exact deposit_opcode_PUSH2
  | exit => exact exit_opcode_PUSH1

/-! ## Prefix reduction under `CallHyp` -/

/-- The five-instruction gate prefix succeeds on any `CallHyp` gas
(≥ 30M ≥ `prefixGasBound`) and lands on `read_requests` or the user
`PUSH0`, independently of storage. -/
theorem pcontrol1_runGatePrefix (kind : Kind) (σ : Storage)
    (h : CallHyp kind σ) :
    runGatePrefix (openingCode kind) h.caller (openingJumps kind) h.gas =
      .ok { pc := if isSystemCaller h.caller then readRequestsPc kind
                  else userPathPc kind,
            stack := [],
            gas := h.gas - Gbase - Gverylow - Gverylow - Gverylow - Ghigh } := by
  have hpre := h.gas_ge_prefix
  cases kind with
  | deposit => exact deposit_runGatePrefix h.caller h.gas hpre
  | exit => exact exit_runGatePrefix h.caller h.gas hpre

/-! ## `∀` parent for IC -/

/-- **P-CONTROL-1 gate.** For both predeploys, every well-formed storage
image, every campaign-gas bound, and every caller: the opening `EQ` /
`JUMPI` sends execution to `read_requests` if and only if
`CALLER = SYSTEM_ADDR`. Does not require an empty queue. -/
theorem pcontrol1_gate_forall (kind : Kind) (σ : Storage)
    (h : CallHyp kind σ) :
    let result :=
      runGatePrefix (openingCode kind) h.caller (openingJumps kind) h.gas
    opcodeAt (openingCode kind) gateEqPc = some (.EQ, none) ∧
      opcodeAt (openingCode kind) (gateJumpiPc kind) = some (.JUMPI, none) ∧
      ∃ m : CfgState, result = .ok m ∧
        (m.pc = readRequestsPc kind ↔ isSystemCaller h.caller) ∧
        (m.pc = userPathPc kind ↔ isUserCaller h.caller) ∧
        m.stack = [] := by
  refine ⟨(pcontrol1_opening_eq_jumpi kind).2.2.1,
    (pcontrol1_opening_eq_jumpi kind).2.2.2, ?_⟩
  refine ⟨_, pcontrol1_runGatePrefix kind σ h, ?_⟩
  exact caller_gate kind h.caller h.gas h.gas_ge
    (pcontrol1_runGatePrefix kind σ h)

/-- Same dispatch, indexed by `CallHyp.isUser` (F4 `callHyp_dispatch`). -/
theorem pcontrol1_gate_callHyp (kind : Kind) (σ : Storage)
    (h : CallHyp kind σ) {m : CfgState}
    (hrun : runGatePrefix (openingCode kind) h.caller (openingJumps kind) h.gas =
      .ok m) :
    (m.pc = readRequestsPc kind ↔ h.isUser = false) ∧
      (m.pc = userPathPc kind ↔ h.isUser = true) ∧
      m.stack = [] :=
  callHyp_dispatch h hrun

/-! ## Both runtimes, named PCs -/

theorem pcontrol1_gate_deposit (σ : Storage) (h : CallHyp .deposit σ) :
    opcodeAt depositOpening gateEqPc = some (.EQ, none) ∧
      opcodeAt depositOpening depositJumpiPc = some (.JUMPI, none) ∧
      ∃ m : CfgState,
        runGatePrefix depositOpening h.caller depositJumpdests h.gas = .ok m ∧
          (m.pc = Deposit.read_requests ↔ isSystemCaller h.caller) ∧
          (m.pc = depositUserPc ↔ isUserCaller h.caller) :=
  let ⟨heq, hjumpi, m, hrun, hsys, huser, _⟩ := pcontrol1_gate_forall .deposit σ h
  ⟨heq, hjumpi, m, hrun, hsys, huser⟩

theorem pcontrol1_gate_exit (σ : Storage) (h : CallHyp .exit σ) :
    opcodeAt exitOpening gateEqPc = some (.EQ, none) ∧
      opcodeAt exitOpening exitJumpiPc = some (.JUMPI, none) ∧
      ∃ m : CfgState,
        runGatePrefix exitOpening h.caller exitJumpdests h.gas = .ok m ∧
          (m.pc = Exit.read_requests ↔ isSystemCaller h.caller) ∧
          (m.pc = exitUserPc ↔ isUserCaller h.caller) :=
  let ⟨heq, hjumpi, m, hrun, hsys, huser, _⟩ := pcontrol1_gate_forall .exit σ h
  ⟨heq, hjumpi, m, hrun, hsys, huser⟩

/-! ## Corollaries: system ↛ fee-quote; user ↛ `accum_loop` -/

/-- A `SYSTEM_ADDR` caller is at `read_requests`, not the user fee-quote
path (`PUSH0` at 27/26, nor `compute_user_fee`). -/
theorem pcontrol1_system_not_fee_quote (kind : Kind) (σ : Storage)
    (h : CallHyp kind σ) (hsys : isSystemCaller h.caller) {m : CfgState}
    (hrun : runGatePrefix (openingCode kind) h.caller (openingJumps kind) h.gas =
      .ok m) :
    m.pc = readRequestsPc kind ∧
      m.pc ≠ userPathPc kind ∧
      m.pc ≠ feeQuotePc kind := by
  have hpc : m.pc = readRequestsPc kind :=
    (caller_gate kind h.caller h.gas h.gas_ge hrun).1.mpr hsys
  refine ⟨hpc, ?_, ?_⟩
  · rw [hpc]; exact readRequestsPc_ne_userPathPc kind
  · rw [hpc]; exact readRequestsPc_ne_feeQuotePc kind

/-- A non-system caller is at the user `PUSH0`, not `read_requests` and
not the drain `accum_loop`. -/
theorem pcontrol1_user_not_accum_loop (kind : Kind) (σ : Storage)
    (h : CallHyp kind σ) (huser : isUserCaller h.caller) {m : CfgState}
    (hrun : runGatePrefix (openingCode kind) h.caller (openingJumps kind) h.gas =
      .ok m) :
    m.pc = userPathPc kind ∧
      m.pc ≠ readRequestsPc kind ∧
      m.pc ≠ accumLoopPc kind := by
  have hpc : m.pc = userPathPc kind :=
    (caller_gate kind h.caller h.gas h.gas_ge hrun).2.1.mpr huser
  refine ⟨hpc, ?_, ?_⟩
  · rw [hpc]; exact (readRequestsPc_ne_userPathPc kind).symm
  · rw [hpc]; exact userPathPc_ne_accumLoopPc kind

theorem pcontrol1_deposit_system_not_fee_quote (σ : Storage)
    (h : CallHyp .deposit σ) (hsys : isSystemCaller h.caller) {m : CfgState}
    (hrun : runGatePrefix depositOpening h.caller depositJumpdests h.gas =
      .ok m) :
    m.pc = Deposit.read_requests ∧
      m.pc ≠ depositUserPc ∧
      m.pc ≠ Deposit.compute_user_fee :=
  pcontrol1_system_not_fee_quote .deposit σ h hsys hrun

theorem pcontrol1_exit_system_not_fee_quote (σ : Storage)
    (h : CallHyp .exit σ) (hsys : isSystemCaller h.caller) {m : CfgState}
    (hrun : runGatePrefix exitOpening h.caller exitJumpdests h.gas = .ok m) :
    m.pc = Exit.read_requests ∧
      m.pc ≠ exitUserPc ∧
      m.pc ≠ Exit.compute_user_fee :=
  pcontrol1_system_not_fee_quote .exit σ h hsys hrun

theorem pcontrol1_deposit_user_not_accum_loop (σ : Storage)
    (h : CallHyp .deposit σ) (huser : isUserCaller h.caller) {m : CfgState}
    (hrun : runGatePrefix depositOpening h.caller depositJumpdests h.gas =
      .ok m) :
    m.pc = depositUserPc ∧
      m.pc ≠ Deposit.read_requests ∧
      m.pc ≠ Deposit.accum_loop :=
  pcontrol1_user_not_accum_loop .deposit σ h huser hrun

theorem pcontrol1_exit_user_not_accum_loop (σ : Storage)
    (h : CallHyp .exit σ) (huser : isUserCaller h.caller) {m : CfgState}
    (hrun : runGatePrefix exitOpening h.caller exitJumpdests h.gas = .ok m) :
    m.pc = exitUserPc ∧
      m.pc ≠ Exit.read_requests ∧
      m.pc ≠ Exit.accum_loop :=
  pcontrol1_user_not_accum_loop .exit σ h huser hrun

end Eip8282.Audit.Guarantees.PControl1
