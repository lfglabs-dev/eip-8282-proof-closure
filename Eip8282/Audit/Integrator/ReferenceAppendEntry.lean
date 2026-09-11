import Eip8282.Audit.Integrator.ReferenceAppendOccurrences

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
