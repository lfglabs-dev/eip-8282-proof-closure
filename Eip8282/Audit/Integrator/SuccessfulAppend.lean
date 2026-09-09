import Eip8282.Audit.Integrator.AppendInversion
import Eip8282.Audit.Integrator.SuccessfulUser

/-!
# Append receipts forced by successful message calls

Invert actual Θ success, derive the complete Ξ append receipt, and transport it
back through the actual settlement. Owner preservation excludes the empty-world
fallback. No gas, fuel, permission or fee-completion bounds are premises.

The independent storage interpretation retains its explicit AppendFits bound.
Other-account preservation is relative to the actual transferred entry world;
funding and installed-code authorization remain separate protocol obligations.
-/
namespace Eip8282.Audit.Integrator.SuccessfulAppend

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Correspondence (runtimeCode)
open MessageCall CallBridge CallSuccess SuccessfulQuote AppendInversion
open CommittedAppend WorldNonempty

/-- A Ξ receipt supplies its own owner witness, which resolves Θ settlement. -/
theorem commit_receipt (c : Context) {kind : Model.Kind}
    (hcode : c.code = runtimeCode kind) (steps : Nat) (hf : c.fuel = steps+1)
    (record : ByteArray) (hr : XiAppendResult (codeCall c hcode steps) record) :
    AppendResult c (codeCall c hcode steps) record := by
  obtain ⟨created, world, gas, substate, he, ho, hs, hp, hl, ha⟩ := hr
  obtain ⟨account, haccount⟩ := ho
  exact ⟨created, world, gas, substate,
    commits_endpoint c hcode steps hf _ _ _ _ _ he
      (beq_empty_false_of_get_some haccount), ⟨account, haccount⟩, hs, hp, hl, ha⟩

/-- Actual successful deposit admission forces the authentic committed append.
The initial owner premise concerns the world before value transfer. -/
theorem deposit_append (c : Context) (hcode : c.code = runtimeCode .deposit)
    (huser : c.caller ≠ EvmRunner.sysAddr) (hsize : c.calldata.size = 184)
    (ho : ∃ account, c.world.get? c.target = some account)
    (hfit : AppendStorage.AppendFits (codeCall c hcode (c.fuel-1)))
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    AppendResult c (codeCall c hcode (c.fuel-1)) c.calldata := by
  have hf : c.fuel = (c.fuel-1)+1 := by have hp := positive_fuel c h; omega
  obtain ⟨ew, es, he, _, _⟩ := codeCall_of_success c hcode (c.fuel-1) hf h
  exact commit_receipt c hcode (c.fuel-1) hf c.calldata
    (deposit_user_receipt _ huser hsize he
      (TransferFrame.codeCall_hasOwner c hcode (c.fuel-1) ho) hfit)

/-- Actual successful exit admission forces the caller-authenticated committed
append. The 20-byte source is the actual message caller. -/
theorem exit_append (c : Context) (hcode : c.code = runtimeCode .exit)
    (huser : c.caller ≠ EvmRunner.sysAddr) (hsize : c.calldata.size = 48)
    (ho : ∃ account, c.world.get? c.target = some account)
    (hfit : AppendStorage.AppendFits (codeCall c hcode (c.fuel-1)))
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    AppendResult c (codeCall c hcode (c.fuel-1)) (ExitRecord.record c.caller c.calldata) := by
  have hf : c.fuel = (c.fuel-1)+1 := by have hp := positive_fuel c h; omega
  obtain ⟨ew, es, he, _, _⟩ := codeCall_of_success c hcode (c.fuel-1) hf h
  exact commit_receipt c hcode (c.fuel-1) hf _
    (exit_user_receipt _ huser hsize he
      (TransferFrame.codeCall_hasOwner c hcode (c.fuel-1) ho) hfit)

/-- The same actual call is uninhibited, paid in natural arithmetic at its
completed operational quote, and commits the independent append receipt. -/
theorem deposit_paid_append (c : Context) (hcode : c.code = runtimeCode .deposit)
    (huser : c.caller ≠ EvmRunner.sysAddr) (hactual : c.apparentValue = c.value)
    (hsize : c.calldata.size = 184)
    (ho : ∃ account, c.world.get? c.target = some account)
    (hfit : AppendStorage.AppendFits (codeCall c hcode (c.fuel-1)))
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    let q := codeCall c hcode (c.fuel-1)
    Deposit.excessWord q ≠ INH ∧ ∃ n price,
      quoteWithin (Deposit.effExcess q) n = some price ∧
      1000000000 ≤ SubmissionCall.amount c.calldata ∧
      price.toNat + 1000000000 * SubmissionCall.amount c.calldata ≤ c.value.toNat ∧
      AppendResult c q c.calldata := by
  obtain ⟨hen, n, price, hq, hc⟩ := SuccessfulUser.deposit_admission c hcode huser hactual
    (by rw [hsize]; decide) h
  rcases hc with ⟨hz, _⟩ | ⟨_, hfloor, hpaid⟩
  · omega
  · exact ⟨hen, n, price, hq, hfloor, hpaid, deposit_append c hcode huser hsize ho hfit h⟩

/-- The actual completed operational fee and authenticated exit receipt belong
to the same successful message call, with actual transferred value binding. -/
theorem exit_paid_append (c : Context) (hcode : c.code = runtimeCode .exit)
    (huser : c.caller ≠ EvmRunner.sysAddr) (hactual : c.apparentValue = c.value)
    (hsize : c.calldata.size = 48)
    (ho : ∃ account, c.world.get? c.target = some account)
    (hfit : AppendStorage.AppendFits (codeCall c hcode (c.fuel-1)))
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (h : c.result = .ok (created, world, gas, substate, true, out)) :
    let q := codeCall c hcode (c.fuel-1)
    Exit.excessWord q ≠ INH ∧ ∃ n price,
      quoteWithin (Exit.effExcess q) n = some price ∧ price.toNat ≤ c.value.toNat ∧
      AppendResult c q (ExitRecord.record c.caller c.calldata) := by
  obtain ⟨hen, n, price, hq, hc⟩ := SuccessfulUser.exit_admission c hcode huser hactual
    (by rw [hsize]; decide) h
  rcases hc with ⟨hz, _⟩ | ⟨_, hpaid⟩
  · omega
  · exact ⟨hen, n, price, hq, hpaid, exit_append c hcode huser hsize ho hfit h⟩

#print axioms commit_receipt
#print axioms deposit_append
#print axioms exit_append
#print axioms deposit_paid_append
#print axioms exit_paid_append

end Eip8282.Audit.Integrator.SuccessfulAppend
