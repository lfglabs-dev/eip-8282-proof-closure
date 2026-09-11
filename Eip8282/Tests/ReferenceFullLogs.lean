import Eip8282.Audit.Integrator.ReferenceFullLogTotal

/-! Injected finite instruction/settlement fixtures, not initialized histories.
They distinguish current-frame transfer emission from an inherited replay
prefix, keep LOG3 before LOG0, and discard both on REVERT or gas failure. -/
namespace Eip8282.Tests.ReferenceFullLogs
open EvmYul EvmYul.EVM Eip8282.Audit.Integrator
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private def ap : ReferenceAccountLookup.Parent Unit := ⟨fun _ => none,fun _ => none⟩
private def accounts : ReferenceAccountLookup.Tx Unit := ⟨fun _ => none,∅⟩
private def sp : ReferenceStorageView.Parent := ⟨fun _ _ => none,fun _ _ => ⟨0⟩⟩
private def storage : ReferenceStorageView.Tx := ⟨fun _ _ => none,∅,∅⟩
private def transfer : LogEntry := ReferenceTransferLogs.entry ⟨1⟩ ⟨1,by decide⟩ (ReachableCalls.address .deposit) ⟨42⟩
private def record : LogEntry := ⟨ReachableCalls.address .deposit,#[],.empty⟩
private def frame (bytes : ByteArray) : View :=
  ⟨{(default : ExecutionEnv .EVM) with code := bytes, codeOwner := ReachableCalls.address .deposit, perm := true},0,[⟨0⟩,⟨0⟩],.empty,storage,[transfer]⟩
private noncomputable def execution (bytes : ByteArray) (fuel gas : Nat) :=
  ReferenceCheckedAccountEvaluator.eval ap [] sp .empty fuel accounts (frame bytes) ∅ (ReferenceChildMeter.init gas 0)
private noncomputable def logs (bytes : ByteArray) (fuel gas : Nat) (inherited : List LogEntry := []) : Option (List LogEntry) :=
  match execution bytes fuel gas with
  | none => none
  | some ((_,out),_) => match ReferenceCheckedFrameOutcome.settle storage inherited ∅ out with
    | .returned r => some r.logsForParent
    | _ => none

/-- Literal LOG0 then STOP forwards the transfer and record exactly once. -/
theorem success_order : logs ⟨#[0xa0,0x00]⟩ 2 1000 = some [transfer,record] := by rfl

/-- Passing the newly emitted transfer as inherited loses it on success. -/
theorem rejects_inherited_prefix :
    logs ⟨#[0xa0,0x00]⟩ 2 1000 [transfer] = some [record] ∧
    logs ⟨#[0xa0,0x00]⟩ 2 1000 [transfer] ≠ logs ⟨#[0xa0,0x00]⟩ 2 1000 := by
  constructor
  · rfl
  · intro wrong
    have lengths := congrArg (fun x : Option (List LogEntry) => x.map List.length) wrong
    change some 1 = some 2 at lengths
    contradiction

/-- LOG0; PUSH0; PUSH0; REVERT has emitted two internal logs but commits none. -/
theorem revert_discards_all :
    logs ⟨#[0xa0,0x5f,0x5f,0xfd]⟩ 4 1000 = some [] ∧
    (match execution ⟨#[0xa0,0x5f,0x5f,0xfd]⟩ 4 1000 with
      | some ((_,.terminal r),_) => r.view.logs = [transfer,record] ∧ r.halt = .reverted
      | _ => False) := by exact ⟨rfl,rfl,rfl⟩

/-- The first actual CALLER in either pinned runtime fails at zero gas;
the transfer remains in the internal view and is discarded at settlement. -/
theorem out_of_gas_discards_transfer (kind : ReachableCalls.Contract) :
    logs (ReachableCalls.runtime kind) 1 0 = some [] := by
  cases kind <;> rfl

#print axioms success_order
#print axioms rejects_inherited_prefix
#print axioms revert_discards_all
#print axioms out_of_gas_discards_transfer
end Eip8282.Tests.ReferenceFullLogs
