import Eip8282.Audit.Integrator.ReferenceSystemTrace

/-! One constructed actual SYSTEM execution carries both its source-shaped
views and its sequential source-formula payment. Empty calldata discharges
the checked-size premise for the proposed mandatory dispatcher. This does not
adopt that dispatcher or identify source storage-gas readings. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemEntry
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView SystemExecutionResources SystemMeterResources
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem attach {kind : Kind} (c : XiCall kind)
    {steps cap outputBytes : Nat}
    (h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes c.fuel c.entry)
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState)
    (permission : c.env.perm = true) (cdfit : c.env.calldata.size < UInt256.size)
    (output_fit : outputBytes ≤ 32*cap) (host : 32*cap < 2^System.Platform.numBits) :
    ReferenceSystemTrace.Observed (parent := parent) h (initial c tx) := by
  have hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) c.entry := by
    cases kind
    · exact ⟨c.code_pinned,Or.inl RuntimeExecutionScope.deposit.entry⟩
    · exact ⟨c.code_pinned,Or.inl RuntimeExecutionScope.exit.entry⟩
  exact ReferenceSystemTrace.attach h hat (initial c tx)
    (initial_related c parent tx slots owner) permission cdfit output_fit host

/-- No independent execution, termination, operand or capacity certificate is
supplied. The one produced execution is used by both view and payment proofs. -/
theorem deposit (inputs : Inputs) (c : XiCall .deposit)
    (system : Deposit.callerWord c = sysW) (permission : c.env.perm = true)
    (gas : c.gas = UInt256.ofNat 30000000) (fuel : 8502 ≤ c.fuel)
    (empty : c.env.calldata = ByteArray.empty)
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) :
    ∃ h : Completed RuntimeExecutionScope.deposit 8500 400 11776 c.fuel c.entry,
      Paid inputs h systemMeter ∧
      ReferenceSystemTrace.Observed (kind := .deposit) (parent := parent) h (initial c tx) := by
  obtain ⟨h,hpaid⟩ := SystemMeterResources.deposit inputs c system permission gas fuel
  refine ⟨h,hpaid,attach c h parent tx slots owner permission ?_ (by decide) ?_⟩
  · rw [empty]; decide
  · rcases System.Platform.numBits_eq with hn | hn <;> rw [hn] <;> decide

theorem exit (inputs : Inputs) (c : XiCall .exit)
    (system : Exit.callerWord c = sysW) (permission : c.env.perm = true)
    (gas : c.gas = UInt256.ofNat 30000000) (fuel : 802 ≤ c.fuel)
    (empty : c.env.calldata = ByteArray.empty)
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) :
    ∃ h : Completed RuntimeExecutionScope.exit 800 40 1088 c.fuel c.entry,
      Paid inputs h systemMeter ∧
      ReferenceSystemTrace.Observed (kind := .exit) (parent := parent) h (initial c tx) := by
  obtain ⟨h,hpaid⟩ := SystemMeterResources.exit inputs c system permission gas fuel
  refine ⟨h,hpaid,attach c h parent tx slots owner permission ?_ (by decide) ?_⟩
  · rw [empty]; decide
  · rcases System.Platform.numBits_eq with hn | hn <;> rw [hn] <;> decide

#print axioms attach
#print axioms deposit
#print axioms exit
end Eip8282.Audit.Integrator.ReferenceSystemEntry
