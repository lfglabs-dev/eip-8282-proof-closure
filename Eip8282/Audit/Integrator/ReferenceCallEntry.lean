import Eip8282.Audit.Integrator.ReferenceValueTransfer
import Eip8282.Audit.Integrator.ReferenceTransferLogs

/-! EL0cc process_call's value-transfer and synthetic-log guards, explicitly
separating apparent value from actual transfer. This binds the source-shaped
entry operations to the pinned Θ context. Python state-diff representation,
actual call-kind production, execution and settlement remain separate. -/
namespace Eip8282.Audit.Integrator.ReferenceCallEntry
open EvmYul EvmYul.EVM
open TransferFunding
open ReachableCalls (Contract address)
set_option autoImplicit false

def transferred (shouldTransfer : Bool) (apparent : UInt256) : UInt256 :=
  if shouldTransfer then apparent else UInt256.ofNat 0

def world (c : MessageCall.Context) (shouldTransfer : Bool) : AccountMap .EVM :=
  if shouldTransfer ∧ c.apparentValue ≠ UInt256.ofNat 0 then
    ProtocolTransfer.transfer c.world c.caller c.target c.apparentValue
  else c.world

def logs (c : MessageCall.Context) (shouldTransfer : Bool)
    (signature : UInt256) : List LogEntry :=
  if shouldTransfer ∧ c.apparentValue ≠ UInt256.ofNat 0 ∧ c.caller ≠ c.target then
    [ReferenceTransferLogs.entry signature c.caller c.target c.apparentValue]
  else []

/-- CALLVALUE continues to expose apparent value when transfer is disabled. -/
theorem apparent_value (c : MessageCall.Context) :
    c.environment.weiValue = c.apparentValue := rfl

theorem world_eq (c : MessageCall.Context) (shouldTransfer : Bool)
    (binding : c.value = transferred shouldTransfer c.apparentValue) :
    world c shouldTransfer = ReferenceValueTransfer.referenceEntry c := by
  cases shouldTransfer <;>
    simp_all [transferred,world,ReferenceValueTransfer.referenceEntry]

theorem lookup (c : MessageCall.Context) (shouldTransfer : Bool)
    (binding : c.value = transferred shouldTransfer c.apparentValue)
    (funded : c.value.toNat ≤ worldBalance c.world c.caller) (addr : AccountAddress) :
    c.entryWorld.get? addr = (world c shouldTransfer).get? addr := by
  rw [world_eq c shouldTransfer binding]
  exact ReferenceValueTransfer.entry_lookup c funded addr

theorem disabled (c : MessageCall.Context)
    (binding : c.value = transferred false c.apparentValue) (signature : UInt256) :
    (∀ addr, c.entryWorld.get? addr = c.world.get? addr) ∧
      logs c false signature = [] ∧ c.environment.weiValue = c.apparentValue := by
  have funded : c.value.toNat ≤ worldBalance c.world c.caller := by
    rw [binding]
    exact Nat.zero_le _
  exact ⟨fun addr => by simpa [world] using lookup c false binding funded addr,
    by simp [logs],rfl⟩

theorem protected_logs (kind : Contract) (c : MessageCall.Context)
    (shouldTransfer : Bool) (signature : UInt256) :
    ReferenceTransferLogs.project (address kind) (logs c shouldTransfer signature) = [] := by
  unfold logs
  split
  · exact ReferenceTransferLogs.project_entry kind signature c.caller c.target c.apparentValue
  · rfl

/-- The same ledger derives checked arithmetic at the enabled branch and
pointwise full-account entry parity; source transfer logs preserve the existing
all-topics protected-address projection, including alias and disabled cases. -/
theorem from_ledger (kind : Contract) (c : MessageCall.Context)
    (shouldTransfer : Bool) (signature : UInt256)
    (binding : c.value = transferred shouldTransfer c.apparentValue)
    {p w s credits : Nat}
    (ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world p w s credits c.world)
    (counts : ProtocolCreditEnvelope.Counts p w s)
    (funded : c.value.toNat ≤ worldBalance c.world c.caller) :
    (shouldTransfer = true →
      c.apparentValue.toNat ≤ worldBalance c.world c.caller ∧
      worldBalance (ProtocolTransfer.debit c.world c.caller c.apparentValue) c.target +
        c.apparentValue.toNat < UInt256.size) ∧
    (∀ addr, c.entryWorld.get? addr = (world c shouldTransfer).get? addr) ∧
    ReferenceTransferLogs.project (address kind) (logs c shouldTransfer signature) = [] ∧
    c.environment.weiValue = c.apparentValue := by
  refine ⟨?_,lookup c shouldTransfer binding funded,protected_logs kind c shouldTransfer signature,rfl⟩
  intro enabled
  have hv : c.value = c.apparentValue := by simpa [transferred,enabled] using binding
  have guard := (ReferenceValueTransfer.from_ledger c ledger counts funded).1
  exact ⟨by simpa [hv] using funded,by simpa [hv] using guard⟩

#print axioms apparent_value
#print axioms world_eq
#print axioms lookup
#print axioms disabled
#print axioms protected_logs
#print axioms from_ledger
end Eip8282.Audit.Integrator.ReferenceCallEntry
