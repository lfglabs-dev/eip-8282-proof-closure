import Eip8282.Audit.Integrator.ProtectedLogFrame
import Eip8282.Audit.Integrator.ReachableCalls

/-! Source-shaped EIP-7708 log projection, not reference execution equivalence.
Proposed EL 0cc100eb190b64b23baba72dac0165652eaec252:
vm/__init__.py:40-43,252-288, SHA256
664702bc483736fca3c4ac4bb9e459a24c83f5365b495485c4674d5c41fbe993.
Emitter is SYSTEM; topics are signature hash, padded sender, padded recipient;
data is the big-endian amount. The signature hash is an explicit argument:
its Keccak/source binding and byte-representation transport are external,
and no cryptographic axiom is needed for address-only projection.
Actual process_call placement/guards and success-only child incorporation
remain reference adapters. Nothing filters LOG0 or changes the public clause.
-/
namespace Eip8282.Audit.Integrator.ReferenceTransferLogs
open EvmYul EvmYul.EVM
open ReachableCalls (Contract address)
set_option autoImplicit false

/-- UInt256 representation of the source's 32-byte padded address topic. -/
def addressTopic (a : AccountAddress) : UInt256 := UInt256.ofNat a.val

/-- Instantiate signature with keccak256("Transfer(address,address,uint256)").
Projection below holds for every signature, without trusting a hash evaluator. -/
def entry (signature : UInt256) (sender recipient : AccountAddress)
    (amount : UInt256) : LogEntry :=
  { address := Eip8282.Audit.EvmRunner.sysAddr,
    topics := #[signature, addressTopic sender, addressTopic recipient],
    data := amount.toByteArray }

/-- The actual helper emits nothing for a zero transfer. -/
def emitted (signature : UInt256) (sender recipient : AccountAddress)
    (amount : UInt256) : List LogEntry :=
  if amount = UInt256.ofNat 0 then [] else [entry signature sender recipient amount]

/-- Ordered all-topics address projection, shared with ProtectedLogFrame. -/
def project (a : AccountAddress) (logs : List LogEntry) : List LogEntry :=
  logs.filter (fun e => decide (e.address = a))

theorem project_substate (a : AccountAddress) (ss : Substate) :
    project a ss.logSeries.toList = ProtectedLogFrame.project a ss := rfl

theorem address_ne_system (kind : Contract) :
    address kind ≠ Eip8282.Audit.EvmRunner.sysAddr := by
  cases kind <;> decide +kernel

theorem project_append (a : AccountAddress) (left right : List LogEntry) :
    project a (left ++ right) = project a left ++ project a right := by
  simp [project,List.filter_append]

theorem project_entry (kind : Contract) (signature : UInt256)
    (sender recipient : AccountAddress) (amount : UInt256) :
    project (address kind) [entry signature sender recipient amount] = [] := by
  simp [project,entry,Ne.symm (address_ne_system kind)]

theorem project_emitted (kind : Contract) (signature : UInt256)
    (sender recipient : AccountAddress) (amount : UInt256) :
    project (address kind) (emitted signature sender recipient amount) = [] := by
  unfold emitted
  split
  · rfl
  · exact project_entry kind signature sender recipient amount

/-- The guarded process_call transfer prefix is invisible at either runtime.
The source producer must establish the actual should-transfer/nonalias guard. -/
theorem frame (kind : Contract) (signature : UInt256)
    (sender recipient : AccountAddress) (amount : UInt256)
    (enabled : Bool) (before after : List LogEntry) :
    project (address kind)
      (before ++ (if enabled then emitted signature sender recipient amount else []) ++ after) =
    project (address kind) before ++ project (address kind) after := by
  cases enabled with
  | false => simp [project]
  | true =>
    simp only [ite_true,project_append,project_emitted,List.append_nil]

/-- Source settlement chooses child logs only on success. This is a list
identity; actual reference error/success selection must be supplied separately. -/
theorem settle (a : AccountAddress) (success : Bool) (parent child : List LogEntry) :
    project a (parent ++ (if success then child else [])) =
    project a parent ++ (if success then project a child else []) := by
  cases success <;> simp [project]

/-- Ordered composition across any supplied frame list; no occurrence loss or
reordering is introduced by the address projection. -/
theorem project_flatMap (a : AccountAddress) (frames : List (List LogEntry)) :
    project a frames.flatten = frames.flatMap (project a) := by
  induction frames with
  | nil => rfl
  | cons head tail ih => simp only [List.flatten_cons,List.flatMap_cons,project_append,ih]

#print axioms project_substate
#print axioms address_ne_system
#print axioms project_append
#print axioms project_entry
#print axioms project_emitted
#print axioms frame
#print axioms settle
#print axioms project_flatMap
end Eip8282.Audit.Integrator.ReferenceTransferLogs
