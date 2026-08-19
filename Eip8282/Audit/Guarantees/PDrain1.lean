import Eip8282.Audit.Guarantees.Registry
import Eip8282.Audit.Model

namespace Eip8282.Audit.Guarantees.PDrain1

open Eip8282.Audit.Model

def guarantee : Guarantee := ⟨.pDrain1, [.model]⟩

theorem system_always_succeeds (s : State) (calldataNonempty : Bool) :
    (systemCall s calldataNonempty).isRevert = false := by
  unfold systemCall
  simp

theorem fifo_bounded (s : State) (calldataNonempty : Bool) :
    (systemCall s calldataNonempty).state.queue = s.queue.drop (capOf s.kind) := by
  unfold systemCall
  simp

theorem fifo_return (s : State) (calldataNonempty : Bool) :
    systemCall s calldataNonempty =
      .success (systemCall s calldataNonempty).state
        (concatReturned (s.queue.take (capOf s.kind))) := by
  unfold systemCall
  simp

theorem empty_queue_after_full_drain
    (s : State) (calldataNonempty : Bool)
    (h : s.queue.length ≤ capOf s.kind) :
    (systemCall s calldataNonempty).state.queue = [] := by
  unfold systemCall
  simp [List.drop_eq_nil_of_le h]

theorem encoding
    (calldata : List Byte) (amount : Nat) (source : Address) (pubkey : List Byte) :
    encodeReturned (.deposit calldata amount) =
      calldata.take 80 ++ toLeBytes amount 8 ++ calldata.drop 88 ∧
    encodeReturned (.exit source pubkey) = toBeBytes source 20 ++ pubkey := by
  constructor <;> rfl

end Eip8282.Audit.Guarantees.PDrain1
