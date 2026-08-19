import Eip8282.Audit.Guarantees.Registry
import Eip8282.Audit.Model

namespace Eip8282.Audit.Guarantees.PSubmit1

open Eip8282.Audit.Model

def guarantee : Guarantee := ⟨.pSubmit1, [.model]⟩

theorem revert_is_atomic
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei) :
    (userCall s caller calldata value).isRevert = true →
      (userCall s caller calldata value).state = s := by
  unfold userCall
  by_cases hInh : inhibited s = true
  · simp [hInh]
  · simp [hInh]
    by_cases hEmpty : calldata = []
    · simp [hEmpty]
      by_cases hVal : value = 0
      · simp [hVal]
      · have : ¬ value = 0 := hVal
        simp [this]
    · simp [hEmpty]
      by_cases hAdm : admissible s calldata value = true
      · simp [hAdm]
      · simp [hAdm]

theorem success_count_and_balance
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei)
    (hInh : inhibited s = false)
    (hne : calldata ≠ [])
    (hAdm : admissible s calldata value = true) :
    let t := (userCall s caller calldata value).state
    t.count = s.count + 1 ∧
      t.balance = s.balance + value ∧
      t.queue = (appendRecord s caller calldata value).queue := by
  unfold userCall
  simp [hInh, hne, hAdm, appendRecord]

theorem deposit_appends_calldata
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei)
    (hk : s.kind = .deposit)
    (hInh : inhibited s = false)
    (hne : calldata ≠ [])
    (hAdm : admissible s calldata value = true) :
    (userCall s caller calldata value).state.queue =
      s.queue ++ [.deposit calldata (depositAmount calldata)] := by
  unfold userCall appendRecord
  simp [hInh, hne, hAdm, hk]

theorem exit_binds_caller
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei)
    (hk : s.kind = .exit)
    (hInh : inhibited s = false)
    (hne : calldata ≠ [])
    (hAdm : admissible s calldata value = true) :
    (userCall s caller calldata value).state.queue =
      s.queue ++ [.exit caller calldata] := by
  unfold userCall appendRecord
  simp [hInh, hne, hAdm, hk]

theorem inhibited_blocks_users
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei)
    (h : inhibited s = true) :
    userCall s caller calldata value = .revert s := by
  unfold userCall
  simp [h]

end Eip8282.Audit.Guarantees.PSubmit1
