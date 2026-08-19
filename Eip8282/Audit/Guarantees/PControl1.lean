import Eip8282.Audit.Guarantees.Registry
import Eip8282.Audit.Model

namespace Eip8282.Audit.Guarantees.PControl1

open Eip8282.Audit.Model

def guarantee : Guarantee := ⟨.pControl1, [.model]⟩

theorem targets :
    targetOf .deposit = 8 ∧ targetOf .exit = 2 := by
  constructor <;> rfl

theorem initial_gating :
    inhibited initialDeposit = false ∧ inhibited initialExit = true := by
  constructor <;> rfl

theorem fee_getter_readonly
    (s : State) (caller : Address)
    (hInh : inhibited s = false) :
    userCall s caller [] 0 = .success s (toBeBytes (currentFee s) 32) := by
  unfold userCall
  simp [hInh]

theorem count_increments
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei)
    (hInh : inhibited s = false)
    (hne : calldata ≠ [])
    (hAdm : admissible s calldata value = true) :
    (userCall s caller calldata value).state.count = s.count + 1 := by
  unfold userCall
  simp [hInh, hne, hAdm, appendRecord]

theorem system_resets_count (s : State) (b : Bool) :
    (systemCall s b).state.count = 0 := by
  unfold systemCall
  simp

theorem nonempty_sets_inhibitor (s : State) :
    (systemCall s true).state.storedExcess = inhibitor := by
  unfold systemCall nextExcess
  simp

theorem empty_clears_inhibitor (s : State) (h : inhibited s = true) :
    (systemCall s false).state.storedExcess = 0 := by
  unfold systemCall nextExcess
  simp [h]

theorem empty_updates_excess (s : State) (h : inhibited s = false) :
    (systemCall s false).state.storedExcess =
      if s.storedExcess + s.count ≥ targetOf s.kind then
        s.storedExcess + s.count - targetOf s.kind
      else 0 := by
  unfold systemCall nextExcess
  simp [h]

theorem inhibit_users_not_system
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei) (b : Bool)
    (h : inhibited s = true) :
    (userCall s caller calldata value).isRevert = true ∧
      (systemCall s b).isRevert = false := by
  constructor
  · unfold userCall; simp [h]
  · unfold systemCall; simp

end Eip8282.Audit.Guarantees.PControl1
