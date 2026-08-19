import Eip8282.Audit.Model
import Eip8282.Audit.Guarantees.PSubmit1
import Eip8282.Audit.Guarantees.PDrain1
import Eip8282.Audit.Guarantees.PControl1

/-!
Kill-line mutants for the abstract model. These compile as counterexamples
to weakened claims. They are not registered guarantees.
-/

namespace Eip8282.Tests.Mutants

open Eip8282.Audit.Model
open Eip8282.Audit.Guarantees

/-- A value-bearing empty user call reverts; the parent forbids a balance change. -/
example (s : State) (caller : Address)
    (h : inhibited s = false) :
    (userCall s caller [] 1).isRevert = true ∧
      (userCall s caller [] 1).state.balance = s.balance := by
  unfold userCall
  simp [h]

/-- Caps are the EIP constants. A mutant that drained 65 deposits would
break `P-DRAIN-1`. -/
example : capOf .deposit = 64 ∧ capOf .exit = 16 := by
  constructor <;> rfl

/-- Exit starts inhibited, so a user write reverts. -/
example :
    inhibited initialExit = true ∧
      (userCall initialExit 0 [0] 0).isRevert = true := by
  constructor
  · rfl
  · unfold userCall
    simp [inhibited, initialExit]

end Eip8282.Tests.Mutants
