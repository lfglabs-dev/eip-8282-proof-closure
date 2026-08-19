import Eip8282.Audit.Guarantees.PSubmit1
import Eip8282.Audit.Guarantees.PDrain1
import Eip8282.Audit.Guarantees.PControl1

/-!
# Canonical three-guarantee public facade

`all` is the complete public surface. P-SUBMIT-1 additionally carries an
`.evm` layer: its parent runs the pinned runtime bytes under
`EvmYul.EVM.Ξ`. Empty Verity layers are intentional blockers, not omitted
proofs.
-/

namespace Eip8282.Audit.Guarantees

def all : List Guarantee :=
  [ PSubmit1.guarantee
  , PDrain1.guarantee
  , PControl1.guarantee
  ]

example : all.length = 3 := by decide

example : all.map (fun g => g.id.text) =
    ["P-SUBMIT-1", "P-DRAIN-1", "P-CONTROL-1"] := by decide

example : PSubmit1.guarantee.checkedLayers = [.model, .evm] := by decide
example : PDrain1.guarantee.checkedLayers = [.model] := by decide
example : PControl1.guarantee.checkedLayers = [.model] := by decide

end Eip8282.Audit.Guarantees
