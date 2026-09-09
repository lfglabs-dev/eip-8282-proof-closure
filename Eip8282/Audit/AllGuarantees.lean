import Eip8282.Audit.Guarantees.PSubmit1
import Eip8282.Audit.Guarantees.PDrain1
import Eip8282.Audit.Guarantees.PControl1
import Eip8282.Audit.Integrator.DirectGuarantees

/-!
# Canonical three-guarantee public facade

`all` is the complete public surface. All three IDs carry an `.evm` layer:
their registered parents quantify actual completed Θ calls under explicit local
domains. Control also includes actual Λ initialization and SYSTEM progress.
Protocol-domain coverage remains OPEN; historical CFG parents remain imported.
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
example : PDrain1.guarantee.checkedLayers = [.model, .evm] := by decide
example : PControl1.guarantee.checkedLayers = [.model, .evm] := by decide


-- Exact registered conditional parents, for each of the two contract kinds.
example (kind : Eip8282.Audit.Model.Kind) :
    Eip8282.Audit.Integrator.DirectGuarantees.PSubmit kind (Eip8282.Audit.Correspondence.runtimeCode kind) :=
  Eip8282.Audit.Integrator.DirectGuarantees.psubmit1_direct kind
example (kind : Eip8282.Audit.Model.Kind) :
    Eip8282.Audit.Integrator.DirectGuarantees.PDrain kind (Eip8282.Audit.Correspondence.runtimeCode kind) :=
  Eip8282.Audit.Integrator.DirectGuarantees.pdrain1_direct kind
example (kind : Eip8282.Audit.Model.Kind) :
    Eip8282.Audit.Integrator.DirectGuarantees.PControl kind
      (Eip8282.Audit.Correspondence.runtimeCode kind) (Eip8282.Audit.Integrator.Initialization.initCode kind) :=
  Eip8282.Audit.Integrator.DirectGuarantees.pcontrol1_direct kind

end Eip8282.Audit.Guarantees
