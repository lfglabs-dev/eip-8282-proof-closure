/-!
# Public guarantee registry

This is an interface registry, not a proof-progress registry. A nonempty
`checkedLayers` list names only the Lean evidence already declared; an empty
list does not manufacture a theorem.

The three public IDs are the campaign's canonical surface:

* `P-SUBMIT-1` — atomic paid submission and authentic append
* `P-DRAIN-1` — exact bounded FIFO system drain
* `P-CONTROL-1` — exact fee, count, and reversible-inhibition state machine
-/

namespace Eip8282.Audit.Guarantees

inductive Id
  | pSubmit1 | pDrain1 | pControl1
  deriving DecidableEq, Repr

def Id.text : Id → String
  | .pSubmit1 => "P-SUBMIT-1"
  | .pDrain1 => "P-DRAIN-1"
  | .pControl1 => "P-CONTROL-1"

inductive CheckedLayer
  /-- Abstract semantic model with machine-checked properties. -/
  | model
  /-- Verity Lean library program of the assembly control flow. -/
  | source
  /-- Verity Executable Contract over a `ContractState`. -/
  | verityTx
  /-- Pinned runtime bytecode executed by `EvmYul.EVM.Ξ`. -/
  | evm
  deriving DecidableEq, Repr

structure Guarantee where
  id : Id
  checkedLayers : List CheckedLayer

end Eip8282.Audit.Guarantees
