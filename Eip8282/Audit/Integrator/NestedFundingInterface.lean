import Eip8282.Audit.Integrator.NestedFrameOccurrence
import Eip8282.Audit.Integrator.ExecutionFunding

/-!
# Entry funding interfaces for actual nested invocation traversal

The world is the literal request input. Only wrapper requests need admission:
Theta's transfer must be affordable, and Lambda additionally starts after a
positive sender nonce update. Actual selected-child gates must derive these
facts; they are not intended as per-child assumptions in the global theorem.
-/
namespace Eip8282.Audit.Integrator.NestedFunding
open EvmYul EvmYul.EVM
open NestedEvents TransferFunding
set_option autoImplicit false

def inputWorld : Request → AccountMap .EVM
  | .x _ _ pre => pre.accountMap
  | .xi _ a => a.world
  | .theta _ a => a.world
  | .lambda _ a => a.world
  | .step _ a => a.pre.accountMap

def GoodFunding : Request → Prop
  | .theta _ a => a.value.toNat ≤ worldBalance a.world a.source
  | .lambda _ a => a.value.toNat ≤ worldBalance a.world a.source ∧
      ExecutionFunding.NonzeroNonce a.world a.source
  | _ => True

end Eip8282.Audit.Integrator.NestedFunding
