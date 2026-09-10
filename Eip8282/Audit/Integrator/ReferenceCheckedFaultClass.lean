import Eip8282.Audit.Integrator.ReferenceCheckedDispatch

/-! Checked-handler fault classification at the audited Python catch boundary.
EL 0cc100eb, archived in direct-reference-amsterdam-gas-sources-20260910.json:
vm/exceptions.py lines 35–98, SHA256
 e3e4b0b24c5b5702a64851d2ac675d1d2fc526aa3f1a439b17d5c2d22c569a01;
vm/interpreter.py lines 443–474, SHA256
 8281535f92be8cfe663033716baf9418ffc37b6c8861f70ac357e41fb6cf4c82.
Only ExceptionalHalt and Revert are caught around instruction execution.
The Ops ValueError is translated locally to InvalidOpcode, not all ValueErrors.
Checked U256 construction raises builtin OverflowError (ethereum-types 0.4.1,
numeric.py, SHA256 47d040d4de043e46d19c2fd9f74b318396b6c83ab01fe346f98a3c477e58db46,
archived in direct-reference-checked-types-sources-20260910.json).
The owner assertion in state_tracker.py line 454 raises builtin AssertionError
(SHA256 ce420ad5682df9051178d298220d1552448e26c37f67be3b604b9f493541cf4a).
Neither builtin exception inherits the source ExceptionalHalt class.

This is a classification of all represented checked faults, not a mechanical
Python extraction theorem or a proof that arbitrary inputs avoid host failures.
Uncaught means not caught by this process_call boundary, not by every caller.
REVERT is a separate terminal result, not a Fault. EOF, unsupported and proof
fuel exhaustion are also not Faults. No rollback or gas forfeiture is performed
or inferred here; the consumer must bind this classification to the same actual
failure and preserve its partial state before source settlement. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedFaultClass
open ReferenceCheckedDispatch
set_option autoImplicit false

inductive SourceException where
  | stackUnderflow | stackOverflow | outOfGas | invalidJump
  | staticWrite | invalidOpcode | conversionOverflow | ownerAssertion
  deriving DecidableEq, Repr

inductive CatchClass where
  | exceptionalHalt | uncaughtConversion | uncaughtAssertion
  deriving DecidableEq, Repr

def binary : ReferenceCheckedBinaryStep.Failure → SourceException
  | .stack .underflow => .stackUnderflow
  | .stack .overflow => .stackOverflow
  | .outOfGas => .outOfGas

/-- Exhaustive mapping of the represented failures; no default OOG branch. -/
def classify : Fault → SourceException
  | .binary e => binary e
  | .environment (.checked e) => binary e
  | .environment .conversionOverflow => .conversionOverflow
  | .stackControl (.checked e) => binary e
  | .stackControl .conversionOverflow => .conversionOverflow
  | .stackControl .invalidJump => .invalidJump
  | .storage (.checked e) => binary e
  | .storage .staticWrite => .staticWrite
  | .storage .missingOwnerAssertion => .ownerAssertion
  | .copyLog (.checked e) => binary e
  | .copyLog .staticWrite => .staticWrite
  | .invalidOpcode _ => .invalidOpcode

def catchClass : SourceException → CatchClass
  | .conversionOverflow => .uncaughtConversion
  | .ownerAssertion => .uncaughtAssertion
  | _ => .exceptionalHalt

def caught (fault : Fault) : Bool :=
  decide (catchClass (classify fault) = .exceptionalHalt)

/-- Precisely the three represented uncaught constructors, independent of any
source reachability or account-initialization premise. -/
theorem caught_iff (fault : Fault) : caught fault = true ↔
    fault ≠ .environment .conversionOverflow ∧
    fault ≠ .stackControl .conversionOverflow ∧
    fault ≠ .storage .missingOwnerAssertion := by
  cases fault with
  | binary e => cases e with
    | stack e => cases e <;> simp [caught, catchClass, classify, binary]
    | outOfGas => simp [caught, catchClass, classify, binary]
  | environment e => cases e with
    | checked e => cases e with
      | stack e => cases e <;> simp [caught, catchClass, classify, binary]
      | outOfGas => simp [caught, catchClass, classify, binary]
    | conversionOverflow => simp [caught, catchClass, classify]
  | stackControl e => cases e with
    | checked e => cases e with
      | stack e => cases e <;> simp [caught, catchClass, classify, binary]
      | outOfGas => simp [caught, catchClass, classify, binary]
    | conversionOverflow => simp [caught, catchClass, classify]
    | invalidJump => simp [caught, catchClass, classify]
  | storage e => cases e with
    | checked e => cases e with
      | stack e => cases e <;> simp [caught, catchClass, classify, binary]
      | outOfGas => simp [caught, catchClass, classify, binary]
    | staticWrite => simp [caught, catchClass, classify]
    | missingOwnerAssertion => simp [caught, catchClass, classify]
  | copyLog e => cases e with
    | checked e => cases e with
      | stack e => cases e <;> simp [caught, catchClass, classify, binary]
      | outOfGas => simp [caught, catchClass, classify, binary]
    | staticWrite => simp [caught, catchClass, classify]
  | invalidOpcode tag => simp [caught, catchClass, classify]

theorem conversion_classes :
    catchClass (classify (.environment .conversionOverflow)) = .uncaughtConversion ∧
    catchClass (classify (.stackControl .conversionOverflow)) = .uncaughtConversion := by
  exact ⟨rfl,rfl⟩

theorem assertion_class :
    catchClass (classify (.storage .missingOwnerAssertion)) = .uncaughtAssertion := rfl

theorem caught_class (fault : Fault) : caught fault = true ↔
    catchClass (classify fault) = .exceptionalHalt := by
  simp only [caught, decide_eq_true_eq]

#print axioms caught_iff
#print axioms conversion_classes
#print axioms assertion_class
#print axioms caught_class
end Eip8282.Audit.Integrator.ReferenceCheckedFaultClass
