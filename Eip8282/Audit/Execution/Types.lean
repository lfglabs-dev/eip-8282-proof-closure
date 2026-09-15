
/-! Execution support used by the registered direct guarantees.
Extracted from Eip8282.Audit.Model; historical model correspondence
is kept in the candidate library. Public namespaces are preserved. -/

namespace Eip8282.Audit.Model

abbrev Byte := Nat

inductive Kind where
  | deposit
  | exit
  deriving DecidableEq, Repr

def beBytes (bs : List Byte) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b) 0

def toLeBytes : Nat → Nat → List Byte
  | _, 0 => []
  | n, w + 1 => (n % 256) :: toLeBytes (n / 256) w

def toBeBytes (n width : Nat) : List Byte := (toLeBytes n width).reverse

/-- Bytes 80–87 of a 184-byte deposit are the big-endian amount. -/
def depositAmount (calldata : List Byte) : Nat :=
  beBytes ((calldata.drop 80).take 8)

end Eip8282.Audit.Model
