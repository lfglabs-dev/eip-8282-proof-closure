/-!
# Abstract EIP-8282 predeploy model

Logical model of the two builder predeploys. This is the layer
`P-SUBMIT-1`, `P-DRAIN-1`, and `P-CONTROL-1` currently prove. It is not a
bytecode, EVM, or Verity claim.

Reachable states start from the specified deployments:

* Builder Deposit starts enabled, all slots zero.
* Builder Exit starts inhibited (`storedExcess = inhibitor`).

The logical queue is the pending records in FIFO order. Stale dequeued
storage slots are out of scope, matching the EIP text.
-/

namespace Eip8282.Audit.Model

abbrev Byte := Nat
abbrev Address := Nat
abbrev Wei := Nat

inductive Kind where
  | deposit
  | exit
  deriving DecidableEq, Repr

inductive Record where
  | deposit (calldata : List Byte) (amount : Nat)
  | exit (sourceAddress : Address) (pubkey : List Byte)
  deriving DecidableEq, Repr

structure State where
  kind : Kind
  storedExcess : Nat
  count : Nat
  queue : List Record
  balance : Wei
  deriving Repr

def inhibitor : Nat := 2 ^ 256 - 1

def systemAddress : Address := 0xfffffffffffffffffffffffffffffffffffffffe

def minRequestFee : Nat := 1
def feeUpdateFraction : Nat := 17
def maxDepositPerBlock : Nat := 64
def maxExitPerBlock : Nat := 16
def targetDeposit : Nat := 8
def targetExit : Nat := 2
def builderMinDepositWei : Wei := 1000000000000000000
def gwei : Wei := 1000000000
def depositInputSize : Nat := 184
def exitInputSize : Nat := 48
def pubkeySize : Nat := 48
def systemGasLimit : Nat := 30000000

def targetOf : Kind → Nat
  | .deposit => targetDeposit
  | .exit => targetExit

def capOf : Kind → Nat
  | .deposit => maxDepositPerBlock
  | .exit => maxExitPerBlock

def inhibited (s : State) : Bool := decide (s.storedExcess = inhibitor)

/-- EIP-1559 / EIP-7002 integer approximation of `factor * e^(numerator/denominator)`. -/
def fakeExponential (factor numerator denominator : Nat) : Nat :=
  let rec go (fuel i output numeratorAccum : Nat) : Nat :=
    match fuel with
    | 0 => output / denominator
    | fuel' + 1 =>
      if numeratorAccum = 0 then
        output / denominator
      else
        let output' := output + numeratorAccum
        let next := numeratorAccum * numerator / (denominator * i)
        go fuel' (i + 1) output' next
  go 256 1 0 (factor * denominator)

def effectiveExcess (s : State) : Nat :=
  s.storedExcess + (s.count - targetOf s.kind)

def currentFee (s : State) : Wei :=
  fakeExponential minRequestFee (effectiveExcess s) feeUpdateFraction

def initialDeposit : State :=
  { kind := .deposit, storedExcess := 0, count := 0, queue := [], balance := 0 }

def initialExit : State :=
  { kind := .exit, storedExcess := inhibitor, count := 0, queue := [], balance := 0 }

def beBytes (bs : List Byte) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b) 0

def toLeBytes : Nat → Nat → List Byte
  | _, 0 => []
  | n, w + 1 => (n % 256) :: toLeBytes (n / 256) w

def toBeBytes (n width : Nat) : List Byte := (toLeBytes n width).reverse

/-- Bytes 80–87 of a 184-byte deposit are the big-endian amount. -/
def depositAmount (calldata : List Byte) : Nat :=
  beBytes ((calldata.drop 80).take 8)

def bytesOk (bs : List Byte) : Bool := bs.all (fun b => decide (b < 256))

def depositWellFormed (calldata : List Byte) : Bool :=
  decide (calldata.length = depositInputSize) &&
    bytesOk calldata &&
    decide (depositAmount calldata * gwei ≥ builderMinDepositWei)

def exitWellFormed (pubkey : List Byte) : Bool :=
  decide (pubkey.length = pubkeySize) && bytesOk pubkey

inductive Outcome where
  | success (state : State) (returnData : List Byte)
  | revert (state : State)
  deriving Repr

def Outcome.state : Outcome → State
  | .success s _ => s
  | .revert s => s

@[simp] theorem Outcome.state_success (s : State) (d : List Byte) :
    (Outcome.success s d).state = s := rfl

@[simp] theorem Outcome.state_revert (s : State) :
    (Outcome.revert s).state = s := rfl

def Outcome.isRevert : Outcome → Bool
  | .success _ _ => false
  | .revert _ => true

@[simp] theorem Outcome.isRevert_success (s : State) (d : List Byte) :
    (Outcome.success s d).isRevert = false := rfl

@[simp] theorem Outcome.isRevert_revert (s : State) :
    (Outcome.revert s).isRevert = true := rfl

/-- System-call return encoding: deposits convert only the amount field to LE. -/
def encodeReturned : Record → List Byte
  | .deposit calldata amount =>
      calldata.take 80 ++ toLeBytes amount 8 ++ calldata.drop 88
  | .exit source pubkey =>
      toBeBytes source 20 ++ pubkey

def concatReturned (rs : List Record) : List Byte :=
  (rs.map encodeReturned).flatten

def admissible (s : State) (calldata : List Byte) (value : Wei) : Bool :=
  !inhibited s &&
    match s.kind with
    | .deposit =>
        depositWellFormed calldata &&
          decide (value ≥ depositAmount calldata * gwei + currentFee s)
    | .exit =>
        exitWellFormed calldata &&
          decide (value ≥ currentFee s)

def appendRecord (s : State) (caller : Address) (calldata : List Byte) (value : Wei)
    : State :=
  let queued : Record :=
    match s.kind with
    | .deposit => .deposit calldata (depositAmount calldata)
    | .exit => .exit caller calldata
  { s with
    count := s.count + 1
    queue := s.queue ++ [queued]
    balance := s.balance + value }

/-- Non-system call. Empty calldata is the fee getter. -/
def userCall (s : State) (caller : Address) (calldata : List Byte) (value : Wei)
    : Outcome :=
  if inhibited s then
    .revert s
  else if calldata = [] then
    if value ≠ 0 then
      .revert s
    else
      .success s (toBeBytes (currentFee s) 32)
  else
    if admissible s calldata value then
      .success (appendRecord s caller calldata value) []
    else
      .revert s

def nextExcess (s : State) (calldataNonempty : Bool) : Nat :=
  if calldataNonempty then inhibitor
  else if inhibited s then 0
  else if s.storedExcess + s.count ≥ targetOf s.kind then
    s.storedExcess + s.count - targetOf s.kind
  else 0

/-- Drain first, then inhibitor / excess, then reset count, then return. -/
def systemCall (s : State) (calldataNonempty : Bool) : Outcome :=
  .success
    { s with
      queue := s.queue.drop (capOf s.kind)
      storedExcess := nextExcess s calldataNonempty
      count := 0 }
    (concatReturned (s.queue.take (capOf s.kind)))

inductive Step where
  | user (caller : Address) (calldata : List Byte) (value : Wei)
  | system (calldataNonempty : Bool)

def step (s : State) : Step → Outcome
  | .user c d v => userCall s c d v
  | .system b => systemCall s b

inductive Reachable : State → Prop where
  | deposit : Reachable initialDeposit
  | exit : Reachable initialExit
  | step {s t} (h : Reachable s) (k : Step) :
      t = (step s k).state → Reachable t

end Eip8282.Audit.Model
