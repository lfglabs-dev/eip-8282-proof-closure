import Eip8282.Audit.EvmRunner

/-!
C4, code-deposit half: the pinned **init** images run under `EvmYul.EVM.Ξ`.

`Ctor.lean` closes C4 on a CFG prefix. Its own note is explicit about the
gap: `fromHex` of the full init blobs times out in the kernel, so the
opcode facts there are `rfl` on the *first* `++` chunk of `depositInitHex`
and the first two chunks of `exitInitHex`. That reads the first 32 / 64
bytes of a 638 / 503-byte image and never runs it. Three things were
therefore unchecked:

* that the init image reaches its `RETURN` at all;
* that the buffer it returns is the pinned runtime **byte for byte**
  rather than merely "a copy starting at the right offset";
* that the exit ctor's `SSTORE` lands, as opposed to being present as an
  opcode 34 bytes in.

This module closes all three by executing the full pinned init images and
comparing the returned buffer against the pinned runtime images.

## What this is, and what it is not

`Λ` (`EvmYul.EVM.Semantics.Lambda`, EVMYulLean `0ff72b2`) is `Ξ` on the
init code followed by the code-deposit step (115): on success it writes
`code := returnedData` into the new account. `initDeploys` below is
exactly that `Ξ` half, plus the equality step (115) would use, stated
against the pinned runtime image.

It is deliberately **not** `Lambda` itself. `Lambda` derives its target
address as `KEC(RLP(sender, nonce))`, and the EIP-8282 contracts are
genesis predeploys at `0x0000bFF4…` / `0x000064D6…`, not `CREATE`
outputs. Driving `Lambda` here would pin an address that is provably not
the predeploy address, and would pull the `opaque @[extern]` keccak FFI
into the trusted base for no gain. The bytes an init image actually
*executes* are its preamble — 10 bytes for deposit, 45 for exit;
everything after that is the runtime carried as `CODECOPY` data — and
neither preamble contains a `SHA3`, `CREATE`, call or precompile-dispatch
opcode, so running them under `Ξ` leaves the `A-NATIVE-DECIDE` disclosure
exactly as `Ctor` and Wave-1 state it.

This does **not** discharge `A-PINNED-SOURCE`. It links `ctor.hex` to
`main.hex` inside the pin; it observes nothing on chain. The residual
open part is the deployed-address / deployed-codehash observation — see
`audit/assumptions.yaml`.
-/

namespace Eip8282.Audit.Guarantees.PControl1.CtorXi

open EvmYul
open EvmYul.EVM
open Eip8282.Audit.Bytecode
open Eip8282.Audit.EvmRunner

/-- The init images halt in far fewer steps than a runtime call: each
preamble is a `CODECOPY` and a `RETURN`. -/
def CTOR_FUEL : Nat := 20000

/-- Account that deploys the predeploy. Its identity is irrelevant to the
init programs — neither image reads `CALLER` before returning. -/
def deployer : Nat := 0x1234

/-- `Ξ` on an init image, with the account being created holding no code.

`Ξ` is entered with `executionEnv.code := initCode`, which is what
`CODESIZE` / `CODECOPY` read during creation, while the account being
created still has none. `EvmRunner.run` would additionally install
`initCode` as that account's code; the pinned preambles never read their
own account code, but leaving it empty is the faithful creation world. -/
def runInit (fuel : Nat) (target : AccountAddress) (initCode : ByteArray)
    : RunResult :=
  let σ : AccountMap .EVM :=
    (default : AccountMap .EVM)
      |>.insert target (mkAccount ByteArray.empty)
      |>.insert (toAddress deployer) (mkAccount ByteArray.empty oneEth)
  Ξ fuel default default default σ σ defaultGas default
    (callEnv target initCode (toAddress deployer) ZERO_U256 ByteArray.empty)

/-- Return buffer of a successful `Ξ`; empty on revert or interpreter error. -/
def returnBuffer (r : RunResult) : ByteArray :=
  match r with
  | .ok (.success _ o) => o
  | _ => ByteArray.empty

/-- The code-deposit step (115) of `Λ`, on bytes: running `initCode`
succeeds, and the buffer it returns is exactly `runtime` — the value
`Λ` would install as the new account's `code`. -/
def initDeploys (target : AccountAddress) (initCode runtime : ByteArray) : Bool :=
  let r := runInit CTOR_FUEL target initCode
  isSuccess r && bytesEq (returnBuffer r) runtime

/-- Deposit ctor: deploys `depositRuntime` and writes no storage. -/
def depositCtorFact (initCode : ByteArray) : Bool :=
  initDeploys depositAddr initCode depositRuntime
    && slots0to3Are (runInit CTOR_FUEL depositAddr initCode) depositAddr 0 0 0 0

/-- Exit ctor: deploys `exitRuntime` and leaves slot 0 = `INHIBITOR` with
slots 1–3 untouched. -/
def exitCtorFact (initCode : ByteArray) : Bool :=
  initDeploys exitAddr initCode exitRuntime
    && slots0to3Are (runInit CTOR_FUEL exitAddr initCode) exitAddr
        ((2 ^ 256) - 1) 0 0 0

/-- Both ctor facts, parameterised by the two init images so that a
one-byte init mutant can be fed to exactly the statement the parent is
registered against. -/
def ctorXiFacts (depInit exitInit : ByteArray) : Bool :=
  depositCtorFact depInit && exitCtorFact exitInit

/--
**C4 code-deposit trace, on pinned init bytecode.**

`Ξ` on the full pinned 638-byte deposit init and 503-byte exit init
images. Each returned buffer is the pinned `depositRuntime` /
`exitRuntime` byte for byte — the `code` that `Λ`'s step (115) would
install. The exit ctor additionally leaves slot 0 at `INHIBITOR` with
slots 1–3 zero; the deposit ctor writes nothing.

This is what ties `pinned/bytecode/*/ctor.hex` to
`pinned/bytecode/*/main.hex`. `audit/artifacts.lock.json` hashes the two
files independently, so until this theorem nothing in the repo ruled out
a ctor that deploys something other than the runtime every other
guarantee is proved about.

Kill-line: `Eip8282.Tests.PControl1Mutant.ctor_mutant_refutes_parent`
flips one byte of each init image — the deposit `CODECOPY` source offset
at 5 (`0x0a` → `0x0b`) and the exit `SSTORE` at 34 (`0x55` → `0x50`,
`POP`) — and shows `ctorXiFacts` is `false` on each.

Discharged by `native_decide` for cost, on the same terms as the Wave-1
traces: each image executes only its preamble before `RETURN`, and
neither preamble contains a `SHA3`, `CREATE`, call or precompile-dispatch
opcode, so no `opaque @[extern]` FFI constant and no `partial` RLP
decoder is reached. See `A-NATIVE-DECIDE`.
-/
theorem pcontrol1_ctor_xi_parent :
    ctorXiFacts depositInit exitInit = true := by
  native_decide

end Eip8282.Audit.Guarantees.PControl1.CtorXi
