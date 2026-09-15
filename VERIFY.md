# Verify EIP-8282

This is the reproduction guide for the three public guarantees
([P-SUBMIT-1](Eip8282/Audit/Integrator/DirectGuarantees.lean),
[P-DRAIN-1](Eip8282/Audit/Integrator/DirectGuarantees.lean),
[P-CONTROL-1](Eip8282/Audit/Integrator/DirectGuarantees.lean))
on the pinned deposit and exit bytecode.

The public report is pinned to
[`5b074e9`](https://github.com/lfglabs-dev/eip-8282-proof-closure/tree/5b074e949508b82168efe18057e1ca56a37078e4).
Bytecode hashes below are the same on that commit and on current `main`.

## Pins

| What | Value |
| --- | --- |
| Proof checkout | [`5b074e949508b82168efe18057e1ca56a37078e4`](https://github.com/lfglabs-dev/eip-8282-proof-closure/tree/5b074e949508b82168efe18057e1ca56a37078e4) |
| sys-asm | [`83f9801245ff56878a450b5625801101b9a225a1`](https://github.com/ethereum/sys-asm/tree/83f9801245ff56878a450b5625801101b9a225a1) |
| Working EIP text | [`lfglabs-dev/EIPs@b759aae8`](https://github.com/lfglabs-dev/EIPs/tree/b759aae809235802e23df47adeea50a1e6a7befb) · [ethereum/EIPs#12120](https://github.com/ethereum/EIPs/pull/12120) |
| Lean | 4.31.0 |
| EVMYulLean | [`b62586650b4f96cc6da25f36574aaa8f329a6420`](https://github.com/lfglabs-dev/EVMYulLean/tree/b62586650b4f96cc6da25f36574aaa8f329a6420) |
| Artifact lock | [`audit/artifacts.lock.json`](audit/artifacts.lock.json) |

## 1. Is this the bytecode?

EIP-8282 is in Review and is not active on any production chain. The two
predeploys are to be installed before the fork by the [EIP-7997](https://eips.ethereum.org/EIPS/eip-7997)
CREATE2 factory at `0x4e59b44847b379578588920cA78FbF26c0B4956C` with a mined
salt. That salt is not published in the EIP or in sys-asm, so the addresses
cannot be re-derived from the bytecode today.

What is already checked:

- the pinned runtime is byte-identical to the sys-asm build at `83f9801`
- each constructor is a copy header followed by that exact runtime
- the Lean initializer theorem shows the pinned constructor installs exactly
  the pinned runtime, with slot 0 zero for deposits and `INHIBITOR` for exits

| Contract | Address | Runtime SHA-256 |
| --- | --- | --- |
| Deposits | `0x0000bFF46984e3725691FA540a8C7589300D8282` | `1b643450f340305ced9814bb38e6ebcdad415674540570a650ebdec5ddb53b5f` |
| Exits | `0x000064D678505ad48F8cCb093BC65613800E8282` | `801baf70a2efb3ee383ff7a914e50113edcabc7a0a52d532af572de2042ca84f` |

Hex files live under [`pinned/bytecode/`](pinned/bytecode/). Assembly sources
live under [`pinned/sys-asm/`](pinned/sys-asm/).

### Check the lock against this checkout

Needs only Python 3:

```bash
python3 scripts/verify-deployment.py --proof-repo .
```

### Once the code is live

The same script checks factory code and, when the salts are published, the
CREATE2 derivation:

```bash
python3 scripts/verify-deployment.py --rpc "$RPC_URL"
```

Without the script, with Foundry’s `cast`:

```bash
cast code 0x0000bFF46984e3725691FA540a8C7589300D8282 --rpc-url "$RPC_URL" \
  | cut -c3- | tr -d '\n' | shasum -a 256
# expect 1b643450f340305ced9814bb38e6ebcdad415674540570a650ebdec5ddb53b5f

cast code 0x000064D678505ad48F8cCb093BC65613800E8282 --rpc-url "$RPC_URL" \
  | cut -c3- | tr -d '\n' | shasum -a 256
# expect 801baf70a2efb3ee383ff7a914e50113edcabc7a0a52d532af572de2042ca84f
```

## 2. Rebuild the proofs

Needs [elan](https://github.com/leanprover/elan) and Lean 4.31.0.

```bash
git checkout 5b074e949508b82168efe18057e1ca56a37078e4
make check
```

`make check` runs metadata lint, builds the three parent theorems, and compiles
the six registered mutation refutations. `make prove` first builds
`EvmYul.FFI.ffi:dynlib`; that is required because `native_decide` loads the
compiled EVM interpreter.

One guarantee plus its kill-line:

```bash
lake build EvmYul.FFI.ffi:dynlib
lake build Eip8282.Audit.Guarantees.PSubmit1 Eip8282.Tests.PSubmit1Mutant
```

The three registered parents are in
[`Eip8282/Audit/Integrator/DirectGuarantees.lean`](Eip8282/Audit/Integrator/DirectGuarantees.lean):

| ID | Theorem |
| --- | --- |
| P-SUBMIT-1 | `psubmit1_direct` |
| P-DRAIN-1 | `pdrain1_direct` |
| P-CONTROL-1 | `pcontrol1_direct` |

## 3. Mutations

Each guarantee has bytecode mutants that make the theorem fail. They are
registered in [`Eip8282/Tests/DirectThetaKills.lean`](Eip8282/Tests/DirectThetaKills.lean).

| Guarantee | What changes |
| --- | --- |
| P-SUBMIT-1 | LOG0 size 184 → 0 |
| P-DRAIN-1 | drain cap 64 → 32 and 16 → 8; HEAD write to a stale slot |
| P-CONTROL-1 | caller `EQ` → `LT`; TARGET 8 → 9 |
