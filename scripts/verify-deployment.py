#!/usr/bin/env python3
"""Check that EIP-8282 predeploys run the runtime bytecode the proofs are about.

No third-party dependencies. Three independent checks:

  1. Pinned artifacts   (--proof-repo PATH)
     Read pinned/bytecode/*.hex from a checkout of lfglabs-dev/eip-8282-proof-closure,
     compare their SHA-256 with audit/artifacts.lock.json values embedded below, and
     confirm each constructor is exactly `header || runtime` (so the initializer
     that the Lean proofs cover installs exactly the runtime they cover).

  2. Live chain          (--rpc URL)
     eth_getCode at the two EIP-8282 addresses and compare with the pinned runtime.
     Also checks the EIP-7997 factory code at 0x4e59...956C.
     EIP-8282 is not activated yet: empty code at both addresses is expected until
     the predeploys are installed before the fork.

  3. Address derivation  (--salt-deposit HEX --salt-exit HEX)
     The EIP says each address is CREATE2(factory, salt, initcode) with a mined salt.
     The salt is not published in EIP-8282 or in sys-asm@83f9801, so this check can
     only run once the salts are known. Requires --proof-repo for the init code.

Examples:
  python3 scripts/verify-deployment.py --proof-repo .
  python3 scripts/verify-deployment.py --rpc https://ethereum-rpc.publicnode.com
  python3 scripts/verify-deployment.py --proof-repo . --salt-deposit 0x... --salt-exit 0x...
"""
import argparse
import hashlib
import json
import sys
import urllib.request
from pathlib import Path

# From audit/artifacts.lock.json at proof pin 5b074e949508b82168efe18057e1ca56a37078e4.
SYS_ASM_COMMIT = "83f9801245ff56878a450b5625801101b9a225a1"
ADDRESSES = {
    "builder_deposits": "0x0000bFF46984e3725691FA540a8C7589300D8282",
    "builder_exits": "0x000064D678505ad48F8cCb093BC65613800E8282",
}
SYSTEM_ADDRESS = "0xfffffffffffffffffffffffffffffffffffffffe"
FACTORY_ADDRESS = "0x4e59b44847b379578588920cA78FbF26c0B4956C"  # EIP-7997
FACTORY_RUNTIME = (
    "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0"
    "3601600081602082378035828234f58015156039578182fd5b8082525050506014600cf3"
)
# SHA-256 of the hex text files (lowercase hex, no trailing newline).
PINNED_SHA256 = {
    "pinned/bytecode/builder_deposits/main.hex": "1b643450f340305ced9814bb38e6ebcdad415674540570a650ebdec5ddb53b5f",
    "pinned/bytecode/builder_deposits/ctor.hex": "20d76f572f22c4f70415bd3310aeb4b0ccd9a9d961f22096afb88d7cdd2c9ef6",
    "pinned/bytecode/builder_exits/main.hex": "801baf70a2efb3ee383ff7a914e50113edcabc7a0a52d532af572de2042ca84f",
    "pinned/bytecode/builder_exits/ctor.hex": "678d5945780f4c3e8cbe713559d63b9a3b8844df73a416a88ef920cb4af4807f",
}


# --- keccak-256 (pure Python, only needed for CREATE2 derivation) -------------
_RHO = [[0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61], [28, 55, 25, 21, 56], [27, 20, 39, 8, 14]]
_RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]
_MASK = (1 << 64) - 1


def _rol(x, n):
    return ((x << n) | (x >> (64 - n))) & _MASK


def _keccak_f(state):
    """Keccak-f[1600] on 25 little-endian lanes, lane index = x + 5*y."""
    a = [[state[x + 5 * y] for y in range(5)] for x in range(5)]
    for rc in _RC:
        c = [a[x][0] ^ a[x][1] ^ a[x][2] ^ a[x][3] ^ a[x][4] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rol(c[(x + 1) % 5], 1) for x in range(5)]
        a = [[a[x][y] ^ d[x] for y in range(5)] for x in range(5)]
        b = [[0] * 5 for _ in range(5)]
        for x in range(5):
            for y in range(5):
                b[y][(2 * x + 3 * y) % 5] = _rol(a[x][y], _RHO[x][y])
        a = [[b[x][y] ^ ((~b[(x + 1) % 5][y]) & b[(x + 2) % 5][y] & _MASK) for y in range(5)] for x in range(5)]
        a[0][0] ^= rc
    return [a[i % 5][i // 5] for i in range(25)]


def keccak256(data: bytes) -> bytes:
    rate = 136
    padded = bytearray(data) + b"\x01"
    while len(padded) % rate:
        padded.append(0)
    padded[-1] |= 0x80
    state = [0] * 25
    for off in range(0, len(padded), rate):
        block = padded[off:off + rate]
        for i in range(rate // 8):
            state[i] ^= int.from_bytes(block[8 * i:8 * i + 8], "little")
        state = _keccak_f(state)
    return b"".join(state[i].to_bytes(8, "little") for i in range(4))


def create2_address(factory: str, salt: bytes, initcode: bytes) -> str:
    pre = b"\xff" + bytes.fromhex(factory[2:]) + salt + keccak256(initcode)
    return "0x" + keccak256(pre)[12:].hex()


# --- checks -------------------------------------------------------------------
def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def load_pinned(proof_repo: Path):
    files = {}
    ok = True
    for rel, expected in PINNED_SHA256.items():
        text = (proof_repo / rel).read_text().strip().lower()
        files[rel] = text
        digest = sha256_text(text)
        status = "ok" if digest == expected else "MISMATCH"
        ok &= digest == expected
        print(f"[pinned]   {status:8} {rel}  sha256={digest[:16]}…")
    for kind in ("builder_deposits", "builder_exits"):
        ctor = files[f"pinned/bytecode/{kind}/ctor.hex"]
        main = files[f"pinned/bytecode/{kind}/main.hex"]
        tail = ctor.endswith(main)
        ok &= tail
        header = ctor[: len(ctor) - len(main)] if tail else ""
        print(f"[pinned]   {'ok' if tail else 'MISMATCH':8} {kind}: constructor = header({len(header)//2} bytes) || runtime({len(main)//2} bytes)")
    return files, ok


def rpc(url: str, method: str, params):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
    req = urllib.request.Request(
        url, data=body,
        headers={"content-type": "application/json", "user-agent": "eip-8282-verify-deployment/1"},
    )
    with urllib.request.urlopen(req, timeout=30) as resp:
        payload = json.loads(resp.read())
    if "error" in payload:
        raise RuntimeError(payload["error"])
    return payload["result"]


def check_chain(url: str, pinned):
    ok = True
    chain_id = int(rpc(url, "eth_chainId", []), 16)
    print(f"[chain]    chainId={chain_id}")
    factory = rpc(url, "eth_getCode", [FACTORY_ADDRESS, "latest"])[2:].lower()
    fstatus = "ok" if factory == FACTORY_RUNTIME else ("absent" if not factory else "MISMATCH")
    ok &= factory == FACTORY_RUNTIME
    print(f"[chain]    {fstatus:8} EIP-7997 factory {FACTORY_ADDRESS}")
    for kind, address in ADDRESSES.items():
        code = rpc(url, "eth_getCode", [address, "latest"])[2:].lower()
        expected = pinned.get(f"pinned/bytecode/{kind}/main.hex") if pinned else None
        if not code:
            print(f"[chain]    absent   {kind} {address}: no code yet (EIP-8282 not activated on this chain)")
            ok = False
            continue
        digest = sha256_text(code)
        if expected is not None:
            match = code == expected
        else:
            match = digest == PINNED_SHA256[f"pinned/bytecode/{kind}/main.hex"]
        ok &= match
        print(f"[chain]    {'ok' if match else 'MISMATCH':8} {kind} {address}: {len(code)//2} bytes, sha256={digest[:16]}…")
    return ok


def check_salts(pinned, salt_deposit: str, salt_exit: str):
    ok = True
    for kind, salt_hex in (("builder_deposits", salt_deposit), ("builder_exits", salt_exit)):
        salt = bytes.fromhex(salt_hex[2:] if salt_hex.startswith("0x") else salt_hex).rjust(32, b"\x00")
        initcode = bytes.fromhex(pinned[f"pinned/bytecode/{kind}/ctor.hex"])
        derived = create2_address(FACTORY_ADDRESS, salt, initcode)
        match = derived.lower() == ADDRESSES[kind].lower()
        ok &= match
        print(f"[create2]  {'ok' if match else 'MISMATCH':8} {kind}: CREATE2(factory, salt, initcode) = {derived}")
    return ok


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--proof-repo", type=Path, help="checkout of lfglabs-dev/eip-8282-proof-closure")
    parser.add_argument("--rpc", help="JSON-RPC endpoint of the chain to inspect")
    parser.add_argument("--salt-deposit", help="CREATE2 salt used for the deposit predeploy (hex)")
    parser.add_argument("--salt-exit", help="CREATE2 salt used for the exit predeploy (hex)")
    args = parser.parse_args()
    if not (args.proof_repo or args.rpc):
        parser.error("give --proof-repo and/or --rpc")

    # self-test the keccak implementation against a known vector
    assert keccak256(b"").hex() == "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

    ok = True
    pinned = None
    print(f"pinned sys-asm commit {SYS_ASM_COMMIT}")
    if args.proof_repo:
        pinned, good = load_pinned(args.proof_repo)
        ok &= good
    if args.rpc:
        ok &= check_chain(args.rpc, pinned)
    if args.salt_deposit or args.salt_exit:
        if not (pinned and args.salt_deposit and args.salt_exit):
            parser.error("--salt-deposit and --salt-exit both require --proof-repo")
        ok &= check_salts(pinned, args.salt_deposit, args.salt_exit)
    print("RESULT:", "all checks passed" if ok else "some checks did not pass (see above)")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
