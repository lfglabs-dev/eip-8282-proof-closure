#!/usr/bin/env python3
"""Finite injected-state regressions on pinned runtimes using local Anvil/revm.

No fork, remote RPC, broadcast, deployment, or protocol-reachability claim.
Only Python's standard library and an installed Anvil executable are required.
Prints a JSON evidence report to stdout; exits nonzero on any failed check.
The 4096-step evaluator guard raises on exhaustion, never returns a partial fee.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import socket
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request


ROOT = Path(__file__).resolve().parents[1]
MODULUS = 1 << 256
CASES = (1607, 1608, 1620, 2892, 2893)
RPC_TIMEOUT = 10
GAS = 1_000_000


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def fee(numerator, word_arithmetic):
    """Return only a completed quote; record a historical 256-step partial sum."""
    output, accumulator, counter = 0, 17, 1
    cutoff_output = None
    overflow = False
    for steps in range(4097):
        if steps == 256:
            cutoff_output = output // 17
        if accumulator == 0:
            return {
                "quote": output // 17,
                "iterations": steps,
                "historical_256_partial_quote": cutoff_output,
                "overflow_observed": overflow,
            }
        require(steps < 4096, "fee evaluator guard exhausted without completion")
        sum_ = output + accumulator
        product = numerator * accumulator
        denominator = counter * 17
        next_counter = counter + 1
        overflow |= any(x >= MODULUS for x in (sum_, product, denominator, next_counter))
        if word_arithmetic:
            sum_, product, denominator, next_counter = (
                x % MODULUS for x in (sum_, product, denominator, next_counter)
            )
        output = sum_
        accumulator = product // denominator if denominator else 0  # EVM DIV by zero.
        counter = next_counter
    raise RuntimeError("unreachable evaluator exit")


class RPCError(RuntimeError):
    def __init__(self, method, payload):
        super().__init__(f"{method}: {payload}")
        self.payload = payload


class RPC:
    def __init__(self, port):
        self.url = f"http://127.0.0.1:{port}"
        self.sequence = 0
        # Do not allow environment proxy settings to redirect local RPC traffic.
        self.opener = urllib.request.build_opener(urllib.request.ProxyHandler({}))

    def __call__(self, method, *params):
        self.sequence += 1
        data = json.dumps({"jsonrpc": "2.0", "id": self.sequence,
                           "method": method, "params": params}).encode()
        request = urllib.request.Request(self.url, data, {"Content-Type": "application/json"})
        with self.opener.open(request, timeout=RPC_TIMEOUT) as response:
            result = json.load(response)
        if "error" in result:
            raise RPCError(method, result["error"])
        return result["result"]


def word(value):
    return "0x" + value.to_bytes(32, "big").hex()


def load_pins():
    lock_path = ROOT / "audit/artifacts.lock.json"
    lock = json.loads(lock_path.read_text())
    runtimes, hashes = {}, {}
    for kind in ("deposit", "exit"):
        path = f"pinned/bytecode/builder_{kind}s/main.hex"
        raw = (ROOT / path).read_bytes()
        actual = hashlib.sha256(raw).hexdigest()
        require(actual == lock["files"][path], f"pin SHA-256 mismatch: {path}")
        code = bytes.fromhex(raw.decode().strip().removeprefix("0x"))
        runtimes[kind] = "0x" + code.hex()
        hashes[kind] = {"path": path, "file_sha256": actual,
                        "runtime_sha256": hashlib.sha256(code).hexdigest(), "bytes": len(code)}
    return lock, runtimes, hashes, hashlib.sha256(lock_path.read_bytes()).hexdigest()


def run_cases(rpc, lock, runtimes):
    addresses = {kind: lock["addresses"][f"builder_{kind}"] for kind in runtimes}
    system = lock["addresses"]["system"]
    sender = rpc("eth_accounts")[0]
    wrapper = "0x1000000000000000000000000000000000000001"
    rpc("anvil_impersonateAccount", system)
    for account in (sender, system):
        rpc("anvil_setBalance", account, hex(10**27))
    for kind, address in addresses.items():
        rpc("anvil_setCode", address, runtimes[kind])
        require(rpc("eth_getCode", address, "latest").lower() == runtimes[kind], "installed code differs")

    def reset(address, excess=0, count=0):
        for slot in range(16):
            value = excess if slot == 0 else count if slot == 1 else 0
            rpc("anvil_setStorageAt", address, word(slot), word(value))
        rpc("anvil_setBalance", address, "0x0")

    def snapshot(address):
        return {"slots_0_through_15": [rpc("eth_getStorageAt", address, hex(i), "latest")
                                       for i in range(16)],
                "balance": rpc("eth_getBalance", address, "latest")}

    def transaction(address, caller=sender, value=0, data="0x", expected_status=1):
        tx = {"from": caller, "to": address, "value": hex(value), "data": data,
              "gas": hex(GAS), "gasPrice": hex(10**10)}
        tx_hash = rpc("eth_sendTransaction", tx)
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            receipt = rpc("eth_getTransactionReceipt", tx_hash)
            if receipt is not None:
                require(int(receipt["status"], 16) == expected_status, f"unexpected status for {tx_hash}")
                return receipt
            time.sleep(0.05)
        raise RuntimeError("receipt deadline exceeded")

    report = {"fees": [], "transactions": []}
    calculated = {x: {"word": fee(x, True), "natural": fee(x, False)} for x in CASES}
    require(calculated[1620]["natural"]["quote"] -
            calculated[1620]["natural"]["historical_256_partial_quote"] == 1,
            "1620 must expose the one-wei historical cutoff discrepancy")
    require(calculated[2893]["word"]["quote"] < calculated[2892]["word"]["quote"],
            "expected adjacent-input word-fee drop")
    require(calculated[2893]["word"]["overflow_observed"], "2893 must expose word overflow")
    for kind, address in addresses.items():
        for excess in CASES:
            reset(address, excess=excess)
            before = snapshot(address)
            returned = rpc("eth_call", {"from": sender, "to": address,
                                        "data": "0x", "value": "0x0", "gas": hex(GAS)}, "latest")
            require(len(returned) == 66, "getter must return exactly 32 bytes")
            require(int(returned, 16) == calculated[excess]["word"]["quote"], "EVM quote differs from word evaluator")
            # eth_call cannot establish readonly behavior: it discards writes.
            # Execute a real transaction and check its committed effects and trace.
            receipt = transaction(address)
            after = snapshot(address)
            require(after == before and not receipt["logs"], "getter transaction retained writes, value, or logs")
            trace = rpc("debug_traceTransaction", receipt["transactionHash"],
                        {"disableMemory": True, "disableStack": True, "disableStorage": True})
            require(bool(trace["structLogs"]), "getter execution trace is empty")
            forbidden_ops = {"SSTORE", "TSTORE", "LOG0", "LOG1", "LOG2", "LOG3", "LOG4"}
            require(not any(step["op"] in forbidden_ops for step in trace["structLogs"]),
                    "getter executed a storage write or log instruction")
            report["fees"].append({"kind": kind, "excess": excess, "count": 0,
                "return_data": returned, **calculated[excess], "getter_receipt": receipt,
                "getter_before": before, "getter_after": after,
                "getter_trace_storage_write_or_log_count": 0})

        reset(address, excess=MODULUS - 5, count=10)
        before = snapshot(address)
        receipt = transaction(address, caller=system)
        after = snapshot(address)
        target = 8 if kind == "deposit" else 2
        expected_excess = max(0, 5 - target)
        require(int(after["slots_0_through_15"][0], 16) == expected_excess, "fold must wrap before comparing")
        require(int(after["slots_0_through_15"][1], 16) == 0, "SYSTEM must reset count")
        # The M-5 / 10 example gives 0 for deposit but 3 for exit.
        report["transactions"].append({"case": "system_intermediate_sum_overflow", "kind": kind,
            "before": before, "after": after, "receipt": receipt,
            "natural_excess": MODULUS - 5 + 10 - target})

        reset(address)
        before = snapshot(address)
        receipt = transaction(address, value=1, expected_status=0)
        after = snapshot(address)
        require(before == after and not receipt["logs"], "paid getter must revert with no retained value, writes, or logs")
        report["transactions"].append({"case": "paid_getter_revert", "kind": kind,
                                        "before": before, "after": after, "receipt": receipt})

    exit_address = addresses["exit"]
    reset(exit_address, excess=MODULUS - 1)
    before = snapshot(exit_address)
    receipt = transaction(exit_address, value=1, data="0x" + "ab" * 48, expected_status=0)
    after = snapshot(exit_address)
    require(before == after and not receipt["logs"], "inhibited user must have no committed effects")
    report["transactions"].append({"case": "inhibited_exit_user", "before": before,
                                    "after": after, "receipt": receipt})
    receipt = transaction(exit_address, caller=system)
    after = snapshot(exit_address)
    require(all(int(slot, 16) == 0 for slot in after["slots_0_through_15"]), "empty SYSTEM must unlock")
    report["transactions"].append({"case": "inhibited_exit_system_unlock", "after": after, "receipt": receipt})

    # Test outer rollback *after* actual inner SSTORE and LOG0 instructions.
    # CALLDATACOPY(0,0,48); CALL(gas,exit,1,0,48,0,0); MSTORE(0,success);
    # REVERT(0,32). Its RETURN variant is used only in eth_call as a positive control.
    prefix = bytes.fromhex("60305f5f375f5f60305f600173" + exit_address[2:] + "5af15f5260205f")
    reset(exit_address)
    rpc("anvil_setCode", wrapper, "0x" + (prefix + b"\xf3").hex())
    rpc("anvil_setBalance", wrapper, "0x0")
    call = {"from": sender, "to": wrapper, "value": "0x1", "data": "0x" + "ab" * 48, "gas": hex(GAS)}
    require(int(rpc("eth_call", call, "latest"), 16) == 1, "inner append positive control failed")
    rpc("anvil_setCode", wrapper, "0x" + (prefix + b"\xfd").hex())
    before = snapshot(exit_address)
    wrapper_balance = rpc("eth_getBalance", wrapper, "latest")
    sender_balance = int(rpc("eth_getBalance", sender, "latest"), 16)
    receipt = transaction(wrapper, value=1, data=call["data"], expected_status=0)
    after = snapshot(exit_address)
    trace = rpc("debug_traceTransaction", receipt["transactionHash"],
                {"disableMemory": True, "disableStack": True, "disableStorage": True})
    require(bool(trace["structLogs"]), "rollback execution trace is empty")
    outer_depth = trace["structLogs"][0]["depth"]
    inner_ops = [step["op"] for step in trace["structLogs"] if step["depth"] == outer_depth + 1]
    require("SSTORE" in inner_ops and "LOG0" in inner_ops and "STOP" in inner_ops,
            "trace must show successful inner append before outer revert")
    require(before == after and not receipt["logs"], "outer rollback failed for inner writes/logs")
    require(rpc("eth_getBalance", wrapper, "latest") == wrapper_balance, "outer value transfer survived revert")
    gas_paid = int(receipt["gasUsed"], 16) * int(receipt["effectiveGasPrice"], 16)
    require(sender_balance - int(rpc("eth_getBalance", sender, "latest"), 16) == gas_paid,
            "sender must lose gas fees only, not reverted call value")
    report["transactions"].append({"case": "outer_revert_after_successful_exit_append",
        "before": before, "after": after, "receipt": receipt, "gas_paid": gas_paid,
        "inner_trace_counts": {op: inner_ops.count(op) for op in ("SSTORE", "LOG0", "STOP")},
        "wrapper_runtime": "0x" + (prefix + b"\xfd").hex()})
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--anvil", default=shutil.which("anvil") or str(Path.home() / ".foundry/bin/anvil"))
    args = parser.parse_args()
    require(Path(args.anvil).is_file(), f"Anvil executable not found: {args.anvil}")
    lock, runtimes, hashes, lock_hash = load_pins()
    version = subprocess.check_output([args.anvil, "--version"], text=True, timeout=10).strip()
    with socket.socket() as sock:
        sock.bind(("127.0.0.1", 0))
        port = sock.getsockname()[1]
    command = [args.anvil, "--host", "127.0.0.1", "--port", str(port),
               "--hardfork", "prague", "--gas-limit", "30000000", "--steps-tracing", "--silent"]
    with tempfile.TemporaryFile(mode="w+") as log:
        process = subprocess.Popen(command, stdout=log, stderr=log, env=os.environ.copy())
        try:
            rpc = RPC(port)
            deadline = time.monotonic() + 15
            while True:
                require(process.poll() is None, "Anvil exited during startup")
                try:
                    client = rpc("web3_clientVersion")
                    break
                except (urllib.error.URLError, TimeoutError, ConnectionError):
                    require(time.monotonic() < deadline, "Anvil startup deadline exceeded")
                    time.sleep(0.1)
            report = {"classification": "finite_injected_state_regressions",
                "protocol_reachability_proved": False, "proof_substitute": False,
                "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                "started_at_utc": datetime.now(timezone.utc).isoformat(),
                "client_version": client, "anvil_version": version, "hardfork": "prague",
                "artifacts_lock_sha256": lock_hash, "pins": lock["pins"], "runtimes": hashes,
                "limitations": ["Storage and runtime code injected into a fresh local Anvil chain.",
                    "SYSTEM impersonation checks CALLER dispatch, not consensus scheduling.",
                    "Gas receipts are specific to this engine/version/hardfork and these inputs.",
                    "Storage snapshots cover slots 0 through 15 for these finite cases.",
                    "No production-chain or protocol-reachability claim."]}
            report.update(run_cases(rpc, lock, runtimes))
            report["status"] = "passed"
            report["completed_at_utc"] = datetime.now(timezone.utc).isoformat()
            print(json.dumps(report, indent=2))
        finally:
            process.terminate()
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=5)


if __name__ == "__main__":
    main()
