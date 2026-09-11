#!/usr/bin/env python3
"""Finite nested rollback corroboration; injected state, never protocol reachability."""
from check_direct_semantics import *


def call_prefix(target, gas=None):
    # Copy 48-byte payload; CALL with value1 and empty return buffer.
    return bytes.fromhex("60305f5f375f5f60305f600173" + target[2:]) + (
        b"\x5a" if gas is None else b"\x62" + gas.to_bytes(3,"big")) + b"\xf1"


def run_cases(rpc, lock, runtimes):
    target = lock["addresses"]["builder_exit"]
    sender = rpc("eth_accounts")[0]
    outer = "0x1000000000000000000000000000000000000001"
    inner = "0x1000000000000000000000000000000000000002"
    payload = bytes.fromhex("ab"*48)
    rpc("anvil_setBalance", sender, hex(10**27))
    rpc("anvil_setCode", target, runtimes["exit"])
    cases = []
    for name in ("commit", "ancestor_revert", "caught_inner_oog"):
        prefix = call_prefix(target)
        if name == "caught_inner_oog":
            # Successful target CALL then an unconditional infinite loop at inner depth.
            loop = len(prefix) + 1
            inner_code = prefix + b"\x50\x5b\x60" + bytes([loop]) + b"\x56"
            outer_code = call_prefix(inner, 200000) + bytes.fromhex("5f5260205ff3")
            caller, depth = inner, 3
        else:
            inner_code = b""
            outer_code = prefix + bytes.fromhex("5f5260205f") + (b"\xf3" if name=="commit" else b"\xfd")
            caller, depth = outer, 2
        for address,code in ((outer,outer_code),(inner,inner_code)):
            rpc("anvil_setCode", address, "0x"+code.hex())
            rpc("anvil_setBalance", address, "0x0")
        for slot in range(16): rpc("anvil_setStorageAt",target,word(slot),word(0))
        rpc("anvil_setBalance",target,"0x0")
        before_sender = int(rpc("eth_getBalance",sender,"latest"),16)
        tx = {"from":sender,"to":outer,"value":"0x1","data":"0x"+payload.hex(),
              "gas":hex(GAS),"gasPrice":hex(10**10)}
        txid = rpc("eth_sendTransaction",tx)
        deadline = time.monotonic()+10
        receipt = None
        while receipt is None:
            require(time.monotonic()<deadline,"missing automined receipt")
            receipt = rpc("eth_getTransactionReceipt",txid)
            if receipt is None: time.sleep(0.05)
        require(int(receipt["status"],16)==(0 if name=="ancestor_revert" else 1),"unexpected final status")
        trace=rpc("debug_traceTransaction",txid,{"disableStorage":True,"enableMemory":True})
        steps=trace["structLogs"]
        logs=[s for s in steps if s["op"]=="LOG0" and s["depth"]==depth]
        require(len(logs)==1,"expected one executed target LOG0")
        log=logs[0]
        offset,size=int(log["stack"][-1],16),int(log["stack"][-2],16)
        memory=bytes.fromhex("".join(x.removeprefix("0x") for x in log["memory"]))
        authentic=bytes.fromhex(caller[2:])+payload
        require(memory[offset:offset+size]==authentic,"executed LOG0 caller/payload mismatch")
        ops=[s["op"] for s in steps if s["depth"]==depth]
        require(ops.count("SSTORE")==5 and "STOP" in ops,"target did not finish actual append")
        slots=[rpc("eth_getStorageAt",target,hex(i),"latest") for i in range(16)]
        balances={a:int(rpc("eth_getBalance",a,"latest"),16) for a in (target,outer,inner)}
        if name=="commit":
            require(len(receipt["logs"])==1,"committed append log missing")
            emitted=receipt["logs"][0]
            require(emitted["address"].lower()==target.lower() and emitted["topics"]==[] and bytes.fromhex(emitted["data"][2:])==authentic,"committed log mismatch")
            require([int(slots[i],16) for i in range(4)]==[0,1,0,1],"committed controls mismatch")
            require(int(slots[4],16)==int(caller,16) and int(slots[5],16)==int.from_bytes(payload[:32],"big") and int(slots[6],16)==int.from_bytes(payload[32:]+bytes(16),"big"),"queue record mismatch")
            require(balances[target]==1 and balances[outer]==0,"committed value mismatch")
        else:
            require(not receipt["logs"] and all(int(x,16)==0 for x in slots),"rolled-back append survived")
            require(balances[target]==0 and balances[inner]==0,"rolled-back nested value survived")
            require(balances[outer]==(1 if name=="caught_inner_oog" else 0),"outer value outcome mismatch")
        if name=="caught_inner_oog":
            require(int(trace["returnValue"].removeprefix("0x") or "0",16)==0,"outer did not catch failed inner CALL")
            inner_steps=[s for s in steps if s["depth"]==2]
            require("OutOfGas" in inner_steps[-1].get("error",""),"missing explicit inner OOG trace")
            require(inner_steps[-1]["op"] in ("JUMP","PUSH1","JUMPDEST"),"inner did not exhaust in loop")
            require(int(receipt["gasUsed"],16)>200000,"inner forwarded gas was not charged")
        fee=int(receipt["gasUsed"],16)*int(receipt["effectiveGasPrice"],16)
        loss=before_sender-int(rpc("eth_getBalance",sender,"latest"),16)
        require(loss==fee+(0 if name=="ancestor_revert" else 1),"sender value/gas accounting mismatch")
        cases.append({"case":name,"receipt":receipt,"slots_0_through_15":slots,"balances":balances,
          "gas_paid":fee,"sender_loss":loss,"executed_log0_data":"0x"+authentic.hex(),
          "actual_append_caller":caller,"target_trace_depth":depth,
          "target_opcode_counts":{op:ops.count(op) for op in ("SSTORE","LOG0","STOP")},
          "outer_code":"0x"+outer_code.hex(),"inner_code":"0x"+inner_code.hex(),
          "wrapper_sha256":{a:hashlib.sha256(c).hexdigest() for a,c in ((outer,outer_code),(inner,inner_code))},
          "inner_wrapper_terminal_step":({k:v for k,v in inner_steps[-1].items() if k not in ("memory","stack","storage")} if name=="caught_inner_oog" else None),
          "trace_return_value":trace["returnValue"],"trace_step_count":len(steps)})
    return {"transactions":cases,"injected_state":"Exact pinned Exit code, zero slots0..15 and target/wrapper balances; sender balance10^27; wrapper code injected. No constructor or canonical history."}

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
                    "Wrapper code and initial balances are injected; no SYSTEM scheduling is tested.",
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
