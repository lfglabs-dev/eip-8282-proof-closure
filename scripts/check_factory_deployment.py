#!/usr/bin/env python3
"""Finite actual factory deployments on injected local Anvil Prague state."""
from check_direct_semantics import *
import ast
import re


def deployment_pins(lock):
    archive_path = ROOT / 'audit/receipts/direct-reference-migration-deployment-sources-20260910.json'
    archive = json.loads(archive_path.read_text())
    sources = {s['path']: s for s in archive['sources']}
    for s in sources.values():
        require(hashlib.sha256(s['text'].encode()).hexdigest() == s['sha256'], 'archive body hash mismatch')
    spec = sources['tests/amsterdam/eip7997_deterministic_factory_predeploy/spec.py']
    factory_code = None
    for node in ast.walk(ast.parse(spec['text'])):
        if isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name) and node.target.id == 'FACTORY_BYTECODE':
            factory_code = bytes.fromhex(ast.literal_eval(node.value.args[0]))
    require(factory_code is not None and len(factory_code) == 69, 'factory source literal missing')
    lean_path = ROOT / 'Eip8282/Audit/Integrator/FactoryRuntimeEntry.lean'
    lean = lean_path.read_text()
    body = re.search(r'def runtime : ByteArray := ⟨#\[(.*?)\]⟩', lean, re.S).group(1)
    require(bytes(int(x.strip(), 16) for x in body.split(',')) == factory_code, 'Lean factory mismatch')
    bytecode_path = ROOT / 'Eip8282/Audit/Bytecode.lean'
    bytecode = bytecode_path.read_text()
    fixtures = {}
    for kind in ('deposit', 'exit'):
        src = sources[f'tests/amsterdam/eip8282_builder_execution_requests/builder_{kind}_factory_deploy.json']
        f = json.loads(src['text'])
        init = bytes.fromhex(f['initcode'][2:])
        ctor_path = f'pinned/bytecode/builder_{kind}s/ctor.hex'
        raw = (ROOT / ctor_path).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == lock['files'][ctor_path], 'ctor file pin mismatch')
        require(bytes.fromhex(raw.decode().strip().removeprefix('0x')) == init, 'source init differs from pinned ctor')
        lean_array = re.search(r'def '+kind+r'InitBytes : Array UInt8 :=\s*#\[(.*?)\]', bytecode, re.S).group(1)
        require(bytes(int(x.strip(), 0) for x in lean_array.split(',') if x.strip()) == init, 'Lean init array mismatch')
        salt = re.search(r'\| \.'+kind+r' => UInt256.ofNat (0x[0-9a-f]+)', lean).group(1)
        require(int(salt,16) == int(f['salt'],16), 'Lean salt mismatch')
        f.update(source_path=src['path'], source_sha256=src['sha256'], init_sha256=hashlib.sha256(init).hexdigest())
        fixtures[kind] = f
    return factory_code, fixtures, {'archive_sha256':hashlib.sha256(archive_path.read_bytes()).hexdigest(),
        'reference_commit':archive['commit'], 'factory_source_path':spec['path'], 'factory_source_sha256':spec['sha256'],
        'lean_factory_sha256':hashlib.sha256(lean_path.read_bytes()).hexdigest(),
        'lean_bytecode_sha256':hashlib.sha256(bytecode_path.read_bytes()).hexdigest()}


def run_cases(rpc, lock, runtimes, factory_code, fixtures):
    sender = rpc('eth_accounts')[0]
    factory = fixtures['deposit']['factory'].lower()
    require(factory == fixtures['exit']['factory'].lower(), 'factory mismatch')
    rpc('anvil_setCode', factory, '0x'+factory_code.hex())
    rpc('anvil_setNonce', factory, '0x1')
    rpc('anvil_setBalance', factory, '0x0')
    rpc('anvil_setBalance', sender, hex(10**27))
    base = rpc('evm_snapshot')
    cases = []

    def state(address):
        return {'code':rpc('eth_getCode',address,'latest'), 'nonce':rpc('eth_getTransactionCount',address,'latest'),
            'balance':rpc('eth_getBalance',address,'latest'),
            'slots_0_through_3':[rpc('eth_getStorageAt',address,hex(i),'latest') for i in range(4)]}

    def send(tx, expected):
        before = int(rpc('eth_getBalance',sender,'latest'),16)
        txid = rpc('eth_sendTransaction',tx)
        deadline = time.monotonic()+10
        receipt = None
        while receipt is None:
            require(time.monotonic()<deadline, 'missing receipt')
            receipt = rpc('eth_getTransactionReceipt',txid)
            if receipt is None: time.sleep(.05)
        require(int(receipt['status'],16)==expected, 'unexpected transaction status')
        trace = rpc('debug_traceTransaction',txid,{'disableStorage':True,'enableMemory':True})
        require(not receipt['logs'], 'deployment unexpectedly emitted logs')
        cost = int(receipt['gasUsed'],16)*int(receipt['effectiveGasPrice'],16)
        loss = before-int(rpc('eth_getBalance',sender,'latest'),16)
        require(loss == cost+(int(tx['value'],16) if expected else 0), 'gas/value accounting mismatch')
        return receipt, trace, cost

    for kind, fixture in fixtures.items():
        expected = lock['addresses'][f'builder_{kind}'].lower()
        init_hash = rpc('web3_sha3',fixture['initcode'])
        preimage = '0xff'+factory[2:]+fixture['salt'][2:]+init_hash[2:]
        calculated = '0x'+rpc('web3_sha3',preimage)[-40:]
        require(calculated.lower()==expected, 'CREATE2 address mismatch')
        fixture.update(init_keccak=init_hash, create2_preimage=preimage, computed_address=calculated)
        for prefund in (0, 1):
            require(rpc('evm_revert',base), 'snapshot revert failed')
            base = rpc('evm_snapshot')
            if prefund: rpc('anvil_setBalance',expected,hex(prefund))
            before = state(expected)
            require(before['code']=='0x' and int(before['nonce'],16)==0 and all(int(x,16)==0 for x in before['slots_0_through_3']), 'target not collision-free')
            require(int(before['balance'],16)==prefund, 'wrong target prefund')
            tx = {'from':sender,'to':factory,'data':fixture['salt']+fixture['initcode'][2:],
                'value':'0x7','gas':hex(1_100_000),'gasPrice':hex(10**10)}
            callout = rpc('eth_call',tx,'latest')
            require(callout.lower()==expected and len(bytes.fromhex(callout[2:]))==20, 'factory eth_call output mismatch')
            require(state(expected)==before, 'eth_call committed state')
            receipt, trace, fee = send(tx,1)
            after = state(expected)
            require(after['code'].lower()==runtimes[kind], 'deployed runtime mismatch')
            require(int(after['nonce'],16)==1 and int(after['balance'],16)==prefund+7, 'deployed nonce/balance mismatch')
            require([int(x,16) for x in after['slots_0_through_3']]==([MODULUS-1,0,0,0] if kind=='exit' else [0]*4), 'initializer slots mismatch')
            require(trace['returnValue'].removeprefix('0x').lower()==expected[2:], 'actual transaction return mismatch')
            steps=trace['structLogs']; creates=[s for s in steps if s['op']=='CREATE2']
            require(len(creates)==1 and creates[0]['depth']==1, 'actual factory CREATE2 missing')
            create = creates[0]
            value,offset,length,salt = [int(create['stack'][-i],16) for i in range(1,5)]
            memory = bytes.fromhex(''.join(x.removeprefix('0x') for x in create['memory']))
            require(value==7 and offset==0 and length==len(bytes.fromhex(fixture['initcode'][2:]))
                and salt==int(fixture['salt'],16), 'actual CREATE2 operands mismatch')
            require(memory[offset:offset+length]==bytes.fromhex(fixture['initcode'][2:]), 'CREATE2 init memory mismatch')
            require(any(s['depth']==2 and s['op']=='RETURN' for s in steps), 'actual initializer RETURN missing')
            require(int(rpc('eth_getBalance',factory,'latest'),16)==0
                and int(rpc('eth_getTransactionCount',factory,'latest'),16)==2, 'factory nonce/value mismatch')
            require(not any(s['op'].startswith('LOG') for s in steps), 'unexpected executed log')
            factory_before_retry=state(factory)
            retry_receipt,retry_trace,retry_fee=send(tx,0)
            require(state(expected)==after and state(factory)==factory_before_retry, 'collision retry changed deployed state/factory')
            require(any(s['op']=='CREATE2' for s in retry_trace['structLogs']) and retry_trace['structLogs'][-1]['op']=='REVERT', 'collision did not reach factory revert')
            cases.append({'kind':kind,'prefund':prefund,'before':before,'after':after,'transaction':tx,
                'eth_call_return':callout,'receipt':receipt,'gas_paid':fee,'trace':trace,
                'collision_retry':{'receipt':retry_receipt,'gas_paid':retry_fee,'trace':retry_trace}})
        require(rpc('evm_revert',base), 'snapshot revert failed')
        base=rpc('evm_snapshot')
        before=state(expected); fb=state(factory)
        tx={'from':sender,'to':factory,'data':fixture['salt']+fixture['initcode'][2:],
            'value':'0x7','gas':hex(80_000),'gasPrice':hex(10**10)}
        receipt,trace,fee=send(tx,0)
        require(state(expected)==before and state(factory)==fb, 'low-gas failure left state changes')
        require(any(s['op']=='CREATE2' for s in trace['structLogs']), 'low-gas failure occurred before CREATE2')
        require(any(s['depth']==2 for s in trace['structLogs']), 'low-gas case did not enter initializer')
        require(trace['failed'], 'low-gas execution unexpectedly succeeded')
        child_steps=[s for s in trace['structLogs'] if s['depth']==2]
        terminal=child_steps[-1]
        if kind=='deposit':
            require(terminal['op']=='RETURN' and terminal['gas'] < 200*len(bytes.fromhex(runtimes[kind][2:])),
                'deposit did not fail at code-deposit gas boundary')
            failure='initializer returned; remaining gas below runtime code-deposit cost'
        else:
            require(terminal['op']=='SSTORE' and 'OutOfGas' in terminal.get('error',''),
                'exit did not exhaust at initializer SSTORE')
            failure='initializer SSTORE out of gas'
        require(trace['structLogs'][-1]['op']=='REVERT', 'factory did not revert after failed creation')
        cases.append({'kind':kind,'case':'insufficient_gas','failure_evidence':failure,'transaction':tx,'before':before,
            'after':state(expected),'receipt':receipt,'gas_paid':fee,'trace':trace})
    return {'factory':factory,'factory_runtime':'0x'+factory_code.hex(), 'factory_runtime_sha256':hashlib.sha256(factory_code).hexdigest(),
        'sender':sender,'injected_state':{'factory':'exact runtime, nonce1, balance0','sender_balance':10**27,
        'target':'absent or balance-only prefund1; code/nonce/storage not injected'},'fixtures':fixtures,'cases':cases}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--anvil',default=shutil.which('anvil') or str(Path.home()/'.foundry/bin/anvil'))
    args=parser.parse_args()
    require(Path(args.anvil).is_file(),'Anvil binary missing')
    lock,runtimes,hashes,lock_hash=load_pins()
    factory,fixtures,binding=deployment_pins(lock)
    version=subprocess.check_output([args.anvil,'--version'],text=True,timeout=10).strip()
    with socket.socket() as sock:
        sock.bind(('127.0.0.1',0));port=sock.getsockname()[1]
    command=[args.anvil,'--host','127.0.0.1','--port',str(port),'--hardfork','prague',
        '--gas-limit','30000000','--steps-tracing','--silent']
    with tempfile.TemporaryFile(mode='w+') as log:
        process=subprocess.Popen(command,stdout=log,stderr=log,env=os.environ.copy())
        try:
            rpc=RPC(port);deadline=time.monotonic()+15
            while True:
                require(process.poll() is None,'Anvil exited during startup')
                try:
                    client=rpc('web3_clientVersion');break
                except (urllib.error.URLError,TimeoutError,ConnectionError):
                    require(time.monotonic()<deadline,'startup timeout');time.sleep(.1)
            report={'classification':'finite_injected_state_factory_deployment_regressions',
                'protocol_reachability_proved':False,'proof_substitute':False,'hardfork':'prague',
                'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                'anvil_version':version,'client_version':client,'command':command,
                'artifacts_lock_sha256':lock_hash,'pins':lock['pins'],'runtimes':hashes,'source_binding':binding,
                'started_at_utc':datetime.now(timezone.utc).isoformat(),
                'limitations':['Fresh local chain with injected factory and sender balance; no canonical genesis/history.',
                    'Prague engine, not proposed Amsterdam dual-pool reference semantics.',
                    'Only slots0..3 checked; trace and installed runtime retained in full.',
                    'No production broadcast, no proof or normative-adoption claim.']}
            report.update(run_cases(rpc,lock,runtimes,factory,fixtures))
            report['status']='passed';report['completed_at_utc']=datetime.now(timezone.utc).isoformat()
            print(json.dumps(report,indent=2))
        finally:
            process.terminate()
            try:process.wait(timeout=5)
            except subprocess.TimeoutExpired:process.kill();process.wait(timeout=5)


if __name__=='__main__':main()
