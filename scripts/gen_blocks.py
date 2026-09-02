#!/usr/bin/env python3
"""Generate the straight-line block tables and rfl shape lemmas for both pinned runtimes.

Blocks are maximal straight-line runs of `blockOps` between the effectful sites
(JUMPI, SSTORE, MSTORE, MSTORE8, CALLDATACOPY, LOG0, halts) and jump targets.
For each block we emit its `Site` list, a `decide +kernel` proof that the sites
decode as listed, and a `rfl` shape lemma computing the symbolic stack effect.
"""
import sys
ops = {0x00:'STOP',0x01:'ADD',0x02:'MUL',0x03:'SUB',0x04:'DIV',0x10:'LT',0x11:'GT',0x14:'EQ',0x15:'ISZERO',0x16:'AND',0x1b:'SHL',0x1c:'SHR',0x33:'CALLER',0x34:'CALLVALUE',0x35:'CALLDATALOAD',0x36:'CALLDATASIZE',0x37:'CALLDATACOPY',0x50:'POP',0x52:'MSTORE',0x53:'MSTORE8',0x54:'SLOAD',0x55:'SSTORE',0x56:'JUMP',0x57:'JUMPI',0x5b:'JUMPDEST',0x5f:'PUSH0',0xa0:'LOG0',0xf3:'RETURN',0xfd:'REVERT'}
for n in range(1,33): ops[0x5f+n]='PUSH%d'%n
for n in range(1,17): ops[0x7f+n]='DUP%d'%n
for n in range(1,17): ops[0x8f+n]='SWAP%d'%n
BOUNDARY = {'JUMPI','SSTORE','MSTORE','MSTORE8','CALLDATACOPY','LOG0','RETURN','REVERT','STOP'}
COST = {'JUMPDEST':1,'POP':2,'CALLER':2,'CALLVALUE':2,'CALLDATASIZE':2,'PUSH0':2,'MUL':5,'DIV':5,'JUMP':8,'SLOAD':2100,
        'CALLDATALOAD':3,'ADD':3,'SUB':3,'LT':3,'GT':3,'EQ':3,'ISZERO':3,'AND':3,'SHL':3,'SHR':3,
        'PUSH1':3,'PUSH2':3,'PUSH4':3,'PUSH8':3,'PUSH20':3,'PUSH32':3,
        'DUP1':3,'DUP2':3,'DUP3':3,'DUP4':3,'DUP5':3,'SWAP1':3,'SWAP2':3,'SWAP3':3,'SWAP4':3}
BLOCKOPS = {'JUMPDEST','POP','CALLER','CALLVALUE','CALLDATASIZE','CALLDATALOAD','ADD','MUL','SUB','DIV','LT','GT','EQ','ISZERO','AND','SHL','SHR','PUSH0','PUSH1','PUSH2','PUSH4','PUSH8','PUSH20','PUSH32','DUP1','DUP2','DUP3','DUP4','DUP5','SWAP1','SWAP2','SWAP3','SWAP4','SLOAD','JUMP'}

def dis(path):
    b=bytes.fromhex(open(path).read().strip())
    pc=0; out={}
    order=[]
    while pc < len(b):
        op=b[pc]; name=ops[op]
        if 0x60<=op<=0x7f:
            w=op-0x5f; imm=int.from_bytes(b[pc+1:pc+1+w],'big'); out[pc]=(name,imm,w); pc+=1+w
        else:
            out[pc]=(name,None,0); pc+=1
        order.append(list(out.keys())[-1])
    return out, order

def site(pc, ins):
    name,imm,w=ins
    if imm is not None:
        return f"({pc}, (.{name}, some (UInt256.ofNat {imm}, {w})))"
    return f"({pc}, (.{name}, none))"

class Sym:
    """symbolic stack machine mirroring pureStep"""
    def __init__(self, st, stack):
        self.st=st; self.stack=list(stack)  # top first
    def step(self, ins):
        name,imm,w=ins; s=self.stack
        def pop(): return s.pop(0)
        def push(x): s.insert(0,x)
        if name=='JUMPDEST': return None
        if name=='POP': pop(); return None
        if name=='CALLER': push(f"callerW {self.st}"); return None
        if name=='CALLVALUE': push(f"valueW {self.st}"); return None
        if name=='CALLDATASIZE': push(f"cdsizeW {self.st}"); return None
        if name=='CALLDATALOAD': a=pop(); push(f"cdW {self.st} ({a})"); return None
        if name in ('ADD','MUL','SUB','DIV'):
            a=pop(); b=pop(); o={'ADD':'+','MUL':'*','SUB':'-','DIV':'/'}[name]; push(f"({a} {o} {b})"); return None
        if name in ('LT','GT','EQ','AND'):
            a=pop(); b=pop(); f={'LT':'UInt256.lt','GT':'UInt256.gt','EQ':'UInt256.eq','AND':'UInt256.land'}[name]; push(f"{f} ({a}) ({b})"); return None
        if name=='ISZERO': a=pop(); push(f"UInt256.isZero ({a})"); return None
        if name=='SHL': a=pop(); b=pop(); push(f"UInt256.shiftLeft ({b}) ({a})"); return None
        if name=='SHR': a=pop(); b=pop(); push(f"UInt256.shiftRight ({b}) ({a})"); return None
        if name=='PUSH0': push("UInt256.ofNat 0"); return None
        if name.startswith('PUSH'): push(f"UInt256.ofNat {imm}"); return None
        if name.startswith('DUP'): n=int(name[3:]); push(s[n-1]); return None
        if name.startswith('SWAP'): n=int(name[4:]); s[0],s[n]=s[n],s[0]; return None
        if name=='SLOAD':
            k=pop(); push(f"slotW {self.st} ({k})"); self.st=f"(touch {self.st} ({k}))"; return None
        if name=='JUMP': d=pop(); return ('jump', d)
        raise Exception(name)

def gen(prog, hexpath, nats, runtime, kind):
    code, order = dis(hexpath)
    # block starts: 0, every JUMPDEST, every pc after a boundary op
    starts=set([0])
    for pc in order:
        if code[pc][0]=='JUMPDEST': starts.add(pc)
    for i,pc in enumerate(order):
        if code[pc][0] in BOUNDARY and i+1 < len(order): starts.add(order[i+1])
    # static stack depth via DFS
    depth={0:{0}}
    work=[0]
    # compute per-pc depth by linear scan with jump edges
    delta={'ADD':-1,'MUL':-1,'SUB':-1,'DIV':-1,'LT':-1,'GT':-1,'EQ':-1,'AND':-1,'SHL':-1,'SHR':-1,'ISZERO':0,
           'CALLER':1,'CALLVALUE':1,'CALLDATASIZE':1,'CALLDATALOAD':0,'POP':-1,'JUMPDEST':0,'SLOAD':0,'JUMP':-1,'JUMPI':-2,
           'SSTORE':-2,'MSTORE':-2,'MSTORE8':-2,'CALLDATACOPY':-3,'LOG0':-2,'RETURN':-2,'REVERT':-2,'STOP':0}
    def d_of(name):
        if name.startswith('PUSH'): return 1
        if name.startswith('DUP'): return 1
        if name.startswith('SWAP'): return 0
        return delta[name]
    idx={pc:i for i,pc in enumerate(order)}
    seen=set()
    while work:
        pc0=work.pop()
        for d in list(depth[pc0]):
            if (pc0,d) in seen: continue
            seen.add((pc0,d))
            pc=pc0
            while True:
                name,imm,w=code[pc]
                nd=d+d_of(name)
                nxt=order[idx[pc]+1] if idx[pc]+1<len(order) else None
                def add(t,nd):
                    if t is None: return
                    if nd not in depth.setdefault(t,set()):
                        depth[t].add(nd); work.append(t)
                if name=='JUMP':
                    prev=order[idx[pc]-1]; tgt=code[prev][1]; add(tgt,nd); break
                if name=='JUMPI':
                    prev=order[idx[pc]-1]; tgt=code[prev][1]; add(tgt,nd); add(nxt,nd); break
                if name in ('RETURN','REVERT','STOP'): break
                if nxt is None: break
                if nxt in starts: add(nxt,nd); break
                depth.setdefault(nxt,set()).add(nd)
                pc=nxt; d=nd
    out=[]
    out.append(f"/-! ### `{prog}` blocks -/\n")
    blocks=[]
    for start in sorted(starts):
        name0=code[start][0]
        if name0 in BOUNDARY: continue   # a boundary op standing alone is not a block
        pcs=[]
        pc=start
        while True:
            name,imm,w=code[pc]
            if name in BOUNDARY: break
            assert name in BLOCKOPS, (pc,name)
            pcs.append(pc)
            if name=='JUMP': break
            nxt=order[idx[pc]+1]
            if nxt in starts: break
            pc=nxt
        blocks.append((start,pcs))
    def reads(name):
        if name.startswith('DUP'): return int(name[3:])
        if name.startswith('SWAP'): return int(name[4:])+1
        if name in ('ADD','MUL','SUB','DIV','LT','GT','EQ','AND','SHL','SHR'): return 2
        if name in ('ISZERO','CALLDATALOAD','POP','SLOAD','JUMP'): return 1
        return 0
    for start,pcs in blocks:
        # maximum depth read: simulate depth along the block
        d=0; maxread=0
        for pc in pcs:
            name=code[pc][0]
            need=reads(name)-d
            if need>maxread: maxread=need
            d+=d_of(name)
        for dd in depth[start]:
            assert dd>=maxread, (start, depth[start], maxread)
        vars_=[f"a{i}" for i in range(maxread)]
        sym=Sym("st", vars_+["r"])
        jump=None
        for pc in pcs:
            r=sym.step(code[pc])
            if r: jump=r
        last=pcs[-1]
        if jump:
            endpc=int(jump[1].split()[-1]) if jump[1].startswith('UInt256.ofNat') else None
            assert endpc is not None, jump
        else:
            endpc=last+1+code[last][2]
        sites=", ".join(site(pc,code[pc]) for pc in pcs)
        listing=" ".join(code[pc][0]+(f"({code[pc][1]})" if code[pc][1] is not None and code[pc][1] < 2**64 else "") for pc in pcs)
        bname=f"{prog}_b{start}"
        def stk(lst):
            assert lst[-1]=="r"
            return "(" + "".join(x+" :: " for x in lst[:-1]) + "r)"
        stk_in=stk(vars_+["r"])
        stk_out=stk(sym.stack)
        binders=" ".join(vars_)
        binder_decl=(f" ({binders} : UInt256)" if vars_ else "") + " (r : Stack UInt256)"
        out.append(f"/-- `{start}`: {listing}. -/\ndef {bname} : List Site :=\n  [{sites}]\n")
        out.append(f"theorem {bname}_ok : sitesOk {runtime} {bname} = true := by decide +kernel\n")
        bound=sum(COST[code[pc][0]] for pc in pcs)
        out.append(f"theorem {bname}_bound : blockBound {bname} = {bound} := rfl\n")
        out.append(f"theorem {bname}_shape (c : XiCall .{kind}) (st : EvmYul.State .EVM) (mem : ByteArray)\n    (aw g : UInt256) (e : Nat){binder_decl} :\n    symBlock {nats} ({bname}.map Prod.snd) (at_ c st mem aw g {start} {stk_in} e)\n      = some (at_ c {sym.st} mem aw g {endpc} {stk_out} e) := rfl\n")
    out.append(f"/-! ### `{prog}` effectful sites -/\n")
    for pc in order:
        name=code[pc][0]
        if name in BOUNDARY:
            out.append(f"theorem {prog}_s{pc} : opcodeAt {runtime} {pc} = some (.{name}, none) := by decide +kernel\n")
    return "\n".join(out), blocks, depth, code

header='''import Eip8282.Audit.EntryReach.Machine

/-!
# The straight-line blocks of the two pinned runtimes

Generated from `pinned/bytecode/builder_{deposits,exits}/main.hex` by
`scripts/gen_blocks.py` (reproducible; do not edit by hand). Every block is a
maximal straight-line run of `SymExec.blockOps` between the effectful sites and
the jump targets. For each block:

* `<name>` lists its sites — offsets and decoded instructions;
* `<name>_ok` kernel-checks, over the pinned byte-array literal, that the image
  really decodes those instructions at those offsets, consecutively;
* `<name>_shape` computes, by `rfl`, what the block does to the program counter,
  the stack and the storage-access state, on a machine whose stack is the
  concrete shape the program has at that offset.

Nothing here is an assumption: the shape lemmas are definitional unfoldings of
`SymExec.symBlock`, whose agreement with EVMYulLean's `EvmYul.step` is
`SymExec.pureStep_sound`.
-/

namespace Eip8282.Audit.EntryReach

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Model (Kind)

set_option maxRecDepth 4000
'''
footer='''
end Eip8282.Audit.EntryReach
'''
base='/workspaces/mission-1971a723/wt-entry-reach/'
dep, dblocks, ddepth, dcode = gen('deposit', base+'pinned/bytecode/builder_deposits/main.hex', 'depositJumpdestNats', 'depositRuntime', 'deposit')
exi, eblocks, edepth, ecode = gen('exit', base+'pinned/bytecode/builder_exits/main.hex', 'exitJumpdestNats', 'exitRuntime', 'exit')
open(base+'Eip8282/Audit/EntryReach/Blocks.lean','w').write(header+"\n"+dep+"\n"+exi+footer)
print("deposit blocks:", len(dblocks), [(s,len(p)) for s,p in dblocks])
print("exit blocks:", len(eblocks), [(s,len(p)) for s,p in eblocks])
print("deposit depths at block starts:", {s:sorted(ddepth[s]) for s,_ in dblocks})
print("exit depths at block starts:", {s:sorted(edepth[s]) for s,_ in eblocks})
