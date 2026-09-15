#!/usr/bin/env python3
"""Generate/check Lake's explicit core, candidate and test module partition.

The core is the transitive local import closure of the registered theorem module.
No module may be unassigned, doubly assigned, or imported across a reversed tier.
"""
from pathlib import Path
import argparse,json,re
ROOT=Path(__file__).resolve().parents[1]
START='-- BEGIN GENERATED LIBRARY PARTITION\n'
END='-- END GENERATED LIBRARY PARTITION\n'
def layout():
    files={'.'.join(p.relative_to(ROOT).with_suffix('').parts):p for p in (ROOT/'Eip8282').rglob('*.lean')}
    edges={n:set(re.findall(r'^import\s+(\S+)',p.read_text(),re.M)) for n,p in files.items()}
    for n, dependencies in edges.items():
        missing={d for d in dependencies if d.startswith('Eip8282.') and d not in files}
        if missing:raise SystemExit(f'{n} imports missing local modules: {sorted(missing)}')
    core=set(); pending=['Eip8282.Audit.Integrator.DirectGuarantees']
    while pending:
        n=pending.pop()
        if n in core or n not in files:continue
        core.add(n);pending.extend(edges[n])
    tests={n for n in files if n.startswith('Eip8282.Tests.') or n=='Eip8282.Audit.Trust'}
    if core&tests:raise SystemExit('Correctness core must not import tests')
    candidates=set(files)-core-tests
    for n in candidates:
        if edges[n]&tests:raise SystemExit(f'Candidate {n} imports tests')
    groups={'Eip8282':core,'Eip8282Candidates':candidates,'Eip8282Tests':tests}
    return files,groups

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write',action='store_true');args=ap.parse_args()
    files,groups=layout();out=START
    for name,names in groups.items():
        out+=('\n@[default_target]\n' if name=='Eip8282' else '\n')
        out+=f'lean_lib «{name}» where\n  globs := #[\n'
        out+=',\n'.join(f'    .one `{n}' for n in [name]+sorted(names))+'\n  ]\n  moreLeanArgs := ffiDynlibs\n'
    out+='\n'+END
    path=ROOT/'lakefile.lean';old=path.read_text();new=old[:old.index(START)]+out+old[old.index(END)+len(END):]
    if args.write:path.write_text(new)
    elif old!=new:raise SystemExit('Library partition changed; run python3 scripts/library_layout.py --write')
    for name,names in groups.items():print(f'{name}: {len(names)} modules, {sum(len(files[n].read_text().splitlines()) for n in names):,} lines')
if __name__=='__main__':main()
