#!/usr/bin/env python3
"""File-level closure check for the LogicalInduction library.

Every `.lean` file under `LogicalInduction/` must be reachable, through `import` lines,
from a root the lakefile builds (`LogicalInduction`, `AxiomAudit`, `APITests`, the
`MachineExec` roots); and every `import` of a `LogicalInduction.*` module must name a
file that exists. A module nothing builds is dead weight; an import of a missing file is
a broken build. Exit 1 on either.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IMPORT = re.compile(r'^import\s+([A-Za-z0-9_.]+)', re.M)
PREFIXES = ('LogicalInduction', 'AxiomAudit', 'APITests')


def path_of(mod):
    return os.path.join(ROOT, mod.replace('.', '/') + '.lean')


def mod_of(path):
    return os.path.relpath(path, ROOT)[:-5].replace('/', '.')


def imports(path):
    with open(path, encoding='utf-8', errors='ignore') as f:
        return IMPORT.findall(f.read())


def lakefile_roots():
    with open(os.path.join(ROOT, 'lakefile.lean'), encoding='utf-8') as f:
        lake = f.read()
    roots = set()
    for m in re.finditer(r'lean_lib\s+(\w+)\s+where(.*?)(?=\nlean_lib|\nlean_exe|\Z)', lake, re.S):
        name, body = m.group(1), m.group(2)
        rm = re.search(r'roots\s*:=\s*#\[([^\]]*)\]', body)
        if rm:
            roots.update(re.findall(r'`([A-Za-z0-9_.]+)', rm.group(1)))
        else:
            roots.add(name)
    return {r for r in roots if r.startswith(PREFIXES) and os.path.exists(path_of(r))}


def main():
    roots = lakefile_roots()
    seen, missing = set(), []
    stack = sorted(roots)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        for i in imports(path_of(m)):
            if not i.startswith(PREFIXES):
                continue
            if os.path.exists(path_of(i)):
                stack.append(i)
            else:
                missing.append((m, i))
    on_disk = {'LogicalInduction'}
    for dp, _, fns in os.walk(os.path.join(ROOT, 'LogicalInduction')):
        for fn in fns:
            if fn.endswith('.lean'):
                on_disk.add(mod_of(os.path.join(dp, fn)))
    unreached = sorted(on_disk - seen)
    ok = True
    if unreached:
        ok = False
        print('modules under LogicalInduction/ that no lakefile root reaches:')
        for u in unreached:
            print('  ' + u)
    if missing:
        ok = False
        print('imports of missing files:')
        for m, i in missing:
            print(f'  {m} imports {i}')
    print(f'{"OK" if ok else "FAIL"}: {len(seen & on_disk)}/{len(on_disk)} LogicalInduction modules reached from {sorted(roots)}')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
