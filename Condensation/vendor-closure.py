"""Compute the PFR-internal import closure of the Shannon-entropy library, copy it, and
emit a topological build order.  Driven by `vendor-pfr.sh`; reads SRC and DST from env."""
import os, re, shutil
from collections import deque

SRC = os.environ['SRC']
DST = os.environ['DST']

SEEDS = ['PFR.ForMathlib.Entropy.Basic',
         'PFR.ForMathlib.Entropy.Measure',
         'PFR.ForMathlib.Entropy.Kernel.Basic',
         'PFR.ForMathlib.Entropy.Kernel.MutualInfo']

IMPORT = re.compile(r'\s*(?:public\s+|meta\s+|private\s+)*import\s+([A-Za-z0-9_.]+)')


def path_of(root, mod):
    return os.path.join(root, mod.replace('.', '/') + '.lean')


def imports_of(mod):
    p = path_of(SRC, mod)
    if not os.path.exists(p):
        return None
    return [m.group(1) for m in map(IMPORT.match, open(p, encoding='utf-8')) if m]


seen, deps = set(), {}
dq = deque(SEEDS)
while dq:
    m = dq.popleft()
    if m in seen or not m.startswith('PFR'):
        continue
    seen.add(m)
    imps = imports_of(m)
    if imps is None:
        raise SystemExit(f'missing source for module {m}')
    deps[m] = [i for i in imps if i.startswith('PFR')]
    dq.extend(i for i in imps if i.startswith('PFR') and i not in seen)

order, mark = [], {}


def visit(m):
    st = mark.get(m)
    if st == 2:
        return
    if st == 1:
        raise SystemExit('import cycle at ' + m)
    mark[m] = 1
    for d in deps.get(m, []):
        visit(d)
    mark[m] = 2
    order.append(m)


for m in sorted(deps):
    visit(m)

shutil.rmtree(DST, ignore_errors=True)
total = 0
for m in order:
    s, d = path_of(SRC, m), path_of(DST, m)
    os.makedirs(os.path.dirname(d), exist_ok=True)
    shutil.copy(s, d)
    total += sum(1 for _ in open(s, encoding='utf-8'))

with open(os.path.join(DST, 'ORDER.txt'), 'w') as f:
    f.write('\n'.join(order) + '\n')

print(f'   {len(order)} modules, {total} lines vendored to {DST}')
