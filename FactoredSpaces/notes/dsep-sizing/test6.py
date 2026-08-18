import sys
sys.path.insert(0, '/private/tmp/claude-501/-Users-anson/66aa0277-2361-4106-8c7e-0106b4ddf9d5/scratchpad')
from fsm import *

# degenerate: |Val_b| = 1  -> does the formula still hold?
dag = {'a': (), 'b': ('a',), 'c': ('b',)}
vals = {'a': (0, 1), 'b': (0,), 'c': (0, 1)}
cache = build(dag, vals)
for Z, z in [((), ()), (('b',), (0,)), (('c',), (0,))]:
    for s in 'abc':
        h = hist((s,), Z, z, dag, vals, cache)
        f = formula_hist((s,), Z, z, dag, vals)
        print(Z, z, s, "brute", sorted(h), "formula", sorted(f), "MATCH" if h == f else "*** MISMATCH")
