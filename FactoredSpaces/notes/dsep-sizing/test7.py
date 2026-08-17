import itertools, sys
sys.path.insert(0, '/private/tmp/claude-501/-Users-anson/66aa0277-2361-4106-8c7e-0106b4ddf9d5/scratchpad')
from fsm import *

def block(w, dag, vals, Z, z):
    T = TT(w, dag, set(Z))
    zmap = dict(zip(Z, z))
    out = set()
    for u in T:
        for y in itertools.product(*[vals[p] for p in dag[u]]):
            if all((p not in zmap) or y[k] == zmap[p] for k, p in enumerate(dag[u])):
                out.add((u, y))
    return out

def check_blocks(dag, vals, name):
    cache = build(dag, vals)
    nodes, order, I, idx, Omega = cache
    V = list(dag.keys())
    bad = 0; tested = 0
    for zsize in range(0, len(V) + 1):
        for Z in itertools.combinations(V, zsize):
            for z in itertools.product(*[vals[w] for w in Z]):
                C = [om for om in Omega if all(Xall(om, dag, order, idx)[w] == zz for w, zz in zip(Z, z))]
                if not C: continue
                n = len(I)
                blocks = {w: block(w, dag, vals, Z, z) for w in Z}
                for mask in range(1 << n):
                    J = [k for k in range(n) if mask >> k & 1]
                    Jc = [k for k in range(n) if not mask >> k & 1]
                    if len(C) != len(set(tuple(om[k] for k in J) for om in C)) * len(set(tuple(om[k] for k in Jc) for om in C)):
                        continue
                    Jset = set(I[k] for k in J)
                    for w in Z:
                        B = blocks[w]
                        tested += 1
                        if (Jset & B) and not (B <= Jset):
                            bad += 1
                            if bad < 5:
                                print("  BAD Z=%s z=%s w=%s J=%s block=%s" % (Z, z, w, sorted(Jset), sorted(B)))
    print("=== all-or-nothing %s: checks=%d violations=%d" % (name, tested, bad), flush=True)

B = {c: (0, 1) for c in 'abcd'}
check_blocks({'a': (), 'b': ('a',), 'c': ('b',)}, B, 'chain')
check_blocks({'a': (), 'b': (), 'c': ('a', 'b')}, B, 'collider')
check_blocks({'a': (), 'b': ('a',), 'c': ('a', 'b')}, B, 'triangle')
check_blocks({'a': (), 'b': (), 'c': ('a', 'b'), 'd': ('c',)}, B, 'collider+desc')
check_blocks({'a': (), 'b': ('a',), 'c': ('a',), 'd': ('b', 'c')}, B, 'diamond')
