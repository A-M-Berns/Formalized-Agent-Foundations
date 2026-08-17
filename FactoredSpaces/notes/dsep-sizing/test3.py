import itertools, sys, time
sys.path.insert(0, '/private/tmp/claude-501/-Users-anson/66aa0277-2361-4106-8c7e-0106b4ddf9d5/scratchpad')
from fsm import *

def check_hist(dag, vals, name, maxZ=None, sets=False):
    cache = build(dag, vals)
    nodes, order, I, idx, Omega = cache
    V = list(dag.keys())
    t0 = time.time(); bad = 0; n = 0
    targets = [(s,) for s in V]
    if sets:
        targets = [t for k in range(1, len(V) + 1) for t in itertools.combinations(V, k)]
    for zsize in range(0, (len(V) if maxZ is None else maxZ) + 1):
        for Z in itertools.combinations(V, zsize):
            for z in itertools.product(*[vals[w] for w in Z]):
                for s in targets:
                    h = hist(s, Z, z, dag, vals, cache)
                    f = formula_hist(s, Z, z, dag, vals)
                    n += 1
                    if h != f:
                        bad += 1
                        if bad < 6:
                            print("  BAD H(X_%s|X_%s=%s) brute=%s formula=%s" % (s, Z, z, sorted(h), sorted(f)), flush=True)
    print("=== %s |I|=%d histories=%d mismatches=%d (%.1fs)" % (name, len(I), n, bad, time.time() - t0), flush=True)


def check_prop55(dag, vals, name, variant=active_strict_endpoints, maxset=2, use_formula=False):
    cache = build(dag, vals)
    V = list(dag.keys())
    subs = [s for k in range(1, maxset + 1) for s in itertools.combinations(V, k)]
    subs3 = [s for k in range(0, maxset + 1) for s in itertools.combinations(V, k)]
    bad = 0; n = 0
    for V1 in subs:
        for V2 in subs:
            for V3 in subs3:
                si = True
                for z in itertools.product(*[vals[w] for w in V3]):
                    if use_formula:
                        h1 = formula_hist(V1, V3, z, dag, vals)
                        h2 = formula_hist(V2, V3, z, dag, vals)
                    else:
                        h1 = hist(V1, V3, z, dag, vals, cache)
                        h2 = hist(V2, V3, z, dag, vals, cache)
                    if h1 is None: continue
                    if h1 & h2:
                        si = False; break
                ds = dsep(dag, V1, V2, V3, variant)
                n += 1
                if si != ds:
                    bad += 1
                    if bad < 10:
                        print("  BAD V1=%s V2=%s V3=%s structindep=%s dsep=%s" % (V1, V2, V3, si, ds), flush=True)
    print("=== prop5.5 %s (formula=%s): triples=%d mismatches=%d" % (name, use_formula, n, bad), flush=True)


B = {c: (0, 1) for c in 'abcde'}
G1 = {'a': (), 'b': ('a',), 'c': ('b',)}
G2 = {'a': (), 'b': (), 'c': ('a', 'b')}
G3 = {'a': (), 'b': (), 'c': ('a', 'b'), 'd': ('c',)}
G4 = {'a': (), 'b': ('a',), 'c': ('a',), 'd': ('b', 'c')}
G5 = {'a': (), 'b': ('a',), 'c': ('a', 'b')}

for G, nm in [(G1, 'chain'), (G2, 'collider'), (G5, 'triangle')]:
    check_hist(G, B, nm, sets=True)
    check_prop55(G, B, nm, maxset=3)
check_hist(G3, B, 'collider+desc', maxZ=2)
check_hist(G4, B, 'diamond', maxZ=2)
check_prop55(G3, B, 'collider+desc', maxset=1)
check_prop55(G4, B, 'diamond', maxset=1)
