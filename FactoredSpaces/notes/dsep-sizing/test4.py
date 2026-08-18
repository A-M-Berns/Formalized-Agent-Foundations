import itertools, random, sys
sys.path.insert(0, '/private/tmp/claude-501/-Users-anson/66aa0277-2361-4106-8c7e-0106b4ddf9d5/scratchpad')
from fsm import Sstar, dsep, active_strict_endpoints, active

def rand_dag(n, p, rng):
    V = list(range(n))
    dag = {}
    for v in V:
        dag[v] = tuple(u for u in range(v) if rng.random() < p)
    return dag

def crit(dag, V1, V2, Z):
    S1 = set(); S2 = set()
    for s in V1: S1 |= Sstar(s, dag, set(Z))
    for s in V2: S2 |= Sstar(s, dag, set(Z))
    return not (S1 & S2)

rng = random.Random(0)
for variant, vname in [(active_strict_endpoints, 'endpoints-block-if-in-Z'), (active, 'endpoints-can-be-colliders')]:
    bad = 0; n = 0; examples = []
    for trial in range(400):
        nn = rng.choice([3, 4, 5])
        dag = rand_dag(nn, rng.choice([0.3, 0.5, 0.8]), rng)
        V = list(dag.keys())
        subs = [s for k in range(1, 3) for s in itertools.combinations(V, k)]
        subs3 = [s for k in range(0, 3) for s in itertools.combinations(V, k)]
        for V1 in subs:
            for V2 in subs:
                for V3 in subs3:
                    a = crit(dag, V1, V2, V3)
                    b = dsep(dag, V1, V2, V3, variant)
                    n += 1
                    if a != b:
                        bad += 1
                        if len(examples) < 5:
                            examples.append((dag, V1, V2, V3, a, b))
    print("variant=%s tested=%d mismatches=%d" % (vname, n, bad))
    for e in examples: print("   ", e)
