import itertools

# DAG: dict node -> tuple(parents).  vals: dict node -> tuple of values (>=2)

def build(dag, vals):
    nodes = list(dag.keys())
    order = []
    while len(order) < len(nodes):
        for v in nodes:
            if v in order:
                continue
            if all(p in order for p in dag[v]):
                order.append(v)
                break
        else:
            raise Exception("cycle")
    I = []
    for v in nodes:
        for y in itertools.product(*[vals[p] for p in dag[v]]):
            I.append((v, y))
    I.sort()
    idx = {i: k for k, i in enumerate(I)}
    Omega = list(itertools.product(*[vals[i[0]] for i in I]))
    return nodes, order, I, idx, Omega


def Xall(om, dag, order, idx):
    x = {}
    for v in order:
        y = tuple(x[p] for p in dag[v])
        x[v] = om[idx[(v, y)]]
    return x


def hist(Xset, Z, z, dag, vals, cache):
    """history of joint variable X_{Xset} given X_Z=z, brute force."""
    nodes, order, I, idx, Omega = cache
    C = []
    XC = []
    for om in Omega:
        xv = Xall(om, dag, order, idx)
        if all(xv[w] == zz for w, zz in zip(Z, z)):
            C.append(om)
            XC.append(xv)
    if not C:
        return None
    n = len(I)
    H = set(range(n))
    for mask in range(1 << n):
        J = [k for k in range(n) if mask >> k & 1]
        Jc = [k for k in range(n) if not mask >> k & 1]
        pj = {}
        for om, xv in zip(C, XC):
            pj.setdefault(tuple(om[k] for k in J), []).append(xv)
        pjc = set(tuple(om[k] for k in Jc) for om in C)
        if len(C) != len(pj) * len(pjc):
            continue
        ok = True
        for key, xvs in pj.items():
            if len(set(tuple(xv[s] for s in Xset) for xv in xvs)) > 1:
                ok = False
                break
        if not ok:
            continue
        H &= set(J)
    return frozenset(I[k] for k in H)


# ---- conjectured formula ----
def TT(u, dag, Z):
    """T_u = {u} u An'(u): v with directed path v->...->u, all nodes but the last not in Z."""
    res = {u}
    frontier = [u]
    while frontier:
        c = frontier.pop()
        for p in dag[c]:
            if p in Z or p in res:
                continue
            res.add(p)
            frontier.append(p)
    return res


def Sstar(s, dag, Z):
    if s in Z:
        return set()
    S = set(TT(s, dag, Z))
    changed = True
    while changed:
        changed = False
        for w in Z:
            Tw = TT(w, dag, Z)
            if (Tw & S) and not (Tw <= S):
                S |= Tw
                changed = True
    return S


def formula_hist(Xset, Z, z, dag, vals):
    S = set()
    for s in Xset:
        S |= Sstar(s, dag, set(Z))
    zmap = dict(zip(Z, z))
    out = set()
    for u in S:
        for y in itertools.product(*[vals[p] for p in dag[u]]):
            if all((p not in zmap) or y[k] == zmap[p] for k, p in enumerate(dag[u])):
                out.add((u, y))
    return frozenset(out)


# ---- d-separation by trail enumeration (endpoints count as non-collider nodes) ----
def trails(dag, s, t):
    """all simple trails (paths in the underlying undirected graph) from s to t,
    yielded as list of (node, dir_in, dir_out) info: we yield node list + edge orientations."""
    adj = {v: [] for v in dag}
    for v, ps in dag.items():
        for p in ps:
            adj[v].append((p, 'in'))    # edge p->v ; from v, neighbour p, edge points into v
            adj[p].append((v, 'out'))   # from p, neighbour v, edge points out of p
    out = []

    def rec(cur, visited, path, dirs):
        if cur == t and len(path) >= 1:
            out.append((list(path), list(dirs)))
        for (nb, d) in adj[cur]:
            if nb in visited:
                continue
            rec(nb, visited | {nb}, path + [nb], dirs + [d])
    rec(s, {s}, [s], [])
    return out


def active(path, dirs, dag, Z):
    """dirs[k] is the orientation of edge path[k]-path[k+1] as seen from path[k]:
    'out' means path[k] -> path[k+1]; 'in' means path[k] <- path[k+1]."""
    n = len(path)
    if n == 1:
        return path[0] not in Z
    for k, node in enumerate(path):
        if k == 0:
            collider = (dirs[0] == 'in')     # edge points into path[0]
        elif k == n - 1:
            collider = (dirs[n - 2] == 'out')  # edge points into last node
        else:
            collider = (dirs[k - 1] == 'out' and dirs[k] == 'in')
        if collider:
            # endpoints with a single edge pointing in: treat as collider? see memo
            if not (node in Z or descendants(dag, node) & Z):
                return False
        else:
            if node in Z:
                return False
    return True


def active_strict_endpoints(path, dirs, dag, Z):
    """variant: endpoints are never colliders; they block iff in Z."""
    n = len(path)
    if n == 1:
        return path[0] not in Z
    for k, node in enumerate(path):
        if k == 0 or k == n - 1:
            if node in Z:
                return False
            continue
        collider = (dirs[k - 1] == 'out' and dirs[k] == 'in')
        if collider:
            if not (node in Z or descendants(dag, node) & Z):
                return False
        else:
            if node in Z:
                return False
    return True


def descendants(dag, v):
    ch = {u: set() for u in dag}
    for u, ps in dag.items():
        for p in ps:
            ch[p].add(u)
    seen = set()
    fr = [v]
    while fr:
        c = fr.pop()
        for d in ch[c]:
            if d not in seen:
                seen.add(d)
                fr.append(d)
    return seen


def dsep(dag, V1, V2, Z, variant=active_strict_endpoints):
    for s in V1:
        for t in V2:
            for path, dirs in trails(dag, s, t):
                if variant(path, dirs, dag, set(Z)):
                    return False
    return True
