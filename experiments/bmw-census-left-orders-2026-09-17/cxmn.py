# Four-vertex complete VH square complexes of degree (m,n): torsion-free type-preserving lattices in
# Aut(T_m) x Aut(T_n) with four vertex orbits.  Same conventions as cx4.py (which is the case m = n = 3):
# vertices (i,j); row-j horizontal edges h_j in range(m); column-i vertical edges v_i in range(n);
# a square is (h0,v1,h1,v0); each pair (h0,v0),(h0,v1),(h1,v1),(h1,v0) lies in exactly one square.
import itertools, json, sys, random
from pysat.solvers import Cadical153, Glucose4
def enumerate_normalized(m, n):
    """All data with P[0] = id and Q[0] = id (every relabelling orbit meets this set)."""
    pn = list(itertools.permutations(range(n))); pm = list(itertools.permutations(range(m)))
    out = []
    for Prest in itertools.product(pn, repeat=m - 1):
        P = (tuple(range(n)),) + Prest                 # P[h0]: v0 -> v1
        Q = [tuple(range(m))] + [None] * (n - 1)       # Q[v0]: h0 -> h1
        used = {(P[h0][0], h0) for h0 in range(m)}
        def rec(v0):
            if v0 == n:
                out.append(tuple(sorted((h0, P[h0][w], Q[w][h0], w) for h0 in range(m) for w in range(n)))); return
            for q in pm:
                pairs = [(P[h0][v0], q[h0]) for h0 in range(m)]
                if any(p in used for p in pairs): continue
                Q[v0] = q; used.update(pairs); rec(v0 + 1); used.difference_update(pairs)
            Q[v0] = None
        rec(1)
    return out
def normalized(S, m, n):
    d = {(h0, v0): (v1, h1) for h0, v1, h1, v0 in S}
    return all(d[(0, v0)][0] == v0 for v0 in range(n)) and all(d[(h0, 0)][1] == h0 for h0 in range(m))
def orbit(S, m, n):
    base = [S]
    base += [tuple((h1, v1, h0, v0) for h0, v1, h1, v0 in B) for B in list(base)]
    base += [tuple((h0, v0, h1, v1) for h0, v1, h1, v0 in B) for B in list(base)]
    if m == n: base += [tuple((v0, h1, v1, h0) for h0, v1, h1, v0 in B) for B in list(base)]
    pm = list(itertools.permutations(range(m))); pn = list(itertools.permutations(range(n)))
    orb = set()
    for B in base:
        for a in pm:
            for c in pm:
                for b in pn:
                    for d in pn:
                        orb.add(tuple(sorted((a[h0], b[v1], c[h1], d[v0]) for h0, v1, h1, v0 in B)))
    return orb
class CX:
    def __init__(s, S, m, n):
        s.S = [tuple(x) for x in S]; s.m, s.n = m, n; s.T = {}
        for h0, v1, h1, v0 in s.S:
            h = (h0, h1); v = (v0, v1)
            for r in (0, 1):
                for c in (0, 1):
                    k = (r, c, h[r], v[c]); assert k not in s.T
                    s.T[k] = (v[1 - c], h[1 - r])
        assert len(s.T) == 4 * m * n
    def mul(s, g1, g2):
        V = list(g1[0]); H = list(g1[1]); T = s.T
        for f in g2[0]:
            r = len(V) % 2; c = len(H) % 2
            for k in range(len(H) - 1, -1, -1):
                f, H[k] = T[(r, c, H[k], f)]; c = 1 - c
            if V and V[-1] == f: V.pop()
            else: V.append(f)
        for e in g2[1]:
            if H and H[-1] == e: H.pop()
            else: H.append(e)
        return (tuple(V), tuple(H))
    def inv(s, g):
        return s.mul(((), tuple(reversed(g[1]))), (tuple(reversed(g[0])), ()))
def reduced(k, q):
    return [w for w in itertools.product(range(q), repeat=k) if all(w[i] != w[i + 1] for i in range(k - 1))]
def ball(G, R):
    els = [((), ())]
    for a in range(0, R + 1, 2):
        for b in range(0, R + 1 - a, 2):
            if a == b == 0: continue
            for V in reduced(a, G.n):
                for H in reduced(b, G.m): els.append((V, H))
    return {g: i for i, g in enumerate(els)}, els
def lo_sat(G, R, short=None):
    idx, els = ball(G, R); cls = []
    for i in range(1, len(els)):
        j = idx[G.inv(els[i])]; assert j != i
        if i < j: cls += [[i, j], [-i, -j]]
    left = range(1, len(els)) if short is None else [i for i in range(1, len(els)) if len(els[i][0]) + len(els[i][1]) <= short]
    seen = set()
    for i in left:
        for j in range(1, len(els)):
            for a, b in ((i, j), (j, i)):
                if (a, b) in seen: continue
                seen.add((a, b)); k = idx.get(G.mul(els[a], els[b]))
                if k is None: continue
                cls.append([-a, -b] if k == 0 else [-a, -b, k])
    return len(els), cls
def solve(cls):
    res = []
    for S in (Cadical153, Glucose4):
        with S(bootstrap_with=cls) as sv: res.append(sv.solve())
    assert len(set(res)) == 1
    return res[0]
def selfcheck(G, rnd, trials=60):
    idx, els = ball(G, 4)
    for _ in range(trials):
        a, b, c = (rnd.choice(els) for _ in range(3))
        assert G.mul(G.mul(a, b), c) == G.mul(a, G.mul(b, c))
        assert G.mul(a, G.inv(a)) == ((), ())
def finite_image(G, transpose=False, cap=4000):
    if transpose:
        G = CX([(v0, h1, v1, h0) for h0, v1, h1, v0 in G.S], G.n, G.m)
    T, L, INP = G.T, G.m, G.n
    def minimize(outs, succ):
        nn = len(outs); cl = {}; part = [cl.setdefault(o, len(cl)) for o in outs]
        while True:
            sig = {}; new = [sig.setdefault((part[i], tuple(part[x] for x in succ[i])), len(sig)) for i in range(nn)]
            if len(sig) == len(set(part)): return new
            part = new
    states_out = [tuple(range(INP))]; states_succ = [(0,) * INP]
    level = [0]; levels = [{0}]; k_ = 0
    while True:
        base = len(states_out); col = (k_ + 1) % 2
        pairs = [(s, (0, col, e)) for s in level for e in range(L)]
        allp = {p: base + k for k, p in enumerate(pairs)}; todo = list(pairs); k = 0
        eo = []; es = []
        while k < len(todo):
            s, (r, c, e) = todo[k]; k += 1
            o = []; sc = []
            for x in range(INP):
                x1, e2 = T[(r, c, e, x)]
                o.append(states_out[s][x1]); q = (states_succ[s][x1], (1 - r, c, e2))
                if q not in allp: allp[q] = base + len(todo); todo.append(q)
                sc.append(allp[q])
            eo.append(tuple(o)); es.append(tuple(sc))
        outs = states_out + eo; succ = states_succ + es
        part = minimize(outs, succ); ncls = max(part) + 1
        no = [None] * ncls; ns = [None] * ncls
        for i in range(len(outs)):
            if no[part[i]] is None: no[part[i]] = outs[i]; ns[part[i]] = tuple(part[x] for x in succ[i])
        levels = [set(part[x] for x in lv) for lv in levels]
        level = sorted(set(part[allp[p]] for p in pairs)); levels.append(set(level))
        states_out, states_succ = no, ns; k_ += 1
        if k_ >= 2 and levels[k_] == levels[k_ - 2]:
            return len(levels[k_] | levels[k_ - 1])
        if ncls > cap: return None
if __name__ == "__main__":
    m, n = int(sys.argv[2]), int(sys.argv[3]); name = f'census_cx_{m}{n}.json'
    if sys.argv[1] == 'enum':
        data = enumerate_normalized(m, n); seen = set(); reps = []
        for S in data:
            if S in seen: continue
            orb = orbit(S, m, n); seen |= {x for x in orb if normalized(x, m, n)}; reps.append(min(orb))
        json.dump(dict(m=m, n=n, normalized=len(data), reps=reps), open(name, 'w'))
        print(json.dumps(dict(m=m, n=n, normalized=len(data), classes=len(reps))))
    else:
        D = json.load(open(name)); rnd = random.Random(11); lo, hi = int(sys.argv[4]), int(sys.argv[5])
        for i, S in enumerate(D['reps']):
            if not lo <= i < hi: continue
            G = CX(S, m, n); selfcheck(G, rnd)
            rec = dict(idx=i, finH=finite_image(G), finV=finite_image(G, True))
            plan = [(4, None)] + ([(6, 4), (6, None), (8, 2)] if rec['finH'] is None or rec['finV'] is None else [])
            for R, sh in plan:
                nb, cls = lo_sat(G, R, sh); sat = solve(cls)
                rec[f'R{R}s{sh}'] = [sat, nb, len(cls)]
                if not sat: break
            print(json.dumps(rec), flush=True)
