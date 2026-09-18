# Four-vertex complete VH square complexes of degree (3,3): all torsion-free lattices in Aut(T_3) x Aut(T_3)
# that preserve both vertex bipartitions and act simply transitively on each of the four vertex types.
# Vertices (i,j), i = column, j = row.  Horizontal edges of row j join (0,j)-(1,j), labels h_j in {0,1,2};
# vertical edges of column i join (i,0)-(i,1), labels v_i in {0,1,2}.  A square is (h0,v1,h1,v0).
# Completeness (link K_{3,3} at every vertex): each of the pairs (h0,v0),(h0,v1),(h1,v1),(h1,v0) occurs in
# exactly one square.  Gamma = pi_1 at (0,0); elements = loops in normal form (V,H): reduced vertical path in
# column 0 from (0,0), then reduced horizontal path; both of even length.
import itertools, json, sys
from pysat.solvers import Cadical153, Glucose4
K3 = range(3)
def enumerate_complexes():
    out = []
    perms = list(itertools.permutations(K3))
    for P in itertools.product(perms, repeat=3):          # for each h0: v0 -> v1 is a permutation
        for Q in itertools.product(perms, repeat=3):      # for each v0: h0 -> h1 is a permutation
            S = [(h0, P[h0][v0], Q[v0][h0], v0) for h0 in K3 for v0 in K3]
            if len({(s[1], s[2]) for s in S}) == 9:
                out.append(frozenset(S))
    return out
def canon_orbit(S):
    orb = set()
    base = [S]
    base += [frozenset((h1, v1, h0, v0) for h0, v1, h1, v0 in B) for B in list(base)]   # row swap
    base += [frozenset((h0, v0, h1, v1) for h0, v1, h1, v0 in B) for B in list(base)]   # column swap
    base += [frozenset((v0, h1, v1, h0) for h0, v1, h1, v0 in B) for B in list(base)]   # transpose
    perms = list(itertools.permutations(K3))
    for B in base:
        for a, b, c, d in itertools.product(perms, repeat=4):
            orb.add(tuple(sorted((a[h0], b[v1], c[h1], d[v0]) for h0, v1, h1, v0 in B)))
    return orb
class CX4:
    def __init__(s, S):
        s.S = [tuple(x) for x in S]; s.T = {}
        for h0, v1, h1, v0 in s.S:
            h = (h0, h1); v = (v0, v1)
            for r in (0, 1):
                for c in (0, 1):
                    k = (r, c, h[r], v[c]); assert k not in s.T
                    s.T[k] = (v[1 - c], h[1 - r])    # e f -> f' e'  at corner vertex (c, r)
        assert len(s.T) == 36
    def mul(s, g1, g2):
        V = list(g1[0]); H = list(g1[1]); T = s.T
        for f in g2[0]:
            r = len(V) % 2; c = len(H) % 2
            for k in range(len(H) - 1, -1, -1):
                f, H[k] = T[(r, c, H[k], f)]; c = 1 - c
            assert c == 0
            if V and V[-1] == f: V.pop()
            else: V.append(f)
        for e in g2[1]:
            if H and H[-1] == e: H.pop()
            else: H.append(e)
        return (tuple(V), tuple(H))
    def inv(s, g):
        return s.mul(((), tuple(reversed(g[1]))), (tuple(reversed(g[0])), ()))
def reduced(k):
    return [w for w in itertools.product(K3, repeat=k) if all(w[i] != w[i + 1] for i in range(k - 1))]
def ball(R):
    els = [((), ())]
    for a in range(0, R + 1, 2):
        for b in range(0, R + 1 - a, 2):
            if a == b == 0: continue
            for V in reduced(a):
                for H in reduced(b): els.append((V, H))
    return {g: i for i, g in enumerate(els)}, els
def lo_sat(G, R, short=None):
    idx, els = ball(R); cls = []
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
    idx, els = ball(6)
    for _ in range(trials):
        a, b, c = (rnd.choice(els) for _ in range(3))
        assert G.mul(G.mul(a, b), c) == G.mul(a, G.mul(b, c))
        assert G.mul(a, G.inv(a)) == ((), ())
def finite_image(G, transpose=False, cap=4000):
    """Image of the row-0 horizontal loop group in Aut of the vertical tree.  Letter (r,c,e) = horizontal edge e
    of row r ending in column c; on vertical input f (column c, from row r): output f' and next letter (1-r,c,e')."""
    if transpose:
        G = CX4([(v0, h1, v1, h0) for h0, v1, h1, v0 in G.S])
    T = G.T
    def minimize(outs, succ):
        n = len(outs); cls = {}; part = [cls.setdefault(o, len(cls)) for o in outs]
        while True:
            sig = {}; new = [sig.setdefault((part[i], tuple(part[x] for x in succ[i])), len(sig)) for i in range(n)]
            if len(sig) == len(set(part)): return new
            part = new
    states_out = [(0, 1, 2)]; states_succ = [(0, 0, 0)]
    level = [0]; levels = [{0}]; n = 0
    while True:
        base = len(states_out)
        col = (n + 1) % 2
        pairs = [(s, (0, col, e)) for s in level for e in K3]
        allp = {p: base + k for k, p in enumerate(pairs)}; todo = list(pairs); k = 0
        extra_out = []; extra_succ = []
        while k < len(todo):
            s, (r, c, e) = todo[k]; k += 1
            o = []; sc = []
            for x in K3:
                x1, e2 = T[(r, c, e, x)]
                o.append(states_out[s][x1]); s2 = states_succ[s][x1]
                q = (s2, (1 - r, c, e2))
                if q not in allp: allp[q] = base + len(todo); todo.append(q)
                sc.append(allp[q])
            extra_out.append(tuple(o)); extra_succ.append(tuple(sc))
        outs = states_out + extra_out; succ = states_succ + extra_succ
        part = minimize(outs, succ); ncls = max(part) + 1
        new_out = [None] * ncls; new_succ = [None] * ncls
        for i in range(len(outs)):
            c_ = part[i]
            if new_out[c_] is None: new_out[c_] = outs[i]; new_succ[c_] = tuple(part[x] for x in succ[i])
        levels = [set(part[x] for x in lv) for lv in levels]
        level = sorted(set(part[allp[p]] for p in pairs)); levels.append(set(level))
        states_out, states_succ = new_out, new_succ; n += 1
        if n >= 2 and levels[n] == levels[n - 2]:
            return len(levels[n] | levels[n - 1])
        if ncls > cap: return None
if __name__ == "__main__":
    import random
    if sys.argv[1] == 'enum':
        data = enumerate_complexes(); seen = set(); reps = []
        for S in data:
            k = tuple(sorted(S))
            if k in seen: continue
            orb = canon_orbit(S); seen |= orb; reps.append((min(orb), len(orb)))
        assert sum(sz for _, sz in reps) == len(data)
        json.dump(dict(raw=len(data), reps=[r for r, _ in reps], sizes=[sz for _, sz in reps]), open('census_cx4_33.json', 'w'))
        print(json.dumps(dict(raw=len(data), classes=len(reps))))
    else:
        D = json.load(open(sys.argv[2])); rnd = random.Random(11)
        lo, hi = int(sys.argv[3]), int(sys.argv[4])
        for i, S in enumerate(D['reps']):
            if not lo <= i < hi: continue
            G = CX4(S); selfcheck(G, rnd)
            rec = dict(idx=i, finH=finite_image(G), finV=finite_image(G, True))
            plan = [(4, None)] + ([(6, 4), (6, None), (8, 2)] if rec['finH'] is None or rec['finV'] is None else [])
            for R, sh in plan:
                nb, cls = lo_sat(G, R, sh); sat = solve(cls)
                rec[f'R{R}s{sh}'] = [sat, nb, len(cls)]
                if not sat: break
            print(json.dumps(rec), flush=True)
