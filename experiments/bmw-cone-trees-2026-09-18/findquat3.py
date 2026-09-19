# Search for rho: Gamma -> D^*/K^*, D = (a, b) over F_p(t), p odd (default 3), with h-letters fixing the
# base vertex of the tree at PV and moving the base vertex at PH by one, v-letters the other way round.
# Same propagation scheme as findquat.py (char 2); letters have polynomial coordinates of degree <= d.
# usage: findquat3.py census.json a b PV PH d cls1 [cls2 ...]
#   polynomials are digit strings, lowest degree first, e.g. "21" = 2 + t;  p via env P (default 3).
import sys, json, itertools, os
import fpoly as F
F.setp(int(os.environ.get('P', '3')))
from quatp import QuatP
C = '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17/'
pp = lambda s: F.tr([int(c) for c in s])
f = sys.argv[1]; a, b, PV, PH = (pp(s) for s in sys.argv[2:6]); d = int(sys.argv[6])
Qa = QuatP(a, b)
irr = F.irreducibles(4)
RF, RINF = __import__('quatp').ramification(a, b, irr)
STRICT = os.environ.get('STRICT') == '1'
print('algebra', a, b, 'ramified (finite, inf):', RF, RINF, 'strict', STRICT, flush=True)
D = json.load(open(C + f)); m, n, iA, iB = D['m'], D['n'], D['iA'], D['iB']
polys = [F.tr(c) for c in itertools.product(range(F.P), repeat=d + 1)]
cand = {('H', True): [], ('H', False): [], ('V', True): [], ('V', False): []}
for X in itertools.product(polys, repeat=4):
    if not any(X): continue
    lead = next(x for x in X if x)[-1]
    if lead != 1: continue                      # projective normalisation: first nonzero coord monic
    g = ()
    for x in X:
        if x: g = F.gcd(g, x) if g else F.monic(x)
    if len(g) > 1: continue                     # primitive
    N = Qa.nrd(X)
    if not N: continue
    if STRICT:                                  # S-integral: nrd supported on PV, PH and the ramified places
        M = N
        for pl in [PV, PH] + RF:
            while not F.divmod_(M, pl)[1]: M = F.divmod_(M, pl)[0]
        if len(M) > 1: continue
    dv, dh = Qa.dist(X, PV), Qa.dist(X, PH)
    for kind, eh, ev in (('H', 1, 0), ('V', 0, 1)):
        if dh == eh and dv == ev:
            cand[kind, False].append(X)
            if not X[0]: cand[kind, True].append(X)
print('candidates', {k: len(v) for k, v in cand.items()}, flush=True)
ONE = ((1,), (), (), ())
inv_ = lambda X: Qa.norm(Qa.conj(X))
def search(ci):
    SQ = {tuple(x): tuple(y) for x, y in D['reps'][ci]}
    def good(X, kind, inv):
        eh, ev = (1, 0) if kind == 'H' else (0, 1)
        if not Qa.nrd(X): return False
        if inv and X[0]: return False
        return Qa.dist(X, PH) == eh and Qa.dist(X, PV) == ev
    def propagate(H, V):
        H = dict(H); V = dict(V); changed = True
        while changed:
            changed = False
            for x in list(H):
                if iA[x] not in H: H[iA[x]] = inv_(H[x]); changed = True
            for x in list(V):
                if iB[x] not in V: V[iB[x]] = inv_(V[x]); changed = True
            for (h, v), (v2, h2) in SQ.items():
                if h in H and v in V:
                    Pr = Qa.mul(H[h], V[v])
                    if v2 in V and h2 not in H: H[h2] = Qa.norm(Qa.mul(Qa.conj(V[v2]), Pr)); changed = True
                    elif h2 in H and v2 not in V: V[v2] = Qa.norm(Qa.mul(Pr, Qa.conj(H[h2]))); changed = True
            if len(H) > m or len(V) > n: return None
        return H, V
    def check(H, V):
        if len(H) < m or len(V) < n: return False
        for x in range(m):
            if not good(H[x], 'H', iA[x] == x): return False
            if not Qa.proj_eq(Qa.mul(H[x], H[iA[x]]), ONE): return False
        for x in range(n):
            if not good(V[x], 'V', iB[x] == x): return False
            if not Qa.proj_eq(Qa.mul(V[x], V[iB[x]]), ONE): return False
        for (h, v), (v2, h2) in SQ.items():
            if not Qa.proj_eq(Qa.mul(H[h], V[v]), Qa.mul(V[v2], H[h2])): return False
        for x in range(m):
            for y in range(x):
                if Qa.dist(Qa.mul(Qa.conj(H[x]), H[y]), PH) == 0: return False
        for x in range(n):
            for y in range(x):
                if Qa.dist(Qa.mul(Qa.conj(V[x]), V[y]), PV) == 0: return False
        return True
    def rec(H, V):
        r = propagate(H, V)
        if r is None: return None
        H, V = r
        for x in H:
            if not good(H[x], 'H', iA[x] == x): return None
        for x in V:
            if not good(V[x], 'V', iB[x] == x): return None
        for x in H:
            if not Qa.proj_eq(Qa.mul(H[x], H[iA[x]]), ONE): return None
            for y in H:
                if y < x and Qa.dist(Qa.mul(Qa.conj(H[x]), H[y]), PH) == 0: return None
        for x in V:
            if not Qa.proj_eq(Qa.mul(V[x], V[iB[x]]), ONE): return None
            for y in V:
                if y < x and Qa.dist(Qa.mul(Qa.conj(V[x]), V[y]), PV) == 0: return None
        for (h, v), (v2, h2) in SQ.items():
            if h in H and v in V and v2 in V and h2 in H:
                if not Qa.proj_eq(Qa.mul(H[h], V[v]), Qa.mul(V[v2], H[h2])): return None
        miss = [('H', x) for x in range(m) if x not in H] + [('V', x) for x in range(n) if x not in V]
        if not miss: return (H, V) if check(H, V) else None
        t, x = miss[0]
        for Y in cand[t, (iA if t == 'H' else iB)[x] == x]:
            s = rec({**H, x: Y}, V) if t == 'H' else rec(H, {**V, x: Y})
            if s: return s
        return None
    return rec({}, {})
for ci in map(int, sys.argv[7:]):
    s = search(ci)
    print(json.dumps(dict(census=f, cls=ci, a=a, b=b, PV=PV, PH=PH, d=d, found=bool(s),
                          H={k: v for k, v in s[0].items()} if s else None, V={k: v for k, v in s[1].items()} if s else None)), flush=True)
