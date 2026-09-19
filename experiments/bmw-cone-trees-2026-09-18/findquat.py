# search for rho: Gamma_c -> D^*/K^*, D = [a, b), h-letters fixing the vertex at PV and moving the vertex at PH by one
import sys, json, itertools
from gf2poly import *
from quat import Quat
C = '/home/user/group-approximation/experiments/bmw-census-left-orders-2026-09-17/'
f, ci, d, a, b, PV, PH = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7])
Qa = Quat(a, b)
D = json.load(open(C + f)); m, n, iA, iB = D['m'], D['n'], D['iA'], D['iB']
SQ = {tuple(x): tuple(y) for x, y in D['reps'][ci]}
els = [X for X in itertools.product(range(1 << (d + 1)), repeat=4) if pgcd(pgcd(X[0], X[1]), pgcd(X[2], X[3])) == 1]
def good(X, dh, dv, inv):
    if Qa.nrd(X) == 0: return False
    if inv and X[1] != 0: return False
    return Qa.dist(X, PH) == dh and Qa.dist(X, PV) == dv
cand = {}
for kind, dh, dv in (('H', 1, 0), ('V', 0, 1)):
    for inv in (True, False): cand[kind, inv] = [X for X in els if good(X, dh, dv, inv)]
print('candidates', {k: len(v) for k, v in cand.items()}, flush=True)
inv_ = lambda X: Qa.norm(Qa.conj(X))
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
                P = Qa.mul(H[h], V[v])
                if v2 in V and h2 not in H: H[h2] = Qa.norm(Qa.mul(Qa.conj(V[v2]), P)); changed = True
                elif h2 in H and v2 not in V: V[v2] = Qa.norm(Qa.mul(P, Qa.conj(H[h2]))); changed = True
    return H, V
def check(H, V):
    if len(H) < m or len(V) < n: return False
    for x in range(m):
        if not good(H[x], 1, 0, iA[x] == x): return False
        if not Qa.proj_eq(Qa.mul(H[x], H[iA[x]]), (1, 0, 0, 0)): return False
    for x in range(n):
        if not good(V[x], 0, 1, iB[x] == x): return False
        if not Qa.proj_eq(Qa.mul(V[x], V[iB[x]]), (1, 0, 0, 0)): return False
    for (h, v), (v2, h2) in SQ.items():
        if not Qa.proj_eq(Qa.mul(H[h], V[v]), Qa.mul(V[v2], H[h2])): return False
    for x in range(m):
        for y in range(x):
            if Qa.dist(Qa.mul(Qa.conj(H[x]), H[y]), PH) == 0: return False
    for x in range(n):
        for y in range(x):
            if Qa.dist(Qa.mul(Qa.conj(V[x]), V[y]), PV) == 0: return False
    return True
found = 0
for Xh in cand['H', iA[0] == 0]:
    for Xv in cand['V', iB[0] == 0]:
        H, V = propagate({0: Xh}, {0: Xv})
        trials = [(H, V)]
        if len(H) < m or len(V) < n:
            miss = [('H', x) for x in range(m) if x not in H] + [('V', x) for x in range(n) if x not in V]
            t, x = miss[0]
            trials = [propagate({**H, x: Y}, V) if t == 'H' else propagate(H, {**V, x: Y})
                      for Y in cand[t, (iA if t == 'H' else iB)[x] == x]]
        for H2, V2 in trials:
            if check(H2, V2):
                found += 1; print('FOUND', H2, V2, flush=True)
                if found >= 2: sys.exit()
print('done found', found)
