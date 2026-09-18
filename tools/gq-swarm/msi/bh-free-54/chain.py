# Is the iterated barycentric edge-split chain U_k cofinal in the O_E order?
import sys, json, time
from ore import *
sys.setrecursionlimit(10000)
def B6(t):
    a, b, d = t
    z = add(add(a, b), d); mab, mbd, mad = add(a, b), add(b, d), add(a, d)
    return [tri(a, mab, z), tri(mab, b, z), tri(b, mbd, z), tri(mbd, d, z), tri(d, mad, z), tri(mad, a, z)]
K = int(sys.argv[1]); SM = int(sys.argv[2])
t0 = time.time()
U = [frozenset([DELTA])]
for k in range(K):
    U.append(frozenset(p for t in U[-1] for p in B6(t)))
assert all(hier(DELTA, U[k]) for k in range(1, min(K, 3) + 1)), "U_k not in O_E"
small = [D for D in up(frozenset([DELTA]), SM) if len(D) >= 2]
need = {}
for D in small:
    kk = None
    for k in range(1, K + 1):
        if geq(U[k], D):
            kk = k; break
    need[kk] = need.get(kk, 0) + 1
# self-similarity: pull U_k back from the half H=(e0,v01,e2) of E_01 and from the half-of-half
def pullback(frame, pieces):
    a, b, d = frame
    import fractions
    M = [[a[0], b[0], d[0]], [a[1], b[1], d[1]], [a[2], b[2], d[2]]]
    D = det(a, b, d)
    def solve(x):  # coordinates of x in basis (a,b,d)
        return (det(x, b, d) // D, det(a, x, d) // D, det(a, b, x) // D)
    return frozenset(tri(*[solve(x) for x in p]) for p in pieces)
out = {"mode": "chain", "K": K, "sizes": [len(u) for u in U], "small_max": SM, "n_small": len(small),
       "min_k_with_Uk_geq_D": {str(k): v for k, v in sorted(need.items(), key=lambda kv: (kv[0] is None, kv[0] or 0))}}
for name, H in (("half_E01", tri(E0, (1, 1, 0), E2)), ("quarter", tri(E0, (2, 1, 0), E2))):
    res = {}
    for k in range(1, K + 1):
        inH = frozenset(p for p in U[k] if all(inside(x, H) for x in p))
        pb = pullback(H, inH)
        best = 0
        for kp in range(1, k + 1):
            if geq(pb, U[kp]): best = kp
        res[k] = best
    out["selfsim_" + name] = res
out["secs"] = round(time.time() - t0, 1)
print(json.dumps(out))
