#!/usr/bin/env sage -python
"""Case (0,1) of sbox.py on (S, box(S)) without u0, for orbit representative k.

With T' = box(S) in place of the census inverse support T, recompute I_01
over QQ (u_0 = 1, u_1 w = 1) in the variables u_1..u_20, v_h (h in T'), w,
and print its dimension and length. If the characteristic polynomial cp of
multiplication by a random linear form L is squarefree of degree = length,
the points are found as in promislow-radius4-census-verify.py: every
coordinate is a polynomial in L, evaluated at the roots of cp in QQ(zeta_8).
Each point is multiplied out in QQ(zeta_8)[P] with the group law, and the
inverse is checked to be supported in T. The 16 census points extend by zeros
to points of I_01 on (S, T'), so length 16 means that they are all of them.

usage: sbox_verify.py k
"""
import json, sys, time, random
from sage.all import PolynomialRing, QQ, CyclotomicField, matrix, vector
from sage.libs.singular.function_factory import singular_function

slimgb = singular_function("slimgb")
kbase = singular_function("kbase")
sdim = singular_function("dim")
T0 = time.time()

def stamp(msg):
    print(f"{msg}  [{time.time() - T0:.1f}s]", flush=True)

ID = ((1, 1, 1), (0, 0, 0))

def mul(g, h):
    return (tuple(p * q for p, q in zip(g[0], h[0])),
            tuple(t + p * q for t, p, q in zip(g[1], g[0], h[1])))

def el(p):
    return (tuple(p[0]), tuple(p[1]))

def table(S, T, ring, u, v):
    eqs = {}
    for a in range(len(S)):
        for b in range(len(T)):
            c = mul(S[a], T[b])
            eqs[c] = eqs.get(c, ring(0)) + u[a] * v[b]
    return eqs

k = int(sys.argv[1])
d = json.load(open("census_pairs.json"))[k]
S, T = [el(p) for p in d["S"]], [el(p) for p in d["T"]]
Tp = [el(p) for p in json.load(open("sbox_pairs.json"))[k]["box"]]
Tset = set(T)
assert Tset <= set(Tp) and len(set(Tp)) == len(Tp)
n, m = len(S), len(Tp)
R = PolynomialRing(QQ, [f"u{i}" for i in range(1, n)] + [f"v{j}" for j in range(m)] + ["w"],
                   order="degrevlex")
g = R.gens()
u, v = [R(1)] + list(g[:n - 1]), g[n - 1:n - 1 + m]
eqs = table(S, Tp, R, u, v)
eqs[ID] -= 1
G = slimgb(R.ideal([e for e in eqs.values() if e != 0] + [u[1] * g[-1] - 1]))
dm = sdim(G)
stamp(f"orbit {k}: |S| = {n}, |T'| = {m} (box), |T| = {len(T)}, GB size {len(G)}, dim {dm}")
if dm == 0:
    GL, B = list(G), list(kbase(G))
    N = len(B)
    idx = {b: i for i, b in enumerate(B)}

    def nf(p):
        r, vec = p.reduce(GL), [QQ(0)] * N
        for c, mon in zip(r.coefficients(), r.monomials()):
            vec[idx[mon]] = c
        return vector(QQ, vec)

    random.seed(k)
    L = sum(random.randint(-9, 9) * x for x in g)
    M = matrix(QQ, [nf(L * b) for b in B])
    cp = M.charpoly()
    sqf = cp.is_squarefree()
    stamp(f"orbit {k}: length {N}, cp squarefree {sqf}, "
          f"factor degrees over QQ {sorted(f.degree() for f, _ in cp.factor())}")
    if sqf:
        rows = [nf(R(1))]
        for _ in range(N - 1):
            rows.append(rows[-1] * M)
        A = matrix(QQ, rows)
        H = {x: A.solve_left(nf(x)) for x in g}
        K8 = CyclotomicField(8)
        roots = [r for r, _ in cp.change_ring(K8).roots()]
        ok_mul = ok_supp = True
        for th in roots:
            P = {x: sum(H[x][i] * th ** i for i in range(N)) for x in g}
            uu, vv = [K8(1)] + [P[x] for x in g[:n - 1]], [P[x] for x in v]
            acc = table(S, Tp, K8, uu, vv)
            ok_mul &= all(val == (1 if c == ID else 0) for c, val in acc.items()) and uu[1] * P[g[-1]] == 1
            ok_supp &= all(vv[b] == 0 for b in range(m) if Tp[b] not in Tset)
        stamp(f"orbit {k}: roots in QQ(zeta_8) {len(roots)} of {N}, u v = 1 for all: {ok_mul}, "
              f"inverse supported in T for all: {ok_supp}")
print("DONE", flush=True)
