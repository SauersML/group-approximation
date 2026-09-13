#!/usr/bin/env sage -python
"""Independent check of census.py and census_points.py on the seven orbit
representatives in census_pairs.json.

1. The product table and trivial pairs are recomputed from the affine model.
2. Case (0,1) (u_0 = 1, u_1 w = 1) over QQ: the characteristic polynomial cp
   of multiplication M by a random linear form L is squarefree of degree =
   length, so 1, L, ..., L^(N-1) is a basis and every coordinate is a
   polynomial in L (shape lemma). The powers are computed as nf(1) M^i. The
   points are these polynomials at the roots of cp in QQ(zeta_8). Each point
   is multiplied out in K[P] with the group law, independently of the
   Groebner basis.
3. Galois: for each point and each j in {3, 5, 7}, zeta_8 -> zeta_8^j moves
   some coordinate, so the coordinates generate QQ(zeta_8). j = 7 is complex
   conjugation, so no point is real.
4. Corroboration of the case split, after 1-3 for all orbits: with the
   normalization sum_s r_s u_s = 1 (random r) instead of cases, the number of
   distinct eigenvalues of a random linear form is #trivial pairs + 16.
"""
import json, time, random
from sage.all import PolynomialRing, QQ, CyclotomicField, matrix, vector
from sage.libs.singular.function_factory import singular_function
from cysignals.alarm import alarm, cancel_alarm, AlarmInterrupt

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

def quotient(R, eqs, seed):
    G = slimgb(R.ideal([e for e in eqs if e != 0]))
    assert sdim(G) == 0
    GL, B = list(G), list(kbase(G))
    idx = {b: i for i, b in enumerate(B)}
    def nf(p):
        r, vec = p.reduce(GL), [QQ(0)] * len(B)
        for c, mon in zip(r.coefficients(), r.monomials()):
            vec[idx[mon]] = c
        return vector(QQ, vec)
    random.seed(seed)
    L = sum(random.randint(-9, 9) * x for x in R.gens())
    M = matrix(QQ, [nf(L * b) for b in B])
    return B, nf, M

def table(S, T, ring, u, v):
    eqs = {}
    for a in range(len(S)):
        for b in range(len(T)):
            c = mul(S[a], T[b])
            eqs[c] = eqs.get(c, ring(0)) + u[a] * v[b]
    return eqs

K8 = CyclotomicField(8)
z8 = K8.gen()
sig = {j: K8.hom([z8 ** j]) for j in (3, 5, 7)}
pairs = json.load(open("census_pairs.json"))
data = []
for k, d in enumerate(pairs):
    S, T = [el(p) for p in d["S"]], [el(p) for p in d["T"]]
    n, m = len(S), len(T)
    cells = {}
    prod = [[cells.setdefault(mul(s, t), len(cells)) for t in T] for s in S]
    assert prod == d["prod"] and len(cells) == d["K"] and cells[ID] == d["eid"]
    triv = [(i, j) for i in range(n) for j in range(m) if mul(S[i], T[j]) == ID]
    assert [tuple(p) for p in d["trivial_pairs"]] == triv
    # 2. case (0,1)
    R = PolynomialRing(QQ, [f"u{i}" for i in range(1, n)] + [f"v{j}" for j in range(m)] + ["w"],
                       order="degrevlex")
    g = R.gens()
    u, v = [R(1)] + list(g[:n - 1]), g[n - 1:n - 1 + m]
    eqs = table(S, T, R, u, v)
    eqs[ID] -= 1
    B, nf, M = quotient(R, list(eqs.values()) + [u[1] * g[-1] - 1], k)
    cp, N = M.charpoly(), len(B)
    assert cp.is_squarefree() and cp.degree() == N
    rows = [nf(R(1))]
    for _ in range(N - 1):
        rows.append(rows[-1] * M)
    A = matrix(QQ, rows)
    H = {x: A.solve_left(nf(x)) for x in g}
    roots = [r for r, _ in cp.change_ring(K8).roots()]
    assert len(roots) == N
    pts = [{x: sum(H[x][i] * th ** i for i in range(N)) for x in g} for th in roots]
    ok_mul = ok_gal = True
    for P in pts:
        uu, vv = [K8(1)] + [P[x] for x in g[:n - 1]], [P[x] for x in v]
        acc = table(S, T, K8, uu, vv)
        ok_mul &= all(val == (1 if c == ID else 0) for c, val in acc.items()) and uu[1] * P[g[-1]] == 1
        ok_gal &= all(any(sig[j](P[x]) != P[x] for x in g) for j in (3, 5, 7))
    stamp(f"orbit {k}: size {d['size']}, trivial pairs {len(triv)}, case (0,1) points {len(pts)}, "
          f"distinct {len({tuple(P[x] for x in g) for P in pts})}, u v = 1 for all: {ok_mul}, "
          f"coordinates generate QQ(zeta_8) (none real): {ok_gal}")
    data.append((S, T, triv, [[K8(1)] + [P[x] for x in g[:n - 1]] for P in pts]))
# 4. generic normalization
for k, (S, T, triv, us) in enumerate(data):
    n, m = len(S), len(T)
    R2 = PolynomialRing(QQ, [f"u{i}" for i in range(n)] + [f"v{j}" for j in range(m)], order="degrevlex")
    h = R2.gens()
    random.seed(1000 + k)
    r = [random.randint(1, 99) for _ in range(n)]
    eq2 = table(S, T, R2, h[:n], h[n:])
    eq2[ID] -= 1
    hit = all(sum(r[a] * uu[a] for a in range(n)) != 0 for uu in us)
    try:
        alarm(1200)
        B2, _, M2 = quotient(R2, list(eq2.values()) + [sum(r[a] * h[a] for a in range(n)) - 1], 2000 + k)
        cp2 = M2.charpoly()
        cancel_alarm()
    except AlarmInterrupt:
        stamp(f"orbit {k}: generic normalization TIMEOUT 1200s")
        continue
    stamp(f"orbit {k}: generic normalization length {len(B2)}, distinct eigenvalues "
          f"{sum(f.degree() for f, _ in cp2.factor())}, expected {len(triv) + len(us)}, "
          f"case (0,1) points off the hyperplane: {hit}")
print("DONE", flush=True)
