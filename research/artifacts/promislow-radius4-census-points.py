#!/usr/bin/env sage -python
"""Points over QQbar of the case (0,1) systems of census.py with T the F_2
inverse support of orbit representative k: u_0 = 1, u_1 w = 1, u * v = 1.
census.py reported these cases nonempty with dim 1, the extra dimension being
the unused variable u_0. Here u_0 is not a variable.

For each k: slimgb over QQ, dimension, length, and the characteristic
polynomial of multiplication by a random linear form L on QQ[u, v, w]/I, with
its real roots and its factorization over QQ and over QQ(zeta_8). The
eigenvalues are the values of L at the points, so no real root means no real
point, and no linear factor over QQ means no rational point.
usage: census_points.py [k ...]
"""
import json, sys, time, random
from sage.all import PolynomialRing, QQ, CyclotomicField, matrix
from sage.libs.singular.function_factory import singular_function

slimgb = singular_function("slimgb")
vdim = singular_function("vdim")
sdim = singular_function("dim")
kbase = singular_function("kbase")
T0 = time.time()

def stamp(msg):
    print(f"{msg}  [{time.time() - T0:.1f}s]", flush=True)

pairs = json.load(open("census_pairs.json"))
ks = [int(a) for a in sys.argv[1:]] or list(range(len(pairs)))
for k in ks:
    d = pairs[k]
    prod, K, eid = d["prod"], d["K"], d["eid"]
    n, m = len(d["S"]), len(prod[0])
    names = [f"u{i}" for i in range(1, n)] + [f"v{j}" for j in range(m)] + ["w"]
    R = PolynomialRing(QQ, names, order="degrevlex")
    g = R.gens()
    u = [R(1)] + list(g[:n - 1])
    v = g[n - 1:n - 1 + m]
    eqs = [R(0)] * K
    for a in range(n):
        for b in range(m):
            eqs[prod[a][b]] += u[a] * v[b]
    eqs[eid] -= 1
    eqs.append(u[1] * g[-1] - 1)
    G = slimgb(R.ideal([e for e in eqs if e != 0]))
    GL = list(G)
    dim = sdim(G)
    stamp(f"orbit {k}: |S| = {n}, |T| = {m}, GB size {len(GL)}, dim {dim}")
    if dim != 0 or any(p.is_constant() for p in GL):
        continue
    B = list(kbase(G))
    stamp(f"orbit {k}: length {vdim(G)}, standard monomials {len(B)}")
    random.seed(k)
    lf = sum(random.randint(-9, 9) * x for x in g)
    idx = {b: i for i, b in enumerate(B)}
    M = matrix(QQ, len(B), len(B))
    for i, b in enumerate(B):
        r = (lf * b).reduce(GL)
        for c, mon in zip(r.coefficients(), r.monomials()):
            M[i, idx[mon]] = c
    cp = M.charpoly()
    with open(f"census_points_{k}.txt", "w") as fh:
        fh.write(f"L = {lf}\n{cp}\n")
    fq = cp.factor()
    stamp(f"orbit {k}: charpoly degree {cp.degree()}, squarefree {cp.is_squarefree()}, "
          f"real roots {cp.number_of_real_roots()}, "
          f"factor degrees over QQ {sorted(f.degree() for f, _ in fq)}")
    f8 = cp.change_ring(CyclotomicField(8)).factor()
    stamp(f"orbit {k}: factor degrees over QQ(zeta_8) {sorted(f.degree() for f, _ in f8)}")
print("DONE", flush=True)
