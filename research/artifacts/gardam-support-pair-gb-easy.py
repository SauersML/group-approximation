#!/usr/bin/env sage -python
"""Exact Groebner basis over QQ of Gardam's localised unit system on (S, T).

Case (0,1) of arXiv:2312.05240 Section 3: u_1 = 1, u_2 w = 1, no other
constraint, where uv = 1 is the bilinear system built by gsp.py (system.json).
Its K-points are the nontrivial units with u_1, u_2 != 0, up to scaling.
Singular's std over QQ is exact, so the output removes the "bad prime" caveat.
"""
import json, time, sys
from sage.all import PolynomialRing, QQ, AA, ZZ, sage_eval, Sequence

alg = sys.argv[1] if len(sys.argv) > 1 else "libsingular:std"
sysd = json.load(open("system.json"))
prod, K, eid = sysd["prod"], sysd["K"], sysd["eid"]
n = 21
names = [f"u{i + 1}" for i in range(n)] + [f"v{j + 1}" for j in range(n)] + ["w"]
R = PolynomialRing(QQ, names, order="degrevlex")
g = R.gens()
u, v, w = g[:n], g[n:2 * n], g[2 * n]
eqs = [R(0)] * K
for i in range(n):
    for j in range(n):
        eqs[prod[i][j]] += u[i] * v[j]
eqs[eid] -= 1
easy = eqs + [u[0] - 1, u[1] * w - 1]
print("equations:", len(easy), flush=True)

try:
    lines = open("zen/easy.ms").read().split("\n")
    assert [s.strip() for s in lines[0].split(",")] == names
    polys = [pp for pp in " ".join(lines[2:]).split(",") if pp.strip()]
    print("zenodo easy.ms equals generated system:", set(R(pp) for pp in polys) == set(easy), flush=True)
except Exception as e:
    print("easy.ms cross-check unavailable:", repr(e), flush=True)

I = R.ideal(easy)
t0 = time.time()
G = I.groebner_basis(algorithm=alg)
print(f"GB over QQ ({alg}): {len(G)} elements in {time.time() - t0:.1f}s", flush=True)
print("dimension:", I.dimension(), flush=True)
print("vector_space_dimension:", I.vector_space_dimension(), flush=True)
print("max |coefficient| in reduced GB:", max(abs(c) for p in G for c in p.coefficients()), flush=True)
try:
    Rz = PolynomialRing(ZZ, names)
    zb = sage_eval(open("zen/groebner_basis.txt").read(), Rz.gens_dict())
    print("equals zenodo groebner_basis.txt (as sets):", set(R(p) for p in zb) == set(G), flush=True)
except Exception as e:
    print("groebner_basis.txt cross-check unavailable:", repr(e), flush=True)
E = I.elimination_ideal([x for x in g if x not in (u[6], u[9])])
print("elimination ideal in u7, u10:", E.gens(), flush=True)
print("rational points:", I.variety(QQ), flush=True)
print("real algebraic points:", len(I.variety(AA)), flush=True)
json.dump([str(p) for p in G], open("gb_easy_qq.json", "w"))
print("DONE", flush=True)
