#!/usr/bin/env sage -python
"""Exact Groebner basis over QQ of Gardam's localised unit system on (S, T), version 2.

Same system as gardam-support-pair-gb-easy.py (u_1 = 1, u_2 w = 1, uv = 1 on the
product table of system.json). Version 1 stalled after its basis step, because
ideal methods silently recompute a basis with the default algorithm. Here every
later step works from the computed basis G:
  * G is computed once by Singular slimgb over QQ (exact rational arithmetic);
  * Buchberger's criterion is checked for G over QQ, and every input equation
    reduces to 0 modulo G, so <G> contains the input ideal; the reverse
    inclusion holds because G is computed from the input equations;
  * vdim, the elimination ideal in (u7, u10), and rational/real points are read off <G>.
"""
import json, time
from sage.all import PolynomialRing, QQ, AA, ZZ, sage_eval, Sequence

def stamp(msg, t0):
    print(f"{msg}  [{time.time() - t0:.1f}s]", flush=True)

T0 = time.time()
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
stamp(f"equations: {len(easy)}", T0)

G = list(R.ideal(easy).groebner_basis(algorithm="libsingular:slimgb"))
stamp(f"GB over QQ (libsingular:slimgb): {len(G)} elements", T0)
print("Buchberger criterion over QQ (is_groebner):", Sequence(G, R).is_groebner(), flush=True)
print("every input equation reduces to 0 mod G:", all(f.reduce(G) == 0 for f in easy), flush=True)
print("max |coefficient| in G:", max(abs(c) for p in G for c in p.coefficients()), flush=True)
try:
    Rz = PolynomialRing(ZZ, names)
    zb = sage_eval(open("zen/groebner_basis.txt").read(), Rz.gens_dict())
    print("equals zenodo groebner_basis.txt (as sets):", set(R(p) for p in zb) == set(G), flush=True)
except Exception as e:
    print("zenodo cross-check unavailable:", repr(e), flush=True)
json.dump([str(p) for p in G], open("gb_easy2_qq.json", "w"))
stamp("wrote gb_easy2_qq.json", T0)

J = R.ideal(G)
stamp(f"dimension: {J.dimension()}", T0)
stamp(f"vector_space_dimension: {J.vector_space_dimension()}", T0)
E = J.elimination_ideal([x for x in g if x not in (u[6], u[9])])
stamp(f"elimination ideal in u7, u10: {E.gens()}", T0)
stamp(f"rational points: {J.variety(QQ)}", T0)
stamp(f"real algebraic points: {len(J.variety(AA))}", T0)
print("DONE", flush=True)
