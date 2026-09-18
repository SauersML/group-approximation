"""Brute-force checks for completeness-dividing-host-transfers-never-beat-random-labeling.

Games are unique games on small complete graphs; permutations of [k] are tuples.
Checks:
  (A) the conditional-expectation labeling reaches value >= 1/k on every instance;
  (B) planted left-shift games over a group of order K have value <= c' + (1-c')/K + eps
      (and pure random ones <= 1/K + eps) -- here only reported, the proof is Hoeffding;
  (E) dominated orbit split: max_j val(U_j) <= val(U) <= sum_{j in D} val(U_j) for a
      dominating set D of orbits under equivariant maps; equality val(U) = val(U_bottom)
      when a bottom orbit exists (cyclic holonomy, orbit sizes {2,4});
  (L) coset lift to S_k-shift games: val(lift) >= val(U)/(k-1)! and val(U) >= val(lift),
      and on planted S_3 instances the lift value sits near val(U)/2, not near val(U).
Run: python3 check_random_floor.py   (well under a minute)
"""
import itertools, random
from fractions import Fraction

random.seed(20260917)

def compose(p, q):  # (p o q)(x) = p[q[x]]
    return tuple(p[x] for x in q)

def value(n, edges, k, lab):
    return sum(1 for (u, v, p) in edges if p[lab[u]] == lab[v])

def best(n, edges, k):
    b = 0
    for lab in itertools.product(range(k), repeat=n):
        s = value(n, edges, k, lab)
        if s > b:
            b = s
    return b

def cond_exp_labeling(n, edges, k):
    """Method of conditional expectations; returns a labeling with value >= |E|/k."""
    lab = [None] * n
    for v in range(n):
        bestscore, bestx = None, None
        for x in range(k):
            lab[v] = x
            sc = Fraction(0)
            for (a, b, p) in edges:
                if lab[a] is not None and lab[b] is not None:
                    sc += 1 if p[lab[a]] == lab[b] else 0
                else:
                    sc += Fraction(1, k)  # at least one endpoint still uniform
            if bestscore is None or sc > bestscore:
                bestscore, bestx = sc, x
        lab[v] = bestx
    return lab

def complete_edges(n):
    return [(u, v) for u in range(n) for v in range(u + 1, n)]

def random_perm(k):
    p = list(range(k)); random.shuffle(p); return tuple(p)

out = []
# (A)
worst = None
for trial in range(200):
    n, k = random.choice([(5, 3), (6, 3), (5, 4), (4, 5)])
    E = [(u, v, random_perm(k)) for (u, v) in complete_edges(n)]
    lab = cond_exp_labeling(n, E, k)
    r = Fraction(value(n, E, k, lab), len(E))
    worst = r * k if worst is None else min(worst, r * k)
    assert r >= Fraction(1, k)
out.append(f"(A) 200 random instances: min over instances of k*val(cond-exp labeling) = {worst} >= 1  OK")

# groups as permutation tables: Z_K (left regular) and S_3 (left regular on itself)
def cyclic_regular(K):
    return [tuple((a + b) % K for a in range(K)) for b in range(K)]

S3 = list(itertools.permutations(range(3)))
S3_index = {p: i for i, p in enumerate(S3)}
def s3_left_regular():
    return [tuple(S3_index[compose(g, h)] for h in S3) for g in S3]

# (B) Hoeffding + union bound on Grass(n, l): degree d = (2^l - 1)(2^(n-l+1) - 2).
# Planted/random shift games over any group of order K with val in [c', c'+(1-c')/K+2 eps]
# exist once eps^2 d >= ln K + 1.  Report the least n for a few (l, K, eps).
import math
def grass_degree(n, l):
    return (2 ** l - 1) * (2 ** (n - l + 1) - 2)
for (l, K, eps) in [(2, 6, 0.01), (3, 24, 0.01), (4, math.factorial(5), 0.001), (5, math.factorial(8), 0.001)]:
    n = l + 1
    while eps * eps * grass_degree(n, l) < math.log(K) + 1:
        n += 1
    out.append(f"(B) Grass(n,{l}), group order K={K}, eps={eps}: Hoeffding condition holds for n >= {n} "
               f"(degree {grass_degree(n, l)})")

# (E) dominated orbit split for cyclic holonomy <h>
def power(h, m):
    p = tuple(range(len(h)))
    for _ in range(m):
        p = compose(h, p)
    return p

def restrict(E, orbit):
    idx = {x: i for i, x in enumerate(orbit)}
    return [(u, v, tuple(idx[p[x]] for x in orbit)) for (u, v, p) in E]

# (E1) orbits {0,1} (stabilizer <h^2>) and {2,3,4,5} (trivial stabilizer): the size-4
# orbit maps equivariantly onto the size-2 orbit, D = {size-2 orbit}, tau = 1, val(U) = val(U_2).
h24 = (1, 0, 3, 4, 5, 2)
for trial in range(30):
    n = 5
    E = [(u, v, power(h24, random.randrange(4))) for (u, v) in complete_edges(n)]
    vU = best(n, E, 6)
    v2 = best(n, restrict(E, [0, 1]), 2)
    v4 = best(n, restrict(E, [2, 3, 4, 5]), 4)
    assert max(v2, v4) <= vU and vU == v2, (vU, v2, v4)
out.append("(E1) 30 instances, holonomy Z_4 with orbit sizes {2,4}: val(U) = val(U_2) >= val(U_4)  OK")

# (E2) orbits {0,1} (stabilizer <h^2>, order 3) and {2,3,4} (stabilizer <h^3>, order 2):
# incomparable, tau = 2.  Planted: block A mod 2, block B mod 3, constraint h^m chosen by CRT.
h23 = (1, 0, 3, 4, 2)
strict = 0
for trial in range(30):
    n = 6
    A, B = {0, 1, 2}, {3, 4, 5}
    s2 = [random.randrange(2) for _ in range(n)]
    s3 = [random.randrange(3) for _ in range(n)]
    E = []
    for (u, v) in complete_edges(n):
        r2 = (s2[v] - s2[u]) % 2 if (u in A and v in A) else random.randrange(2)
        r3 = (s3[v] - s3[u]) % 3 if (u in B and v in B) else random.randrange(3)
        m = [x for x in range(6) if x % 2 == r2 and x % 3 == r3][0]
        E.append((u, v, power(h23, m)))
    vU = best(n, E, 5)
    v2 = best(n, restrict(E, [0, 1]), 2)
    v3 = best(n, restrict(E, [2, 3, 4]), 3)
    assert max(v2, v3) <= vU <= v2 + v3, (vU, v2, v3)
    strict += vU > max(v2, v3)
out.append(f"(E2) 30 instances, holonomy Z_6 with orbit sizes {{2,3}}: max <= val(U) <= v2 + v3  OK; "
           f"val(U) > max in {strict} of 30")

# (L) coset lift of a general UG on [3] to an S_3 left-shift game on the same graph
def lift(E):
    return [(u, v, tuple(S3_index[compose(p, s)] for s in S3)) for (u, v, p) in E]

ratios = []
for trial in range(20):
    n = 5
    sig = [random.randrange(3) for _ in range(n)]
    E = []
    for (u, v) in complete_edges(n):
        if random.random() < 0.8:
            while True:
                p = random_perm(3)
                if p[sig[u]] == sig[v]:
                    break
        else:
            p = random_perm(3)
        E.append((u, v, p))
    vU = best(n, E, 3)
    vL = best(n, lift(E), 6)
    assert Fraction(vU, 2) <= vL <= vU, (vU, vL)
    ratios.append(Fraction(vL, vU))
out.append(f"(L) 20 planted S_3 instances: val(U)/2 <= val(lift) <= val(U)  OK; "
           f"val(lift)/val(U) ranges over [{float(min(ratios)):.3f}, {float(max(ratios)):.3f}]")

if __name__ == "__main__":
    import os
    text = "\n".join(out)
    print(text)
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "output.txt"), "w") as f:
        f.write(text + "\n")
