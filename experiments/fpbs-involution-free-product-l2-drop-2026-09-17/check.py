#!/usr/bin/env python3
"""Checks for fpbs-involution-free-products-drop-l2-threshold-at-trees.

1. Busemann Schur count on T_d: vertices v at distance n from u, split by
   Busemann displacement, weighted by (d-1)^(-(beta(v)-beta(u))/2), sum to at
   most (n+1)(d-1)^(n/2).  Checked by brute force on a finite tree.
2. Cheeger bound on Cay(A * Z/2) with A = Z^2 (an infinite amenable group):
   for random finite F, |dF| >= max(m, |F| - 2(m-1)) >= |F|/2, where m is the
   number of A-cosets met by F.
3. Free-product threshold: p (chi_{T_4}(p) - 1) = 1 at p = 1/4 = p_c(T_5).
4. The numbers of the drop: p_c(T_4)=1/3, p_c(T_5)=1/4, 1/sqrt(4)=1/2.
Run: python3 check.py   (exit 0 iff all checks pass)
"""
import random
from fractions import Fraction as Fr

ok = True


def check(cond, msg):
    global ok
    print(("PASS " if cond else "FAIL ") + msg)
    ok = ok and cond


# ---------- 1. Busemann Schur count on T_d ----------
# Model T_d as the tree of a fixed end: vertex = (level h, index path) is
# awkward; instead use the count formula and verify it by BFS on a big finite
# ball of the free product (Z/2)^{*d} (Cayley graph T_d), with a horofunction
# given by an infinite reduced ray xi = s0 s1 s0 s1 ... truncated deep enough.
def tree_check(d, nmax):
    gens = list(range(d))
    L = 2 * nmax + 4  # ray length
    ray = [i % 2 for i in range(L)]  # alternating s0 s1 s0 ..., reduced

    def mult(w, s):
        return w[:-1] if w and w[-1] == s else w + (s,)

    def beta(w):
        # Busemann function toward the end xi = ray: beta(w) = lim |w^-1 xi_t| - t
        # with xi_t = ray[:t]; common prefix c: |w^-1 xi_t| = |w| + t - 2c.
        c = 0
        while c < len(w) and w[c] == ray[c]:
            c += 1
        return len(w) - 2 * c

    u = ()
    # BFS ball of radius nmax around u
    layer = [u]
    seen = {u}
    for n in range(1, nmax + 1):
        nxt = []
        for w in layer:
            for s in gens:
                v = mult(w, s)
                if v not in seen:
                    seen.add(v)
                    nxt.append(v)
        layer = nxt
        tot = sum((d - 1) ** (-(beta(v) - beta(u)) / 2.0) for v in layer)
        bound = (n + 1) * (d - 1) ** (n / 2.0)
        if tot > bound * (1 + 1e-12):
            return False, n, tot, bound
    return True, nmax, tot, bound


for d in (3, 4, 5, 6):
    res = tree_check(d, 7 if d <= 4 else 5)
    check(res[0], f"T_{d}: Busemann Schur count <= (n+1)(d-1)^(n/2) up to n={res[1]}")


# ---------- 2. Cheeger bound on Cay(Z^2 * Z/2) ----------
# Normal form: tuple of Z^2 vectors separated by c; element = (v_0, c, v_1, c, ...)
# represented as tuple of vectors (v_0, v_1, ..., v_m) with v_i != 0 for 0<i<m
# (v_0, v_m may be 0).  Right multiplication by a generator.
A_GENS = [(1, 0), (-1, 0), (0, 1), (0, -1)]


def rmul(g, s):
    if s == 'c':
        last = g[-1]
        if last == (0, 0) and len(g) > 1:
            return g[:-1]
        return g + ((0, 0),)
    last = g[-1]
    new = (last[0] + s[0], last[1] + s[1])
    if new == (0, 0) and len(g) > 1:
        # v_m becomes 0: fine, it is the trailing slot, keep it
        return g[:-1] + (new,)
    return g[:-1] + (new,)


def canon(g):
    return g


def coset(g):
    # A-coset gA is determined by the prefix g[:-1]
    return g[:-1]


GENS = A_GENS + ['c']
random.seed(20260917)
worst = None
trials = 0
for t in range(400):
    # grow a random connected set by random accretion
    F = {((0, 0),)}
    frontier = [((0, 0),)]
    size = random.randint(2, 120)
    bias = random.random()
    while len(F) < size:
        g = random.choice(list(F))
        s = 'c' if random.random() < bias * 0.5 else random.choice(A_GENS)
        h = rmul(g, s)
        F.add(h)
    # boundary edges (each vertex has 5 neighbours; c is an involution)
    bd = 0
    for g in F:
        for s in GENS:
            if rmul(g, s) not in F:
                bd += 1
    m = len({coset(g) for g in F})
    lower = max(m, len(F) - 2 * (m - 1))
    trials += 1
    if bd < lower or 2 * bd < len(F):
        check(False, f"Cheeger bound fails on |F|={len(F)} m={m} bd={bd}")
    r = Fr(bd, len(F))
    worst = r if worst is None or r < worst else worst
check(worst is not None and worst >= Fr(1, 2),
      f"Cay(Z^2*Z/2): |dF|>=max(m,|F|-2m+2)>=|F|/2 on {trials} random sets; min |dF|/|F| = {float(worst):.3f}")

# involution sanity: c c = e, and group law consistency on random words
g = ((0, 0),)
for _ in range(1000):
    s = random.choice(GENS)
    g2 = rmul(g, s)
    inv = 'c' if s == 'c' else (-s[0], -s[1])
    back = rmul(g2, inv)
    if back != g:
        check(False, f"inverse law fails at {g} {s}")
        break
    g = g2
check(True, "right multiplication is a group action on normal forms (1000 random steps)")


# ---------- 3. free-product threshold on F_2 * Z/2 ----------
def chi_T4(p):
    # susceptibility of the 4-regular tree: 1 + 4p/(1-3p)
    return 1 + 4 * p / (1 - 3 * p)


p = Fr(1, 4)
check(p * (chi_T4(p) - 1) == 1, "p (chi_{T_4}(p)-1) = 1 at p=1/4 = 1/(5-1) = p_c(T_5)")

# ---------- 4. numbers ----------
pc4, pc5, p22_5 = Fr(1, 3), Fr(1, 4), Fr(1, 2)
check(p22_5 - pc5 == Fr(1, 4) and pc4 - pc5 == Fr(1, 12),
      "slack(T_5) >= 1/4 while limsup slack(A_n*Z/2) <= 1/3-1/4 = 1/12")
# eta from conductance Phi >= (1/2)/5: 1 - rho >= Phi^2/2 = 1/200
check((Fr(1, 2) / 5) ** 2 / 2 == Fr(1, 200), "eta = Phi^2/2 = 1/200 with Phi = (1/2)/5")

raise SystemExit(0 if ok else 1)
