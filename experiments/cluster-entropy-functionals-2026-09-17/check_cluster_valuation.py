#!/usr/bin/env python3
"""Checks for cluster-entropy-splitting-functionals-certify-nothing-on-one-ended-groups.

A cluster functional F(Q) = sum_W c_W H(join_{w in W} w^-1 Q), evaluated on the coordinate
partition Q_B of a Bernoulli shift, equals H(base) * psi(B), where psi(B) = sum_W c_W |B W|.

1. Valuation lemma. Put C = B1 cap B2 and R = max |w' w^-1|. If d(B1 \\ C, B2 \\ C) > R, then
   psi(B1 u B2) = psi(B1) + psi(B2) - psi(C). Checked on random functionals over Z^2.
2. The explicit fat digon, built from a bi-infinite geodesic and a detour around B(m, Delta)
   on Z^2, satisfies the hypotheses, and psi(B1 u B2) = psi(B1)+psi(B2)-psi(C')-psi(C'').
3. Bowen's functional gives psi = |B| - #edges. On F_2 it is 1 on random finite subtrees.
   On Z^2 it does not increase when a neighbour is added, and it is 0 on the digon union.
Pure python, deterministic seed. Exit code 0 iff every check passes.
"""
import random
import sys

random.seed(20260917)


# ---------- Z^2 ----------
def zmul(g, h):
    return (g[0] + h[0], g[1] + h[1])


def zinv(g):
    return (-g[0], -g[1])


def znorm(g):
    return abs(g[0]) + abs(g[1])


ZGEN = [(1, 0), (-1, 0), (0, 1), (0, -1)]


def psi(B, functional, mul):
    return sum(c * len({mul(b, w) for b in B for w in W}) for W, c in functional)


def radius(functional, mul, inv, norm):
    return max(norm(mul(w2, inv(w1))) for W, _ in functional for w1 in W for w2 in W)


def random_functional(k=4, box=2):
    fun = []
    for _ in range(k):
        size = random.randint(1, 4)
        W = {(0, 0)} | {(random.randint(-box, box), random.randint(-box, box)) for _ in range(size - 1)}
        fun.append((frozenset(W), random.randint(-5, 5)))
    return fun


def setdist(X, Y):
    if not X or not Y:
        return 10 ** 9
    return min(znorm(zmul(zinv(x), y)) for x in X for y in Y)


fails = 0

# check 1: valuation lemma
tested = 0
for trial in range(400):
    fun = random_functional()
    R = radius(fun, zmul, zinv, znorm)
    C = {(random.randint(-3, 3), random.randint(-3, 3)) for _ in range(6)}
    B1 = C | {(random.randint(-12, -6), random.randint(-3, 3)) for _ in range(8)}
    B2 = C | {(random.randint(6, 12), random.randint(-3, 3)) for _ in range(8)}
    if setdist(B1 - C, B2 - C) <= R:
        continue
    tested += 1
    lhs = psi(B1 | B2, fun, zmul)
    rhs = psi(B1, fun, zmul) + psi(B2, fun, zmul) - psi(C, fun, zmul)
    if lhs != rhs:
        fails += 1
        print("valuation FAIL", fun, B1, B2)
print(f"check1 valuation lemma: {tested} admissible random instances, fails={fails}")


# check 2: the fat digon on Z^2
def digon(R):
    Delta = 2 * R + 3
    L = Delta + 1
    a = Delta // 2
    # sigma = [(t, 0) for t in range(-L, L + 1)] is the geodesic, with midpoint m = (0,0).
    # The detour pi runs from (-L,0) to (L,0) outside the L1-ball of radius Delta, at height L+1.
    pi = ([(-L, y) for y in range(0, L + 2)] + [(x, L + 1) for x in range(-L + 1, L + 1)]
          + [(L, y) for y in range(L, -1, -1)])
    A1 = [(t, 0) for t in range(-a, a + 1)]
    Cp = [(t, 0) for t in range(-a - R - 1, -a)]
    Cpp = [(t, 0) for t in range(a + 1, a + R + 2)]
    B1 = set(A1) | set(Cp) | set(Cpp)
    B2 = set(pi) | {(t, 0) for t in range(-L, -a)} | {(t, 0) for t in range(a + 1, L + 1)}
    return B1, B2, set(Cp), set(Cpp), Delta


def connected(S, mul=zmul, gens=ZGEN):
    S = set(S)
    start = next(iter(S))
    seen = {start}
    stack = [start]
    while stack:
        g = stack.pop()
        for s in gens:
            h = mul(g, s)
            if h in S and h not in seen:
                seen.add(h)
                stack.append(h)
    return seen == S


tested2 = 0
for trial in range(60):
    fun = random_functional()
    R = radius(fun, zmul, zinv, znorm)
    B1, B2, Cp, Cpp, Delta = digon(R)
    C = B1 & B2
    ok = (C == Cp | Cpp and connected(B1) and connected(B2) and connected(Cp) and connected(Cpp)
          and setdist(Cp, Cpp) > R and setdist(B1 - C, B2 - C) > R
          and min(znorm(p) for p in B2 - C if p[1] != 0) > Delta)
    if not ok:
        fails += 1
        print("digon hypotheses FAIL", R)
        continue
    tested2 += 1
    lhs = psi(B1 | B2, fun, zmul)
    rhs = psi(B1, fun, zmul) + psi(B2, fun, zmul) - psi(Cp, fun, zmul) - psi(Cpp, fun, zmul)
    if lhs != rhs:
        fails += 1
        print("digon identity FAIL")
print(f"check2 fat digon on Z^2: {tested2} functionals, fails={fails}")

# check 3: Bowen's functional F = (1-2r)H(Q) + sum_i H(Q v s_i^-1 Q), with r = 2
bowenZ = [(frozenset({(0, 0)}), -3), (frozenset({(0, 0), (1, 0)}), 1), (frozenset({(0, 0), (0, 1)}), 1)]
B1, B2, Cp, Cpp, _ = digon(radius(bowenZ, zmul, zinv, znorm))
vals = (psi(B1, bowenZ, zmul), psi(B2, bowenZ, zmul), psi(Cp, bowenZ, zmul),
        psi(Cpp, bowenZ, zmul), psi(B1 | B2, bowenZ, zmul))
print("check3a Bowen functional on the Z^2 digon: psi(B1),psi(B2),psi(C'),psi(C''),psi(B1uB2) =", vals)
if vals != (1, 1, 1, 1, 0):
    fails += 1
for trial in range(50):
    B = {(0, 0)}
    prev = psi(B, bowenZ, zmul)
    for step in range(40):
        g = random.choice(sorted(B))
        B = B | {zmul(g, random.choice(ZGEN))}
        cur = psi(B, bowenZ, zmul)
        if cur > prev:
            fails += 1
            print("monotonicity FAIL")
            break
        prev = cur
ball = {(x, y) for x in range(-6, 7) for y in range(-6, 7) if abs(x) + abs(y) <= 6}
print("check3b Bowen psi on the Z^2 L1-ball of radius 6:", psi(ball, bowenZ, zmul))

# F_2: reduced words as tuples of letters in {a, A, b, B}
INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def fmul(g, h):
    g = list(g)
    for x in h:
        if g and g[-1] == INV[x]:
            g.pop()
        else:
            g.append(x)
    return tuple(g)


bowenF = [(frozenset({()}), -3), (frozenset({(), ('a',)}), 1), (frozenset({(), ('b',)}), 1)]
f2fails = 0
for trial in range(50):
    B = {()}
    for step in range(60):
        g = random.choice(sorted(B))
        B = B | {fmul(g, (random.choice('aAbB'),))}
    v = psi(B, bowenF, fmul)
    if v != 1:
        f2fails += 1
        print("F2 subtree FAIL", v)
fails += f2fails
print(f"check3c Bowen psi on 50 random finite subtrees of F_2: fails={f2fails}")
print("ALL CHECKS PASS" if fails == 0 else f"FAILURES: {fails}")
sys.exit(0 if fails == 0 else 1)
