"""Exact check of the stochastic-section counterexample on Z (and Z^2).

sigma(x)_i = x_i - x_{i+1} mod n  (surjective, kernel = constants).
T g (y) = average of g over the fiber sigma^{-1}(y) (Haar on the kernel).
Checks, with exact rationals, on random locally constant functions:
  (1) T(g o sigma) = g            (T sigma* = id)
  (2) sigma*(T g) != g for some g (sigma* T != id), T positive, T 1 = 1
  (3) uniform Bernoulli mean preserved by T
  (4) window shrink: window [0,L) goes to [0,L-1)
A Z^2 check uses s = (1,0): cosets are rows, kernel = row-constants.
"""
import itertools
import random
from fractions import Fraction as Fr


def sig_star(f, L, n):
    # f on window [0,L); returns f o sigma on window [0,L+1)
    return {x: f[tuple((x[i] - x[i + 1]) % n for i in range(L))]
            for x in itertools.product(range(n), repeat=L + 1)}


def T(g, L, n):
    # g on window [0,L); returns Tg on window [0,L-1)
    out = {}
    for y in itertools.product(range(n), repeat=L - 1):
        x = [0]
        for i in range(L - 1):
            x.append((x[-1] - y[i]) % n)
        out[y] = sum(Fr(g[tuple((xi + c) % n for xi in x)]) for c in range(n)) / n
    return out


def mean(f):
    return sum(Fr(v) for v in f.values()) / len(f)


random.seed(1)
for n in (2, 3, 4):
    for L in (1, 2, 3, 4):
        for trial in range(20):
            f = {x: random.randint(-5, 5) for x in itertools.product(range(n), repeat=L)}
            assert T(sig_star(f, L, n), L + 1, n) == {k: Fr(v) for k, v in f.items()}
            g = {x: random.randint(0, 5) for x in itertools.product(range(n), repeat=L + 1)}
            Tg = T(g, L + 1, n)
            assert all(v >= 0 for v in Tg.values())
            assert mean(Tg) == mean(g)
        one = {x: 1 for x in itertools.product(range(n), repeat=L + 1)}
        assert all(v == 1 for v in T(one, L + 1, n).values())
    # sigma* T != id: T of the indicator [x_0 = 0] is the constant 1/n
    ind = {(a,): 1 if a == 0 else 0 for a in range(n)}
    c = T(ind, 1, n)[()]
    assert c == Fr(1, n)
    print(f"n={n}: T sigma* = id, T Markov and Haar-preserving; "
          f"sigma* T [x0=0] = {c}, not the indicator")

# Z^2 with s=(1,0) on a 2x2 window: rows are cosets, kernel = row constants
n = 2
W = [(0, 0), (1, 0), (0, 1), (1, 1)]


def T2(g):
    out = {}
    for y00, y01 in itertools.product(range(n), repeat=2):
        base = {(0, 0): 0, (1, 0): (-y00) % n, (0, 1): 0, (1, 1): (-y01) % n}
        acc = Fr(0)
        for c0, c1 in itertools.product(range(n), repeat=2):
            x = tuple((base[w] + (c0 if w[1] == 0 else c1)) % n for w in W)
            acc += g[x]
        out[(y00, y01)] = acc / n ** 2
    return out


for trial in range(50):
    f = {y: random.randint(-3, 3) for y in itertools.product(range(n), repeat=2)}
    g = {x: f[((x[0] - x[1]) % n, (x[2] - x[3]) % n)]
         for x in itertools.product(range(n), repeat=4)}
    assert T2(g) == {k: Fr(v) for k, v in f.items()}
print("Z^2, s=(1,0): T sigma* = id on 2x2 windows")
print("ALL CHECKS PASSED")
