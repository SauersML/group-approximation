"""Sanity check of the layer-increment inequality in the positive monoid of Thompson's F.

For a finite Y in M and n >= 1 put Z_(n+1) = Y, Z_k = X_k Z_(k+1) with X_k = {x_0, ..., x_k},
t_k = |Z_k|, e_k = t_k - t_(k+1).  Claim: e_k <= k * e_(k+1) for 1 <= k <= n-1 (and e_0 = 0).
Corollary: |X_m ... X_n Y| - |Y| <= c(m, d) (|X_n Y| - |Y|), d = n - m + 1,
c(m, d) = sum_(j=0)^(d-1) (n-1)!/(n-1-j)!.

Proof in research/thompson-f-guba-set-expansion-bounded-by-one-letter-set-proof.md.
This script only tests it on random finite sets and on optimal sets read from files
(one normal form per line, letters comma separated).  Cheap: a few seconds.

usage: python3 layer_increment_check.py [trials] [file ...]
"""
import itertools
import math
import random
import sys


def lm(j, w):
    """Normal form of x_j * w for a nondecreasing tuple w."""
    out = []
    k = 0
    n = len(w)
    while k < n and w[k] < j:
        out.append(w[k])
        j += 1
        k += 1
    out.append(j)
    out.extend(w[k:])
    return tuple(out)


def layers(Y, n):
    """Return [t_0, ..., t_(n+1)] for the chain Z_k = X_k ... X_n Y."""
    Z = set(Y)
    t = {n + 1: len(Z)}
    for k in range(n, -1, -1):
        Z = {lm(j, w) for w in Z for j in range(k + 1)}
        t[k] = len(Z)
    return [t[k] for k in range(n + 2)]


def c(m, d):
    n = m + d - 1
    return sum(math.factorial(n - 1) // math.factorial(n - 1 - j) for j in range(d))


def check(Y, n, label):
    t = layers(Y, n)
    e = [t[k] - t[k + 1] for k in range(n + 1)]
    bad = 0
    if e[0] != 0:
        bad += 1
    for k in range(1, n):
        if e[k] > k * e[k + 1]:
            bad += 1
            print('VIOLATION', label, 'k', k, 'e', e)
    for m in range(1, n + 1):
        d = n - m + 1
        lhs = t[m] - t[n + 1]
        rhs = c(m, d) * e[n]
        if lhs > rhs:
            bad += 1
            print('VIOLATION corollary', label, m, d, lhs, rhs)
    return bad, e


def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    rng = random.Random(20260917)
    total_bad = 0
    tight = 0
    for tr in range(trials):
        D = rng.randint(1, 6)
        L = rng.randint(1, 8)
        U = list(itertools.combinations_with_replacement(range(L + 1), D))
        size = rng.randint(1, min(len(U), 60))
        Y = rng.sample(U, size)
        n = rng.randint(1, 4)
        bad, e = check(Y, n, 'random D=%d L=%d n=%d' % (D, L, n))
        total_bad += bad
        if n >= 2 and e[n - 1] == (n - 1) * e[n]:
            tight += 1
    print('random trials', trials, 'violations', total_bad, 'trials tight at top layer', tight)
    for path in sys.argv[2:]:
        Y = [tuple(int(a) for a in line.strip().split(',')) for line in open(path) if line.strip()]
        for n in (2, 3):
            bad, e = check(Y, n, path)
            total_bad += bad
            print(path, '|Y|', len(Y), 'n', n, 'increments e_0..e_n', e)
    sys.exit(1 if total_bad else 0)


if __name__ == '__main__':
    main()
