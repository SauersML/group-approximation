# Finite test of Theorem S (spectral fold-seed floor).
# Q = Schreier graph of two random permutations a, b of [n].  Triples T_w = {w, a w, b w}
# (with multiplicity); cl = 2-of-3 closure.  r(Q) = least |A| with cl(A) = [n].
# Theorem S, finite form: if |A| <= m <= n and cl(A) = [n], then
#   |A| >= min_{|I| = m} |I \ (a^-1 I  ∩  b^-1 I)|  =: kap(m)
# and, spectrally, kap(n/2) >= (n/4) (1 - lam2), lam2 = top eigenvalue of
# M = (a + a^-1 + b + b^-1)/4 on mean-zero vectors.
# Exhaustive for small n: checks r(Q) >= kap(n/2) >= n(1-lam2)/4 on every sample.
import itertools
import random
import sys

import numpy as np


def closure(A, a, b, n):
    S = set(A)
    ch = True
    while ch:
        ch = False
        for w in range(n):
            t = (w, a[w], b[w])
            for i in range(3):
                # 2-of-3 with multiplicity: the two OTHER positions are in S
                if t[i] not in S and all(t[j] in S for j in range(3) if j != i):
                    S.add(t[i]); ch = True
    return S


def r_exact(a, b, n):
    for k in range(n + 1):
        for A in itertools.combinations(range(n), k):
            if len(closure(A, a, b, n)) == n:
                return k


def kap(a, b, n, m):
    ainv = [0] * n; binv = [0] * n
    for i in range(n):
        ainv[a[i]] = i; binv[b[i]] = i
    best = n
    for I in itertools.combinations(range(n), m):
        S = set(I)
        # x in I with x notin a^-1 I or x notin b^-1 I, i.e. a x notin I or b x notin I
        v = sum(1 for x in I if a[x] not in S or b[x] not in S)
        best = min(best, v)
    return best


def lam2(a, b, n):
    P = np.zeros((n, n))
    for i in range(n):
        P[a[i], i] += 1; P[i, a[i]] += 1; P[b[i], i] += 1; P[i, b[i]] += 1
    ev = np.sort(np.linalg.eigvalsh(P / 4))
    return ev[-2]


if __name__ == '__main__':
    n = int(sys.argv[1]); trials = int(sys.argv[2])
    rng = random.Random(1)
    worst = None
    for t in range(trials):
        a = list(range(n)); b = list(range(n))
        rng.shuffle(a); rng.shuffle(b)
        r = r_exact(a, b, n)
        k = kap(a, b, n, n // 2)
        l2 = lam2(a, b, n)
        sb = n * (1 - l2) / 4
        ok = r >= k >= sb - 1e-9
        print('n=%d r=%d kap(n/2)=%d n(1-lam2)/4=%.3f lam2=%.3f %s' % (n, r, k, sb, l2, 'OK' if ok else 'FAIL'))
