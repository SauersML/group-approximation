"""Rigorous upper bound on delta_k = 1/2 - E max_a |W_f(a)| / (2K), f uniform on
{+-1}^(F_2^k), from the first M binomial moments of N_t = #{a : |W(a)| >= t}.

Exactness:
  * S_r(t) = E C(N_t, r) = sum over r-subsets {a_1..a_r} of Pr[|W(a_l)| >= t all l].
    The joint law of (W(a_1..a_r)) depends only on the multiset of image counts
    of i -> (a_l . i)_l (up to a permutation of l, which the symmetric event
    ignores). Each law is computed as integer counts (out of 2^K) modulo enough
    primes below 2^20 and recovered by CRT (the counts are <= 2^K <
    product of the primes, chosen > 2^(K+1)). So every S_r(t) is an exact Fraction.
  * For each even t, a float LP gives a dual polynomial
    P(n) = y_0 + sum_r y_r C(n, r). It is rounded to rationals, and y_0 is
    lowered until P(n) <= 1[n >= 1] holds exactly for n = 0..K. Then
    Pr[N_t >= 1] >= E P(N_t) = y_0 + sum_r y_r S_r(t) (weak duality), exactly.
  * E max|W| = sum_{t even >= 2} 2 Pr[max |W| >= t], since W is even.
Usage: python3 delta_exact_certificate.py k M
"""
import itertools, sys
from fractions import Fraction as Fr
from math import comb
import numpy as np
from scipy.optimize import linprog

k = int(sys.argv[1]); M = int(sys.argv[2])
K = 2 ** k
def _primes_below(n, need_bits):
    out, prod, x = [], 1, n - 1
    while prod <= 2 ** need_bits:
        if all(x % d for d in range(2, int(x ** 0.5) + 1)):
            out.append(x); prod *= x
        x -= 1
    return out
PRIMES = _primes_below(2 ** 20, K + 1)   # product > 2^(K+1) > every count
dot = lambda a, i: bin(a & i).count("1") & 1


def image_counts(tup):
    counts = {}
    for i in range(K):
        v = tuple(dot(a, i) for a in tup)
        counts[v] = counts.get(v, 0) + 1
    return counts


def canon(counts, m):
    best = None
    for perm in itertools.permutations(range(m)):
        key = tuple(sorted((tuple(v[p] for p in perm), c) for v, c in counts.items()))
        if best is None or key < best:
            best = key
    return best


def law_mod(key, m, p):
    """Integer counts (mod p) of idx-vectors; W_l = 2 idx_l - K."""
    arr = np.ones((1,) * m, dtype=np.int64)
    n = 0
    for v, c in key:
        for _ in range(c):
            new = np.zeros((n + 2,) * m, dtype=np.int64)
            plus = tuple(slice(1, None) if b == 0 else slice(0, n + 1) for b in v)
            minus = tuple(slice(0, n + 1) if b == 0 else slice(1, None) for b in v)
            new[plus] += arr
            new[minus] += arr
            np.remainder(new, p, out=new)
            arr = new; n += 1
    assert n == K
    return arr


def crt(res):
    x, mod = 0, 1
    for r, p in zip(res, PRIMES):
        t = ((r - x) * pow(mod, -1, p)) % p
        x += mod * t; mod *= p
    return x


absW = np.abs(2 * np.arange(K + 1) - K)
TS = list(range(2, K + 1, 2))


def tail_counts(key, m):
    """Exact #{f : min_l |W(a_l)| >= t} for each t in TS."""
    mins = absW
    for ax in range(1, m):
        shp = [1] * (ax + 1); shp[ax] = K + 1
        mins = np.minimum(mins[..., None], absW.reshape(shp))
    mins = mins.ravel()
    per_p = []
    for p in PRIMES:
        arr = law_mod(key, m, p).ravel()
        h = np.bincount(mins, weights=arr.astype(np.float64), minlength=K + 1)
        hi = [int(round(x)) % p for x in h]
        tails = [0] * (K + 2)
        for v in range(K, -1, -1):
            tails[v] = (tails[v + 1] + hi[v]) % p
        per_p.append(tails)
    out = {}
    for t in TS:
        c = crt([tl[t] for tl in per_p])
        assert 0 <= c <= 2 ** K
        out[t] = c
    return out


# ---- exact binomial moments S[r][t], r = 1..M ----
S = {r: {t: Fr(0) for t in TS} for r in range(1, M + 1)}
for m in range(1, M + 1):
    cnt = {}
    for tup in itertools.combinations(range(K), m):
        key = canon(image_counts(tup), m)
        cnt[key] = cnt.get(key, 0) + 1
    assert sum(cnt.values()) == comb(K, m)
    print("m", m, "types", len(cnt), file=sys.stderr, flush=True)
    for key, c in cnt.items():
        tc = tail_counts(key, m)
        for t in TS:
            S[m][t] += Fr(c * tc[t], 2 ** K)

# ---- per-threshold dual certificate, verified exactly ----
Emax = Fr(0)
for t in TS:
    s = [S[r][t] for r in range(1, M + 1)]
    if s[0] == 0:
        continue
    A_eq = [[comb(j, r) for j in range(K + 1)] for r in range(1, M + 1)] + [[1] * (K + 1)]
    b = [float(x) for x in s] + [1.0]
    res = linprog([0] + [1] * K, A_eq=A_eq, b_eq=b, bounds=[(0, None)] * (K + 1), method="highs")
    if res.status != 0:
        print("t", t, "LP status", res.status, file=sys.stderr)
        continue
    y = [Fr(float(v)).limit_denominator(10 ** 12) for v in res.eqlin.marginals]
    yr, y0 = y[:M], y[M]
    P = lambda n: y0 + sum(yr[r - 1] * comb(n, r) for r in range(1, M + 1))
    viol = max(P(n) - (1 if n >= 1 else 0) for n in range(K + 1))
    if viol > 0:
        y0 -= viol
    assert all(P(n) <= (1 if n >= 1 else 0) for n in range(K + 1))
    lb = y0 + sum(yr[r - 1] * s[r - 1] for r in range(1, M + 1))
    lb = max(Fr(0), lb)
    Emax += 2 * lb
    print("t", t, "S1", float(s[0]), "LP", res.fun, "certified", float(lb), file=sys.stderr, flush=True)

dub = Fr(1, 2) - Emax / (2 * K)
rub = 1 + dub * (3 - Fr(4, K))
print(k, M, "certified E max|W| >=", float(Emax), "delta_k <=", float(dub), "R*(k) <=", float(rub))
print("  exact delta_k bound:", dub)
print("  exact R*(k) bound:", rub)
