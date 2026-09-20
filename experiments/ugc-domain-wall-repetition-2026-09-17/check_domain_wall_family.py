"""Numerical check of the domain-wall XOR family in
research/lambda-gamma-repetition-rates-capped-at-sqrt-gap.md.

Game G(w, L): questions in [L] for each prover. With prob 1/2 ask (i, i) and
check equality. With prob 1/2 sample an edge of H(w, L) and check the XOR sign:
  * with weight 1-w: a uniform cycle edge {i, i+1 mod L}, random orientation,
    sign + except the edge {L-1, 0}, whose sign is -;
  * with weight w: a uniform ordered pair (i, j) in [L]^2, sign +.
Checks:
  (a) sigma_2 of the (symmetric) biadjacency M = I/2 + P_H/2 is <= 1 - w/2;
  (b) exact two-prover value (brute force, small L) <= 1 - (1-w)/(2L);
  (c) SDP deficit of the explicit domain-wall vectors <= 3.24 sqrt(w)/L;
  (d) the parametric choice w = 2 lam, L = floor((1-2lam)/(2gam)) meets
      L >= ceil(1/sqrt w) + 1, gam0 >= gam and delta <= 37 sqrt(lam) gam
      on a grid with lam <= 1/4, gam <= sqrt(lam/128).
"""
import itertools
import math

import numpy as np


def walk(w, L):
    P = np.full((L, L), w / L)
    for i in range(L):
        P[i, (i + 1) % L] += (1 - w) / 2
        P[i, (i - 1) % L] += (1 - w) / 2
    return P


def sigma2(w, L):
    M = 0.5 * np.eye(L) + 0.5 * walk(w, L)
    s = np.sort(np.abs(np.linalg.eigvalsh(M)))[::-1]
    return s[1]


def sign(i, j, L):
    a, b = min(i, j), max(i, j)
    return -1 if (a, b) == (0, L - 1) else 1


def two_prover_value(w, L):
    # distribution over (u, v, s)
    dist = []
    for i in range(L):
        dist.append((i, i, 1, 0.5 / L))
    for i in range(L):
        j = (i + 1) % L
        s = sign(i, j, L)
        dist.append((i, j, s, 0.5 * (1 - w) / L / 2))
        dist.append((j, i, s, 0.5 * (1 - w) / L / 2))
    for i in range(L):
        for j in range(L):
            dist.append((i, j, 1, 0.5 * w / L / L))
    best = 0.0
    for f in itertools.product((1, -1), repeat=L):
        for g in itertools.product((1, -1), repeat=L):
            val = sum(p for (u, v, s, p) in dist if g[v] == s * f[u])
            best = max(best, val)
    return best


def profile(L, W):
    assert L >= W + 1
    th = [0.0] * L
    for t in range(W + 1):
        th[L - W - 1 + t] = t * math.pi / W
    return th


def sdp_deficit(w, L, W):
    th = profile(L, W)
    link = 0.0
    for i in range(L):
        j = (i + 1) % L
        s = sign(i, j, L)
        d = th[j] - th[i] + (0.0 if s == 1 else math.pi)
        link += (1 - math.cos(d)) / 2
    comp = sum((1 - math.cos(th[i] - th[j])) / 2 for i in range(L) for j in range(L))
    return 0.5 * ((1 - w) * link / L + w * comp / L / L)


def main():
    ok = True
    # (a), (c)
    worst_a, worst_c = -1.0, 0.0
    for w in [0.5, 0.3, 0.1, 0.03, 0.01, 0.003]:
        W = math.ceil(1 / math.sqrt(w))
        for L in sorted({W, W + 1, 2 * W + 1, 5 * W, 20 * W + 3}):
            if L < max(3, W + 1):
                continue
            s2 = sigma2(w, L)
            worst_a = max(worst_a, s2 - (1 - w / 2))
            d = sdp_deficit(w, L, W)
            worst_c = max(worst_c, d / (math.sqrt(w) / L))
    print(f"(a) max sigma2 - (1 - w/2) = {worst_a:.3e}  (must be <= 1e-12)")
    print(f"(c) max delta / (sqrt(w)/L) = {worst_c:.4f}  (must be <= 3.24)")
    ok &= worst_a <= 1e-12 and worst_c <= 3.24
    # (b)
    for w, L in [(0.5, 3), (0.2, 3), (0.5, 5), (0.1, 5), (0.3, 7)]:
        v = two_prover_value(w, L)
        bound = 1 - (1 - w) / (2 * L)
        print(f"(b) w={w} L={L}: val={v:.6f}  bound={bound:.6f}  {'ok' if v <= bound + 1e-12 else 'FAIL'}")
        ok &= v <= bound + 1e-12
    # (d)
    worst_d = 0.0
    for lam in [0.25, 0.1, 0.03, 0.01, 1e-3, 1e-4]:
        gmax = math.sqrt(lam / 128)
        for frac in [1.0, 0.7, 0.3, 0.1, 0.01]:
            gam = gmax * frac
            w = 2 * lam
            L = math.floor((1 - 2 * lam) / (2 * gam))
            W = math.ceil(1 / math.sqrt(w))
            gam0 = (1 - w) / (2 * L)
            if not (L >= W + 1 and gam0 >= gam and L >= 3):
                print(f"(d) FAIL feasibility lam={lam} gam={gam}")
                ok = False
                continue
            d = sdp_deficit(w, L, W) if L < 20000 else (math.pi ** 2 / (8 * L * W) + w * W / L)
            worst_d = max(worst_d, d / (math.sqrt(lam) * gam))
    print(f"(d) max delta / (sqrt(lam) gam) = {worst_d:.4f}  (must be <= 37)")
    ok &= worst_d <= 37
    print("ALL OK" if ok else "SOME CHECK FAILED")


if __name__ == "__main__":
    main()
