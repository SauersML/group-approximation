"""Green (return) certificate versus l1/l2 certificate for the pushed
Duminil-Copin--Tassion ball measure on the k-regular tree T_k, pushed to the
horocycle quotient D = Z (heights with respect to a fixed end xi).

For S = B_R, P_p(o <->_S u) = p^d(o,u), boundary edges go from the sphere
S_R to S_(R+1), so the pushed measure is
    mu_R(h) = p^(R+1) * #{v in S_(R+1) : height(v) = h},
and the final factor is a_R(h) = #{y in B_R : height(y) = h}.
A vertex at distance n reached by j up-steps then n-j down-steps has height
2j-n; the counts are c(n,n) = 1, c(n,0) = (k-1)^n and
c(n,j) = (k-2)(k-1)^(n-j-1) for 0 < j < n.

Printed per (k,p):
  mass  = total mass of mu_R  (the l1 = l2(Z) norm; DT certificate needs < 1)
  chern = inf_lambda sum_h mu_R(h) e^(lambda h)  (Chernoff bound on the
          return rate; < 1 certifies D(B_R,p) < infinity)
  green = partial sums of D(B_R,p) = sum_k (mu^k * a)(0), k <= K, computed by
          direct convolution, to check finiteness numerically.
"""
import math
import numpy as np


def sphere_heights(k, n):
    out = {}
    if n == 0:
        return {0: 1}
    out[n] = out.get(n, 0) + 1
    out[-n] = out.get(-n, 0) + (k - 1) ** n
    for j in range(1, n):
        h = 2 * j - n
        out[h] = out.get(h, 0) + (k - 2) * (k - 1) ** (n - j - 1)
    return out


def mu_and_a(k, R, p):
    mu = {h: c * p ** (R + 1) for h, c in sphere_heights(k, R + 1).items()}
    a = {}
    for n in range(R + 1):
        for h, c in sphere_heights(k, n).items():
            a[h] = a.get(h, 0) + c
    return mu, a


def chernoff(mu):
    best = float("inf")
    for i in range(-4000, 4001):
        lam = i / 1000.0
        best = min(best, sum(w * math.exp(lam * h) for h, w in mu.items()))
    return best


def green_partial(mu, a, K):
    hs = sorted(mu)
    lo, hi = hs[0], hs[-1]
    kern = np.zeros(hi - lo + 1)
    for h, w in mu.items():
        kern[h - lo] = w
    alo, ahi = min(a), max(a)
    cur = np.zeros(ahi - alo + 1)
    for h, c in a.items():
        cur[h - alo] = c
    off = alo  # index 0 of cur corresponds to height off
    total = 0.0
    sums = []
    for kk in range(K + 1):
        if off <= 0 <= off + len(cur) - 1:
            total += cur[-off]
        sums.append(total)
        cur = np.convolve(cur, kern)
        off += lo
        m = cur.max()
        if m > 1e300:
            return sums, "overflow"
    return sums, "ok"


if __name__ == "__main__":
    for k in (3, 4):
        pc, pt = 1.0 / (k - 1), 1.0 / math.sqrt(k - 1)
        print(f"k={k}  p_c={pc:.4f}  p_t={pt:.4f}")
        for p in (0.9 * pc + 0.1 * pt, 0.5 * (pc + pt), 0.9 * pt + 0.1 * pc,
                  1.05 * pt):
            for R in (4, 8, 16):
                mu, a = mu_and_a(k, R, p)
                mass = sum(mu.values())
                ch = chernoff(mu)
                g, st = green_partial(mu, a, 300 if R <= 8 else 120)
                print(f"  p={p:.4f} R={R:2d} mass={mass:9.3e} chern={ch:.4f} "
                      f"green[K/2]={g[len(g)//2]:.4e} green[K]={g[-1]:.4e} {st}")
