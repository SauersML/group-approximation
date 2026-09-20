"""Scan: smallest ball radius R whose pushed DT measure on the horocycle
quotient of T_k has Chernoff value inf_lambda sum_h mu_R(h) e^(lambda h) < 1
(a Green certificate, D(B_R,p) < infinity), versus the total mass test
(the l1 = l2(Z) norm, which is the quotient spectral certificate on Z).
Everything in logs.  At lambda = (1/2) log(k-1) all up/down weights balance;
the scan also minimises over lambda on a grid.
"""
import math


def log_chernoff(k, n, p, lam):
    # n = R+1; terms: j=n (height n), j=0 (height -n, count (k-1)^n),
    # 0<j<n (height 2j-n, count (k-2)(k-1)^(n-j-1))
    terms = [lam * n, n * math.log(k - 1) - lam * n]
    for j in range(1, n):
        terms.append(math.log(k - 2) + (n - j - 1) * math.log(k - 1)
                     + lam * (2 * j - n))
    m = max(terms)
    return n * math.log(p) + m + math.log(sum(math.exp(t - m) for t in terms))


def best(k, n, p):
    lam0 = 0.5 * math.log(k - 1)
    return min(log_chernoff(k, n, p, lam0 + d / 200.0) for d in range(-40, 41))


if __name__ == "__main__":
    for k in (3, 4, 6):
        pc, pt = 1.0 / (k - 1), 1.0 / math.sqrt(k - 1)
        print(f"k={k} p_c={pc:.4f} p_t={pt:.4f}")
        for frac in (0.25, 0.5, 0.75, 0.9, 0.97, 1.0, 1.03):
            p = pc + frac * (pt - pc)
            hit = None
            for R in range(0, 800):
                if best(k, R + 1, p) < 0:
                    hit = R
                    break
            mass_log = (R + 1) * math.log(p) + math.log(k) + R * math.log(k - 1)
            print(f"  p={p:.4f} (frac {frac}) first R with Green cert: {hit}"
                  f"   log mass at that R: {mass_log:.1f}")
