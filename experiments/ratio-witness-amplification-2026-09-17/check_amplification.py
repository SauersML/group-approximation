"""Numerical sanity check for classical-unitary-ratio-witnesses-amplify-to-metric-models.

Exact arithmetic on spectral measures (atomic measures on the circle group
Z/N, written additively), no matrices needed: the eigenvalue measure of a
k-fold tensor power is the k-fold convolution of the eigenvalue measure.

Checks:
 (R) rank: if mu has atom 1-delta at 0 (delta < 1/2) and k = ceil(pi / delta),
     then mu^{*k}({0}) <= 3/4.  Also checks the bound S <= (1 + M)/2,
     M = max binomial pmf, and M <= sqrt(pi / (8 k p q)).
 (H) HS: for random / adversarial spectra, the case split of the proof yields
     tensor exponent k and separation as claimed.
"""
import math
import random
from fractions import Fraction


def convolve(a, b, N):
    out = [0.0] * N
    for i, x in enumerate(a):
        if x == 0.0:
            continue
        for j, y in enumerate(b):
            if y:
                out[(i + j) % N] += x * y
    return out


def power(mu, k, N):
    res = [0.0] * N
    res[0] = 1.0
    base = mu[:]
    while k:
        if k & 1:
            res = convolve(res, base, N)
        base = convolve(base, base, N)
        k >>= 1
    return res


def binom_max(k, p):
    # max pmf of Bin(k,p), computed in log space
    best = 0.0
    for j in range(k + 1):
        lg = (math.lgamma(k + 1) - math.lgamma(j + 1) - math.lgamma(k - j + 1)
              + (j * math.log(p) if p > 0 else 0) + ((k - j) * math.log(1 - p)))
        best = max(best, math.exp(lg))
    return best


def check_rank(trials=300, seed=1):
    rnd = random.Random(seed)
    worst = 0.0
    for t in range(trials):
        N = rnd.choice([2, 3, 4, 6, 12, 60])
        delta = rnd.choice([0.4, 0.2, 0.1, 0.05, 0.02])
        nu = [0.0] * N
        if t % 3 == 0:
            nu[N // 2 if N % 2 == 0 else 1] = 1.0  # adversarial: eigenvalue -1
        else:
            support = rnd.sample(range(1, N), max(1, min(N - 1, rnd.randint(1, 3))))
            for s in support:
                nu[s] = rnd.random()
            tot = sum(nu)
            nu = [x / tot for x in nu]
        mu = [delta * x for x in nu]
        mu[0] += 1 - delta
        k = math.ceil(math.pi / delta)
        S = power(mu, k, N)[0]
        M = binom_max(k, delta)
        assert S <= (1 + M) / 2 + 1e-9, (N, delta, S, M)
        assert M <= 0.5 + 1e-12
        assert M <= math.sqrt(math.pi / (8 * k * delta * (1 - delta))) + 1e-12
        assert S <= 0.75 + 1e-9, (N, delta, k, S)
        worst = max(worst, S)
    return worst


def check_hs(trials=2000, seed=2):
    rnd = random.Random(seed)
    worst = 9.0
    for _ in range(trials):
        n = rnd.randint(1, 6)
        ang = [rnd.choice([0.0, rnd.uniform(-math.pi, math.pi), rnd.gauss(0, 0.01)]) for _ in range(n)]
        w = [rnd.random() for _ in range(n)]
        tw = sum(w)
        w = [x / tw for x in w]
        tau = sum(wi * complex(math.cos(a), math.sin(a)) for wi, a in zip(w, ang))
        s = 2 - 2 * tau.real
        if s < 1e-12:
            continue
        rho = abs(tau)
        if rho <= 1 - s / 8:
            C = 1.0
            k = math.ceil(8 * C / s)
            val = rho ** (2 * k)  # trace of (U tensor conj U)^{tensor k}
            sep = 2 - 2 * val
            assert sep >= 2 * (1 - math.exp(-C)) - 1e-9
        else:
            theta = abs(math.atan2(tau.imag, tau.real))
            assert theta >= math.sqrt(3 * s / 4) - 1e-9, (s, rho, theta)
            k = math.ceil(math.pi / (2 * theta))
            assert k <= 2 / math.sqrt(s) + 1 + 1e-9
            val = (tau ** k).real
            sep = 2 - 2 * val
            assert sep >= 2 - 1e-9
        worst = min(worst, sep)
    return worst


if __name__ == "__main__":
    print("rank: worst fixed fraction after amplification =", round(check_rank(), 4), "(bound 0.75)")
    print("HS: worst squared separation after amplification =", round(check_hs(), 4), "(bound 2(1-e^-1))")
