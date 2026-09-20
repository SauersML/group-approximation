"""Exploratory (floating point) continuum model of the random-priority pin-ball
adversary for Had_k -> Max-2Lin(2), k -> infinity.

Adversary: backbone tau*x_i (i uniform, tau = +-1); every pin y = +-chi_a gets
an independent radius r_y (r_{-y} = r_y) with survival g(d/K) = Pr[r > d] and
an independent uniform priority; x takes the label of the top-priority pin
whose ball contains it, else the backbone.  Per-edge cost K*Pr[cut] in the
limit, for an edge whose endpoint sees pins at normalized distances s_l:

  cost = sum_i a(s_i) * int_0^1 prod_{l != i} (1 - u g(s_l)) du + prod_l (1 - g(s_l)),
  a = -g'/2.

Configurations obey Parseval sum (1 - 2 s_l)^2 <= 1 and triangle s_i + s_l >= 1/2.
This script only explores; it proves nothing.
"""
import numpy as np
from numpy.polynomial import polynomial as P
from scipy.interpolate import PchipInterpolator
from scipy.optimize import minimize

rng = np.random.default_rng(1)


def make_profile(smax, vals):
    """vals: interior values of g on a uniform grid of [0, smax], decreasing."""
    xs = np.linspace(0, smax, len(vals) + 2)
    ys = np.concatenate([[1.0], vals, [0.0]])
    f = PchipInterpolator(xs, ys)
    df = f.derivative()

    def g(s):
        s = np.asarray(s, float)
        return np.where(s >= smax, 0.0, f(np.clip(s, 0, smax)))

    def a(s):
        s = np.asarray(s, float)
        return np.where(s >= smax, 0.0, -0.5 * df(np.clip(s, 0, smax)))
    return g, a


def cost(s, g, a):
    s = np.asarray(s, float)
    gs, as_ = g(s), a(s)
    total = np.prod(1 - gs)
    for i in range(len(s)):
        poly = np.array([1.0])
        for l in range(len(s)):
            if l != i:
                poly = P.polymul(poly, [1.0, -gs[l]])
        integ = P.polyint(poly)
        total += as_[i] * P.polyval(1.0, integ)
    return float(total)


def worst(g, a, smax, Mmax=10, starts=40):
    best, bestc = -1, None
    for M in range(1, Mmax + 1):
        for _ in range(starts):
            x0 = rng.uniform(0.25, smax, M)
            if M == 1:
                x0 = rng.uniform(0, smax, 1)
            cons = [{'type': 'ineq', 'fun': lambda s: 1 - np.sum((1 - 2 * s) ** 2)}]
            for i in range(M):
                for l in range(i + 1, M):
                    cons.append({'type': 'ineq', 'fun': lambda s, i=i, l=l: s[i] + s[l] - 0.5})
            if np.sum((1 - 2 * x0) ** 2) > 1:
                continue
            r = minimize(lambda s: -cost(s, g, a), x0, method='SLSQP',
                         bounds=[(0, 0.5)] * M, constraints=cons,
                         options={'maxiter': 200})
            s = np.clip(r.x, 0, 0.5)
            if np.sum((1 - 2 * s) ** 2) <= 1 + 1e-7:
                c = cost(s, g, a)
                if c > best:
                    best, bestc = c, s
    return best, bestc


if __name__ == '__main__':
    for smax in [0.3, 0.35, 0.4, 0.45]:
        n = 8
        xs = np.linspace(0, smax, n + 2)[1:-1]
        # start from the single-pin exponential optimum truncated at smax
        C = 1 / (1 - np.exp(-2 * smax))
        vals = 1 - C * (1 - np.exp(-2 * xs))
        g, a = make_profile(smax, vals)
        w, cfg = worst(g, a, smax, Mmax=8, starts=15)
        print(f"smax={smax} expo-profile C1={C:.4f} worst={w:.4f} cfg={np.round(cfg,3)}")
