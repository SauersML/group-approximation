#!/usr/bin/env python3
"""Two-cell data-processing cap for Phi(nu, eta) = BC(nu,eta)^2 + BC(nu*eta, nu)  (float scouting).

For a threshold t put x' = F(t-1), x = F(t) (cdf of nu), y = G(t) (cdf of eta).  Coarse-graining to
{<= t}, {> t} and P(X+Y <= t) <= F(t-1) G(t-1) <= x' y give
    Phi <= H(x', x) := max_y (sqrt(x y) + sqrt((1-x)(1-y)))^2 + sqrt(x x' y) + sqrt((1-x)(1-x' y)).
H is increasing in x'.  For any x0 some t has x' <= x0 <= x, hence Phi <= C(x0) := sup_{x >= x0} H(x0, x).
Prints min over x0 of C(x0) on a grid.  Float scouting only: not used by any proof (the proved cap
is the analytic 71/72 of thompson-f-product-forest-vectors-stay-below-71-72-proof).
"""
import numpy as np

y = np.linspace(0, 1, 4001)[None, :]


def H(xp, x):
    x = np.asarray(x)[:, None]
    v = (np.sqrt(x * y) + np.sqrt((1 - x) * (1 - y))) ** 2 + np.sqrt(x * xp * y) + np.sqrt((1 - x) * (1 - xp * y))
    return v.max(axis=1)


best = None
for x0 in np.linspace(0.3, 0.9, 121):
    xs = np.linspace(x0, 1, 2001)
    c = H(x0, xs).max()
    if best is None or c < best[1]:
        best = (x0, c)
print('best x0 = %.4f  cap Phi <= %.6f  normP <= %.6f' % (best[0], best[1], best[1] / 2))
