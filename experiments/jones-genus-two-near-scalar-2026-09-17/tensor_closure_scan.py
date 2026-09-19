"""Random search over tensor products of the Jones family (closed-form t_s spectrum, (J2) of
mod-s2-jones-rectangular-separating-twist-spectrum) for the minimum of ||rho(t_s) - omega^{+-1} I||_op.
Claimed uniform lower bound (J5): 2 sin(pi/24) = 0.2611; the scan should never go below it."""
import math, cmath, random
import numpy as np

W = [cmath.exp(2j * math.pi / 3), cmath.exp(-2j * math.pi / 3)]

def spectrum(xs, zetas):
    ev = [1]
    for x, z in zip(xs, zetas):
        f = [z * cmath.exp(96j * x / 5)] + [z * cmath.exp(-24j * x / 5)] * 4
        ev = [a * b for a in ev for b in f]
    return np.array(ev)

def dist(ev):
    return min(np.max(np.abs(ev - w)) for w in W)

if __name__ == "__main__":
    random.seed(1)
    best, arg = 9.0, None
    for trial in range(40000):
        n = random.randint(1, 4)
        xs = [random.choice([0, math.pi / 12, -math.pi / 12]) + random.gauss(0, 0.05 * random.random())
              for _ in range(n)]
        if trial % 2:
            xs = [random.uniform(-math.pi / 8, math.pi / 8) for _ in range(n)]
        xs = [max(-math.pi / 8 + 1e-6, min(math.pi / 8 - 1e-6, x)) for x in xs]
        zs = [cmath.exp(2j * math.pi * random.randrange(5) / 5) for _ in range(n)]
        d = dist(spectrum(xs, zs))
        if d < best:
            best, arg = d, (n, [round(x, 4) for x in xs])
    print("min distance found:", round(best, 5), "at", arg,
          " bound 2sin(pi/24) =", round(2 * math.sin(math.pi / 24), 5))
