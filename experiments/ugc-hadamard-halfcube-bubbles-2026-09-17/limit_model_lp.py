"""K -> infinity model of the half-cube bubble adversary, and its minimax LP.

Normalize distances by K.  The common radius has density gamma on [0, 1/2)
(gamma = K q_t), F(s) = int_s gamma.  A configuration is a point x whose
Fourier mass sits on the span of m characters, x = f(L(i)), with f either
Boolean or [-1,1]-valued (then x_i is +-1 with mean f(L(i))).  Its pins are
the nearer signed characters, at normalized distance (1 - |f^(a)|)/2.
A coordinate i with pattern v activates pin a iff x_i sigma_a chi_a(v) = 1
(the pin lies in x's half {z : z_i = x_i}).  With B the uniform random bad
set and u the pattern of the edge direction j, the limit price is

  1 - int gamma(s) (a(s) + b(s) - 2 a(s) b(s)) ds + E_v E_B gamma(D(v))

where D(v) is the distance to the nearest bad pin active at v, a(s) =
Pr[D(u) <= s], and b(s) = Pr[nearest bad pin inactive at u is <= s].
(The second term is sum_{i != j} Pr[cut | i] for a smooth radius law; the
first is Pr[cut | i = j] = Pr[x, y both flipped or both unflipped].)

The LP minimizes the max price over the listed configurations, with gamma
piecewise constant on cells of width h centred on multiples of h, and zero on
cells within `gap` of 1/2.
"""
import itertools, sys
import numpy as np
from scipy.optimize import linprog


def boolean_configs(m):
    """Yield (pins, points): pins = list of (dist, act) with act a dict
    point->bool; points = list of (point, weight)."""
    V = list(range(1 << m))
    chi = lambda a, v: -1 if bin(a & v).count("1") % 2 else 1
    seen = set()
    for bits in itertools.product((1, -1), repeat=len(V)):
        if bits[0] != 1:
            continue  # f -> -f symmetry
        key = bits
        if key in seen:
            continue
        seen.add(key)
        f = dict(zip(V, bits))
        pins = []
        for a in V:
            fh = sum(f[v] * chi(a, v) for v in V) / len(V)
            if abs(fh) < 1e-12:
                continue
            s = 1 if fh > 0 else -1
            act = {v: f[v] * s * chi(a, v) == 1 for v in V}
            pins.append(((1 - abs(fh)) / 2, act))
        yield pins, [(v, 1.0 / len(V)) for v in V]


def fractional_configs(m, grid):
    """[-1,1]-valued f on F_2^m with values in `grid`; points are (v, sign)."""
    V = list(range(1 << m))
    chi = lambda a, v: -1 if bin(a & v).count("1") % 2 else 1
    for vals in itertools.product(grid, repeat=len(V)):
        f = dict(zip(V, vals))
        pts = []
        for v in V:
            for sg in (1, -1):
                w = (1 + sg * f[v]) / 2 / len(V)
                if w > 1e-12:
                    pts.append(((v, sg), w))
        pins = []
        for a in V:
            fh = sum(f[v] * chi(a, v) for v in V) / len(V)
            if abs(fh) < 1e-12:
                continue
            s = 1 if fh > 0 else -1
            act = {(v, sg): sg * s * chi(a, v) == 1 for v in V for sg in (1, -1)}
            pins.append(((1 - abs(fh)) / 2, act))
        yield pins, pts


def nearest_bad_law(dists):
    """Given pin distances, return list of (level, prob nearest bad is there)."""
    out = []
    below = 0
    for lev in sorted(set(dists)):
        n = sum(1 for d in dists if d == lev)
        out.append((lev, 2.0 ** -below * (1 - 2.0 ** -n)))
        below += n
    return out


def cdf(dists, s):
    return 1 - 2.0 ** -sum(1 for d in dists if d <= s + 1e-12)


class Cells:
    def __init__(self, h, gap):
        self.h = h
        n = int(round(0.5 / h))
        self.centres = np.array([k * h for k in range(n) if k * h < 0.5 - gap - 1e-12])
        self.lo = np.maximum(self.centres - h / 2, 0)
        self.hi = self.centres + h / 2

    def index(self, x):
        k = int(round(x / self.h))
        return k if k < len(self.centres) and abs(k * self.h - x) < 1e-9 else None


def coef_rows(configs, cells):
    rows = []
    n = len(cells.centres)
    for pins, pts in configs:
        if any(cells.index(d) is None and d < cells.hi[-1] for d, _ in pins):
            raise ValueError("pin distance off the cell grid")
        # E_v E_B gamma(D(v)) : independent of u
        t2 = np.zeros(n)
        for v, w in pts:
            for lev, p in nearest_bad_law([d for d, act in pins if act[v]]):
                k = cells.index(lev)
                if k is not None:
                    t2[k] += w * p
        for u, _ in pts:
            plus = [d for d, act in pins if act[u]]
            minus = [d for d, act in pins if not act[u]]
            t1 = np.zeros(n)
            for k in range(n):
                # a, b are step functions with jumps only at cell centres
                for lo, hi in ((cells.lo[k], cells.centres[k]), (cells.centres[k], cells.hi[k])):
                    if hi <= lo:
                        continue
                    s = (lo + hi) / 2
                    a, b = cdf(plus, s), cdf(minus, s)
                    t1[k] += (hi - lo) * (a + b - 2 * a * b)
            rows.append(t2 - t1)
    return np.array(rows)


def solve(rows, cells):
    n = len(cells.centres)
    rows = np.unique(np.round(rows, 12), axis=0)
    c = np.zeros(n + 1)
    c[-1] = 1
    A = np.hstack([rows, -np.ones((len(rows), 1))])
    b = -np.ones(len(rows))
    widths = cells.hi - cells.lo
    res = linprog(c, A_ub=A, b_ub=b, A_eq=[list(widths) + [0]], b_eq=[1],
                  bounds=[(0, None)] * n + [(None, None)], method="highs")
    return res.x[:n], res.x[-1], rows


if __name__ == "__main__":
    mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    h = float(sys.argv[2]) if len(sys.argv) > 2 else 1 / 16
    gap = float(sys.argv[3]) if len(sys.argv) > 3 else 0.0
    cells = Cells(h, gap)
    configs = []
    for m in range(0, mmax + 1):
        configs += list(boolean_configs(m))
    # single fractional pins at every cell centre
    grid1 = [1 - 2 * c for c in cells.centres]
    configs += list(fractional_configs(0, grid1))
    rows = coef_rows(configs, cells)
    g, z, rows = solve(rows, cells)
    print("mmax", mmax, "h", h, "gap", gap, "configs", len(configs), "rows", len(rows))
    print("LP value (limit price of best radius law in this family):", z)
    print("gamma", " ".join("%.3f" % v for v in g))
