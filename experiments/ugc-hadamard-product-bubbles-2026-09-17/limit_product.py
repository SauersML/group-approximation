"""K -> infinity first-order price of the product-threshold adversary P_g.

A configuration is f: F_2^m -> [-1,1]; coordinate i has pattern v = L(i)
and sign s = x_i with Pr[s = 1 | v] = (1 + f(v))/2.  Pin a has correlation
fh_a = E_v f(v) chi_a(v), and in the half-cube of a coordinate (v, s) its
signed correlation is w_a = s chi_a(v) fh_a.  g: [-1,1] -> [0,1] with
g = 0 on w <= 0 and g(1) = 1.  An edge flips a coordinate j of pattern
(u, sigma); every pin's w moves by 2/K in absolute value.  First order:

  sum_{i != j} Pr[cut | i] -> B = E_(v,s) [ prod_b (1 - g_b/2) * sum_a 2|g'_a|/(2 - g_a) ]
  Pr[cut | i = j]          -> A = 1 - Px - Py + 2 Px Py,
      Px = prod_a (1 - g(wx_a)/2), Py = prod_a (1 - g(-wx_a)/2), wx_a = sigma chi_a(u) fh_a.

price(f, u, sigma) = A + B (|g'| taken as the larger one-sided slope).
"""
import itertools
import numpy as np


def chi_table(m):
    V = 1 << m
    return np.array([[(-1) ** bin(a & v).count("1") for v in range(V)] for a in range(V)], float)


class Profile:
    """Piecewise-linear g on knots w_0 = 0 < ... < w_n = 1, g(0) = 0, g(1) = 1."""

    def __init__(self, knots, vals):
        self.w = np.asarray(knots, float)
        self.g = np.asarray(vals, float)

    def val(self, w):
        return np.where(w <= 0, 0.0, np.interp(np.clip(w, 0, 1), self.w, self.g))

    def slope(self, w):
        sl = np.diff(self.g) / np.diff(self.w)
        w = np.clip(w, 0, 1)
        idx = np.searchsorted(self.w, w, side="right") - 1
        idx = np.clip(idx, 0, len(sl) - 1)
        left = np.clip(np.searchsorted(self.w, w, side="left") - 1, 0, len(sl) - 1)
        s = np.maximum(np.abs(sl[idx]), np.abs(sl[left]))
        return np.where(w <= 0, np.where(w == 0, np.abs(sl[0]), 0.0), s)


def config_prices(f, C, prof):
    """Return list of prices over admissible edge types (u, sigma)."""
    V = len(f)
    fh = C @ f / V
    keep = np.abs(fh) > 1e-12
    Ck, fk = C[keep], fh[keep]
    # B term
    B = 0.0
    for v in range(V):
        for s in (1, -1):
            p = (1 + s * f[v]) / 2 / V
            if p <= 1e-15:
                continue
            w = s * Ck[:, v] * fk
            gv = prof.val(w)
            gd = prof.slope(w) * (w >= 0)
            B += p * np.prod(1 - gv / 2) * np.sum(2 * gd / (2 - gv))
    out = []
    for u in range(V):
        for sg in (1, -1):
            if (1 + sg * f[u]) / 2 <= 1e-15:
                continue
            wx = sg * Ck[:, u] * fk
            Px = np.prod(1 - prof.val(wx) / 2)
            Py = np.prod(1 - prof.val(-wx) / 2)
            out.append(1 - Px - Py + 2 * Px * Py + B)
    return out


def boolean_configs(m):
    V = 1 << m
    for bits in itertools.product((1.0, -1.0), repeat=V):
        if bits[0] != 1:
            continue
        yield np.array(bits)


def fractional_configs(m, grid):
    V = 1 << m
    for vals in itertools.product(grid, repeat=V):
        yield np.array(vals)
