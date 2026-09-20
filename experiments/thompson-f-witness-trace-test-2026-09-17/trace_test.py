#!/usr/bin/env python3
"""Trace-consistency test for Hilbert--Schmidt witnesses of Thompson's F.

Every tracial limit of HS almost-representations of F is t*tau_reg + (1-t)*chi, where chi factors
through F^ab = Z^2 (thompson-f-character-simplex).  So a *good* witness (small relator defect) must
have, for every word w in F_2 with image g in F:
  g = 1            : tr(w) ~ 1
  g in F' \ {1}    : tr(w) ~ 1 - t        (one common value!)
  g notin F'       : tr(w) ~ (1-t) * mu^(ab(g))
This script enumerates all reduced words of length <= L in a, b (a = x0, b = x1), decides the
class of each word exactly (PL homeomorphisms of [0,1] with Fraction breakpoints), evaluates the
normalized trace in a saved witness, and reports the spread of tr over the class F' \ {1}.
The spread is a lower bound on how far the witness is from *any* trace of F on the ball of radius L.

Usage: python3 trace_test.py WITNESS.npy [L]
"""

import sys
import json
from fractions import Fraction as Q

import numpy as np

# ---- PL maps: sorted breakpoint lists [(x, y)], from (0,0) to (1,1); composition (f*g)(x) = f(g(x))


def ev(f, x):
    for (x0, y0), (x1, y1) in zip(f, f[1:]):
        if x0 <= x <= x1:
            return y0 + (y1 - y0) * (x - x0) / (x1 - x0)
    raise ValueError(x)


def inv(f):
    return [(y, x) for (x, y) in f]


def compose(f, g):
    """x -> f(g(x))."""
    xs = set(x for x, _ in g)
    gi = inv(g)
    xs |= set(ev(gi, x) for x, _ in f)
    xs = sorted(xs)
    pts = [(x, ev(f, ev(g, x))) for x in xs]
    # drop collinear interior points
    out = [pts[0]]
    for i in range(1, len(pts) - 1):
        (xa, ya), (xb, yb), (xc, yc) = out[-1], pts[i], pts[i + 1]
        if (yb - ya) * (xc - xb) != (yc - yb) * (xb - xa):
            out.append(pts[i])
    out.append(pts[-1])
    return out


ID = [(Q(0), Q(0)), (Q(1), Q(1))]
X0 = [(Q(0), Q(0)), (Q(1, 2), Q(1, 4)), (Q(3, 4), Q(1, 2)), (Q(1), Q(1))]
X1 = [(Q(0), Q(0)), (Q(1, 2), Q(1, 2)), (Q(3, 4), Q(5, 8)), (Q(7, 8), Q(3, 4)), (Q(1), Q(1))]


def slope_germs(f):
    """F' = elements with slope 1 at both ends (standard)."""
    (x0, y0), (x1, y1) = f[0], f[1]
    (u0, v0), (u1, v1) = f[-2], f[-1]
    return (y1 - y0) / (x1 - x0), (v1 - v0) / (u1 - u0)


# Word letters: 0=a,1=A,2=b,3=B.  Convention: the matrix of a word w1...wk is W(w1)...W(wk); the
# PL element is chosen so that the map word -> PL is a homomorphism for the same product order.
# We check both composition orders against the relators and keep the one that works.

def word_pl(word, order):
    gens = [X0, inv(X0), X1, inv(X1)]
    f = ID
    for l in word:
        f = compose(f, gens[l]) if order == 0 else compose(gens[l], f)
    return f


def rel_words():
    a, A, b, B = 0, 1, 2, 3
    x = [a, B]
    xi = [b, A]
    y = [A, b, a]
    yi = [A, B, a]
    z = [A, A, b, a, a]
    zi = [A, A, B, a, a]
    R1 = x + y + xi + yi
    R2 = x + z + xi + zi
    c = [a, b, A, B]
    return R1, R2, c


def pick_order():
    R1, R2, c = rel_words()
    for order in (0, 1):
        if word_pl(R1, order) == ID and word_pl(R2, order) == ID and word_pl(c, order) != ID:
            return order
    raise RuntimeError("no composition order satisfies the relators")


def main():
    path = sys.argv[1]
    L = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    W = np.load(path)
    n = W.shape[-1]
    Ua, Ub = W[0], W[1]
    mats = [Ua, Ua.conj().T, Ub, Ub.conj().T]
    order = pick_order()
    gens_pl = [X0, inv(X0), X1, inv(X1)]
    INV = [1, 0, 3, 2]
    recs = []  # (length, class, abelian exps, trace)

    def dfs(word, M, f, ea, eb):
        if word:
            s0, s1 = slope_germs(f)
            if f == ID:
                cls = "trivial"
            elif ea == 0 and eb == 0:
                cls = "Fprime"
            else:
                cls = "other"
            recs.append((len(word), cls, (ea, eb), float(np.real(np.trace(M))) / n))
        if len(word) == L:
            return
        for l in range(4):
            if word and l == INV[word[-1]]:
                continue
            f2 = compose(f, gens_pl[l]) if order == 0 else compose(gens_pl[l], f)
            da = (1 if l == 0 else -1 if l == 1 else 0)
            db = (1 if l == 2 else -1 if l == 3 else 0)
            dfs(word + [l], M @ mats[l], f2, ea + da, eb + db)

    dfs([], np.eye(n, dtype=complex), ID, 0, 0)
    out = {"witness": path, "n": n, "L": L, "order": order}
    R1, R2, c = rel_words()
    out["tr_c"] = float(np.real(np.trace(Ua @ Ub @ Ua.conj().T @ Ub.conj().T))) / n
    for k in range(1, L + 1):
        fp = [r[3] for r in recs if r[0] == k and r[1] == "Fprime"]
        tv = [r[3] for r in recs if r[0] == k and r[1] == "trivial"]
        row = {}
        if fp:
            row["Fprime"] = {"count": len(fp), "mean": round(float(np.mean(fp)), 4), "min": round(min(fp), 4),
                             "max": round(max(fp), 4), "std": round(float(np.std(fp)), 4)}
        if tv:
            row["trivial"] = {"count": len(tv), "mean": round(float(np.mean(tv)), 4), "min": round(min(tv), 4)}
        out[f"len{k}"] = row
    print(json.dumps(out))


if __name__ == "__main__":
    main()
