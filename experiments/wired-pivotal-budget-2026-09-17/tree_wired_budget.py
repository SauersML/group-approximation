#!/usr/bin/env python3
"""Free versus wired random-walk pivotal counts on the d-regular tree T_d.

Calibration for fpbs-wired-pivotal-budget-fails-universally.

Setting (notation of fpbs-pivotal-budget-universal): X_n is simple random walk
from the root o, independent of Bernoulli(q) bond percolation; R >= n.

  free   E_(n,R)   = {o <-> X_n inside the induced ball B_R}
  wired  E^w_(n,R) = E_(n,R) union {o <-> S_R and X_n <-> S_R inside B_R}
                   (connection in the ball with the sphere S_R identified)

By Russo's formula in the finite edge set,
  E_q[N | E] = q d/dq log P_q(E)
for both events, where N counts open pivotal edges.  This script computes
both probabilities exactly (as closed forms on the tree, with exact first
derivatives propagated alongside the values) and prints the maximum over a
grid of q in [p_c, p0] of the conditional pivotal counts, divided by n.

Tree formulas.  u_m(q) = P(a vertex reaches m further levels through its d-1
outward subtrees):  u_0 = 1,  u_m = 1-(1-q u_(m-1))^(d-1).
For |x| = k along the geodesic v_0=o,...,v_k=x, the side branches of v_i reach
S_R with probability w_i = 1-(1-q u_(R-i-1))^(s_i), s_0 = s_k = d-1, else d-2
(w_i = 1 if i = R).  With first closed geodesic edge a and last closed b,
  P^w(k) = q^k + sum_(1<=a<=b<=k) q^(a-1)(1-q)[a<b](1-q) q^(k-b) A_(a-1) B_b,
  A_j = 1 - prod_(i<=j)(1-w_i),  B_b = 1 - prod_(i>=b)(1-w_i).
Free: P(k) = q^k, and the free count is the q^k-tilted mean of |X_n| (<= n).

Run:  python3 tree_wired_budget.py            (d=3, n=10,20,40,60, R=1e2..1e5)
      python3 tree_wired_budget.py 3 100,140 1000,100000
"""
import math
import sys


class D:
    """Forward-mode dual number (value, derivative in q)."""
    __slots__ = ("v", "d")

    def __init__(self, v, d=0.0):
        self.v = v
        self.d = d

    def __add__(self, o):
        o = o if isinstance(o, D) else D(o)
        return D(self.v + o.v, self.d + o.d)
    __radd__ = __add__

    def __sub__(self, o):
        o = o if isinstance(o, D) else D(o)
        return D(self.v - o.v, self.d - o.d)

    def __rsub__(self, o):
        return D(o) - self

    def __mul__(self, o):
        o = o if isinstance(o, D) else D(o)
        return D(self.v * o.v, self.d * o.v + self.v * o.d)
    __rmul__ = __mul__

    def pw(self, k):
        if k == 0:
            return D(1.0)
        return D(self.v ** k, k * self.v ** (k - 1) * self.d)


def radial_law(d, n):
    """Law of |X_n| for simple random walk on T_d."""
    law = {0: 1.0}
    for _ in range(n):
        new = {}
        for k, pr in law.items():
            if k == 0:
                new[1] = new.get(1, 0.0) + pr
            else:
                new[k + 1] = new.get(k + 1, 0.0) + pr * (d - 1) / d
                new[k - 1] = new.get(k - 1, 0.0) + pr / d
        law = new
    return law


def u_tails(d, q, Rs, window):
    """Return {R: [u_(R-1-i) for i in 0..window]} as duals, for each R in Rs."""
    Rmax = max(Rs)
    need = {}
    for R in Rs:
        for i in range(window + 1):
            m = R - 1 - i
            if m >= 0:
                need.setdefault(m, []).append((R, i))
    out = {R: [None] * (window + 1) for R in Rs}
    u, du = 1.0, 0.0
    if 0 in need:
        for R, i in need[0]:
            out[R][i] = D(u, du)
    for m in range(1, Rmax):
        base = 1.0 - q * u
        dbase = -(u + q * du)
        p = base ** (d - 2)
        u, du = 1.0 - p * base, -(d - 1) * p * dbase
        if m in need:
            for R, i in need[m]:
                out[R][i] = D(u, du)
    return out


def wired_prob(d, q, k, R, tails):
    Q = D(q, 1.0)
    if k == 0:
        return D(1.0)
    w = []
    for i in range(k + 1):
        if i == R:
            w.append(D(1.0))
            continue
        s = d - 1 if i in (0, k) else d - 2
        w.append(1 - (1 - Q * tails[i]).pw(s))
    A = []
    prod = D(1.0)
    for i in range(k + 1):
        prod = prod * (1 - w[i])
        A.append(1 - prod)
    B = [None] * (k + 1)
    prod = D(1.0)
    for i in range(k, -1, -1):
        prod = prod * (1 - w[i])
        B[i] = 1 - prod
    total = Q.pw(k)
    one_minus = 1 - Q
    for a in range(1, k + 1):
        left = Q.pw(a - 1) * one_minus * A[a - 1]
        for b in range(a, k + 1):
            f = left * Q.pw(k - b) * B[b]
            if b > a:
                f = f * one_minus
            total = total + f
    return total


def counts(d, q, n, Rs, law):
    tails = u_tails(d, q, Rs, n + 1)
    Q = D(q, 1.0)
    free = D(0.0)
    for k, pr in law.items():
        free = free + pr * Q.pw(k)
    res = {}
    for R in Rs:
        wired = D(0.0)
        for k, pr in law.items():
            wired = wired + pr * wired_prob(d, q, k, R, tails[R])
        res[R] = (q * wired.d / wired.v, wired.v)
    return q * free.d / free.v, free.v, res


def main():
    d = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    pc = 1.0 / (d - 1)
    p0 = pc + 0.1
    rho = 2 * math.sqrt(d - 1) / d
    ns = [10, 20, 40, 60]
    Rs = [100, 1000, 10000, 100000]
    if len(sys.argv) > 2:
        ns = [int(t) for t in sys.argv[2].split(",")]
    if len(sys.argv) > 3:
        Rs = [int(t) for t in sys.argv[3].split(",")]
    grid = [pc] + [pc + 10 ** (-e / 8.0) * 0.1 for e in range(48, -1, -1)]
    print(f"T_{d}: p_c={pc:.4f}  p0={p0:.4f}  rho={rho:.6f}")
    print("columns: n | max_q free/n | max_q wired/n for R in", Rs,
          "| argmax q-p_c for largest R")
    for n in ns:
        law = radial_law(d, n)
        best_free = 0.0
        best_w = {R: (0.0, None) for R in Rs}
        a_pc_free = None
        a_pc_w = None
        for q in grid:
            f, fv, res = counts(d, q, n, Rs, law)
            if q == pc:
                a_pc_free = fv
                a_pc_w = res[Rs[-1]][1]
            best_free = max(best_free, f)
            for R in Rs:
                if res[R][0] > best_w[R][0]:
                    best_w[R] = (res[R][0], q - pc)
        row = " ".join(f"{best_w[R][0] / n:10.3f}" for R in Rs)
        print(f"n={n:3d} | {best_free / n:6.3f} | {row} | {best_w[Rs[-1]][1]:.2e}"
              f" | a_n(pc)={a_pc_free:.3e} a^w(pc,R={Rs[-1]})={a_pc_w:.3e}")
    sys.stdout.flush()


if __name__ == "__main__":
    main()
