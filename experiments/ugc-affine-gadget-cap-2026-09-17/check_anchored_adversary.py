#!/usr/bin/env python3
"""Exact check of the anchored threshold adversary for 3Lin(G) -> 2-CSP gadgets.

Node: three-lin-gadgets-stay-below-padding-line.

Setting (see the node). G = Z_q, H = {(u,v,w) in G^3 : u+v+w = 0}, |H| = q^2.
Canonical variables are functions y : H -> G. The primaries are the three
coordinate projections p_0, p_1, p_2. Gamma is a permutation group of G. The
output constraints are z = gamma(y) with gamma in Gamma. An anchor is a pair
(p, gamma), whose function is gamma o p. rho is the largest fraction of H on
which two distinct anchors coincide.

The adversary:
  * draw I uniformly from the three 2-subsets of {0,1,2} and xi uniform on G^3;
  * h* is the unique point of H with h*_I = xi_I, b is the primary not in I,
    and D is the event xi_b != h*_b;
  * draw t uniform on [alpha0, 1], where alpha0 N = ceil(N (1 + rho) / 2),
    N = |H|;
  * y is near if its largest anchor agreement m(y) is > t N. Near y whose
    (unique) anchor is (b, gamma), under D, gets gamma(xi_b). Every other y
    gets the dictator value y(h*).

For every length-one edge (y, y') (y' = y changed at one point) the script
computes N * Pr[A(y) != A(y')] exactly, as a Fraction. That uses the finite
(I, xi) average and the exact length of the t-set where the two values differ.

It checks the following, exhaustively for q = 2, 3 and on samples for q = 4, 5:
  (a) anchors of functions with m > alpha0 N are unique, and neighbours of such
      a function that are also above alpha0 N share its anchor;
  (b) the adversary is Gamma-equivariant and random on the primaries
      (A(gamma o p) = gamma(xi_p));
  (c) h* is uniform, and D is independent of h*;
  (d) max over edges of N Pr[cut] <= 1 + delta (2(1 - 1/N)/(1 - alpha0) ... )
      as in the node, with delta = (1 - 1/q)/3. The bound is printed next to
      the observed maximum.
Edges with no endpoint above alpha0 N have N Pr[cut] = N Pr[h* = h0] = 1 by (c).
"""
import itertools
import random
import sys
from fractions import Fraction as Fr
from math import ceil


def perm_group(q, kind):
    if kind == "shift":
        return [tuple((g + c) % q for g in range(q)) for c in range(q)]
    if kind == "affine":  # q prime
        return [tuple((a * g + c) % q for g in range(q))
                for a in range(1, q) for c in range(q)]
    if kind == "sym":
        return [tuple(p) for p in itertools.permutations(range(q))]
    raise ValueError(kind)


class Setup:
    def __init__(self, q, kind):
        self.q = q
        self.H = [(u, v, (-u - v) % q) for u in range(q) for v in range(q)]
        self.N = len(self.H)
        self.idx = {h: i for i, h in enumerate(self.H)}
        self.Gamma = perm_group(q, kind)
        self.anchors = []  # (p, gamma, function tuple)
        for p in range(3):
            for gm in self.Gamma:
                self.anchors.append((p, gm, tuple(gm[h[p]] for h in self.H)))
        rho = 0
        for (p1, g1, f1), (p2, g2, f2) in itertools.combinations(self.anchors, 2):
            rho = max(rho, sum(a == b for a, b in zip(f1, f2)))
        self.rho_count = rho  # rho * N
        # alpha0 N = ceil(N(1+rho)/2) = ceil((N + rho N)/2)
        self.a0N = ceil(Fr(self.N + rho, 2))
        self.alpha0 = Fr(self.a0N, self.N)
        pairs = [(0, 1), (0, 2), (1, 2)]
        self.cases = []  # (b, D, xi_b, hstar index), each of weight 1/(3 q^3)
        for I in pairs:
            b = ({0, 1, 2} - set(I)).pop()
            for xi in itertools.product(range(q), repeat=3):
                hs = [h for h in self.H if h[I[0]] == xi[I[0]] and h[I[1]] == xi[I[1]]]
                assert len(hs) == 1
                hstar = hs[0]
                self.cases.append((b, xi[b] != hstar[b], xi, self.idx[hstar]))
        self.W = Fr(1, len(self.cases))

    def anchor(self, y):
        best, arg, ties = -1, None, 0
        for k, (p, gm, f) in enumerate(self.anchors):
            a = sum(u == v for u, v in zip(y, f))
            if a > best:
                best, arg, ties = a, k, 1
            elif a == best:
                ties += 1
        return best, arg, ties

    def values(self, y, case):
        """Return (m, near_value or None, far_value): y is near iff m > t N."""
        b, D, xi, hs = case
        m, k, ties = self.anchor(y)
        far = y[hs]
        if m > self.a0N:
            assert ties == 1, ("anchor not unique", y)
            p, gm, _ = self.anchors[k]
            if D and p == b:
                return m, gm[xi[b]], far
        return m, None, far

    def cut_measure(self, vx, vy):
        """Length of {t in [alpha0,1] : A(x) != A(y)}, divided by (1-alpha0)."""
        lo, hi = self.alpha0, Fr(1)
        pts = {lo, hi}
        for (m, nv, fv) in (vx, vy):
            if nv is not None:
                pts.add(min(max(Fr(m, self.N), lo), hi))
        pts = sorted(pts)
        tot = Fr(0)
        for s, e in zip(pts, pts[1:]):
            mid = (s + e) / 2
            val = []
            for (m, nv, fv) in (vx, vy):
                val.append(nv if (nv is not None and m > mid * self.N) else fv)
            if val[0] != val[1]:
                tot += e - s
        return tot / (hi - lo)

    def edge_cost(self, x, y):
        tot = Fr(0)
        for case in self.cases:
            tot += self.cut_measure(self.values(x, case), self.values(y, case))
        return tot * self.W * self.N

    def bound(self):
        q, N = self.q, self.N
        delta = Fr(q - 1, 3 * q)
        return 1 + delta * (1 - Fr(1, N)) / (1 - self.alpha0) - delta / (q - 1)

    def check_decoder(self):
        cnt, dcnt = {}, {}
        for (b, D, xi, hs) in self.cases:
            cnt[hs] = cnt.get(hs, 0) + 1
            dcnt[hs] = dcnt.get(hs, 0) + (1 if D else 0)
        assert len(cnt) == self.N and len(set(cnt.values())) == 1, "h* not uniform"
        assert len(set(dcnt.values())) == 1, "D not independent of h*"
        # per-primary: Pr[D and b = p | h*] constant
        for p in range(3):
            per = {}
            for (b, D, xi, hs) in self.cases:
                per[hs] = per.get(hs, 0) + (1 if (D and b == p) else 0)
            assert len(set(per.values())) == 1
            assert Fr(sum(per.values()), len(self.cases)) == Fr(self.q - 1, 3 * self.q)

    def check_random_on_primaries(self, ts):
        for case in self.cases:
            b, D, xi, hs = case
            for (p, gm, f) in self.anchors:
                m, nv, fv = self.values(f, case)
                for t in ts:
                    v = nv if (nv is not None and m > t * self.N) else fv
                    assert v == gm[xi[p]], "not random on primaries"

    def check_equivariance(self, y, ts):
        for gm in self.Gamma:
            gy = tuple(gm[v] for v in y)
            for case in self.cases:
                m1, n1, f1 = self.values(y, case)
                m2, n2, f2 = self.values(gy, case)
                for t in ts:
                    v1 = n1 if (n1 is not None and m1 > t * self.N) else f1
                    v2 = n2 if (n2 is not None and m2 > t * self.N) else f2
                    assert v2 == gm[v1], "not equivariant"


def near_functions(S, extra):
    """All y with agreement >= a0N+1-extra with some anchor (as tuples)."""
    need = S.a0N + 1 - extra
    out = set()
    for (p, gm, f) in S.anchors:
        for r in range(S.N - need + 1):
            for pos in itertools.combinations(range(S.N), r):
                for vals in itertools.product(range(S.q), repeat=r):
                    if any(vals[i] == f[pos[i]] for i in range(r)):
                        continue
                    y = list(f)
                    for i, j in enumerate(pos):
                        y[j] = vals[i]
                    out.add(tuple(y))
    return out


def run(q, kind, exhaustive, samples=0, seed=1):
    S = Setup(q, kind)
    S.check_decoder()
    ts = [S.alpha0 + (1 - S.alpha0) * Fr(i, 17) for i in range(17)]
    S.check_random_on_primaries(ts)
    rng = random.Random(seed)
    worst = Fr(0)
    nedges = 0
    if exhaustive:
        E = near_functions(S, 0)
        for x in E:
            S.anchor(x)
            for j in range(S.N):
                for v in range(q):
                    if v == x[j]:
                        continue
                    y = list(x); y[j] = v; y = tuple(y)
                    # (a): neighbour above threshold shares the anchor
                    mx, kx, _ = S.anchor(x); my, ky, ty = S.anchor(y)
                    if my > S.a0N:
                        assert ty == 1 and S.anchors[ky][0] == S.anchors[kx][0] \
                            and S.anchors[ky][1] == S.anchors[kx][1]
                    c = S.edge_cost(x, y)
                    nedges += 1
                    worst = max(worst, c)
        for x in rng.sample(sorted(E), min(40, len(E))):
            S.check_equivariance(x, ts)
    else:
        for _ in range(samples):
            p, gm, f = rng.choice(S.anchors)
            r = rng.randint(0, S.N - S.a0N - 1)
            x = list(f)
            for j in rng.sample(range(S.N), r):
                x[j] = rng.choice([v for v in range(q) if v != f[j]])
            x = tuple(x)
            j = rng.randrange(S.N)
            y = list(x); y[j] = rng.choice([v for v in range(q) if v != x[j]]); y = tuple(y)
            c = S.edge_cost(x, y)
            nedges += 1
            worst = max(worst, c)
            if _ < 5:
                S.check_equivariance(x, ts)
    b = S.bound()
    assert worst <= b, (worst, b)
    print(f"q={q} Gamma={kind} |Gamma|={len(S.Gamma)} N={S.N} rho*N={S.rho_count} "
          f"alpha0={S.alpha0} edges={'all' if exhaustive else 'sampled'}:{nedges} "
          f"max N*Pr[cut]={worst} ~{float(worst):.4f} bound={b} ~{float(b):.4f}")
    return worst, b


if __name__ == "__main__":
    full = "--quick" not in sys.argv
    run(2, "shift", True)
    run(3, "shift", True)
    run(3, "sym", True)
    run(4, "shift", False, samples=400 if full else 60)
    run(5, "affine", False, samples=300 if full else 40)
    run(4, "sym", False, samples=300 if full else 40)
    print("all checks passed")
