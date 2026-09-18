#!/usr/bin/env python3
"""Local-limit (one-giant) expansion ratio for the monomial sets S(n->k) of Thompson's F.

S(n->k) = all ways to add d = n-k carets to n roots leaving k roots (S_(3,5) = S(5->3),
S_(2,4) = S(4->2), X_m = S(m+2 -> m+1)).  By the five-root reduction (tuples_model.py), the doubling
ratio of S_(m+1,m+d+1) is inf |S A| / |A| over finite A subset T^n, A mapped into T^k.

Regime.  Uniform families A_N subset T^n_N (N carets) whose membership depends on bounded top
structure converge, as N -> oo, to the critical Boltzmann local limit: one tuple entry is a giant
(Kesten tree: infinite spine, independent Boltzmann siblings, weight 4^-carets), the other n-1
entries are Boltzmann trees.  Then |S A_N| / |A_N| -> 4^d mu_k(S A) / mu_n(A), where mu_j is the
local-limit measure on j-tuples with one giant.  For A = everything this is 2^d k / n.

This script fixes a truncation depth h, takes as universe all depth-h profiles of n-tuples with one
giant, all depth-(h+d) profiles of k-tuples with one giant, joins a profile P to a profile Q when some
split of Q truncates to P, and computes by weighted min cut + Dinkelbach

    R_h = min over nonempty unions A of depth-h profiles of 4^d mu_k(S A) / mu_n(A).

R_h is non-increasing in h (finer sets) and every R_h is an upper bound for the asymptotic ratio of
some explicit uniform family; lim R_h is the best ratio of the one-giant regime.
"""
import itertools, sys
from fractions import Fraction
from math import lcm
from collections import defaultdict, deque

STAR, LEAF, GIANT = '*', 0, 'G'


def small_profiles(H):
    if H == 0:
        return [STAR]
    sub = small_profiles(H - 1)
    return [LEAF] + [(l, r) for l in sub for r in sub]


def giant_profiles(H):
    if H == 0:
        return [GIANT]
    sub_g, sub_s = giant_profiles(H - 1), small_profiles(H - 1)
    return [(g, s) for g in sub_g for s in sub_s] + [(s, g) for g in sub_g for s in sub_s]


def weight(p):
    if p == STAR:
        return Fraction(2)
    if p == LEAF or p == GIANT:
        return Fraction(1)
    return Fraction(1, 4) * weight(p[0]) * weight(p[1])


def has_giant(p):
    if p == GIANT:
        return True
    if p in (STAR, LEAF):
        return False
    return has_giant(p[0]) or has_giant(p[1])


def truncate(p, H):
    if H == 0:
        return GIANT if has_giant(p) else STAR
    if p in (STAR, LEAF, GIANT):
        return p
    return (truncate(p[0], H - 1), truncate(p[1], H - 1))


def forests(n, k):
    """All ways to add n-k carets to n roots leaving k roots, as words (tuples of letters)."""
    out = set()

    def rec(f, word):
        if len(f) == k:
            out.add(tuple(f)); return
        for i in range(len(f) - 1):
            rec(f[:i] + [(f[i], f[i + 1])] + f[i + 2:], word)
    rec([('v', j) for j in range(n)], ())
    return sorted(out, key=str)


def match(shape, tree, env):
    """Match a shape built from variables ('v', j) and carets against a profile; fill env."""
    if isinstance(shape, tuple) and len(shape) == 2 and shape[0] == 'v':
        env[shape[1]] = tree; return True
    if tree in (STAR, LEAF):
        return False  # cannot split a leaf; STAR never occurs at split depth
    if tree == GIANT:
        raise ValueError("giant marker at split depth")
    return match(shape[0], tree[0], env) and match(shape[1], tree[1], env)


def build(n, k, h):
    d = n - k
    shapes = forests(n, k)
    # a-profiles
    sp_h, gp_h = small_profiles(h), giant_profiles(h)
    left = {}
    for pos in range(n):
        for combo in itertools.product(*[(gp_h if j == pos else sp_h) for j in range(n)]):
            left[combo] = Fraction(1)
            for p in combo:
                left[combo] *= weight(p)
    # G-profiles at depth h + d
    H = h + d
    sp_H, gp_H = small_profiles(H), giant_profiles(H)
    classes = defaultdict(Fraction)
    transport = defaultdict(Fraction)
    for pos in range(k):
        for combo in itertools.product(*[(gp_H if j == pos else sp_H) for j in range(k)]):
            w = Fraction(1)
            for p in combo:
                w *= weight(p)
            sig = set()
            for si, shape in enumerate(shapes):
                env = {}
                if all(match(shape[j], combo[j], env) for j in range(k)):
                    a = tuple(truncate(env[j], h) for j in range(n))
                    sig.add(a)
                    transport[(si, a)] += w
            if sig:
                classes[frozenset(sig)] += w
    # mass transport check: for each shape s and a-profile P, sum of mu_k over Q with split_s(Q) = P
    # must be mu_n(P) / 4^d
    for si in range(len(shapes)):
        for a, wa in left.items():
            if transport[(si, a)] != wa / 4 ** d:
                raise SystemExit(f"transport mismatch shape {si} profile {a}: {transport[(si, a)]} vs {wa / 4 ** d}")
    return left, classes, len(shapes)


class Dinic:
    def __init__(self, n):
        self.g = [[] for _ in range(n)]
        self.e = []

    def add(self, a, b, c):
        self.g[a].append(len(self.e)); self.e.append([b, c])
        self.g[b].append(len(self.e)); self.e.append([a, 0])

    def maxflow(self, s, t):
        flow = 0
        n = len(self.g)
        while True:
            level = [-1] * n; level[s] = 0; q = deque([s])
            while q:
                v = q.popleft()
                for id_ in self.g[v]:
                    w, c = self.e[id_]
                    if c > 0 and level[w] < 0:
                        level[w] = level[v] + 1; q.append(w)
            if level[t] < 0:
                return flow, level
            it = [0] * n

            def dfs(v, f):
                if v == t:
                    return f
                while it[v] < len(self.g[v]):
                    id_ = self.g[v][it[v]]
                    w, c = self.e[id_]
                    if c > 0 and level[w] == level[v] + 1:
                        r = dfs(w, min(f, c))
                        if r > 0:
                            self.e[id_][1] -= r; self.e[id_ ^ 1][1] += r
                            return r
                    it[v] += 1
                return 0
            while True:
                f = dfs(s, float('inf'))
                if f == 0:
                    break
                flow += f


def optimize(left, classes, d):
    L = list(left)
    lid = {a: i for i, a in enumerate(L)}
    C = list(classes.items())
    scale = 1
    for w in list(left.values()) + [w for _, w in C]:
        scale = lcm(scale, w.denominator)
    lw = [int(left[a] * scale) for a in L]
    cw = [int(w * 4 ** d * scale) for _, w in C]
    edges = [[lid[a] for a in sig] for sig, _ in C]
    ratio = Fraction(sum(cw), sum(lw))
    lastA = list(range(len(L)))
    while True:
        K, J = ratio.numerator, ratio.denominator
        nl, nc = len(L), len(C)
        s, t = nl + nc, nl + nc + 1
        D = Dinic(nl + nc + 2)
        INF = K * sum(lw) + 1
        for i in range(nl):
            D.add(s, i, K * lw[i])
        for ci, members in enumerate(edges):
            for i in members:
                D.add(i, nl + ci, INF)
            D.add(nl + ci, t, J * cw[ci])
        flow, level = D.maxflow(s, t)
        best = K * sum(lw) - flow
        if best <= 0:
            return ratio, [L[i] for i in lastA]
        A = {i for i in range(nl) if level[i] >= 0}
        SA = {ci for ci, members in enumerate(edges) if any(i in A for i in members)}
        new = Fraction(sum(cw[c] for c in SA), sum(lw[i] for i in A))
        if new >= ratio:
            return ratio, [L[i] for i in lastA]
        ratio = new
        lastA = sorted(A)


if __name__ == "__main__":
    n, k, h = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    left, classes, ns = build(n, k, h)
    d = n - k
    allratio = Fraction(4 ** d) * sum(classes.values()) / sum(left.values())
    print(f"S({n}->{k}) |S|={ns} h={h} a-profiles={len(left)} image classes={len(classes)} "
          f"ratio(all)={allratio}={float(allratio):.6f} (2^d k/n={Fraction(2**d*k, n)})")
    r, A = optimize(left, classes, d)
    print(f"R_h = {r} ~ {float(r):.6f}")
