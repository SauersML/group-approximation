#!/usr/bin/env python3
"""Certificates for the fold-bootstrap characterization (left-action convention).

Pair: L = F_2 = <a,b>, K = <a, k> with k = b a b^-2.  For a free action of L
and A a subset of X, let R' = R_K v b|_A and D = {w : w R' b w}.

(1) EXACTNESS TEST.  On the free action of F_2 on itself (the Cayley tree),
    compute D by union-find on R' (generators a, k everywhere, b on A),
    truncated to a ball, and compare it with the 2-of-3 closure cl(A) for
    the triples T_w = {w, a w, b w}.  The claim is D = cl(A).  Finite
    quotients are NOT valid tests: there L does not act freely, K may
    surject, and D is strictly larger than cl(A).

(2) SEED CERTIFICATE.  On Q = <1+X, 1+Y> in F_p<X,Y>/(deg > c), with
    alpha = 1+X, beta = 1+Y, find a small S with cl(S) = Q.  Verify it both by
    the closure and by union-find on R' (single class).  Save S as Magnus
    coefficient vectors so the certificate does not depend on BFS order.

Usage: certify.py [p c trials out.json]
"""
import json
import os
import random
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bootstrap_seed import (Bootstrap, inverse_table, psl_mul, psl_random,
                            enumerate_group, subgroup_order, perm_mul, perm_random)
from pgroup_seed import words
from prune_scale import greedy_seeds, prune


class UF:
    def __init__(self, n):
        self.p = list(range(n))

    def find(self, x):
        p = self.p
        while p[x] != x:
            p[x] = p[p[x]]
            x = p[x]
        return x

    def union(self, x, y):
        x, y = self.find(x), self.find(y)
        if x != y:
            self.p[x] = y


def compose(*tabs):
    """Left-multiplication table of g1 g2 ... gr from tables of g1..gr:
    (g1 g2 ... gr) w = g1(g2(...(gr w)))."""
    n = len(tabs[0])
    out = list(range(n))
    for t in reversed(tabs):
        out = [t[x] for x in out]
    return out


def relation_D(La, Lb, A):
    n = len(La)
    Lbi = inverse_table(Lb)
    Lk = compose(Lb, La, Lbi, Lbi)
    uf = UF(n)
    for w in range(n):
        uf.union(w, La[w])
        uf.union(w, Lk[w])
    for w in A:
        uf.union(w, Lb[w])
    D = [w for w in range(n) if uf.find(w) == uf.find(Lb[w])]
    classes = len({uf.find(w) for w in range(n)})
    return set(D), classes


def closure(La, Lb, A):
    bs = Bootstrap(inverse_table(La), inverse_table(Lb))  # tri[w] = (w, a w, b w)
    for w in range(bs.n):
        assert bs.tri[w] == (w, La[w], Lb[w])
    bs.reset()
    for w in A:
        bs.add(w)
    return {w for w in range(bs.n) if bs.inS[w]}, bs


def left_tables(ident, gens, mul):
    """Left multiplication tables: enumerate by right mult, then build L_g."""
    elts, idx, _ = enumerate_group(ident, gens, mul)
    return elts, [[idx[mul(g, x)] for x in elts] for g in gens]


INV = {'a': 'A', 'A': 'a', 'b': 'B', 'B': 'b'}


def lmul(g, w):
    """Left multiply reduced word w (string over aAbB) by the word g."""
    for x in reversed(g):
        if w and w[0] == INV[x]:
            w = w[1:]
        else:
            w = x + w
    return w


def ball(N):
    out, layer = [""], [""]
    for _ in range(N):
        nxt = []
        for w in layer:
            for x in "aAbB":
                if not w or w[0] != INV[x]:
                    nxt.append(x + w)
        out += nxt
        layer = nxt
    return out


def f2_closure(A):
    S = set(A)
    changed = True
    while changed:
        changed = False
        for s in list(S):
            for w in (s, lmul("A", s), lmul("B", s)):
                T = (w, lmul("a", w), lmul("b", w))
                inn = [t in S for t in T]
                if sum(inn) == 2:
                    S.add(T[inn.index(False)])
                    changed = True
    return S


def exactness_tests(rng, reps=30, N=9, r=2):
    """Free action: F_2 acting on itself (the Cayley tree).  Relation R' is
    truncated to the ball B_N (edges with both ends in B_N), giving
    D_N = {w in B_{N-1} : w ~_N b w}, which increases to D as N grows.
    Test D_N == cl(A) for random finite A inside B_r."""
    B = ball(N)
    pos = {w: i for i, w in enumerate(B)}
    small = [w for w in B if len(w) <= r]
    total = 0
    for _ in range(reps):
        A = [w for w in small if rng.random() < rng.choice((0.2, 0.35, 0.5))]
        uf = UF(len(B))
        for w in B:
            for g in ("a", "baBB"):
                v = lmul(g, w)
                if v in pos:
                    uf.union(pos[w], pos[v])
        for w in A:
            uf.union(pos[w], pos[lmul("b", w)])
        D = {w for w in B if len(w) < N and uf.find(pos[w]) == uf.find(pos[lmul("b", w)])}
        C = f2_closure(A)
        assert D == C, (A, sorted(D - C), sorted(C - D))
        total += 1
    print(dict(test="exactness_on_F2_tree", ball_radius=N, seed_radius=r, reps=reps,
               D_equals_closure=True))
    return total


def magnus_left(p, c):
    lst, idx = words(c)
    Dm = len(lst)
    pre = [[None] * Dm, [None] * Dm]
    for i, w in enumerate(lst):
        if len(w) < c:
            pre[0][i] = idx[(0,) + w]
            pre[1][i] = idx[(1,) + w]

    def lmul(P, s):
        Q = list(P)
        t = pre[s]
        for i in range(Dm):
            j = t[i]
            if j is not None and P[i]:
                Q[j] = (Q[j] + P[i]) % p
        return tuple(Q)

    one = tuple([1] + [0] * (Dm - 1))
    elts, pos = [one], {one: 0}
    i = 0
    while i < len(elts):
        for s in (0, 1):
            Q = lmul(elts[i], s)
            if Q not in pos:
                pos[Q] = len(elts)
                elts.append(Q)
        i += 1
    La = [pos[lmul(P, 0)] for P in elts]
    Lb = [pos[lmul(P, 1)] for P in elts]
    return elts, La, Lb, lst


def main():
    rng = random.Random(20260918)
    ntests = exactness_tests(rng)
    p, c, trials = 2, 4, 6
    out = None
    if len(sys.argv) > 4:
        p, c, trials, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    elts, La, Lb, lst = magnus_left(p, c)
    n = len(elts)
    bs = Bootstrap(inverse_table(La), inverse_table(Lb))
    best = None
    for _ in range(trials):
        s = prune(bs, greedy_seeds(bs, rng), rng)
        if best is None or len(s) < len(best):
            best = s
    C, _ = closure(La, Lb, best)
    D, classes = relation_D(La, Lb, best)
    assert len(C) == n and len(D) == n and classes == 1
    row = dict(test="seed_certificate", p=p, c=c, n=n, seeds=len(best),
               ratio=round(len(best) / n, 6), closure_full=True, union_find_classes=classes,
               exactness_tests=ntests)
    print(row, flush=True)
    if out:
        with open(out, "w") as f:
            json.dump(dict(p=p, c=c, n=n, basis_words=["".join("XY"[t] for t in w) for w in lst],
                           seeds=[list(elts[v]) for v in best]), f)


if __name__ == "__main__":
    main()
