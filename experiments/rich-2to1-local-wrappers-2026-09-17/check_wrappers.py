#!/usr/bin/env python3
"""Brute-force checks for local-richness-wrappers-collapse-to-affine-unique-games.

Part 1 (dichotomy).  Random affine sources A = F_2^n with affine surjections
r_u : A -> F_2^l, u in S.  Agreement classes are computed by union-find on the
points of A (no linear algebra).  Every locally complete 2-to-1 labeling is
found by enumerating all pairings of Sigma_{u0}.  Each survivor must be
  (A) all edges translation pairings x <-> x + b_u with {0,b_u} = dr_u(B), or
  (D) all kernels equal and h_{u'} = h_u o phi_{u'u}.
Survivors exist iff |B| <= 2 |ker r_u|.

Part 2 (mass).  Exact enumeration of perfect pairings of F_2^l for l = 2, 3:
translation pairings have uniform probability (2k-1)/(2k-1)!! <= alpha.

Part 3 (value floor).  Random small wrappers mixing merge-type and
translation-type right vertices: check val(W) >= w(D) val(U_W) over all left
labelings, and the certificate completeness bound.
"""
import itertools
import random
from fractions import Fraction

random.seed(20260917)


def apply_lin(rows, x):
    y = 0
    for i, row in enumerate(rows):
        if bin(row & x).count("1") % 2:
            y |= 1 << i
    return y


def rank(vecs):
    basis = []
    for v in vecs:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis)


def span(vecs):
    s = {0}
    for v in vecs:
        s |= {x ^ v for x in s}
    return s


def random_surjection(n, l):
    while True:
        rows = [random.randrange(1 << n) for _ in range(l)]
        if rank(rows) == l:
            return rows, random.randrange(1 << l)


def pairings(points):
    points = list(points)
    if not points:
        yield []
        return
    a = points[0]
    for i in range(1, len(points)):
        b = points[i]
        rest = points[1:i] + points[i + 1:]
        for p in pairings(rest):
            yield [(a, b)] + p


class UF:
    def __init__(self, n):
        self.p = list(range(n))

    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, a, b):
        self.p[self.find(a)] = self.find(b)


def part1(trials=400):
    stats = {"A": 0, "D": 0, "sources": 0, "with_survivor": 0}
    for _ in range(trials):
        n = random.choice([2, 3, 4, 5])
        l = random.choice([2, 3])
        if l > n:
            continue
        s = random.choice([1, 2, 3])
        maps = [random_surjection(n, l) for _ in range(s)]
        N = 1 << n
        r = [[apply_lin(rows, f) ^ off for f in range(N)] for rows, off in maps]
        uf = UF(N)
        for u in range(s):
            first = {}
            for f in range(N):
                x = r[u][f]
                if x in first:
                    uf.union(f, first[x])
                else:
                    first[x] = f
        classes = {}
        for f in range(N):
            classes.setdefault(uf.find(f), set()).add(f)
        kers = [frozenset(f for f in range(N) if apply_lin(maps[u][0], f) == 0)
                for u in range(s)]
        B = span([v for K in kers for v in K])
        for C in classes.values():  # union-find classes are cosets of B
            c0 = min(C)
            assert C == {c0 ^ b for b in B}
        kersize = N >> l
        stats["sources"] += 1
        survivors = 0
        for P in pairings(range(1 << l)):
            lab = {}
            for i, (a, b) in enumerate(P):
                lab[a] = i
                lab[b] = i
            g = [lab[r[0][f]] for f in range(N)]
            parts = []
            ok = True
            for u in range(s):
                hu = {}
                for f in range(N):
                    x = r[u][f]
                    if hu.setdefault(x, g[f]) != g[f]:
                        ok = False
                        break
                if not ok:
                    break
                blocks = {}
                for x, c in hu.items():
                    blocks.setdefault(c, []).append(x)
                if any(len(v) != 2 for v in blocks.values()):
                    ok = False
                    break
                parts.append(hu)
            if not ok:
                continue
            survivors += 1
            if all(K == kers[0] for K in kers) and len(B) == kersize:
                stats["D"] += 1
                for u in range(s):  # r_u = phi o r_0 and h_0 = h_u o phi
                    phi = {}
                    for f in range(N):
                        assert phi.setdefault(r[0][f], r[u][f]) == r[u][f]
                    assert sorted(phi.values()) == list(range(1 << l))
                    for x in range(1 << l):
                        assert parts[0][x] == parts[u][phi[x]]
            else:
                assert len(B) == 2 * kersize
                assert all(K != B for K in kers)
                stats["A"] += 1
                for u in range(s):
                    img = {apply_lin(maps[u][0], b) for b in B}
                    assert len(img) == 2
                    bu = max(img)
                    for x in range(1 << l):
                        assert parts[u][x] == parts[u][x ^ bu]
        if survivors:
            stats["with_survivor"] += 1
        assert (survivors > 0) == (len(B) <= 2 * kersize), (n, l, s, len(B))
    return stats


def part2():
    out = []
    for l in (2, 3):
        K2 = 1 << l
        k = K2 // 2
        allp = [frozenset(frozenset(e) for e in P) for P in pairings(range(K2))]
        trans = {frozenset(frozenset((x, x ^ b)) for x in range(K2))
                 for b in range(1, K2)}
        assert len(trans) == K2 - 1 and trans <= set(allp)
        p_unif = Fraction(len(trans), len(allp))
        alpha = Fraction(4 * k - 5, (2 * k - 1) * (2 * k - 3))
        # the two events used in the 2-wise bound, under the uniform law
        x0, x1 = 0, 1
        e_single = Fraction(sum(1 for P in allp if frozenset((x0, x1)) in P), len(allp))
        assert e_single == Fraction(1, K2 - 1)
        for b in range(2, K2):
            ev = sum(1 for P in allp if frozenset((x0, x0 ^ b)) in P
                     and frozenset((x1, x1 ^ b)) in P)
            assert Fraction(ev, len(allp)) == Fraction(1, (K2 - 1) * (K2 - 3))
        assert p_unif <= alpha
        out.append((K2, str(p_unif), str(alpha)))
    return out


def affine_table(n, l, rows_off):
    rows, off = rows_off
    return [apply_lin(rows, f) ^ off for f in range(1 << n)]


def random_merge_vertex(U, l):
    s = random.choice([1, 2, 3])
    S = random.sample(U, s)
    edges = []
    base = random.choice(list(pairings(range(1 << l))))
    lab = {}
    for i, (a, b) in enumerate(base):
        lab[a] = lab[b] = i
    for u in S:
        while True:
            rows, off = random_surjection(l, l)
            t = affine_table(l, l, (rows, off))
            if len(set(t)) == 1 << l:
                break
        h = {t[f]: lab[f] for f in range(1 << l)}  # h_u o r_u = base labeling
        edges.append((u, t, h, random.randint(1, 5)))
    return ("D", l, edges)


def random_translation_vertex(U, l):
    n = l + 1
    while True:
        S = random.sample(U, 2)
        maps = [random_surjection(n, l) for _ in S]
        tabs = [affine_table(n, l, m) for m in maps]
        kers = [frozenset(f for f in range(1 << n) if apply_lin(m[0], f) == 0)
                for m in maps]
        if kers[0] == kers[1]:
            continue
        B = span([v for K in kers for v in K])
        edges = []
        for u, m, t in zip(S, maps, tabs):
            bu = max(apply_lin(m[0], b) for b in B)
            h = {}
            for f in range(1 << n):
                h.setdefault(t[f], min(f ^ b for b in B))
            for x in range(1 << l):
                assert h[x] == h[x ^ bu]
            assert len(set(h.values())) == 1 << (l - 1)
            edges.append((u, t, h, random.randint(1, 5)))
        for f in range(1 << n):  # local completeness check
            vals = {h[t[f]] for (_, t, h, _) in edges}
            assert len(vals) == 1
        return ("A", n, edges)


def part3(instances=60):
    worst = None
    for _ in range(instances):
        l = 2
        U = list(range(4))
        Z = [random_merge_vertex(U, l) for _ in range(random.randint(1, 4))]
        Z += [random_translation_vertex(U, l) for _ in range(random.randint(0, 3))]
        total = sum(w for (_, _, E) in Z for (_, _, _, w) in E)
        wD = Fraction(sum(w for (ty, _, E) in Z if ty == "D" for (_, _, _, w) in E), total)
        for L in itertools.product(range(1 << l), repeat=len(U)):
            valW = Fraction(0)
            for (_, _, E) in Z:
                best = max(sum(w for (u, _, h, w) in E if h[L[u]] == c)
                           for c in set(h[L[u]] for (u, _, h, _) in E))
                valW += Fraction(best, total)
            valU = Fraction(0)
            bad = Fraction(0)
            for (ty, n, E) in Z:
                wz = sum(w for (_, _, _, w) in E)
                certified = any(all(t[f] == L[u] for (u, t, _, _) in E)
                                for f in range(1 << n))
                if not certified:
                    bad += Fraction(wz, total)
                if ty != "D":
                    continue
                acc = Fraction(0)
                for (u0, t0, _, w0) in E:
                    inv0 = {t0[f]: f for f in range(1 << n)}
                    for (u, t, _, w) in E:
                        if L[u] == t[inv0[L[u0]]]:  # L_u = phi_{u0 u}(L_{u0})
                            acc += Fraction(w0 * w, wz * wz)
                valU += Fraction(wz, total) * acc / wD
            assert valW >= wD * valU, (valW, wD, valU)
            assert valW >= 1 - bad
            assert valU >= 1 - bad / wD
            gap = valW - wD * valU
            worst = gap if worst is None else min(worst, gap)
    return str(worst)


if __name__ == "__main__":
    print("part1 dichotomy:", part1())
    print("part2 translation mass (2k, uniform prob, alpha):", part2())
    print("part3 min over labelings of val(W) - w(D) val(U_W):", part3())
    print("ALL CHECKS PASSED")
