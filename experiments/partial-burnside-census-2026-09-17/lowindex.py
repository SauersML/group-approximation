#!/usr/bin/env python3
"""Low-index census of partial Burnside groups.

Pi_R(m,N) = F_m / << h^N : 1 <= |h| <= R >>.

Enumerates, up to isomorphism, every transitive permutation representation of
degree <= n of Pi_R(m,N) (Sims' low-index algorithm: standard coset tables,
relator scanning with deductions, canonicity over all base points), then
computes the order of each image group by Schreier--Sims.

A transitive image of degree n is a finite quotient of Pi_R(m,N) whose
generating tuple satisfies h^N = 1 for every word of length <= R. When n is
not a power of a prime dividing N the image is not of exponent N... precisely,
it is not a p-group, so for N = p prime it is not a quotient of R(m,p).

Usage: python3 lowindex.py m N R nmax
"""
import sys
from math import factorial
from itertools import product

sys.setrecursionlimit(10000)


def inv(x):
    return x ^ 1


def reduce_word(w):
    out = []
    for x in w:
        if out and out[-1] == inv(x):
            out.pop()
        else:
            out.append(x)
    return tuple(out)


def cyc_reduce(w):
    w = list(reduce_word(w))
    while len(w) >= 2 and w[0] == inv(w[-1]):
        w = w[1:-1]
    return tuple(w)


def word_inverse(w):
    return tuple(inv(x) for x in reversed(w))


def canon(w):
    cands = []
    for u in (w, word_inverse(w)):
        for i in range(len(u)):
            cands.append(u[i:] + u[:i])
    return min(cands)


def is_proper_power(w):
    L = len(w)
    for d in range(1, L):
        if L % d == 0 and w == w[:d] * (L // d):
            return True
    return False


def relators(m, N, R):
    letters = list(range(2 * m))
    seen = set()
    rels = []
    for L in range(1, R + 1):
        for w in product(letters, repeat=L):
            if reduce_word(w) != w:
                continue
            c = cyc_reduce(w)
            if not c or is_proper_power(c):
                continue
            r = canon(c * N)
            if r not in seen:
                seen.add(r)
                rels.append(r)
    return rels


class LowIndex:
    def __init__(self, m, rels, nmax):
        self.m = m
        self.G = 2 * m
        self.n = nmax
        self.T = [[-1] * nmax for _ in range(self.G)]
        self.rot = [[] for _ in range(self.G)]
        for r in rels:
            for u in (r, word_inverse(r)):
                for i in range(len(u)):
                    v = u[i:] + u[:i]
                    self.rot[v[0]].append(v)
        for g in range(self.G):
            self.rot[g] = list(set(self.rot[g]))
        self.trail = []
        self.found = []

    def define(self, c, g, d, queue):
        T = self.T
        T[g][c] = d
        T[inv(g)][d] = c
        self.trail.append((g, c))
        self.trail.append((inv(g), d))
        queue.append((c, g))
        queue.append((d, inv(g)))

    def undo(self, mark):
        T = self.T
        tr = self.trail
        while len(tr) > mark:
            g, c = tr.pop()
            T[g][c] = -1

    def scan(self, c, w, queue):
        T = self.T
        L = len(w)
        f = c
        i = 0
        while i < L:
            nx = T[w[i]][f]
            if nx < 0:
                break
            f = nx
            i += 1
        if i == L:
            return f == c
        b = c
        j = L - 1
        while j >= i:
            nx = T[inv(w[j])][b]
            if nx < 0:
                break
            b = nx
            j -= 1
        if j < i:
            return b == f
        if j == i:
            self.define(f, w[i], b, queue)
        return True

    def process(self, queue):
        while queue:
            c, g = queue.pop()
            for w in self.rot[g]:
                if not self.scan(c, w, queue):
                    return False
        return True

    def canonical(self, k):
        T = self.T
        G = self.G
        for base in range(1, k):
            perm = {base: 0}
            order = [base]
            i = 0
            decided = False
            while i < len(order) and not decided:
                old = order[i]
                for g in range(G):
                    x = T[g][i]
                    yo = T[g][old]
                    if x < 0 or yo < 0:
                        decided = True
                        break
                    if yo not in perm:
                        perm[yo] = len(order)
                        order.append(yo)
                    y = perm[yo]
                    if y < x:
                        return False
                    if y > x:
                        decided = True
                        break
                i += 1
        return True

    def run(self):
        self.search(1)
        return self.found

    def search(self, k):
        T = self.T
        G = self.G
        c0 = g0 = None
        for c in range(k):
            for g in range(G):
                if T[g][c] < 0:
                    c0, g0 = c, g
                    break
            if c0 is not None:
                break
        if c0 is None:
            self.found.append([row[:k] for row in T])
            return
        ig = inv(g0)
        cands = [d for d in range(k) if T[ig][d] < 0]
        if k < self.n:
            cands.append(k)
        for d in cands:
            mark = len(self.trail)
            q = []
            self.define(c0, g0, d, q)
            k2 = k + 1 if d == k else k
            if self.process(q) and self.canonical(k2):
                self.search(k2)
            self.undo(mark)


def perm_mul(p, q):
    # apply p then q
    return tuple(q[x] for x in p)


def schreier_sims_order(gens, n):
    """Deterministic Schreier--Sims; returns group order."""
    ident = tuple(range(n))
    gens = [g for g in gens if g != ident]
    base = []
    S = []  # strong generators per level

    def orbit_transversal(level):
        b = base[level]
        tr = {b: ident}
        frontier = [b]
        while frontier:
            new = []
            for x in frontier:
                for s in S[level]:
                    y = s[x]
                    if y not in tr:
                        tr[y] = perm_mul(tr[x], s)
                        new.append(y)
            frontier = new
        return tr

    def inverse(p):
        r = [0] * n
        for i, x in enumerate(p):
            r[x] = i
        return tuple(r)

    def sift(h, level, trs):
        while level < len(base):
            b = base[level]
            y = h[b]
            if y not in trs[level]:
                return h, level
            h = perm_mul(h, inverse(trs[level][y]))
            level += 1
        return h, level

    if not gens:
        return 1
    for g in gens:
        for x in range(n):
            if g[x] != x:
                break
        if x not in base and g[x] != x:
            pass
    # initialise base with a moved point
    base.append(next(x for x in range(n) if gens[0][x] != x))
    S.append(list(gens))
    changed = True
    while changed:
        changed = False
        trs = [orbit_transversal(l) for l in range(len(base))]
        for l in range(len(base) - 1, -1, -1):
            for x, u in list(trs[l].items()):
                for s in S[l]:
                    sch = perm_mul(perm_mul(u, s), inverse(trs[l][s[x]]))
                    h, lev = sift(sch, l + 1, trs)
                    if h != ident:
                        if lev == len(base):
                            base.append(next(y for y in range(n) if h[y] != y))
                            S.append([])
                        for j in range(l + 1, lev + 1):
                            if h not in S[j]:
                                S[j].append(h)
                        changed = True
                        break
                if changed:
                    break
            if changed:
                break
    trs = [orbit_transversal(l) for l in range(len(base))]
    order = 1
    for t in trs:
        order *= len(t)
    return order


def factor(x):
    f = {}
    d = 2
    while d * d <= x:
        while x % d == 0:
            f[d] = f.get(d, 0) + 1
            x //= d
        d += 1
    if x > 1:
        f[x] = f.get(x, 0) + 1
    return f


def main():
    m, N, R, nmax = map(int, sys.argv[1:5])
    rels = relators(m, N, R)
    print(f"Pi_{R}({m},{N}): {len(rels)} relator classes, max length "
          f"{max(len(r) for r in rels)}")
    li = LowIndex(m, rels, nmax)
    tables = li.run()
    stats = {}
    for tab in tables:
        k = len(tab[0])
        gens = [tuple(tab[2 * i]) for i in range(m)]
        order = schreier_sims_order(gens, k)
        stats.setdefault(k, []).append(order)
    for k in sorted(stats):
        orders = stats[k]
        desc = sorted(set(orders))
        tags = []
        for o in desc:
            tag = str(factor(o))
            if o == factorial(k) // 2:
                tag += "=|A_%d|" % k
            elif o == factorial(k):
                tag += "=|S_%d|" % k
            tags.append(f"{o} {tag} x{orders.count(o)}")
        print(f"degree {k}: {len(orders)} reps; image orders: " + "; ".join(tags))
    print("done")


if __name__ == "__main__":
    main()
