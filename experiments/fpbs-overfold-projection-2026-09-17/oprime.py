"""Test of the one-level projection statement (O'-rel) at depth j.

Gamma = Gamma_{j+1}(Q), p_1 : Gamma -> Gamma_1(Q).  A same-fibre pair has
level >= 1 iff its two ends have the same image under p_1.

(O'-rel, depth j): for every seed set P (any levels), the family
  cl(P) ∩ ker p_1
is the fold closure of at most |P| seeds of level >= 1.

With Lemma D (depth shift) this, applied at every depth, gives (O-rel) and
hence (O).  At j = 1 it is (O-rel) itself.

Level >= 1 pairs fall into blocks (components of the level >= 1 pair
graph); a fold-closed family containing one pair of a block contains all
of it.  So cl(P) ∩ ker p_1 = cl(blocks it contains), and its seed number is
the least number of those blocks whose closure contains all of them.

Seed number: greedy upper bound first (certifies (O'-rel) when <= |P|),
then exact search over block subsets of size <= |P| if greedy fails.

Usage: python3 oprime.py j n trials kmax seed mode
mode 0: all seeds of level 0; mode 1: random levels.
"""
import itertools
import os
import random
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
from foldlib import Graph, gamma, A, t, closure, random_q  # noqa: E402


def level_maps(PA, PB, j):
    n = len(PA)
    G = Graph(gamma(PA, PB, [A, t(j + 1)]), n, PA, PB)
    maps = []
    for i in range(j + 1):
        Gi = Graph(gamma(PA, PB, [A, t(i)]), n, PA, PB)
        mi = []
        for v in range(G.V):
            p, w = G.word[v]
            mi.append(Gi.read(p, w))
            assert mi[-1] is not None
        maps.append(mi)
    return G, maps


def blocks_of(G, pairs):
    idx = {}
    for i, p in enumerate(pairs):
        idx[p] = i
        idx[(p[1], p[0])] = i
    par = list(range(len(pairs)))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for (x, y) in pairs:
        for k, u in G.nb[x].items():
            w = G.nb[y].get(k)
            if w is not None and u != w:
                par[f(idx[(u, w)])] = f(idx[(x, y)])
    bl = {}
    for p in pairs:
        bl.setdefault(f(idx[p]), []).append(p)
    return list(bl.values())


def contained(cls, blocks):
    out = []
    for b in blocks:
        h = [cls[x] == cls[y] for (x, y) in b]
        if any(h):
            assert all(h)
            out.append(b)
    return out


def full(cls, B):
    return all(cls[b[0][0]] == cls[b[0][1]] for b in B)


def greedy(G, B):
    chosen = []
    cls = list(range(G.V))
    while not full(cls, B):
        best, bc, bs = None, None, -1
        for b in B:
            if cls[b[0][0]] == cls[b[0][1]]:
                continue
            c2 = closure(G, [x[0] for x in chosen] + [b[0]])
            s = sum(c2[x[0][0]] == c2[x[0][1]] for x in B)
            if s > bs:
                best, bc, bs = b, c2, s
        chosen.append(best)
        cls = bc
    return len(chosen)


def exact(G, B, kmax):
    if not B:
        return 0
    for r in range(1, min(kmax, len(B)) + 1):
        for tau in itertools.combinations(range(len(B)), r):
            if full(closure(G, [B[i][0] for i in tau]), B):
                return r
    return None


def main():
    j, n, trials, kmax, sd, mode = map(int, sys.argv[1:7])
    rng = random.Random(sd)
    hist, viol = {}, 0
    for _ in range(trials):
        PA, PB = random_q(n, rng)
        G, maps = level_maps(PA, PB, j)
        m1 = maps[1] if j >= 1 else maps[0]
        byfib = {}
        for v in range(G.V):
            byfib.setdefault(G.over[v], []).append(v)
        lvl0, hi = [], []
        for vs in byfib.values():
            for x, y in itertools.combinations(vs, 2):
                (hi if m1[x] == m1[y] else lvl0).append((x, y))
        if not lvl0:
            continue
        k = rng.randint(1, kmax)
        if mode == 0:
            P = rng.sample(lvl0, min(k, len(lvl0)))
        else:
            n0 = rng.randint(1, k)
            P = rng.sample(lvl0, min(n0, len(lvl0)))
            P += rng.sample(hi, min(k - len(P), len(hi)))
        cls = closure(G, P)
        B = contained(cls, blocks_of(G, hi))
        g = greedy(G, B) if B else 0
        s = g if g <= len(P) else exact(G, B, len(P))
        n0 = sum(m1[x] != m1[y] for (x, y) in P)
        # slack statistic: is s <= |P| - 1 whenever P has a level-0 seed?
        if s is not None and s > len(P) - 1:
            e = exact(G, B, len(P) - 1)
            if e is None:
                print('NO-SLACK |P|=%d level0=%d' % (len(P), n0), flush=True)
        key = (len(P), n0, s)
        hist[key] = hist.get(key, 0) + 1
        if s is None:
            viol += 1
            print('VIOLATION PA', PA, 'PB', PB, 'P', P, flush=True)
    for key in sorted(hist, key=lambda x: (x[0], x[1], -1 if x[2] is None else x[2])):
        print('|P|=%d level0=%d seeds>=1(upper)=%s : %d' % (key + (hist[key],)))
    print('violations', viol)


if __name__ == '__main__':
    main()
