"""Test of the lawful-projection statement (S_law).

(S_law, depth j): for every finite L-set Q and every set sigma of k
same-fibre seeds of Gamma_{j+1}(Q) (lawful or overfold, hit or not), the
lawful part  cl(sigma) ∩ ker m  is the fold closure of at most k lawful
seeds.

Lawful pairs fall into lawful blocks (components of the lawful pair graph);
a fold-closed family contains a block as soon as it contains one pair of
it, so the lawful part is cl(B) for the set B of blocks it contains, and
its lawful seed number is the least |tau|, tau ⊆ B, with cl(tau) ⊇ B.

Usage: python3 slaw.py j n trials kmax seed [mode]
mode 0 (default): random mix of overfold and lawful seeds; mode 1: overfold only.
Prints every violation (lawful seed number > k) and a histogram.
"""
import itertools
import os
import random
import sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'fpbs-depth-overfolding-2026-09-17'))
from foldlib import depth_graphs, closure, random_q  # noqa: E402


def setup(PA, PB, j):
    Gj, G, m = depth_graphs(PA, PB, j)
    V = G.V
    byfib = {}
    for v in range(V):
        byfib.setdefault(G.over[v], []).append(v)
    law, over = [], []
    for vs in byfib.values():
        for x, y in itertools.combinations(vs, 2):
            (law if m[x] == m[y] else over).append((x, y))
    # lawful blocks: union-find on lawful pairs along common edges
    idx = {}
    for i, p in enumerate(law):
        idx[p] = i
        idx[(p[1], p[0])] = i
    par = list(range(len(law)))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for (x, y) in law:
        for k, u in G.nb[x].items():
            w = G.nb[y].get(k)
            if w is not None and u != w:
                par[f(idx[(u, w)])] = f(idx[(x, y)])
    blocks = {}
    for p in law:
        blocks.setdefault(f(idx[p]), []).append(p)
    return G, m, law, over, list(blocks.values())


def lawful_part_blocks(cls, blocks):
    inB = []
    for b in blocks:
        hits = [cls[x] == cls[y] for (x, y) in b]
        if any(hits):
            assert all(hits)
            inB.append(b)
    return inB


def law_seed_number(G, B, kmax):
    """least |tau| (tau ⊆ B) with cl(tau) ⊇ B; None if > kmax."""
    if not B:
        return 0
    for r in range(1, min(kmax, len(B)) + 1):
        for tau in itertools.combinations(range(len(B)), r):
            cls = closure(G, [B[i][0] for i in tau])
            if all(cls[b[0][0]] == cls[b[0][1]] for b in B):
                return r
    return None


def main():
    j, n, trials, kmax, sd = map(int, sys.argv[1:6])
    mode = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    rng = random.Random(sd)
    hist = {}
    viol = 0
    for t in range(trials):
        PA, PB = random_q(n, rng)
        G, m, law, over, blocks = setup(PA, PB, j)
        if not over:
            continue
        k = rng.randint(1, kmax)
        nover = k if mode == 1 else rng.randint(1, k)
        sigma = rng.sample(over, min(nover, len(over)))
        sigma += rng.sample(law, min(k - len(sigma), len(law)))
        cls = closure(G, sigma)
        B = lawful_part_blocks(cls, blocks)
        s = law_seed_number(G, B, len(sigma))
        key = (len(sigma), len(B), s)
        hist[key] = hist.get(key, 0) + 1
        if s is None:
            viol += 1
            print('VIOLATION', 'PA', PA, 'PB', PB, 'sigma', sigma,
                  '|B|', len(B), flush=True)
    for key in sorted(hist, key=lambda x: (x[0], x[1], -1 if x[2] is None else x[2])):
        print('k=%d |B|=%d lawseeds=%s : %d' % (key + (hist[key],)))
    print('violations', viol)


if __name__ == '__main__':
    main()
