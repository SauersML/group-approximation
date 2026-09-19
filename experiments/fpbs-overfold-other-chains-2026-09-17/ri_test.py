"""Group-level test of relative inertia (RI) for B <= F(a,b):
    rk((J cap B) : X) <= rk(J : X)   for X <= B,  J = <X, g_1..g_k>.
Necessary condition tested (a lower bound on the left side):
    c_p := dim_{F_p} coker( H_1(X) -> H_1(J cap B) ) <= k,   p = 2, 3.
J cap B is the base component of the Stallings pullback core(J) x core(B).
Prints every violation (a certified failure of (RI) for this B) and a summary.
Usage: python3 ri_test.py trials seed rB LB sX LX k Lg [mal]
  mal=1 keeps only B malnormal in F.
"""
import random
import sys
from chains import W
from foldlib import Graph, gamma
from malnormal import malnormal, rank
from randchains import rword, tostr


def core(words):
    return Graph(gamma([0], [0], [W(s) for s in words]), 1, [0], [0])


def pullback(G, H):
    """Base component of G x H: vertex list, edge list (i, label, j)."""
    idx = {(0, 0): 0}
    verts = [(0, 0)]
    edges = []
    i = 0
    while i < len(verts):
        u, v = verts[i]
        for k, u2 in G.nb[u].items():
            if k[1] != 1:
                continue
            v2 = H.nb[v].get(k)
            if v2 is None:
                continue
            if (u2, v2) not in idx:
                idx[(u2, v2)] = len(verts)
                verts.append((u2, v2))
            edges.append((i, k[0], idx[(u2, v2)]))
        # also inverse edges discover vertices
        for k, u2 in G.nb[u].items():
            if k[1] != -1:
                continue
            v2 = H.nb[v].get(k)
            if v2 is not None and (u2, v2) not in idx:
                idx[(u2, v2)] = len(verts)
                verts.append((u2, v2))
        i += 1
    return idx, verts, edges


def chain_of(word, idx, G, H, eindex):
    """Edge chain of the closed path reading `word` from the base."""
    u = v = 0
    c = {}
    for (l, e) in word:
        u2, v2 = G.nb[u][(l, e)], H.nb[v][(l, e)]
        a, b = idx[(u, v)], idx[(u2, v2)]
        if e == 1:
            k = eindex[(a, l)]
            c[k] = c.get(k, 0) + 1
        else:
            k = eindex[(b, l)]
            c[k] = c.get(k, 0) - 1
        u, v = u2, v2
    assert (u, v) == (0, 0)
    return c


def main():
    trials, seed, rB, LB, sX, LX, k, Lg = [int(x) for x in sys.argv[1:9]]
    mal = len(sys.argv) > 9 and sys.argv[9] == '1'
    from verify_gaps import rank_mod
    rng = random.Random(seed)
    viol, done, hist = 0, 0, {}
    while done < trials:
        us = [tostr(W(tostr(rword(rng, 'ab', LB)))) for _ in range(rB)]
        if '' in us or rank(us) != rB or (mal and not malnormal(us)[0]):
            continue
        xs = []
        for _ in range(sX):
            ww = rword(rng, list(range(rB)), LX)
            s = tostr(W(''.join(us[i] if e == 1 else us[i][::-1].swapcase()
                               for (i, e) in ww)))
            if s:
                xs.append(s)
        gs = [tostr(W(tostr(rword(rng, 'ab', Lg)))) for _ in range(k)]
        gs = [g for g in gs if g]
        if not xs or len(gs) < k:
            continue
        done += 1
        G, H = core(xs + gs), core(us)
        idx, verts, edges = pullback(G, H)
        eindex = {(a, l): i for i, (a, l, b) in enumerate(edges)}
        dimH1 = len(edges) - len(verts) + 1
        chains = [chain_of(W(x), idx, G, H, eindex) for x in xs]
        c = max(dimH1 - rank_mod(chains, p) for p in (2, 3))
        hist[c] = hist.get(c, 0) + 1
        if c > k:
            viol += 1
            print('VIOLATION coker', c, '> k', k, 'B', us, 'X', xs, 'g', gs,
                  'rk(JcapB)', dimH1, flush=True)
    print('trials', trials, 'seed', seed, 'rB', rB, 'LB', LB, 'sX', sX, 'LX', LX,
          'k', k, 'Lg', Lg, 'mal', mal, 'violations', viol,
          'hist(coker)', sorted(hist.items()))


if __name__ == '__main__':
    main()
