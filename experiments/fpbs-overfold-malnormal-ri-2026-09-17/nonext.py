"""Targeted top-case hunt with NON-extendable kernels (swarm-0917-w19-w19-fp-follow).

For B <= F(a,b) of rank 2 and onto rho : B -> G, set X = ker rho.
If rho = sigma|_B for an onto sigma : F -> G, then <X, g> >= B is impossible
for every g (Proposition N: sigma<X, g> = <sigma g> is cyclic but contains
sigma(B) = G).  So only non-extendable rho can give a violation of
(RI_B) at k = 1.  This script samples B (malnormal or not), keeps the
non-extendable onto rho (one per kernel), and searches all g with |g| <= LMAX
for <X, g> >= B.

usage: python3 nonext.py MODE GROUP LMAX NB SEED    MODE = mal | nonmal | any
"""
import random
import sys
from itertools import product
from stall import red, fold_graph, member, rank, basis
from maln import malnormal
from ri1 import GROUPS, closure, pmul, pinv, randword
from longg import kernel_words, words_upto, canon


def evalF(w, A, B, n):
    m = {'a': A, 'A': pinv(A), 'b': B, 'B': pinv(B)}
    r = tuple(range(n))
    for x in w:
        r = pmul(r, m[x])
    return r


def main():
    mode, gname, lmax, nb, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    rng = random.Random(seed)
    els, n = GROUPS[gname]
    N = len(els)
    allg = [g for g in words_upto(lmax)]
    tot = dict(B=0, kernels=0, nonext_kernels=0, hits=0)
    for _ in range(nb):
        while True:
            Bg = [randword(rng, 2, 6) for _ in range(2)]
            BG = fold_graph(Bg)
            if rank(BG) != 2:
                continue
            mal = malnormal(BG)
            if mode == 'mal' and not mal:
                continue
            if mode == 'nonmal' and mal:
                continue
            break
        tot['B'] += 1
        ext = set()
        for A in els:
            for Bx in els:
                if len(closure([A, Bx], n)) == N:
                    ext.add(tuple(evalF(w, A, Bx, n) for w in Bg))
        seen = set()
        for imgs in product(els, repeat=2):
            if len(closure(list(imgs), n)) != N:
                continue
            XG = fold_graph(kernel_words(Bg, imgs, n))
            key = canon(XG)
            if key in seen:
                continue
            seen.add(key)
            tot['kernels'] += 1
            if imgs in ext:
                continue
            tot['nonext_kernels'] += 1
            Xb = basis(XG)[1]
            for g in allg:
                if member(BG, g):
                    continue
                JG = fold_graph(Xb + [g])
                if all(member(JG, w) for w in Bg):
                    tot['hits'] += 1
                    print('HIT B=%s mal=%s rho=%s g=%s rkJ=%d' % (Bg, mal, imgs, g, rank(JG)), flush=True)
                    break
    print('STATS', mode, gname, lmax, nb, seed, tot, flush=True)


if __name__ == '__main__':
    main()
