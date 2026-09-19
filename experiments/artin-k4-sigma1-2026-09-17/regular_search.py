#!/usr/bin/env python3
"""For every hom rho: A_K -> S_n (n <= 5, u1 up to conjugacy), take the
REGULAR representation of the image Q = rho(A_K) and test the Fox matrix of
Z x Q (Lemma 3.4 of arXiv:2501.08692, with psi = (chi, rho)) over:
  char 0 (mod 1000003), char 2 (GF(2^12)), char 3 (GF(3^7)).
Homs are deduplicated by a word-signature of the image (heuristic only
affects which homs are skipped as presumed duplicates).
usage: regular_search.py n
"""
import sys, itertools, random, json
import numpy as np
from twisted_alexander import RELS, CHI
from perm_fox_gfq import fox_blocks, coeff_matrix, evaluate
from gftab import GFT, PrimeField

n = int(sys.argv[1])
perms = np.array(list(itertools.permutations(range(n))), dtype=np.int16)

exec(open('perm_search_enum.py').read())  # defines enumerate_homs(n, perms)
homs = enumerate_homs(n, perms)
print("homs", len(homs), flush=True)


def image_group(gens):
    idn = tuple(range(n))
    elems = [idn]
    idx = {idn: 0}
    k = 0
    while k < len(elems):
        h = elems[k]
        for g in gens:
            e = tuple(int(g[h[x]]) for x in range(n))
            if e not in idx:
                idx[e] = len(elems)
                elems.append(e)
        k += 1
    return elems, idx


def regular(gens):
    elems, idx = image_group(gens)
    out = []
    for g in gens:
        out.append(np.array([idx[tuple(int(g[h[x]]) for x in range(n))] for h in elems]))
    return out, len(elems)


WORDS = [[0], [1], [2], [3], [0, 2], [1, 2], [1, 3], [0, 3], [0, 1, 2], [0, 2, 3],
         [0, 1, 2, 3], [0, 2, 1, 3], [0, 0, 2], [2, 2, 0], [0, 3, 3], [1, 1, 3], [0, 2, 1]]


def signature(regs):
    sig = [len(regs[0])]
    for w in WORDS:
        p = np.arange(len(regs[0]))
        for g in w:
            p = p[regs[g]]
        # cycle type
        seen = np.zeros(len(p), bool)
        ct = []
        for i in range(len(p)):
            if not seen[i]:
                c = 0
                j = i
                while not seen[j]:
                    seen[j] = True
                    j = p[j]
                    c += 1
                ct.append(c)
        sig.append(tuple(sorted(ct)))
    return tuple(sig)


FIELDS = [("char0", PrimeField()), ("char2", GFT(2, 12)), ("char3", GFT(3, 7))]
rng = random.Random(11)
sigs = {}
for h in homs:
    gens = [perms[i] for i in h]
    regs, order = regular(gens)
    if order == 1:
        continue
    s = signature(regs)
    if s in sigs:
        continue
    C, d = coeff_matrix(regs)
    res = {}
    for name, F in FIELDS:
        t0 = rng.randrange(2, F.q)
        res[name] = F.rank(evaluate(F, C, d, t0))
    sigs[s] = (h, order, res)
    flag = "DEFICIENT" if any(v < 3 * d for v in res.values()) else "full"
    print(flag, "order", order, "3d", 3 * d, res, "gens", [list(map(int, g)) for g in gens], flush=True)
print("distinct images tested:", len(sigs))
