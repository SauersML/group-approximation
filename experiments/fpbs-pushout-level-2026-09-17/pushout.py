"""Pushout census: for finite quotients G = L/N of L = F(a,b), compute
Ghat = L / <<K cap N>>^L, K = <a, c>, c = b a b^-2, by coset enumeration.

Relators of Kbar (image of K in G) on generators a, c are the fundamental
cycles of the Cayley graph Cay(Kbar,{a,c}); they freely generate K cap N, so
their normal closure in L is M = <<K cap N>>^L.  Then
  I = [Ghat : image of K],  t = [G : Kbar],  |N/M| = |Ghat|/|G| = I/t
(the image of K in Ghat is isomorphic to Kbar).
"""
import random
import sys
from tc import enumerate_cosets, free_reduce

A, AI, B, BI = 0, 1, 2, 3
C_WORD = [B, A, BI, BI]
CI_WORD = [B, B, AI, BI]


def pmul(p, q):  # right action: first p then q
    return tuple(q[i] for i in p)


def pinv(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)


def closure_order(gens, limit=10 ** 6):
    e = tuple(range(len(gens[0])))
    seen = {e}
    frontier = [e]
    while frontier:
        nf = []
        for g in frontier:
            for s in gens:
                h = pmul(g, s)
                if h not in seen:
                    seen.add(h)
                    nf.append(h)
                    if len(seen) > limit:
                        return None
        frontier = nf
    return len(seen)


def kbar_relators(al, ga):
    """Fundamental cycles of Cay(<al,ga>, {al, ga}) as words in letters
    0=a,1=A,4=c,5=C.  Returns (order, relators)."""
    e = tuple(range(len(al)))
    gens = [(al, 0), (ga, 4)]
    word = {e: []}
    order = [e]
    i = 0
    while i < len(order):
        g = order[i]
        i += 1
        for s, lt in gens:
            h = pmul(g, s)
            if h not in word:
                word[h] = word[g] + [lt]
                order.append(h)
    inv_lt = {0: 1, 1: 0, 4: 5, 5: 4}
    rels = []
    for g in order:
        for s, lt in gens:
            h = pmul(g, s)
            w = word[g] + [lt] + [inv_lt[x] for x in reversed(word[h])]
            w = reduce_ac(w)
            if w:
                rels.append(w)
    return len(order), rels


def reduce_ac(w):
    inv_lt = {0: 1, 1: 0, 4: 5, 5: 4}
    out = []
    for x in w:
        if out and out[-1] == inv_lt[x]:
            out.pop()
        else:
            out.append(x)
    return out


def ac_to_ab(w):
    out = []
    for x in w:
        if x == 0:
            out.append(A)
        elif x == 1:
            out.append(AI)
        elif x == 4:
            out += C_WORD
        else:
            out += CI_WORD
    return free_reduce(out)


def census_one(al, be, maxcos=400000):
    ga = pmul(pmul(pmul(be, al), pinv(be)), pinv(be))  # c = b a b^-1 b^-1
    nG = closure_order([al, be])
    nK, rels_ac = kbar_relators(al, ga)
    rels = [ac_to_ab(w) for w in rels_ac]
    # dedupe cyclic duplicates cheaply
    rels = sorted({tuple(r) for r in rels}, key=len)
    rels = [list(r) for r in rels]
    t = nG // nK
    I = enumerate_cosets(rels, [[A], C_WORD], maxcos=maxcos)
    return nG, nK, t, I


def rand_perm(n, rng):
    p = list(range(n))
    rng.shuffle(p)
    return tuple(p)


def psl2_perms(p, rng):
    pts = [(1, x) for x in range(p)] + [(0, 1)]
    idx = {v: i for i, v in enumerate(pts)}

    def norm(v):
        x, y = v[0] % p, v[1] % p
        if x != 0:
            ix = pow(x, p - 2, p)
            return (1, y * ix % p)
        return (0, 1)

    def perm(m):
        a, b, c, d = m
        return tuple(idx[norm((a * x + c * y, b * x + d * y))] for (x, y) in pts)

    def rmat():
        while True:
            a, b, c = rng.randrange(p), rng.randrange(p), rng.randrange(p)
            if a == 0:
                continue
            d = (1 + b * c) * pow(a, p - 2, p) % p
            return (a, b, c, d)

    return perm(rmat()), perm(rmat())


if __name__ == "__main__":
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    fam = sys.argv[2] if len(sys.argv) > 2 else "sym"
    trials = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    for _ in range(trials):
        if fam.startswith("sym"):
            n = int(fam[3:] or 5)
            al, be = rand_perm(n, rng), rand_perm(n, rng)
            tag = "S%d" % n
        else:
            p = int(fam[3:])
            al, be = psl2_perms(p, rng)
            tag = "PSL2(%d)" % p
        nG, nK, t, I = census_one(al, be)
        ratio = None if I is None else (I / t)
        print(tag, "|G|=%d |Kbar|=%d t=%d  [Ghat:K]=%s  |N/M|=%s" % (nG, nK, t, I, ratio), flush=True)
