"""Cross-check: the squares read from Figure picture:64n (fig64n.py) induce the local permutations
printed in the proof of Radu's Theorem 64n.  A 'reading' of a local permutation from the swap map
v u = u' v' is one of: fix the b-letter on the left (v) or on the right (v'), optionally inverted,
then optionally invert the permutation and/or conjugate by letter inversion.  Report the readings
that match Radu's printed permutations for every letter.  usage: python3 xcheck64n.py n [corrected]"""
import sys, itertools
import fig64n
from bmw import BMW
from g64n import radu_perms, invp, conj

n = int(sys.argv[1])
sq = fig64n.instantiate(fig64n.build(n), n)
G = BMW(3, 2 * n, [fig64n.fmtw(fig64n.word(s, 0)) for _, _, s in sq])
sw = G.swap
corrected = len(sys.argv) > 2 and sys.argv[2] == "corrected"
P, S = radu_perms(n, corrected)


def bperm(j, side, sgn):
    out = {}
    for (v, u), (u2, v2) in sw.items():
        if (v if side == 0 else v2) == sgn * j:
            out[u] = u2
    return out


def aperm(i, side, sgn):
    out = {}
    for (v, u), (u2, v2) in sw.items():
        if (u if side == 0 else u2) == sgn * i:
            out[v] = v2
    return out


def variants(p):
    for inv_, cj in itertools.product((0, 1), repeat=2):
        q = p
        if inv_: q = invp(q)
        if cj: q = conj(q)
        yield (inv_, cj), q


matchB = set(itertools.product((0, 1), (1, -1), (0, 1), (0, 1)))
for j in range(1, 2 * n + 1):
    ok = set()
    for side, sgn in itertools.product((0, 1), (1, -1)):
        p = bperm(j, side, sgn)
        for c, q in variants(P[j]):
            if p == q:
                ok.add((side, sgn) + c)
    matchB &= ok
matchA = set(itertools.product((0, 1), (1, -1), (0, 1), (0, 1)))
for i in (1, 2, 3):
    ok = set()
    for side, sgn in itertools.product((0, 1), (1, -1)):
        p = aperm(i, side, sgn)
        for c, q in variants(S[i]):
            if p == q:
                ok.add((side, sgn) + c)
    matchA &= ok
print("corrected=%s n=%d squares=%d b-readings matching all b_j: %s ; a-readings matching a1,a2,a3: %s" % (corrected, n, len(sq), sorted(matchB), sorted(matchA)))
