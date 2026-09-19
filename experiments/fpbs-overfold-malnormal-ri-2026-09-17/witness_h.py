"""Top case for L_1, k = 1: when <X, g> = F with X <= L_1, find h with
<X, h> = L_1 (swarm-0917-w19-w19-fp-follow).

X = <random words in a, t> (t = b a b^-2); g ranges over reduced words
with |g| <= GMAX.  For every hit <X, g> >= L_1 with X != L_1, search h
among words in (a, t) of length <= HMAX.  Reports hits with no h found
(candidates for a violation) and statistics.

usage: python3 witness_h.py SEED NX GMAX HMAX NTRIALS [skip]
  with a 6th argument 'skip', g in L_1 is skipped (only nontrivial g count).
"""
import random
import sys
from stall import red, inv, fold_graph, member, rank, basis, L
from ri1 import randword, subst
from longg import words_upto


SKIP_IN_L1 = len(sys.argv) > 6 and sys.argv[6] == 'skip'


def main():
    seed, nxmax, gmax, hmax, ntr = map(int, sys.argv[1:6])
    rng = random.Random(seed)
    L1 = L(1)
    L1G = fold_graph(L1)
    hs = [subst(w, L1) for w in words_upto(hmax)]
    gs = list(words_upto(gmax))
    stats = dict(X=0, hits=0, h_found=0, h_missing=0)
    for _ in range(ntr):
        nx = rng.randint(1, nxmax)
        Xw = [subst(randword(rng, 1, 5), L1) for _ in range(nx)]
        XG = fold_graph(Xw)
        Xb = basis(XG)[1]
        if all(member(XG, w) for w in L1):
            continue
        stats['X'] += 1
        for g in gs:
            if SKIP_IN_L1 and member(L1G, g):
                continue  # g in L_1 gives the trivial witness h = g
            JG = fold_graph(Xb + [g])
            if not all(member(JG, w) for w in L1):
                continue
            stats['hits'] += 1
            found = None
            for h in hs:
                HG = fold_graph(Xb + [h])
                if all(member(HG, w) for w in L1):
                    found = h
                    break
            if found is None:
                stats['h_missing'] += 1
                print('NO-h X=%s g=%s rkX=%d' % (Xb, g, len(Xb)), flush=True)
            else:
                stats['h_found'] += 1
                print('ok X=%s g=%s h=%s' % (Xb, g, found), flush=True)
            break  # one g per X
    print('STATS', seed, stats)


if __name__ == '__main__':
    main()
