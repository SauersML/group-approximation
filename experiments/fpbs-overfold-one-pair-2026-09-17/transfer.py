"""For every collapsing pair (u,w) of Exp(Gamma_0), test which 'projected'
pairs of Gamma_0 collapse Gamma_0.  Projection: ('o',x)->x, ('1',z)->z,
('2',(s,r))->s or r.  Reports per pair type the counts of success of each
projection rule, and hits where no projected pair works.
usage: transfer.py seed trials maxgens maxlen
"""
import random, sys
from collections import Counter
from folding import *
from expansion import expansion, collapses

seed, T, G, Lm = (int(x) for x in sys.argv[1:5])
rng = random.Random(seed)
cnt = Counter()
tot = Counter()
noproj = 0
hits_total = 0
for trial in range(T):
    X0 = [rand_word(rng.randint(1, Lm), rng) for _ in range(rng.randint(2, G))]
    n0, E0 = graph_of(X0)
    if rank(n0, E0) < 2 or is_rose(n0, E0):
        continue
    n, E, idx = expansion(n0, E0)
    rev = {v: k for k, v in idx.items()}
    for u in range(n):
        for w in range(u + 1, n):
            if not collapses(n, E, [(u, w)]):
                continue
            hits_total += 1
            ku, kw = rev[u], rev[w]
            if ku[0] > kw[0]:
                ku, kw = kw, ku
            typ = ku[0] + kw[0]
            tot[typ] += 1
            pu = [('s', ku[1])] if ku[0] != '2' else [('s', ku[1][0]), ('r', ku[1][1])]
            pw = [('s', kw[1])] if kw[0] != '2' else [('s', kw[1][0]), ('r', kw[1][1])]
            anyok = False
            for (tu, x) in pu:
                for (tw, y) in pw:
                    ok = collapses(n0, E0, [(x, y)])
                    cnt[(typ, tu + tw)] += ok
                    anyok |= ok
            if not anyok:
                noproj += 1
print('hits', hits_total, 'by type', dict(tot))
print('projection successes', dict(cnt))
print('hits with no projected pair collapsing Gamma_0:', noproj)
