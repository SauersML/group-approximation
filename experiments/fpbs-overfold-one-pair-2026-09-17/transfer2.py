"""For collapsing mixed pairs of Exp(Gamma_0), tally which shifted projected
pairs (x.w1, y.w2), w1,w2 short words, collapse Gamma_0.
usage: transfer2.py seed trials maxgens maxlen"""
import random, sys
from collections import Counter
from folding import *
from expansion import expansion, collapses

seed, T, G, Lm = (int(x) for x in sys.argv[1:5])
rng = random.Random(seed)
SH = ['', 'a', 'A', 'b', 'B', 'aa', 'AA', 'ab', 'aB', 'Ab', 'AB', 'ba', 'bA',
      'Ba', 'BA', 'bb', 'BB']
cnt = {}
tot = Counter()
none = Counter()
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
            ku, kw = sorted([rev[u], rev[w]], key=lambda k: k[0])
            typ = ku[0] + kw[0]
            tot[typ] += 1
            x = ku[1] if ku[0] != '2' else ku[1][0]
            y = kw[1] if kw[0] != '2' else kw[1][0]
            good = False
            for w1 in SH:
                xx = read_path(n0, E0, w1, x)
                if xx is None:
                    continue
                for w2 in SH:
                    yy = read_path(n0, E0, w2, y)
                    if yy is None:
                        continue
                    if collapses(n0, E0, [(xx, yy)]):
                        cnt.setdefault(typ, Counter())[(w1, w2)] += 1
                        good = True
            if not good:
                none[typ] += 1
print('tot', dict(tot), 'none', dict(none))
for typ in cnt:
    print(typ, cnt[typ].most_common(8))
