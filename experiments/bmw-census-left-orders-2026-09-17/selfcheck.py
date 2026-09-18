# For every complex of a census: the complete rewriting system's critical pairs resolve (Newman), and the
# fast normal-form multiplication used by lo_census.py agrees with the rewriting normal form on random words.
import sys, random
from lo_census import load
def nf(G, w): return G.rw(w)
def as_word(g): return tuple(('v', x) for x in g[0]) + tuple(('h', x) for x in g[1])
tot = 0
for path in sys.argv[1:]:
    rnd = random.Random(7); n = 0
    for i, G in load(path):
        G.confluence()
        L = G.H + G.V
        for _ in range(40):
            w1 = [rnd.choice(L) for _ in range(rnd.randint(0, 6))]
            w2 = [rnd.choice(L) for _ in range(rnd.randint(0, 6))]
            g1, g2 = G.rw(w1), G.rw(w2)
            e1 = (tuple(x for t, x in g1 if t == 'v'), tuple(x for t, x in g1 if t == 'h'))
            e2 = (tuple(x for t, x in g2 if t == 'v'), tuple(x for t, x in g2 if t == 'h'))
            assert as_word(e1) == g1      # irreducible words are (vertical)(horizontal)
            assert as_word(G.mul(e1, e2)) == G.rw(w1 + w2)
        n += 1
    print(path, 'complexes checked', n); tot += n
print('total', tot)
