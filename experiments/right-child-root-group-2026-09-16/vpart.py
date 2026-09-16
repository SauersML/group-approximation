"""Find permutation (Thompson V) elements in balls of Gamma' = <u,x,y,beta>."""
import sys
from leavitt_ops import *

u = ident_plus([('0', '1')])
x = ident_plus([('0', '10')])
y = ident_plus([('10', '11')])
beta = monomial_sum([('00', '0'), ('01', '11'), ('1', '10')])
betainv = monomial_sum([('0', '00'), ('11', '01'), ('10', '1')])
gens = [u, x, y, beta, betainv]
names = ['u', 'x', 'y', 'B', 'b']
R = int(sys.argv[1])
seen = {key(IDENT): ''}
frontier = [(IDENT, '')]
found = []
for r in range(1, R + 1):
    nf = []
    for g, w in frontier:
        for i, s in enumerate(gens):
            h = mul(g, s)
            k = key(h)
            if k not in seen:
                seen[k] = w + names[i]
                nf.append((h, w + names[i]))
                if all(len(F) == 1 for F in h.values()):
                    found.append((w + names[i], h))
    frontier = nf
    print('radius', r, 'perm elements so far', len(found), flush=True)
for w, h in found[:40]:
    print(w, sorted((a, sorted(F)) for a, F in h.items()))
