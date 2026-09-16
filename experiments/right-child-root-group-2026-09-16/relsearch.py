"""Search for short relations in <u, beta> and other pairs by BFS over reduced words, detecting
coincidences of group elements (two distinct reduced words with the same element)."""
import sys
from leavitt_ops import *

u = ident_plus([('0', '1')])
x = ident_plus([('0', '10')])
y = ident_plus([('10', '11')])
beta = monomial_sum([('00', '0'), ('01', '11'), ('1', '10')])
betainv = monomial_sum([('0', '00'), ('11', '01'), ('10', '1')])

def search(gens, names, inv, R):
    # gens: list of elements; inv[i] = index of inverse generator
    seen = {key(IDENT): ''}
    frontier = [(IDENT, '', -1)]
    for r in range(1, R + 1):
        nf = []
        for g, word, last in frontier:
            for i, s in enumerate(gens):
                if last >= 0 and inv[last] == i:
                    continue
                h = mul(g, s)
                k = key(h)
                w2 = word + names[i]
                if k in seen:
                    other = seen[k]
                    if len(other) + 0 >= 0:
                        print('coincidence len', r, ':', w2, '=', other, flush=True)
                        return
                else:
                    seen[k] = w2
                    nf.append((h, w2, i))
        frontier = nf
        print('radius', r, 'new', len(nf), flush=True)

which = sys.argv[1]
R = int(sys.argv[2])
if which == 'u-beta':
    search([u, beta, betainv], ['u', 'B', 'b'], [0, 2, 1], R)
elif which == 'y-beta':
    search([y, beta, betainv], ['y', 'B', 'b'], [0, 2, 1], R)
elif which == 'x-beta':
    search([x, beta, betainv], ['x', 'B', 'b'], [0, 2, 1], R)
