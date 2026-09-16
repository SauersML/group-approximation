import sys
from leavitt_ops import *

u = ident_plus([('0', '1')])
x = ident_plus([('0', '10')])
y = ident_plus([('10', '11')])
beta = monomial_sum([('00', '0'), ('01', '11'), ('1', '10')])
betainv = monomial_sum([('0', '00'), ('11', '01'), ('10', '1')])
gens = [u, x, y, beta, betainv]
R = int(sys.argv[1])
seen = {key(IDENT): IDENT}
frontier = [IDENT]
counts = [1]
for r in range(1, R + 1):
    nf = []
    for g in frontier:
        for s in gens:
            h = mul(g, s)
            k = key(h)
            if k not in seen:
                seen[k] = h
                nf.append(h)
    frontier = nf
    counts.append(len(nf))
    print(r, len(nf), len(seen), flush=True)
