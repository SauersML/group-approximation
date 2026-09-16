"""Sphere sizes of <g,h> (with inverses) to detect short relations; free group of rank 2 has 4*3^(n-1)."""
import sys
from leavitt_ops import *

u = ident_plus([('0', '1')])
x = ident_plus([('0', '10')])
y = ident_plus([('10', '11')])
beta = monomial_sum([('00', '0'), ('01', '11'), ('1', '10')])
betainv = monomial_sum([('0', '00'), ('11', '01'), ('10', '1')])
u2 = mul(mul(beta, y), betainv)

def inv_of_word(letters):
    # letters: list of (elem, inverse elem)
    pass

def sphere(g, gi, h, hi, R, maxsize=4000):
    gens = [g, gi, h, hi]
    inv = [1, 0, 3, 2]
    seen = {key(IDENT)}
    frontier = [(IDENT, -1)]
    out = []
    for r in range(1, R + 1):
        nf = []
        coinc = 0
        for el, last in frontier:
            for i, s in enumerate(gens):
                if last >= 0 and inv[last] == i:
                    continue
                e2 = mul(el, s)
                if size(e2) > maxsize:
                    continue
                k = key(e2)
                if k in seen:
                    coinc += 1
                    continue
                seen.add(k)
                nf.append((e2, i))
        frontier = nf
        out.append((r, len(nf), coinc))
        print(r, len(nf), 'coinc', coinc, 'free would be', 4 * 3 ** (r - 1), flush=True)
    return out

which = sys.argv[1]; R = int(sys.argv[2])
G = mul(u, u2); Gi = mul(u2, u)
if which == 'G-beta':
    sphere(G, Gi, beta, betainv, R)
elif which == 'G-betaGbeta':
    H = mul(mul(beta, G), betainv); Hi = mul(mul(beta, Gi), betainv)
    sphere(G, Gi, H, Hi, R)
elif which == 'G-x':
    sphere(G, Gi, mul(x, beta), mul(betainv, x), R)
