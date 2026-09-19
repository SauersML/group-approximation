# Check of (P1): H(g-2) annihilates the Fox ideal J = d_x(w) ZG + d_y(w) ZG in Z[H\G].
# Exact identity in ZG (normal form of G = F_4 x| Z):
#     (g - 2) d_v(w) = sum_z (d_z u_1 - 2 d_z u_0) d_v(phi z)      (v = x, y)
# and every coefficient d_z u_1 - 2 d_z u_0 lies in ZH with augmentation e_z(u_1) - 2 e_z(u_0) = 0.
# So H(g-2) d_v(w) = sum_z 0 * H d_v(phi z) = 0.
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'c2-free-by-cyclic-2026-09-18'))
from verify_unimodular import BAS, U0, U1, W, inv, fred, ring, rmul, fox, nf

def foxw(u, v):
    """Fox derivative d_v u of a word in x, y, as signed prefixes (words in x, y)."""
    out, pre = [], ''
    for c in u:
        if c == v: out.append((+1, pre))
        pre += c
        if c == v.upper(): out.append((-1, pre))
    return out

def add(A, B, s=1):
    out = dict(A)
    for k, v in B.items(): out[k] = out.get(k, 0) + s * v
    return {k: v for k, v in out.items() if v}

G_ = 'Xy'
for z in 'abcde':
    e0 = sum(1 for c in U0 if c == z) - sum(1 for c in U0 if c == z.upper())
    e1 = sum(1 for c in U1 if c == z) - sum(1 for c in U1 if c == z.upper())
    assert e1 == 2 * e0, (z, e0, e1)
print('e_z(u_1) = 2 e_z(u_0) for all z')
for v in 'xy':
    lhs = rmul(ring([(1, G_), (-2, '')]), ring(foxw(W, v)))
    rhs = {}
    for z in 'abcde':
        coef = ring([(s, u) for s, u in fox(U1, z)] + [(-2 * s, u) for s, u in fox(U0, z)])
        rhs = add(rhs, rmul(coef, ring(foxw(BAS[z], v))))
    assert lhs == rhs, v
    print('(g-2) d_%s w = sum_z (d_z u1 - 2 d_z u0) d_%s(phi z) in ZG: OK (%d terms)' % (v, v, len(lhs)))
