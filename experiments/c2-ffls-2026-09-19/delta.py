"""Torsion degree of H_1(N; D_N) for H = <b,c,d,e | r>, eps = (3,0,1,1).

With R = D_N[t^+-1] (Linnell skew field of the free group N = H cap F_4), H_1(H; R) = R^3 / R v with
v = (d_b r, d_d r, d_e r) (Fox derivatives, basis of ker d_1 adapted to c, since c - 1 is a unit).
d_c r = -P C (1 - u), P = eDDEddb, u = B z b D, z = eDDEdd, eps(u) = -1.  So the torsion is R/R lambda
with lambda R = sum_x d_x r R  containing q R, q = P C (1 - u); deg lambda = 1 iff every d_x r lies in
q R, iff every f_x = (PC)^-1 d_x r lies in (1 - u) QH (Novikov expansion argument, see the proof node),
iff the image of f_x in Q[<u> \ H] vanishes.  A right coset <u>h has the unique eps-0 representative
u^eps(h) h; we compare these in the fibre F_4 (exact word problem in G = F_4 x| Z).
"""
from hlib import R, EPS, eps, toxy, hinv
from fbc import tofib

def fox(r, x):
    out = []
    for i, ch in enumerate(r):
        if ch == x: out.append((1, r[:i]))
        elif ch == x.upper(): out.append((-1, r[:i + 1]))
    return out

z = 'eDDEdd'; P = z + 'b'; C = 'C'; u = 'B' + z + 'b' + 'D'
assert eps(u) == -1

def power(w, m): return w * m if m >= 0 else hinv(w) * (-m)

def coset_key(h):
    return tofib(toxy(power(u, eps(h)) + h))

def image(terms):
    acc = {}
    for s, h in terms:
        k = coset_key(hinv(P + C) + h)
        acc[k] = acc.get(k, 0) + s
    return {k: v for k, v in acc.items() if v}

if __name__ == '__main__':
    # sanity: f_c = -(1 - u) maps to zero; and the fundamental formula holds in ZH
    assert image(fox(R, 'c')) == {}, image(fox(R, 'c'))
    for x in 'bde':
        im = image(fox(R, x))
        print(x, 'terms', len(fox(R, x)), 'nonzero cosets', len(im), im if len(im) < 9 else '')
