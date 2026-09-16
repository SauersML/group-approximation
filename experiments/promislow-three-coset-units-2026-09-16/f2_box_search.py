#!/usr/bin/env python3
"""Certified exhaustive search: units u = p + q a + r b of F_2[P] with p, q, r supported in a box BX of L.

Method: (1) necessary filter  Nrd(u)(chi) = 1 for all 27 characters chi: L -> F_4^x (chi(x),chi(y),chi(z) cube roots of 1),
using the 9-term s=0 reduced norm (validated in validate_engine.py) evaluated through f^g(chi) = f(chi o g);
(2) every survivor is checked exactly: det of right multiplication (engine.det_right_mult, mod 2) == 1.
By the criterion of promislow-group-ring-units-are-constant-reduced-norm, (2) decides unithood.
Output: counts of trivial and nontrivial units found; nontrivial ones printed.
Usage: f2_box_search.py I0 I1 J0 J1 K0 K1   (inclusive exponent ranges of the box)
"""
import sys, itertools, json
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from engine import assemble, det_right_mult, act

I0, I1, J0, J1, K0, K1 = map(int, sys.argv[1:7]) if len(sys.argv) > 6 else (0, 1, 0, 1, 0, 1)
BX = [(i, j, k) for i in range(I0, I1 + 1) for j in range(J0, J1 + 1) for k in range(K0, K1 + 1)]
nb = len(BX)
NS = 1 << nb
# F_4 = F_2[w]/(w^2+w+1), encoded a+2b; addition = xor
def f4mul(u, v):
    a1, b1, a2, b2 = u & 1, u >> 1, v & 1, v >> 1
    # (a1 + b1 w)(a2 + b2 w) = a1a2 + (a1b2+a2b1) w + b1b2 w^2 ; w^2 = w + 1
    c0 = (a1 & a2) ^ (b1 & b2)
    c1 = (a1 & b2) ^ (a2 & b1) ^ (b1 & b2)
    return c0 | (c1 << 1)
MUL = np.array([[f4mul(u, v) for v in range(4)] for u in range(4)], dtype=np.uint8)
POW = [1, 2, 3]  # w^0, w^1, w^2
chars = list(itertools.product(range(3), repeat=3))
cidx = {c: n for n, c in enumerate(chars)}
def chi_val(c, m):
    return POW[(c[0] * m[0] + c[1] * m[1] + c[2] * m[2]) % 3]
# twisted character index: f^g(chi) = f(chi o g), chi o g has exponents act(g, c)
TWI = {g: np.array([cidx[tuple(v % 3 for v in act(g, c))] for c in chars]) for g in 'eABC'}
# value table VAL[S, chi]
ptval = np.array([[chi_val(c, m) for c in chars] for m in BX], dtype=np.uint8)  # (nb, 27)
VAL = np.zeros((NS, 27), dtype=np.uint8)
for S in range(1, NS):
    low = (S & -S).bit_length() - 1
    VAL[S] = VAL[S & (S - 1)] ^ ptval[low]
TW = {g: VAL[:, TWI[g]] for g in 'eABC'}
def m(*arrs):
    out = arrs[0]
    for a in arrs[1:]:
        out = MUL[out, a]
    return out
NN = m(TW['e'], TW['A'], TW['B'], TW['C'])
eA, BC, eB, AC, eC, AB = m(TW['e'], TW['A']), m(TW['B'], TW['C']), m(TW['e'], TW['B']), m(TW['A'], TW['C']), m(TW['e'], TW['C']), m(TW['A'], TW['B'])
def mono_vals(mm):
    return np.array([chi_val(c, mm) for c in chars], dtype=np.uint8)
Xv, Xiv, Yv, Yiv, Zv, Ziv = [mono_vals(mm) for mm in [(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)]]
r_Y_eB = MUL[Yv[None, :], eB]      # y * (r r^B)   -> term y p^A p^C r^B r = AC[p] * (y eB[r])
r_Yi_AC = MUL[Yiv[None, :], AC]    # y^-1 (r^A r^C) -> term y^-1 p^B p r^A r^C = eB[p] * (y^-1 AC[r])
r_Zi_eC = MUL[Ziv[None, :], eC]    # z^-1 r r^C  -> term z^-1 q^A q^B r^C r = AB[q] * (z^-1 eC[r])
r_Z_AB = MUL[Zv[None, :], AB]      # z r^A r^B   -> term z q^C q r^A r^B = eC[q] * (z AB[r])
ONEv = np.ones(27, dtype=np.uint8)
survivors = []
for P in range(NS):
    for Q in range(NS):
        base = NN[P] ^ NN[Q] ^ MUL[MUL[Xiv, eA[P]], BC[Q]] ^ MUL[MUL[Xv, BC[P]], eA[Q]]
        tot = NN ^ base[None, :] ^ MUL[AC[P][None, :], r_Y_eB] ^ MUL[eB[P][None, :], r_Yi_AC] \
              ^ MUL[AB[Q][None, :], r_Zi_eC] ^ MUL[eC[Q][None, :], r_Z_AB]
        ok = np.nonzero((tot == 1).all(axis=1))[0]
        for R in ok:
            survivors.append((P, Q, int(R)))
def poly_of(S):
    return {BX[i]: 1 for i in range(nb) if S >> i & 1}
units, nontriv = 0, []
for P, Q, R in survivors:
    p, q, r = poly_of(P), poly_of(Q), poly_of(R)
    D = det_right_mult(assemble(p, q, r), mod=2)
    if D == {(0, 0, 0): 1}:
        units += 1
        if len(p) + len(q) + len(r) != 1:
            nontriv.append((sorted(p), sorted(q), sorted(r)))
res = {'box': [I0, I1, J0, J1, K0, K1], 'box_points': nb, 'search_space': NS ** 3,
       'filter_survivors': len(survivors), 'units_found': units, 'nontrivial_units': len(nontriv)}
print(json.dumps(res))
for t in nontriv[:20]:
    print('NONTRIVIAL', t)
