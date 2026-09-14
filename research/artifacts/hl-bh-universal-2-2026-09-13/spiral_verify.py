#!/usr/bin/env python3
"""Verify the finite-window gate words for the square spiral enumeration of Z^2.

1. sigma equals the four-piece translation
      R  = {x > |y|}                 -> +e2
      T  = {y >= |x|, x + y > 0}     -> -e1
      Lf = {-x >= |y|, y > x}        -> -e2
      B  = {-y >= |x|}               -> +e1
   (the four sets partition Z^2) at every enumerated point.
2. The explicit words W_e1, W_e2 built from L_h, sigma L_h sigma^-1 and
   sigma^2 L_h sigma^-2 agree with sigma^-1 L_g sigma on a whole annulus.
3. Conjugation of the correction delta_1(e1) = L_-e1 sigma L_e1 sigma^-1 by sigma,
   L_e1, L_e2 moves every diagonal line offset by the stated characters.
"""
import json
exec(open('spiral_common.py').read())
exec(open('spiral_vectors.py').read().split("H = {'e1'")[0])  # reuse quadrant/offset/vec helpers

def piece(p):
    x, y = p
    if x > abs(y): return (0, 1)
    if y >= abs(x) and x + y > 0: return (-1, 0)
    if -x >= abs(y) and y > x: return (0, -1)
    if -y >= abs(x): return (1, 0)
    raise AssertionError(p)

bad_piece = [p for p in pts[:-1] if sig(p) != (p[0] + piece(p)[0], p[1] + piece(p)[1])]

def Lh(h): return L(h)
def neg(h): return (-h[0], -h[1])
def d1(h): return compose(Lh(neg(h)), sig, Lh(h), sig_inv)
def d2(h): return compose(Lh(neg(h)), sig, sig, Lh(h), sig_inv, sig_inv)
def Tk(k, f): return compose(Lh(k), f, Lh(neg(k)))

W = {
 'e1': compose(Lh((1, 0)), d1((-1, 0)), Tk((-1, 0), d1((-1, 0))), Tk((-2, 0), d1((-1, 0))), d2((1, 0))),
 'e2': compose(Lh((0, 1)), Tk((1, -1), d1((0, -1))), Tk((0, -1), d1((0, -1))), Tk((-1, -1), d1((0, -1))), d2((0, 1))),
}
RLO, RHI = 40, RMAX - 12
test = [p for p in pts if RLO <= rad(p) <= RHI]
res = {'piece_formula_mismatches': len(bad_piece), 'annulus': [RLO, RHI], 'npoints': len(test)}
for g, f in W.items():
    Xg = X[g]
    mism = [p for p in test if f(p) != Xg(p)]
    res['word_%s_mismatches' % g] = len(mism)
    res['word_%s_sample' % g] = mism[:5]

# characters on line offsets
def corr_vec(M, r):
    v = {}
    for p in ring(r):
        a = M(p)
        if a == p:
            continue
        corr = (a[0] - p[0], a[1] - p[1])
        q = quadrant(p)
        o = OUT.get(q)
        amt = -1 if corr == o else (+1 if o and corr == (-o[0], -o[1]) else None)
        if amt is None:
            v.setdefault('OTHER', []).append((p, corr))
            continue
        key = '%s:%d' % (q, offset(q, p))
        v[key] = v.get(key, 0) + amt
    return v

base = d1((1, 0))
for name, M in (('base', base), ('sigma_conj', compose(sig, base, sig_inv)),
                ('Le1_conj', Tk((1, 0), base)), ('Le2_conj', Tk((0, 1), base))):
    res['vec_' + name] = {r: corr_vec(M, r) for r in (70, 71)}
print(json.dumps(res, indent=0, default=str))
print('DONE')
