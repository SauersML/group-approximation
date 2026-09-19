"""Transposition chains: the least number of single-edge swaps (a transposition of two b-values or two
c-values) that lowers the total excess of a pair, allowing a flat donor torus padded beside it."""
from swap import *
from stalls_lib import *
import json, sys

def vlab(b, c):
    return vertices(b, c)[0]

def lowering_moves(b, c, lab=None):
    """all single transpositions that lower the excess (exact check on candidates)."""
    if lab is None: lab = vlab(b, c)
    d = len(b); ex0 = excess(b, c); out = []
    groups = {}
    for y in range(d):
        groups.setdefault(('b', lab[4*y+1], lab[4*y+2]), []).append(y)   # right edge BR->TR
        groups.setdefault(('c', lab[4*y+3], lab[4*y+2]), []).append(y)   # top edge TL->TR
    for (g, _, _), ys in groups.items():
        for i in range(len(ys)):
            for j in range(i+1, len(ys)):
                y1, y2 = ys[i], ys[j]
                b2, c2 = b[:], c[:]
                f = b2 if g == 'b' else c2
                f[y1], f[y2] = f[y2], f[y1]
                ex = excess(b2, c2)
                if ex < ex0: out.append((g, y1, y2, ex))
    return out

def all_moves(d):
    for g in 'bc':
        for y1 in range(d):
            for y2 in range(y1+1, d): yield g, y1, y2

def chain2(b, c):
    """least k in {1,2} such that k transpositions lower the excess; returns (k, example)."""
    lm = lowering_moves(b, c)
    if lm: return 1, lm[0]
    ex0 = excess(b, c); d = len(b)
    for g, y1, y2 in all_moves(d):
        b2, c2 = b[:], c[:]
        f = b2 if g == 'b' else c2
        f[y1], f[y2] = f[y2], f[y1]
        if excess(b2, c2) > ex0: continue
        lm = lowering_moves(b2, c2)
        if lm: return 2, ((g, y1, y2), lm[0])
    return None, None

def pad(b, c, w, h):
    tb, tc = tori([(w, h)]); d = len(b)
    return b + [d + x for x in tb], c + [d + x for x in tc]

if __name__ == '__main__':
    st = json.load(open('stalls.json'))
    for s in st:
        bb, cc = s['bs'], s['cs']
        for cm in components(bb, cc):
            B, C = restrict(bb, cc, cm)
            if excess(B, C) == 0: continue
            res = []
            for dn in [None, (1, 1), (2, 1), (1, 2), (2, 2)]:
                b2, c2 = (B, C) if dn is None else pad(B, C, *dn)
                k, ex = chain2(b2, c2)
                res.append((dn, k))
            print("trial", s['trial'], "comp", len(cm), res, flush=True)
