"""Least number k of transpositions (single-edge swaps) that lowers the total excess, when every intermediate
state has excess <= the start (so the chain is excess-monotone), optionally beside a flat donor torus."""
from swap import *
from stalls_lib import *
from tchain import pad
import json, sys

def cand_moves(b, c, lab):
    """transpositions that can keep the excess: the two edges share an endpoint vertex, or both are loops
    (start vertex = end vertex).  Any other pair merges two vertex pairs and raises the excess by 2."""
    d = len(b); seen = set()
    for g, e0, e1 in (('b', 1, 2), ('c', 3, 2)):
        ends = [(lab[4*y+e0], lab[4*y+e1]) for y in range(d)]
        grp = {}
        for y in range(d):
            for v in set(ends[y]): grp.setdefault(v, []).append(y)
        loops = [y for y in range(d) if ends[y][0] == ends[y][1]]
        for ys in list(grp.values()) + [loops]:
            for i in range(len(ys)):
                for j in range(i+1, len(ys)):
                    key = (g, ys[i], ys[j])
                    if key not in seen: seen.add(key); yield key

def apply(b, c, mv):
    g, y1, y2 = mv; b2, c2 = b[:], c[:]
    f = b2 if g == 'b' else c2
    f[y1], f[y2] = f[y2], f[y1]
    return b2, c2

def least_chain(b, c, kmax):
    ex0 = excess(b, c)
    level = [(b, c, ())]; seen = {(tuple(b), tuple(c))}
    for k in range(1, kmax + 1):
        nxt = []
        for (bb, cc, hist) in level:
            lab = vertices(bb, cc)[0]
            for mv in cand_moves(bb, cc, lab):
                b2, c2 = apply(bb, cc, mv)
                ex = excess(b2, c2)
                if ex < ex0: return k, hist + (mv,)
                if ex == ex0 and k < kmax:
                    key = (tuple(b2), tuple(c2))
                    if key not in seen: seen.add(key); nxt.append((b2, c2, hist + (mv,)))
        level = nxt
        if len(level) > 200000: return ('>', k), len(level)
    return None, None

if __name__ == '__main__':
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    st = json.load(open('stalls.json'))
    for s in st:
        bb, cc = s['bs'], s['cs']
        for cm in components(bb, cc):
            B, C = restrict(bb, cc, cm)
            if excess(B, C) == 0: continue
            res = []
            for dn in [None, (1, 1), (2, 1), (1, 2)]:
                b2, c2 = (B, C) if dn is None else pad(B, C, *dn)
                k, h = least_chain(b2, c2, kmax)
                res.append((dn, k))
            print("trial", s['trial'], "comp", len(cm), res, flush=True)
