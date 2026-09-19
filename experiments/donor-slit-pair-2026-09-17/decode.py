"""Decode the shortest (1 + L2) chains on stalls: first move a transposition, second a same-vertex slit swap."""
import json, sys
from swap import Surf, apply_swap, excess
from stalls_lib import components, restrict
from handle import path
def angles(S):
    return {v: len(cl)//4 for v, cl in S.cls.items() if len(cl) > 4}
def lowering(S, L, ex0):
    cones = set(S.cones()); out = []
    sts = [(x, k) for x in range(len(S.b)) for k in range(4) if S.vstart((x, k)) in cones]
    import itertools
    for i, a in enumerate(sts):
        for bst in sts[i+1:]:
            if bst[1] != a[1] or S.vstart(a) != S.vstart(bst): continue
            for w in itertools.product(range(3), repeat=L-1):
                P1, P2 = path(S, a, w), path(S, bst, w)
                if S.vend(P1[-1]) != S.vend(P2[-1]): continue
                r = apply_swap(S, P1, P2)
                if r and excess(*r) < ex0: out.append((a, bst, w))
    return out
st = json.load(open('stalls.json'))
for s in st:
    if s['trial'] not in map(int, sys.argv[1:]): continue
    for cm in components(s['bs'], s['cs']):
        B, C = restrict(s['bs'], s['cs'], cm)
        if not excess(B, C): continue
        S = Surf(B, C); e0 = excess(B, C); print('trial', s['trial'], 'cones', angles(S))
        cones = set(S.cones()); found = 0
        for x in range(len(B)):
            for k in range(4):
                a = (x, k)
                if S.vstart(a) not in cones: continue
                for y in range(len(B)):
                    p = (y, k)
                    if p == a: continue
                    r = apply_swap(S, [a], [p])
                    if not r or excess(*r) != e0: continue
                    T = Surf(*r)
                    for L2 in (1, 2):
                        lw = lowering(T, L2, e0)
                        if lw:
                            e1 = (S.vstart(a), S.vend(a)); e2 = (S.vstart(p), S.vend(p))
                            print(' first: edge', a, e1, 'with', p, e2, '-> cones', angles(T), '; then', L2, lw[0]); found += 1; break
                    if found >= 3: break
                if found >= 3: break
            if found >= 3: break
