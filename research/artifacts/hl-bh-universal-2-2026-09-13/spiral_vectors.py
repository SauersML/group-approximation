#!/usr/bin/env python3
"""Correction vectors of window conjugates sigma^j L_h sigma^-j for the square spiral.

For each label j and unit h, the map M = sigma^j L_h sigma^-j is compared with L_h
on whole rings r.  Every defect p should be moved by one diagonal step along the
diagonal line through p (inward or outward).  The correction delta = L_h^-1 M is
recorded as {quadrant, line offset: amount}, amount +1 = inward step, -1 = outward.
Q1: x,y>0 (offset c=x-y), Q2: x<0<y (offset d=x+y), Q3: x,y<0 (c=x-y), Q4: y<0<x (d=x+y).
Consistency across rings shows the vectors are ring independent (translation along
the diagonal preserves the local configuration).
"""
import json
exec(open('spiral_common.py').read())

OUT = {'Q1': (1, 1), 'Q2': (-1, 1), 'Q3': (-1, -1), 'Q4': (1, -1)}

def quadrant(p):
    x, y = p
    if x > 0 and y > 0: return 'Q1'
    if x < 0 < y: return 'Q2'
    if x < 0 and y < 0: return 'Q3'
    if y < 0 < x: return 'Q4'
    return 'AXIS'

def offset(q, p):
    return p[0] - p[1] if q in ('Q1', 'Q3') else p[0] + p[1]

def vec(j, h, r):
    M = compose(sigpow(j), L(h), sigpow(-j))
    v, other = {}, []
    for p in ring(r):
        a = M(p)
        b = (p[0] + h[0], p[1] + h[1])
        if a == b:
            continue
        corr = (a[0] - b[0], a[1] - b[1])
        q = quadrant(p)
        o = OUT.get(q)
        if o is not None and corr == o:
            amt = -1
        elif o is not None and corr == (-o[0], -o[1]):
            amt = +1
        else:
            other.append({'p': p, 'corr': corr, 'q': q})
            continue
        key = '%s:%d' % (q, offset(q, p))
        v[key] = v.get(key, 0) + amt
    return {k: x for k, x in v.items() if x}, other

H = {'e1': (1, 0), '-e1': (-1, 0), 'e2': (0, 1), '-e2': (0, -1)}
res = {}
for j in (-1, 1, 2, 3):
    for hn, h in H.items():
        rings = {}
        for r in (60, 61, 90, 91):
            v, other = vec(j, h, r)
            rings[r] = {'v': v, 'other': other}
        same = all(rings[r]['v'] == rings[60]['v'] for r in rings) and all(not rings[r]['other'] for r in rings)
        res['j=%d h=%s' % (j, hn)] = {'v': rings[60]['v'], 'ring_independent_and_diagonal_only': same,
                                       'other_r60': rings[60]['other'][:4]}
print(json.dumps(res, indent=0))
print('DONE')
