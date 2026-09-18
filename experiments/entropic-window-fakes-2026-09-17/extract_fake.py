#!/usr/bin/env python3
"""Extract the rationalised vertex polymatroid of a cyclic minimal-window fake as an integer target.

usage: extract_fake.py n 'E' 'F' out.json          (cyclic Z/n, E, F comma lists)
       extract_fake.py GROUP 'E' 'F' out.json      (GROUP from torsion2_scan.group, E, F Python literals)
Writes {m, d, sizes, reads, h, phi, scale}.  Bit order: x_g for g in X (build order), then y_g for g in F.
"""
import sys, json, os
from fractions import Fraction as Fr
from math import lcm
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'shannon-window-certificates-2026-09-17'))
sys.path.insert(0, os.path.join(HERE, '..', 'promislow-shannon-windows-2026-09-17'))
import ast
from random_scan import Cyc
from shannon_lp import build
from verify_fake import lp_vertex

if sys.argv[1].isdigit():
    n = int(sys.argv[1]); E = [int(t) for t in sys.argv[2].split(',')]; F = [int(t) for t in sys.argv[3].split(',')]
    G = Cyc(n)
else:
    from torsion2_scan import group
    G = group(sys.argv[1])[0]; E = ast.literal_eval(sys.argv[2]); F = ast.literal_eval(sys.argv[3])
d = build(G, E, F)
res = lp_vertex(d)
assert res.status == 0
val = [Fr(v).limit_denominator(1000) for v in res.x]
N = 1 << d['n']
h = [val[d['col'][mm]] for mm in range(N)]
scale = 1
for v in h:
    scale = lcm(scale, v.denominator)
items = d['items']
X = [g for (k, g) in items if k == 'x']
Y = [g for (k, g) in items if k == 'y']
reads = [[X.index(G.mul(g, e)) for e in E] for g in Y]
yid = [items.index(('y', g)) for g in Y]
x1 = items.index(('x', G.one))
S_yF = sum(1 << i for i in yid)
phi = h[1 << yid[0]] + h[S_yF | (1 << x1)] - h[S_yF]
out = dict(group=sys.argv[1], E=[str(e) for e in E], F=[str(f) for f in F], X=[str(g) for g in X], Y=[str(g) for g in Y], m=len(X), d=int(scale), sizes=[int(h[1 << i] * scale) for i in yid],
           reads=reads, h={str(S): int(h[S] * scale) for S in range(N)}, phi=str(phi), scale=int(scale))
json.dump(out, open(sys.argv[4], 'w'))
with open(sys.argv[4][:-5] + '.txt', 'w') as fo:
    fo.write('%d %d %d\n' % (out['m'], out['d'], len(out['sizes'])))
    for sz, rd in zip(out['sizes'], reads):
        fo.write('%d %d %s\n' % (sz, len(rd), ' '.join(map(str, rd))))
    fo.write(' '.join(str(out['h'][str(S)]) for S in range(N)) + '\n')
print('phi', phi, 'scale', scale, 'sizes', out['sizes'], 'h(all)', out['h'][str(N - 1)])
