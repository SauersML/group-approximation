#!/usr/bin/env python3
"""Write the relaxed linear-realization problem of a minimal-window configuration.

usage: relaxed_target.py GROUP 'E' 'F' out.txt
  GROUP: integer n (cyclic Z/n; E, F comma lists) or a torsion2_scan group name (E, F Python literals).

Unlike extract_fake.py this does not fix the LP vertex. It records only
  * the reads of each codeword (blocks of x_(fE)),
  * the translation classes of subsets (d['col'] of shannon_lp.build): (T) asks rank to be constant on a class,
  * the masks entering Phi = h(y_f0) + h(x_1 y_F) - h(y_F).
File format:
  m r
  nread idx...                         (r lines)
  col[S] for S = 0 .. 2^(m+r)-1
  mask_y0 mask_x1yF mask_yF
"""
import sys, os, ast
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'shannon-window-certificates-2026-09-17'))
sys.path.insert(0, os.path.join(HERE, '..', 'promislow-shannon-windows-2026-09-17'))
from random_scan import Cyc
from shannon_lp import build

if sys.argv[1].isdigit():
    G = Cyc(int(sys.argv[1]))
    E = [int(t) for t in sys.argv[2].split(',')]
    F = [int(t) for t in sys.argv[3].split(',')]
else:
    from torsion2_scan import group
    G = group(sys.argv[1])[0]
    E = ast.literal_eval(sys.argv[2]); F = ast.literal_eval(sys.argv[3])
d = build(G, E, F)
items = d['items']
X = [g for (k, g) in items if k == 'x']
Y = [g for (k, g) in items if k == 'y']
m, r = len(X), len(Y)
assert items == [('x', g) for g in X] + [('y', g) for g in Y]
reads = [[X.index(G.mul(g, e)) for e in E] for g in Y]
N = 1 << (m + r)
yF = sum(1 << (m + j) for j in range(r))
x1 = 1 << X.index(G.one)
with open(sys.argv[4], 'w') as fo:
    fo.write('%d %d\n' % (m, r))
    for rd in reads:
        fo.write('%d %s\n' % (len(rd), ' '.join(map(str, rd))))
    fo.write(' '.join(str(int(d['col'][S])) for S in range(N)) + '\n')
    fo.write('%d %d %d\n' % (1 << m, yF | x1, yF))
print('m', m, 'r', r, 'classes', d['nv'], 'X', [G.show(g) for g in X], 'Y', [G.show(g) for g in Y])
