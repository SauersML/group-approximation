"""Export Bbar_e = <b,d> as its right regular permutation representation for GAP.

Reads ck<e>/L<K>.npz (levels_ck.py, a stable level, so G_K = Bbar_e). Point g (1-based g+1) goes to
g o b, resp. g o d. GAP permutations act on the right, so b -> Pb, d -> Pd is a homomorphism
(an isomorphism onto Group(Pb, Pd)).
usage: python3 qbexport.py e K   -> bbar_e<e>.g
"""
import sys
import numpy as np
e = int(sys.argv[1]); K = int(sys.argv[2])
z = np.load('ck%d/L%d.npz' % (e, K)); z0 = np.load('ck%d/L%d.npz' % (e, K - 1))
assert len(z['Rb']) == len(z0['Rb']), "not a stable level"
with open('bbar_e%d.g' % e, 'w') as f:
    f.write('# qbexport.py %d %d: right regular representation of Bbar_%d, order %d\n' % (e, K, e, len(z['Rb'])))
    f.write('BbarOrder:=%d;;\nBbarPerms:=[\n' % len(z['Rb']))
    for R in (z['Rb'], z['Rd']):
        f.write('PermList([' + ','.join(str(int(x) + 1) for x in R) + ']),\n')
    f.write('];;\n')
