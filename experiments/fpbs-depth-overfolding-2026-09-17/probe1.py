import random, sys
from foldlib import *
rng = random.Random(int(sys.argv[3]) if len(sys.argv)>3 else 1)
n = int(sys.argv[1]); j = int(sys.argv[2])
print('t_j len', len(t(j)), 't_j+1 len', len(t(j+1)))
PA, PB = random_q(n, rng)
Gj, Gj1, m = depth_graphs(PA, PB, j)
print('V(Gamma_j)', Gj.V, 'per point', Gj.V / n, ' V(Gamma_j+1)', Gj1.V, 'per point', Gj1.V / n)
img = set(m)
print('surjective on vertices', len(img) == Gj.V)
# edges surjective?
eimg = set()
for v in range(Gj1.V):
    for k, u in Gj1.nb[v].items():
        eimg.add((m[v], k, m[u]))
        assert Gj.nb[m[v]].get(k) == m[u]
etot = sum(len(Gj.nb[v]) for v in range(Gj.V))
print('surjective on edges', len(eimg) == etot, len(eimg), etot)
