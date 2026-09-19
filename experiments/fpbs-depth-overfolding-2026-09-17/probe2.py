"""Single merges on Gamma_{j+1}(Q): closure sizes, lawful versus overfolding.

A pair (u, v) in one fibre is lawful when u, v have the same image in
Gamma_j(Q); otherwise it is an overfolding merge.
Usage: python3 probe2.py n j trials seed
"""
import random
import sys
from foldlib import random_q, depth_graphs, closure, contains_kernel

n, j, trials, seed = [int(x) for x in sys.argv[1:5]]
rng = random.Random(seed)
PA, PB = random_q(n, rng)
Gj, Gj1, m = depth_graphs(PA, PB, j)
fib = {}
for v in range(Gj1.V):
    fib.setdefault(Gj1.over[v], []).append(v)
nker = len(set(m))
print('V(Gamma_j+1)', Gj1.V, 'V(Gamma_j)', nker, 'n', n)
for _ in range(trials):
    y = rng.randrange(n)
    u, v = rng.sample(fib[y], 2)
    law = m[u] == m[v]
    cls = closure(Gj1, [(u, v)])
    ncl = len(set(cls))
    ck = contains_kernel(Gj1, cls, m)
    print('lawful' if law else 'over  ', 'classes', ncl, 'contains ker', ck)
