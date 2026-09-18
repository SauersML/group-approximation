"""Two-face pivot path P -> [F1] -> [F2] -> rho P for even n (generalising the best n = 8 path), optimised.

F1 = {34,...,(n-3)(n-2)} < {12(n-1)n, 34, ..., (n-3)(n-2)},  F2 = {1n} < {1n, 23...(n-1)}.
Blocks are written with base-36 digits (1..9, a = 10, ...). Usage: python3 gen_path.py n [restarts]
"""
import sys, math
import refine
from ncp_lib import *

D = '123456789abcdefghijklmnopqrstuvwxyz'


def part(blks, n):
    groups = [tuple(D.index(c) for c in b) for b in blks]
    return canon(groups + [(i,) for i in range(n) if not any(i in g for g in groups)], n)


n = int(sys.argv[1]); restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 8
pairs = [D[2 * t] + D[2 * t + 1] for t in range(n // 2)]
P = part(pairs, n)
Q = part([D[2 * t + 1] + D[(2 * t + 2) % n] for t in range(n // 2)], n)
mid = pairs[1:-1]
F1 = (part(mid, n), part(mid + [pairs[0] + pairs[-1]], n))
F2 = (part([D[0] + D[n - 1]], n), part([D[0] + D[n - 1], D[1:n - 1]], n))
faces = [(P,), F1, F2, (Q,)]
for f, g in zip(faces, faces[1:]):
    assert refine.common_tree(list(f) + list(g), n) is not None, (f, g)
cosd = refine.make(n)
one = math.acos(cosd(P, part([D[0] + D[1]], n))) + math.acos(cosd(part([D[0] + D[1]], n), Q))
L, lams = refine.optimise(faces, n, restarts=restarts)
print('n', n, 'one-pivot {12}:', round(one / math.pi, 6), 'pi | two-face path:', round(L / math.pi, 6), 'pi',
      'd_B(P,Q)', round(math.acos(cosd(P, Q)) / math.pi, 6), 'pi', flush=True)
for f, lam in zip(faces, lams):
    print('  ', [(refine.fmt(v), round(float(l), 4)) for v, l in zip(f, lam)])
