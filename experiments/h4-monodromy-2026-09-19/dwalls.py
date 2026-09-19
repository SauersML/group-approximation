# Collision walls of the l_X fibration: puncture r sits at z_r = -B(r,q)/r_1, so z_r = z_r' on the
# hyperplane with normal n = r/r_1 - r'/r'_1 (an X-space vector).  Normals not proportional to an
# X-root are the D-walls.  Report which D-walls contain the rank-2 X-flats L_23, L_24, L_34.
import sys; sys.path.insert(0, sys.path[0])
from mono import *
A = Arr('H4'); nx = A.nonX
def key(n):
    n = n / n[np.argmax(np.abs(n) > 1e-9)]; return tuple(np.round(n, 6))
Xk = {key(r) for r in A.X}; D = {}
for p in range(len(nx)):
    for q in range(p + 1, len(nx)):
        n = nx[p] / nx[p][0] - nx[q] / nx[q][0]
        if np.abs(n).max() < 1e-9: continue
        k = key(n)
        if k not in Xk: D.setdefault(k, []).append((p, q))
print('distinct D-walls', len(D), ' bad pairs', sum(len(v) for v in D.values()))
for (i, j) in ((1, 2), (1, 3), (2, 3)):
    hits = [k for k in D if all(abs(k[t]) < 1e-9 for t in range(4) if t not in (i, j))]
    print('flat L_%d%d lies in %d D-walls:' % (i + 1, j + 1, len(hits)), hits, [len(D[k]) for k in hits])
