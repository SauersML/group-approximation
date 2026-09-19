"""Fibred two-cluster shadows: sub-arrangements of B_V u B_V' (two fibred I_2(5) flats) in which l_x IS modular.

twoflat.py (w9-042) showed l_x is not modular in B_V u B_V' : two pairs (q, q') of extra fibre points of V and V'
collide on hyperplanes that are not H_4 walls.  common.py shows the other two pairs collide on an A_z wall.
Here: for each pair of flats and each choice of one extra point a of V and one b of V' (besides the shared
point o14), test whether the fibre set  {p1,p2,p3, o14, a, b}  has all pairwise collisions on walls of A_x.
For the good choices print the collision incidences (which pairs collide on which wall), the rigid
sub-clusters (walls on which >= 3 points collide simultaneously), the double collisions, the affine rank of
the fibre normals, and the real order of the fibre points at the base point used in i25cluster.py.
Run: python3 twocluster.py > twocluster.log"""
import itertools, os, sys
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'h4-case1-fibred-quotient-2026-09-17'))
from fibred import setup, through, walls, is_wall
import common as CM

W, x, Ax, Az, name, idx, flats = CM.W, CM.x, CM.Ax, CM.Az, CM.name, CM.idx, CM.flats
b0 = x + 1e-3 * (CM.om[1] + CM.om[2] + CM.om[3])


def analyse(fib):
    fibw = [W[k] if np.dot(W[k], x) > 0 else -W[k] for k in fib]
    inc = {}
    for (i, u), (j, v) in itertools.combinations(enumerate(fibw), 2):
        k = idx(np.dot(v, x) * u - np.dot(u, x) * v)
        if k is None or not is_wall(W[k], Ax):
            return None
        inc.setdefault(k, []).append((name(fib[i]), name(fib[j])))
    return inc, fibw


for i, j in itertools.combinations(range(len(flats)), 2):
    fi = [idx(f) for f in flats[i][1]]; fj = [idx(f) for f in flats[j][1]]
    shared = [k for k in fi if k in fj]
    ai = [k for k in fi if k not in fj]; aj = [k for k in fj if k not in fi]
    qi = [k for k in ai if name(k)[0] == 'o']; qj = [k for k in aj if name(k)[0] == 'o']
    for a in qi:
        for b in qj:
            fib = shared + [a, b]
            r = analyse(fib)
            if r is None:
                print('V%d,V%d  extra %s,%s : NOT fibred' % (i, j, name(a), name(b)))
                continue
            inc, fibw = r
            pos = {name(k): -np.dot(w, b0) / np.dot(w, x) for k, w in zip(fib, fibw)}
            print('V%d,V%d  extra %s,%s : fibred; %d fibre points %s, %d collision walls'
                  % (i, j, name(a), name(b), len(fib), [name(k) for k in fib], len(inc)))
            for k, prs in sorted(inc.items(), key=lambda t: -len(t[1])):
                pts = sorted(set(sum(prs, ())))
                kind = ('cluster' if len(pts) >= 3 and len(prs) == len(pts) * (len(pts) - 1) // 2
                        else ('double' if len(prs) > 1 else 'single'))
                print('    wall %-4s %-7s %s' % (name(k), kind, prs))
            print('    rank of fibre normals together with x: %d' % np.linalg.matrix_rank(np.array(fibw + [x]), tol=1e-8))
            print('    real order at base point:', sorted(pos, key=lambda s: pos[s]), '< t')
