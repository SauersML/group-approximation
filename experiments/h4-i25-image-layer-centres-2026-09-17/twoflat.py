"""Is l_x modular in B_V u B_V' for two of the three fibred I2(5) flats?  Criterion (as in i25probe.py):
every pair of fibre walls (walls not containing x) collides on a wall of A_x.  Also reports the fibre
points, how the two rigid clusters share points, and the collision walls.
Run: python3 twoflat.py > twoflat.log (needs fibred.py from experiments/h4-case1-fibred-quotient-2026-09-17)."""
import itertools, numpy as np
from fibred import setup, through, walls, is_wall
n, sim, W, om = setup('H4'); x = om[0]; y = om[3]
Ax = through(W, [x]); Ay = through(W, [y]); Az = through(W, [x, y])
Ap = walls(Ax + Ay); Ayz = [w for w in Ay if not is_wall(w, Az)]; Axz = [w for w in Ax if not is_wall(w, Az)]


def modular(B):
    fib = [w for w in B if abs(np.dot(w, x)) > 1e-9]
    bad = 0
    for u, v in itertools.combinations(fib, 2):
        nv = np.dot(v, x) * u - np.dot(u, x) * v
        if not is_wall(nv, Ax):
            bad += 1
    return fib, bad


flats = []
for w1 in Ayz:
    for w2 in Axz:
        B2 = np.array([w1, w2]); P = B2.T @ np.linalg.pinv(B2.T)
        AV = [w for w in W if np.linalg.norm(P @ w - w) < 1e-9]
        if len(AV) != 5:
            continue
        fib, bad = modular(walls(Ap + AV))
        if bad == 0 and not any(all(is_wall(a, F) for a in AV) for F in flats):
            flats.append(AV)
print('good I2(5) flats', len(flats))
for i, j in itertools.combinations(range(len(flats)), 2):
    B = walls(Ap + flats[i] + flats[j])
    fib, bad = modular(B)
    print('flats', i, j, ': walls', len(B), 'fibre points', len(fib), 'non-A_x collisions', bad,
          '-> l_x modular' if bad == 0 else '-> l_x NOT modular')
B = walls(Ap + flats[0] + flats[1] + flats[2]) if len(flats) == 3 else None
if B is not None:
    fib, bad = modular(B)
    print('all three: walls', len(B), 'fibre points', len(fib), 'non-A_x collisions', bad)

# which fibre pairs collide off A_x: label each fibre wall by origin (p = A_y \ A_z, q = flat 0/1/2 extra walls)
def label(w):
    if is_wall(w, Ayz):
        return 'p'
    for k, F in enumerate(flats):
        if is_wall(w, F):
            return 'q%d' % k
    return '?'
for i, j in itertools.combinations(range(len(flats)), 2):
    B = walls(Ap + flats[i] + flats[j])
    fib = [w for w in B if abs(np.dot(w, x)) > 1e-9]
    out = []
    for u, v in itertools.combinations(fib, 2):
        nv = np.dot(v, x) * u - np.dot(u, x) * v
        if not is_wall(nv, Ax):
            out.append((label(u), label(v), 'collision normal is a wall of H4: %s' % is_wall(nv, W)))
    print('flats', i, j, 'bad pairs', out)
