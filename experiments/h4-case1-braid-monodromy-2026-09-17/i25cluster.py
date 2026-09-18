"""The three fibred I2(5) flats V of H4 (21-wall augmentations B_V, 6 fibre points): collision incidences.
For each V this prints
  - which pairs of fibre points collide on which of the 10 collision walls (all in A_x);
  - the rigid cluster: the fibre point from A_y minus A_z lying on V, together with the 3 new fibre points,
    has normals of rank 2, and all 6 pairs of it collide on ONE wall w2 of A_x minus A_z (the wall of V
    containing l_x); every other collision is a single pair;
  - the cluster shape: p_j = p_c + kappa_j * s(u) with s = <w2,u>, and the 5 walls of V give the 5 points
    {0, kappa_4, kappa_5, kappa_6, oo} of the pencil P^1; the angles between the 5 normals in the plane of V^perp
    (multiples of 36 degrees: the I2(5) pencil);
  - the real order of the 6 fibre points at the base point x + 1e-3(om2+om3+om4), with t = 0 above them.
Needs fibred.py from ../h4-case1-fibred-quotient-2026-09-17/ (lane w5-042).
Run: python3 i25cluster.py > i25cluster.log  (seconds, numpy only)."""
import itertools, numpy as np, os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'h4-case1-fibred-quotient-2026-09-17'))
from fibred import setup, through, walls, is_wall
n, sim, W, om = setup('H4'); x = om[0]; y = om[3]
Ax = through(W, [x]); Ay = through(W, [y]); Az = through(W, [x, y])
Ap = walls(Ax+Ay); Ayz = [w for w in Ay if not is_wall(w, Az)]; Axz = [w for w in Ax if not is_wall(w, Az)]
b = x+1e-3*(om[1]+om[2]+om[3])
seen = []
for w1 in Ayz:
    for w2 in Axz:
        B2 = np.array([w1, w2]); P = B2.T@np.linalg.pinv(B2.T)
        AV = [w for w in W if np.linalg.norm(P@w-w) < 1e-9]
        if len(AV) != 5: continue
        B = walls(Ap+AV); fib = [w for w in B if abs(np.dot(w, x)) > 1e-9]
        fib = [f if np.dot(f, x) > 0 else -f for f in fib]
        fib = sorted(fib, key=lambda f: 0 if is_wall(f, Ay) else 1)   # p1,p2,p3 from A_y minus A_z; p4,p5,p6 new
        coll = []; pairs = {}; ok = True
        for (i, u), (j, v) in itertools.combinations(enumerate(fib), 2):
            nv = np.dot(v, x)*u-np.dot(u, x)*v
            if not is_wall(nv, Ax): ok = False; break
            nv = nv/np.linalg.norm(nv)
            k = next((a for a, c in enumerate(coll) if abs(abs(np.dot(c, nv))-1) < 1e-9), None)
            if k is None: coll.append(nv); k = len(coll)-1
            pairs.setdefault(k, []).append((i+1, j+1))
        if not ok: continue
        print('I2(5) flat V%d: %d collision walls' % (len(seen), len(coll))); seen.append(1)
        for k in pairs:
            tag = 'A_z' if is_wall(coll[k], Az) else ('A_x-A_z' if is_wall(coll[k], Ax) else '?')
            print('   wall %d (%s): %s' % (k, tag, pairs[k]))
        big = [k for k in pairs if len(pairs[k]) > 1]
        assert len(big) == 1 and len(pairs[big[0]]) == 6 and all(len(pairs[k]) == 1 for k in pairs if k != big[0])
        cl = sorted(set(sum(pairs[big[0]], ())))
        c = cl[0]; w2v = coll[big[0]]
        print('   cluster (simultaneous collision on one wall):', ['p%d' % i for i in cl],
              ' rank of cluster normals: %d' % np.linalg.matrix_rank(np.array([fib[i-1] for i in cl]), tol=1e-8),
              ' wall of V through l_x equals the cluster wall:', any(abs(abs(np.dot(w/np.linalg.norm(w), w2v))-1) < 1e-9 for w in AV if is_wall(w, Ax)))
        # kappa_j: n_j = a_j n_c + b_j w2  =>  p_j = p_c - (b_j/a_j) <w2,u>/<n_c,x>
        nc = fib[c-1]; M = np.array([nc, w2v]).T
        kap = []
        for i in cl[1:]:
            ab = np.linalg.lstsq(M, fib[i-1], rcond=None)[0]
            assert np.linalg.norm(M@ab-fib[i-1]) < 1e-9
            kap.append(-ab[1]/ab[0]/np.dot(nc, x))
        print('   kappa (cluster shape, p_j = p_c + kappa_j s):', [0.0]+[round(float(k), 6) for k in kap])
        pl = [nc]+[fib[i-1] for i in cl[1:]]+[w2v]
        ang = sorted((np.degrees(np.arctan2(np.dot(v, w2v), np.dot(v, nc-np.dot(nc, w2v)*w2v)/np.linalg.norm(nc-np.dot(nc, w2v)*w2v)))) % 180 for v in pl)
        print('   angles of the 5 normals in the plane of V^perp (deg mod 180):', [round(float(a), 6) for a in ang])
        p = [-np.dot(f, b)/np.dot(f, x) for f in fib]
        print('   real order at b:', ['p%d' % (i+1) for i in sorted(range(6), key=lambda i: p[i])], '< t (all < 0: %s)' % all(q < 0 for q in p))
        print('   rank of all 6 fibre normals: %d' % np.linalg.matrix_rank(np.array(fib), tol=1e-8))
