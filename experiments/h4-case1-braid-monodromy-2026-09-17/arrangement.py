"""Part 1 (exact linear algebra on the H4 root system): the 19-wall fibred augmentations B_V of
A' = A_x u A_y (V an A2 flat w cap w', w in A_y minus A_z, w' in A_x minus A_z) and the 10-wall
sub-arrangement C_V = (4 fibre walls) u (6 collision walls).

For each of the 9 flats V this checks:
  (a) the fibre map Psi: u -> (p_1(u),...,p_4(u)) mod diagonal, p_k(u) = -<n_k,u>/<n_k,v_x>, is a
      linear isomorphism l_x^perp -> C^4/C(1,1,1,1)   (the 4 fibre normals are independent);
  (b) the collision walls {p_i = p_j} are exactly 6 walls of A_x: the 3 walls of A_z and 3 walls of
      A_x minus A_z (one for each pair {p_4, p_i});
  (c) hence C_V is linearly isomorphic to the A4 braid arrangement: in the coordinates (t,p_1,..,p_4)
      mod the diagonal its 10 walls are {q_a = q_b} (see the comment in main());
  (d) whether C_V is closed under its own reflections (an A4 root subsystem) -- it is not;
  (e) which of the 12 walls of A_x minus A_z occur as collision walls for some V.
Also records the real order of p_1..p_4 and the base point t = 0 in the fundamental chamber, and
runs the same check for the two A2 flats of H3 (function h3()).
Needs fibred.py from ../h4-case1-fibred-quotient-2026-09-17/ (lane w5-042).
Run: python3 arrangement.py > arrangement.log  (seconds, numpy only)."""
import itertools, numpy as np
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'h4-case1-fibred-quotient-2026-09-17'))
from fibred import setup, through, walls, is_wall

def idx(v, W):
    v = v/np.linalg.norm(v)
    for i, w in enumerate(W):
        if abs(abs(np.dot(v, w))-1) < 1e-9: return i
    return None

def refl(r, v): return v-2*np.dot(v, r)/np.dot(r, r)*r

def flats(n, sim, W, om):
    x = om[0]; y = om[n-1]
    Ax = through(W, [x]); Ay = through(W, [y]); Az = through(W, [x, y])
    Ayz = [w for w in Ay if not is_wall(w, Az)]; Axz = [w for w in Ax if not is_wall(w, Az)]
    out = []
    for w1 in Ayz:
        for w2 in Axz:
            B2 = np.array([w1, w2]); P = B2.T@np.linalg.pinv(B2.T)
            AV = [w for w in W if np.linalg.norm(P@w-w) < 1e-9]
            if len(AV) == 3: out.append((w1, w2, AV))
    return x, y, Ax, Ay, Az, Ayz, Axz, out

def main():
    n, sim, W, om = setup('H4')
    x, y, Ax, Ay, Az, Ayz, Axz, fl = flats(n, sim, W, om)
    print('H4: |W|=%d |A_x|=%d |A_y|=%d |A_z|=%d, A2 flats V: %d' % (len(W), len(Ax), len(Ay), len(Az), len(fl)))
    # fundamental chamber point near x* = om[0]; also a point near y* = om[3]
    d = om[1]+om[2]+om[3]
    cover = {}
    for k, (w1, w2, AV) in enumerate(fl):
        third = [w for w in AV if not is_wall(w, Ax+Ay)]
        assert len(third) == 1
        fib = Ayz+third                         # p_1,p_2,p_3 from A_y minus A_z, p_4 from the new wall
        # orient normals so that <n,x> > 0
        fib = [f if np.dot(f, x) > 0 else -f for f in fib]
        rankfib = np.linalg.matrix_rank(np.array(fib))
        coll = {}
        for i, j in itertools.combinations(range(4), 2):
            u, v = fib[i], fib[j]
            nv = np.dot(v, x)*u-np.dot(u, x)*v   # p_i = p_j  <=>  <nv,u> = 0
            c = idx(nv, W)
            coll[(i, j)] = c
        colAz = all(is_wall(W[coll[(i, j)]], Az) for i, j in itertools.combinations(range(3), 2))
        col4 = [coll[(i, 3)] for i in range(3)]
        col4out = all(W[c] is not None and not is_wall(W[c], Az) and is_wall(W[c], Ax) for c in col4)
        for c in col4: cover[c] = cover.get(c, 0)+1
        C = [W[idx(f, W)] for f in fib]+[W[coll[p]] for p in coll]
        # (c) coordinates (p_1..p_4,t): in the chart v = u + t*v_x, p_k = -<n_k,u>/<n_k,x>.
        # The linear form <n_k,v> = <n_k,x>(t - p_k)  and the collision form nv_ij is a multiple of p_i - p_j.
        # So in the coordinates (q_0,...,q_4) = (t,p_1,..,p_4) the 10 walls are q_a = q_b: braid arrangement A4,
        # provided (t,p_1..p_4) mod diagonal is a coordinate system, i.e. the 4 fibre normals are independent.
        closed = all(idx(refl(a, b), C) is not None for a in C for b in C)
        # real order in the chamber at b = x + eps*d
        eps = 1e-3; b = x+eps*d
        p = [-np.dot(f, b)/np.dot(f, x) for f in fib]
        order = sorted(range(4), key=lambda i: p[i])
        eps2 = 1e-3; b2 = y+eps2*(om[0]+om[1]+om[2])
        p2 = [-np.dot(f, b2)/np.dot(f, x) for f in fib]
        order2 = sorted(range(4), key=lambda i: p2[i])
        print('V%d: rank(fibre normals)=%d  collisions among p1..p3 on A_z: %s  p4-collisions on A_x minus A_z: %s  '
              'C_V reflection-closed: %s' % (k, rankfib, colAz, col4out, closed))
        print('     order near x*: %s (all < 0: %s)   order near y*: %s (all < 0: %s)' % (
            ['p%d' % (i+1) for i in order], all(q < 0 for q in p), ['p%d' % (i+1) for i in order2], all(q < 0 for q in p2)))
    print('walls of A_x minus A_z used as p4-collision walls (index: multiplicity):', dict(sorted(cover.items())),
          ' covered %d of %d' % (len(cover), len(Axz)))

def h3():
    """Same check in H3 (X = {s2,s3} of type I2(5), Y = {s1,s2} of type A2): each of the A2 flats gives 3
    independent fibre normals and 3 collision walls (1 in A_z, 2 in A_x minus A_z), so C_V is the A3 braid
    arrangement and the shadow is a retraction onto P_4."""
    n, sim, W, om = setup('H3')
    x, y, Ax, Ay, Az, Ayz, Axz, fl = flats(n, sim, W, om)
    print('H3: |W|=%d |A_x|=%d |A_y|=%d |A_z|=%d, A2 flats V: %d' % (len(W), len(Ax), len(Ay), len(Az), len(fl)))
    for k, (w1, w2, AV) in enumerate(fl):
        third = [w for w in AV if not is_wall(w, Ax+Ay)]
        fib = [f if np.dot(f, x) > 0 else -f for f in Ayz+third]
        cs = [idx(np.dot(v, x)*u-np.dot(u, x)*v, W) for u, v in itertools.combinations(fib, 2)]
        print('V%d: rank(fibre normals)=%d  collision walls in A_z: %d  in A_x minus A_z: %d' % (
            k, np.linalg.matrix_rank(np.array(fib)), sum(is_wall(W[c], Az) for c in cs),
            sum(is_wall(W[c], Ax) and not is_wall(W[c], Az) for c in cs)))

if __name__ == '__main__':
    main()
    h3()
