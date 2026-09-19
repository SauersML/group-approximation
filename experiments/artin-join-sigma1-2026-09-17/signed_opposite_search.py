"""Opposite-twos 2x2 dead join (halves ac = 2, bc = q, be = 2, ae = p), representations
  A = I,  C = -I,  B = -M_d,  E = M_f
with d, f permutations in S_m satisfying (df)^2 = (fd)^2.  All Artin relations then hold
(A, C are central; (BE)^2 = (M_d M_f)^2).  The reduced criterion (Step 2) reads
  S_p(M_f) p = 0,  S_q(M_d)(t M_d + 1) p = 0,  (1 - M_d M_f)(t M_d + 1) p = 0
(the block of ac vanishes identically since 1 + AC = 0).
Positive rank iff the stacked 3m x m matrix has rank < m over F_l(t); decided by
evaluating at m + 1 values of t.  Usage: python3 signed_opposite_search.py q p m1,m2 [l]
"""
import itertools, sys
import numpy as np
from opposite_trivial_a_search import rank_mod, pmat, Smat, cycle_type


def run(q, p, m, l=101, limit=3):
    P = np.array(list(itertools.permutations(range(m))), dtype=np.int64)
    ident = P[0]

    def compose(X, Y):
        return np.take_along_axis(X, Y, axis=-1)

    def power(X, k):
        R = np.broadcast_to(ident, X.shape).copy()
        for _ in range(k):
            R = compose(R, X)
        return R

    reps = {}
    for i in range(len(P)):
        ct = cycle_type(P[i])
        if ct not in reps:
            reps[ct] = i
    I = np.eye(m, dtype=np.int64)
    found = []
    count = 0
    for ct, di in reps.items():
        D = P[di]
        if all(np.gcd(c, q) == 1 for c in ct):
            continue  # S_q(M_d) invertible: the bc block forces p = 0
        Db = np.broadcast_to(D, P.shape)
        mask = np.all(power(compose(Db, P), 2) == power(compose(P, Db), 2), axis=1)
        MD = pmat(D)
        SD = Smat(MD, q)
        for F in P[mask]:
            if all(np.gcd(c, p) == 1 for c in cycle_type(F)):
                continue
            count += 1
            MF = pmat(F)
            top = Smat(MF, p)
            X = I - MD @ MF
            full = False
            for t0 in range(1, m + 2):
                R = np.vstack([top, SD @ (t0 * MD + I), X @ (t0 * MD + I)]) % l
                if rank_mod(R, l) == m:
                    full = True
                    break
            if not full:
                found.append((D.tolist(), F.tolist()))
                if len(found) >= limit:
                    return count, found
    return count, found


if __name__ == '__main__':
    q, p = int(sys.argv[1]), int(sys.argv[2])
    ms = [int(x) for x in sys.argv[3].split(',')]
    l = int(sys.argv[4]) if len(sys.argv) > 4 else 101
    for m in ms:
        cnt, found = run(q, p, m, l)
        print(f"opposite (q,p)=({q},{p}), A=I, C=-I, B=-d, E=f in S_{m} over F_{l}: "
              f"candidates={cnt}; positive-rank found={len(found)}", flush=True)
        for f in found[:2]:
            print("  d,f =", f, flush=True)
