"""Two-step certificate for multi-pair joins: rk(Y:X) <= rk(Y:Z) + rk(Z:X).

For J = fold(Gamma_X / npairs random pairs), Y = J cap B, Z = pi_1(m(Gamma_X))
as in analyze.py.  Certify each step with the exact rank <= 1 test
relrank_le1 ('eq' | 'arc' | 'pair' | None).  Tally the step types.  A join is
'certified' when both steps pass and the number of non-'eq' steps is
<= npairs.

usage: analyze2.py seed trials host npairs samples
"""
import random
import sys
from collections import Counter
from census import (host, rand_X, fold, canon, compact, pullback, rank,
                    image_map, relrank_le1)


def pair_then_one(nx, Ex, pairs, nz, Ez):
    """Z = <X, h1, h2>?  Try X1 = fold(X / p) over the m-fibre pairs p (and
    the pairs they generate), then the exact one-step test X1 -> Z."""
    cz = canon(nz, Ez)
    seen = set()
    for p in pairs:
        m1, F1, _ = fold(nx, Ex, [p])
        n1, E1 = compact(m1, F1)
        c1 = canon(n1, E1)
        if c1 in seen:
            continue
        seen.add(c1)
        if relrank_le1(n1, E1, nz, Ez, cz) is not None:
            return 'pair+1'
    return None


def main(seed, T, kind, npairs, samples):
    rng = random.Random(seed)
    st = Counter()
    for t in range(T):
        Bws, Bg, Cws = host(kind, rng)
        Xg, desc = rand_X(Cws, rng)
        nx, Ex = Xg
        if nx > 120:
            continue
        st['inst'] += 1
        nB, EB = Bg
        cx = canon(nx, Ex)
        seen = set()
        for _ in range(samples):
            prs = [tuple(rng.sample(range(nx), 2)) for _ in range(npairs)]
            m, F, _ = fold(nx, Ex, prs)
            c = canon(m, F)
            if c in seen:
                continue
            seen.add(c)
            ny, Ey = compact(*pullback(m, F, nB, EB))
            cy = canon(ny, Ey)
            if cy == cx:
                continue
            st['Yneq'] += 1
            mm = image_map(nx, Ex, ny, Ey)
            fib = {}
            for v, im in mm.items():
                fib.setdefault(im, []).append(v)
            pairs = [(vs[0], v) for vs in fib.values() for v in vs[1:]]
            mz, Fz, _ = fold(nx, Ex, pairs)
            nz, Ez = compact(mz, Fz)
            s1 = relrank_le1(nx, Ex, nz, Ez)
            s2 = relrank_le1(nz, Ez, ny, Ey, cy)
            if s1 is None:
                s1 = pair_then_one(nx, Ex, pairs, nz, Ez)
            st['X->Z:%s' % s1] += 1
            st['Z->Y:%s' % s2] += 1
            if s1 is not None and s2 is not None:
                steps = (s1 != 'eq') + (s2 != 'eq') + (s1 == 'pair+1')
                st['cert<=%d' % steps] += 1
                if steps > npairs:
                    print('OVER', Bws, desc[:2], prs, s1, s2, flush=True)
            else:
                st['uncert'] += 1
                print('UNCERT host=%s X=%s prs=%s rkX=%d rkZ=%d rkY=%d s1=%s s2=%s'
                      % (Bws, desc[:2], prs, rank(nx, Ex), rank(nz, Ez),
                         rank(ny, Ey), s1, s2), flush=True)
        if st['inst'] % 10 == 0:
            print('progress', kind, dict(st), flush=True)
    print('analyze2', kind, 'seed', seed, 'npairs', npairs, dict(st), flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4]),
         int(sys.argv[5]))
