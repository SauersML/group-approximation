"""Split the k = 1 statement into two structural sub-claims and test each.

For a one-pair join J = fold(Gamma_X / u~w), let P be the based component of
Gamma_J x Gamma_B (so Y = J cap B = pi_1(P)), and m : Gamma_X -> P the map
x -> (q(x), f(x)).  Let I = m(Gamma_X) and Z = pi_1(I) = <X, h_{x,x'} :
m(x) = m(x')>.

  (A) image claim:    Z = Y      (the extra part of P carries no new loops)
  (B) one-pair claim: Z = fold(Gamma_X / x~x') for ONE pair of an m-fibre

(A) and (B) together give rk(Y : X) <= 1.  Report, per host type, how often
each fails, among joins with Y != X.

usage: analyze.py seed trials host [npairs samples]
  npairs = 1 (default): all one-pair joins; npairs >= 2: `samples` random
  joins fold(Gamma_X / npairs random pairs) per instance.
"""
import random
import sys
from census import (host, rand_X, fold, canon, compact, pullback, rank,
                    image_map)


def joins(nx, Ex, rng, npairs, samples):
    if npairs == 1:
        for u in range(nx):
            for w in range(u + 1, nx):
                yield (u, w), [(u, w)]
    else:
        for _ in range(samples):
            ps = [tuple(rng.sample(range(nx), 2)) for _ in range(npairs)]
            yield ps[0], ps


def main(seed, T, kind, npairs=1, samples=0, cap=120):
    rng = random.Random(seed)
    st = dict(inst=0, Yneq=0, A_fail=0, B_fail=0, both_ok=0, fibre_pairs_max=0)
    for t in range(T):
        Bws, Bg, Cws = host(kind, rng)
        Xg, desc = rand_X(Cws, rng)
        nx, Ex = Xg
        if nx > cap:
            continue
        st['inst'] += 1
        nB, EB = Bg
        cx = canon(nx, Ex)
        seen = set()
        for (u, w), prs in joins(nx, Ex, rng, npairs, samples):
            if True:
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
                st['fibre_pairs_max'] = max(st['fibre_pairs_max'], len(pairs))
                mz, Fz, _ = fold(nx, Ex, pairs)
                cz = canon(mz, Fz)
                okA = (cz == cy)
                okB = False
                for vs in fib.values():
                    for i in range(len(vs)):
                        for k in range(i + 1, len(vs)):
                            m1, F1, _ = fold(nx, Ex, [(vs[i], vs[k])])
                            if canon(m1, F1) == cz:
                                okB = True
                                break
                        if okB:
                            break
                    if okB:
                        break
                if not okA:
                    st['A_fail'] += 1
                if not okB:
                    st['B_fail'] += 1
                if okA and okB:
                    st['both_ok'] += 1
                if not (okA and okB):
                    print('FAIL A=%s B=%s host=%s X=%s pair=(%d,%d) rkX=%d rkY=%d rkZ=%d'
                          % (okA, okB, Bws, desc[:2], u, w, rank(nx, Ex),
                             rank(ny, Ey), rank(mz, Fz)), prs, flush=True)
        if st['inst'] % 25 == 0:
            print('progress', kind, st, flush=True)
    print('analyze', kind, 'seed', seed, st, flush=True)


if __name__ == '__main__':
    extra = [int(x) for x in sys.argv[4:6]]
    main(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], *extra)
