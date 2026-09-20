"""Where does rank 2 enter the k = 1 relative-inertia statement?

For a one-pair join J = fold(Gamma_X / u~w) with X <= B, let P be the based
component of Gamma_J x Gamma_B (Y = J cap B = pi_1 P), m = (q, f) : Gamma_X -> P
and Z = pi_1(m Gamma_X).
  (A) image claim   Z = Y
  (B) one-pair claim Z = fold(Gamma_X / x~x') for one m-fibre pair
  viol              rk(Y : X) > 1   (exact, relrank_le1 of census.py)
Hosts: random malnormal B of rank r (r = 2, 3), or non-malnormal rank 2.
X: finite index in B (point stabiliser of a random transitive action of the
free basis), or a random f.g. subgroup <words in the basis> ('sub').

usage: ab_split.py seed trials rank mal(1|0) xmode(fi|sub) [cap]
"""
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', 'fpbs-overfold-malnormal-host-census-2026-09-17'))
from census import (fold, graph_of, rank, canon, compact, pullback,  # noqa
                    image_map, is_malnormal, rand_word, relrank_le1,
                    rand_transitive_action, fi_subgroup, reduce_word, INV)


def rand_host(rng, r, want, Lmin=3, Lmax=7):
    while True:
        ws = [rand_word(rng.randint(Lmin, Lmax), rng) for _ in range(r)]
        n, E = compact(*graph_of(ws))
        if rank(n, E) != r:
            continue
        full = all(sum(1 for e in E if e[0] == x) == 2 and
                   sum(1 for e in E if e[2] == x) == 2 for x in range(n))
        if full:
            continue
        if is_malnormal(n, E) == want:
            return ws, (n, E)


def subst_word(w, ws):
    """Word over abstract letters 0..r-1 (+/-) -> word over a,b."""
    out = ''
    for (i, s) in w:
        v = ws[i]
        if s < 0:
            v = ''.join(INV[c] for c in reversed(v))
        out += v
    return reduce_word(out)


def rand_X(ws, rng, mode, nmax=6):
    r = len(ws)
    if mode == 'fi':
        n = rng.randint(2, nmax)
        perms = rand_transitive_action(r, n, rng)
        return fi_subgroup(ws, perms), ('fi', n, perms)
    k = rng.randint(1, 3)
    gens = []
    for _ in range(k):
        L = rng.randint(1, 4)
        w = []
        while len(w) < L:
            t = (rng.randrange(r), rng.choice((1, -1)))
            if w and w[-1][0] == t[0] and w[-1][1] == -t[1]:
                continue
            w.append(t)
        gens.append(subst_word(w, ws))
    gens = [g for g in gens if g]
    if not gens:
        gens = [ws[0]]
    return compact(*graph_of(gens)), ('sub', gens)


def analyse(nx, Ex, nB, EB, u, w):
    """Return (Yneq, okA, okB, relrank result, ranks)."""
    m, F, _ = fold(nx, Ex, [(u, w)])
    ny, Ey = compact(*pullback(m, F, nB, EB))
    cy = canon(ny, Ey)
    if cy == canon(nx, Ex):
        return None
    mm = image_map(nx, Ex, ny, Ey)
    fib = {}
    for v, im in mm.items():
        fib.setdefault(im, []).append(v)
    pairs = [(vs[0], v) for vs in fib.values() for v in vs[1:]]
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
    rr = relrank_le1(nx, Ex, ny, Ey, cy)
    return okA, okB, rr, (rank(nx, Ex), rank(ny, Ey), rank(mz, Fz))


def main(seed, T, r, mal, xmode, cap=60):
    rng = random.Random(seed)
    st = dict(inst=0, Yneq=0, A_fail=0, B_fail=0, viol=0, viol_Aok=0,
              viol_Bok=0)
    for t in range(T):
        ws, (nB, EB) = rand_host(rng, r, bool(mal))
        (nx, Ex), desc = rand_X(ws, rng, xmode)
        if nx > cap or rank(nx, Ex) < 1:
            continue
        st['inst'] += 1
        seen = set()
        for u in range(nx):
            for w in range(u + 1, nx):
                m, F, _ = fold(nx, Ex, [(u, w)])
                c = canon(m, F)
                if c in seen:
                    continue
                seen.add(c)
                res = analyse(nx, Ex, nB, EB, u, w)
                if res is None:
                    continue
                okA, okB, rr, rks = res
                st['Yneq'] += 1
                st['A_fail'] += (not okA)
                st['B_fail'] += (not okB)
                if rr is None:
                    st['viol'] += 1
                    st['viol_Aok'] += okA
                    st['viol_Bok'] += okB
                if (not okA) or rr is None:
                    print('CASE A=%s B=%s rr=%s host=%s X=%s pair=(%d,%d) '
                          'rk X,Y,Z=%s' % (okA, okB, rr, ws, desc, u, w, rks),
                          flush=True)
    print('ab_split seed=%d r=%d mal=%d xmode=%s' % (seed, r, mal, xmode), st,
          flush=True)


if __name__ == '__main__':
    a = sys.argv[1:]
    main(int(a[0]), int(a[1]), int(a[2]), int(a[3]), a[4],
         *(int(x) for x in a[5:6]))
