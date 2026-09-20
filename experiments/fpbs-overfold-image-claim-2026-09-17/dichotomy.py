"""Image dichotomy test.

For J = fold(Gamma_X / pairs) (npairs = k), P = based component of
Gamma_J x Gamma_B, Y = pi_1 P = J cap B, m : Gamma_X -> P, Z = pi_1(m Gamma_X).
Z is the pi_1 of a based subgraph of P, hence a FREE FACTOR of Y, so
    rk(Y : X) <= (rk Y - rk Z) + rk(Z : X),
and for rk B = 2 the strengthened Hanna Neumann inequality gives rk Y <= rk J.
Classify every join with Y != X:
    ZX    Z = X   (then rk(Y:X) <= rk Y - rk X <= rk J - rk X <= k by SHN)
    ZY    Z = Y   (then rk(Y:X) = rk(Z:X): the one-fibre claim (B))
    MIX   X < Z < Y
and for k = 1 also record the exact rk(Y:X) <= 1 test.

hosts: mal2 | nonmal2 | mal3 | L1 | L1overL2 | L2overL3
xmode: fi (finite index in the sub-host C) | sub (random f.g. subgroup of C)
usage: dichotomy.py seed trials host xmode npairs [samples] [cap]
"""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ab_split import rand_host, rand_X  # noqa: E402
from census import (fold, graph_of, rank, canon, compact, pullback,  # noqa
                    image_map, relrank_le1, phij)


def get_host(kind, rng):
    if kind == 'mal2':
        ws, g = rand_host(rng, 2, True)
        return ws, g, ws
    if kind == 'nonmal2':
        ws, g = rand_host(rng, 2, False)
        return ws, g, ws
    if kind == 'mal3':
        ws, g = rand_host(rng, 3, True)
        return ws, g, ws
    if kind == 'L1':
        ws = ['a', phij('b', 1)]
        return ws, compact(*graph_of(ws)), ws
    if kind == 'L1overL2':
        ws = ['a', phij('b', 1)]
        return ws, compact(*graph_of(ws)), ['a', phij('b', 2)]
    if kind == 'L2overL3':
        ws = ['a', phij('b', 2)]
        return ws, compact(*graph_of(ws)), ['a', phij('b', 3)]
    raise ValueError(kind)


def classify(nx, Ex, nB, EB, prs):
    m, F, _ = fold(nx, Ex, prs)
    nj, Ej = m, F
    ny, Ey = compact(*pullback(m, F, nB, EB))
    cy, cx = canon(ny, Ey), canon(nx, Ex)
    if cy == cx:
        return None
    mm = image_map(nx, Ex, ny, Ey)
    fib = {}
    for v, im in mm.items():
        fib.setdefault(im, []).append(v)
    pairs = [(vs[0], v) for vs in fib.values() for v in vs[1:]]
    mz, Fz, _ = fold(nx, Ex, pairs)
    cz = canon(mz, Fz)
    if cz == cx:
        cls = 'ZX'
    elif cz == cy:
        cls = 'ZY'
    else:
        cls = 'MIX'
    rks = (rank(nx, Ex), rank(*compact(nj, Ej)), rank(ny, Ey), rank(mz, Fz))
    return cls, rks, (ny, Ey, cy), (mz, Fz)


def main(seed, T, kind, xmode, npairs, samples=40, cap=80):
    rng = random.Random(seed)
    st = dict(inst=0, Yneq=0, ZX=0, ZY=0, MIX=0, shn_fail=0, viol1=0,
              mix_viol1=0)
    for t in range(T):
        Bws, (nB, EB), Cws = get_host(kind, rng)
        (nx, Ex), desc = rand_X(Cws, rng, xmode)
        if nx > cap or rank(nx, Ex) < 1:
            continue
        st['inst'] += 1
        seen = set()
        if npairs == 1:
            joins = [[(u, w)] for u in range(nx) for w in range(u + 1, nx)]
        else:
            joins = [[tuple(rng.sample(range(nx), 2)) for _ in range(npairs)]
                     for _ in range(samples)]
        for prs in joins:
            m, F, _ = fold(nx, Ex, prs)
            c = canon(m, F)
            if c in seen:
                continue
            seen.add(c)
            res = classify(nx, Ex, nB, EB, prs)
            if res is None:
                continue
            cls, rks, (ny, Ey, cy), _ = res
            st['Yneq'] += 1
            st[cls] += 1
            rX, rJ, rY, rZ = rks
            if rY > max(rJ, 1):
                st['shn_fail'] += 1
            v1 = None
            if npairs == 1:
                v1 = relrank_le1(nx, Ex, ny, Ey, cy)
                if v1 is None:
                    st['viol1'] += 1
                    if cls == 'MIX':
                        st['mix_viol1'] += 1
            if cls == 'MIX' or (npairs == 1 and v1 is None):
                print('CASE %s rr=%s host=%s X=%s prs=%s rk X,J,Y,Z=%s'
                      % (cls, v1, Bws, desc, prs, rks), flush=True)
    print('dichotomy seed=%d host=%s xmode=%s k=%d' % (seed, kind, xmode,
                                                        npairs), st, flush=True)


if __name__ == '__main__':
    a = sys.argv[1:]
    main(int(a[0]), int(a[1]), a[2], a[3], int(a[4]),
         *(int(x) for x in a[5:7]))
