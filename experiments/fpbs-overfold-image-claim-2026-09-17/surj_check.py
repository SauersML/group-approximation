"""Surjective-host test of the image claim.

Z = pi_1(m Gamma_X) depends on B only through the image subgraph f(Gamma_X)
of Gamma_B, whose pi_1 is a free factor B_X of B containing X, with
Gamma_X -> Gamma_{B_X} onto.  Test whether the image claim holds for the
surjective host:  Z == J cap B_X  (call it (A_surj)).
Also re-check Z against the fibre fold for B itself (sanity) and record
rk B_X.

usage: surj_check.py seed trials host xmode npairs [samples]
"""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dichotomy import get_host, classify  # noqa: E402
from ab_split import rand_X  # noqa: E402
from census import (fold, canon, compact, pullback, rank, image_map)  # noqa


def image_subgraph(nx, Ex, nB, EB):
    """f(Gamma_X) as a based graph (renumbered), f the immersion to Gamma_B."""
    fm = image_map(nx, Ex, nB, EB)
    assert fm is not None
    E = sorted(set((fm[u], l, fm[v]) for (u, l, v) in Ex))
    verts = sorted(set(fm.values()) | {0})
    ren = {v: i for i, v in enumerate(verts)}
    assert ren[0] == 0
    return len(ren), [(ren[u], l, ren[v]) for (u, l, v) in E]


def main(seed, T, kind, xmode, npairs, samples=30):
    rng = random.Random(seed)
    st = dict(inst=0, Yneq=0, surj_fail=0, bx_rank={})
    for t in range(T):
        Bws, (nB, EB), Cws = get_host(kind, rng)
        (nx, Ex), desc = rand_X(Cws, rng, xmode)
        if nx > 80 or rank(nx, Ex) < 1:
            continue
        st['inst'] += 1
        nbx, Ebx = image_subgraph(nx, Ex, nB, EB)
        rbx = rank(*compact(nbx, Ebx))
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
            cls, rks, _, (mz, Fz) = res
            st['Yneq'] += 1
            st['bx_rank'][rbx] = st['bx_rank'].get(rbx, 0) + 1
            nyx, Eyx = compact(*pullback(m, F, nbx, Ebx))
            if canon(nyx, Eyx) != canon(mz, Fz):
                st['surj_fail'] += 1
                print('SURJFAIL cls=%s host=%s X=%s prs=%s rk X,J,Y,Z=%s '
                      'rkBX=%d rkYX=%d' % (cls, Bws, desc, prs, rks, rbx,
                                           rank(nyx, Eyx)), flush=True)
    print('surj seed=%d host=%s xmode=%s k=%d' % (seed, kind, xmode, npairs),
          st, flush=True)


if __name__ == '__main__':
    a = sys.argv[1:]
    main(int(a[0]), int(a[1]), a[2], a[3], int(a[4]),
         *(int(x) for x in a[5:6]))
