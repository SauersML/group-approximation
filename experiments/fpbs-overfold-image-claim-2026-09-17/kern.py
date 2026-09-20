"""Normal finite-index layer of (RI_B) at k = 1.

X = ker(B -> G) for a random finite quotient G (regular action of random
permutations of the free basis of B).  Then Z = Y for every join (Gamma_X ->
Gamma_B is a cover, the image claim is automatic), Y/X = H <= G, and
rk(Y : X) <= 1  iff  H is cyclic.  We test every one-pair join exactly.

usage: kern.py seed trials host(mal2|mal3|nonmal2) [cap]
"""
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ab_split import rand_host  # noqa: E402
from census import (fold, rank, canon, compact, pullback, relrank_le1,  # noqa
                    regular_action, fi_subgroup)


def rand_kernel(ws, rng):
    r = len(ws)
    while True:
        m = rng.randint(3, 5)
        perms = []
        for _ in range(r):
            p = list(range(m))
            rng.shuffle(p)
            perms.append(p)
        reg = regular_action(perms)
        if reg is None or len(reg[0]) < 4 or len(reg[0]) > 60:
            continue
        return fi_subgroup(ws, reg), len(reg[0]), perms


def main(seed, T, kind, cap=260):
    rng = random.Random(seed)
    st = dict(inst=0, Yneq=0, viol=0, Ytop=0)
    for t in range(T):
        mal = kind != 'nonmal2'
        r = 3 if kind == 'mal3' else 2
        ws, (nB, EB) = rand_host(rng, r, mal)
        (nx, Ex), order, perms = rand_kernel(ws, rng)
        if nx > cap:
            continue
        st['inst'] += 1
        cx = canon(nx, Ex)
        cB = canon(nB, EB)
        seen = set()
        for w in range(1, nx):
            # u = 0 is enough up to the deck group only when the base is
            # the unique vertex over its image; test all pairs to be safe
            for u in range(0, w):
                m, F, _ = fold(nx, Ex, [(u, w)])
                c = canon(m, F)
                if c in seen:
                    continue
                seen.add(c)
                ny, Ey = compact(*pullback(m, F, nB, EB))
                cy = canon(ny, Ey)
                if cy == cx:
                    continue
                st['Yneq'] += 1
                st['Ytop'] += (cy == cB)
                if relrank_le1(nx, Ex, ny, Ey, cy) is None:
                    st['viol'] += 1
                    print('KVIOL host=%s |G|=%d perms=%s pair=(%d,%d) '
                          'rk X,Y=%d,%d' % (ws, order, perms, u, w,
                                            rank(nx, Ex), rank(ny, Ey)),
                          flush=True)
    print('kern seed=%d host=%s' % (seed, kind), st, flush=True)


if __name__ == '__main__':
    a = sys.argv[1:]
    main(int(a[0]), int(a[1]), a[2], *(int(x) for x in a[3:4]))
