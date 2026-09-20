#!/usr/bin/env python3
"""Machine check of the absorbed-block homomorphism theta (see absorbed_block.py).

theta : PLB_{n-2} (rings [n] minus {v,w}, ring c kept) -> P = PLB_n,
  A_ij -> A_ij,  A_kc -> A_kc,  A_cj -> B_j := A_cj A_vj A_wj.
Checks, for n = 6, 7 and (v,w,c) = (1,2,3):
  (a) theta kills every McCool relator [A_ij,A_kl], [A_ij,A_kj], [A_ij A_kj, A_ik] on the rings
      other than v, w (all index tuples), so theta is a homomorphism;
  (b) theta(generators) commute with A_vc and A_wc;
  (c) random vertices g[u], g in P_vw, u of type meeting c: count those passing the rank test
      against A_vc b0 (evidence that L has no vertex of type meeting c).
(pi o theta = id is immediate: killing x_v, x_w turns B_j into A_cj.)
"""
import itertools
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'loop-braid-bfmwz-push-2026-09-17'))
import mutual_link as M  # noqa: E402
import one_ring_push as O  # noqa: E402
import random  # noqa: E402


def theta(i, j, n, v, w, c):
    if i == c:
        return M.mul(M.mul(M.A(c, j, n), M.A(v, j, n), n), M.A(w, j, n), n)
    return M.A(i, j, n)


def comm(x, y, n):
    return M.mul(M.mul(x, y, n), M.mul(M.inverse(x), M.inverse(y), n), n)


def is_id(x, n):
    return M.same(x, (M.ident(n), M.ident(n)), n)


def main():
    allok = True
    for n in (6, 7):
        v, w, c = 1, 2, 3
        R = [i for i in range(1, n + 1) if i not in (v, w)]
        T = {(i, j): theta(i, j, n, v, w, c) for i in R for j in R if i != j}
        ok1 = all(is_id(comm(T[(i, j)], T[(k, l)], n), n)
                  for (i, j, k, l) in itertools.permutations(R, 4))
        ok2 = all(is_id(comm(T[(i, j)], T[(k, j)], n), n)
                  for (i, j, k) in itertools.permutations(R, 3))
        ok3 = all(is_id(comm(M.mul(T[(i, j)], T[(k, j)], n), T[(i, k)], n), n)
                  for (i, j, k) in itertools.permutations(R, 3))
        hs = [M.A(v, c, n), M.A(w, c, n)]
        ok4 = all(is_id(comm(t, h, n), n) for t in T.values() for h in hs)
        print('n=%d: theta kills [A_ij,A_kl]: %s; [A_ij,A_kj]: %s; [A_ij A_kj, A_ik]: %s; '
              'theta(gens) commute with A_vc, A_wc: %s' % (n, ok1, ok2, ok3, ok4))
        allok &= ok1 and ok2 and ok3 and ok4
        # (c) types meeting c: vertices g[(c,j)], g[(j,c)] with g a random word in gens(P_vw);
        # count how many pass the rank test against b0' = A_vc b0 (conjecture: none is in L).
        gens = [x for _, x in M.cabling_gens((v, w), n)]
        e = (M.ident(n), M.ident(n))
        h = M.A(v, c, n)
        rng = random.Random(7 + n)
        ctypes = [(c, j) for j in R if j != c] + [(j, c) for j in R if j != c]
        std = O.I(e, (4, 5), e, (v, w), n)
        passed, total, stdc = 0, 0, set()
        for u in ctypes:
            stdc.add(O.I(e, u, e, (v, w), n))
        for length in (0, 1, 2, 3):
            for _ in range(30 if length else 1):
                g = e
                for _ in range(length):
                    x = rng.choice(gens)
                    g = M.mul(g, x if rng.random() < 0.5 else M.inverse(x), n)
                for u in ctypes:
                    total += 1
                    passed += O.I(g, u, h, (v, w), n) in stdc
        print('n=%d: vertices g[type meeting c], g in P_vw: rank(C_u cap C_vw) = %s; '
              'passing the rank test against A_vc b0: %d of %d' % (n, sorted(stdc), passed, total))
    print('ALL CHECKS PASSED' if allok else 'SOME CHECK FAILED')


if __name__ == '__main__':
    main()
