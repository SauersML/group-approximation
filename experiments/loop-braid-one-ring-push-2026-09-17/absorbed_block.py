#!/usr/bin/env python3
"""Absorbed-block model for the one-ring push mutual link L = lk(b0) cap lk(A_vc b0).

b0 = [(v,w)], b0' = A_vc b0.  theta : PLB_{n-2} (rings other than v,w; ring c kept) -> P,
  A_ij -> A_ij,  A_kc -> A_kc,  A_cj -> B_j := A_cj A_vj A_wj   (block {v,w,c} through j).
pi : P -> PLB_{n-2} deletes rings v, w (kill x_v, x_w).  pi o theta = id.

For a random word g in the generators of P_vw (so u = g[(a,b)] lies in lk(b0)), with
{a,b} disjoint from {v,w,c}, the script compares
  (i)  RANK TEST: I(u, b0') == I_std   (fails  =>  u not in lk(b0'), rigorous);
  (ii) MODEL:     g(C_ab) == theta(pi(g))(C_ab)  (Stallings equality of subgroups),
where theta(pi(g)) is computed on the word: generators touching v or w are deleted and A_cj is
replaced by B_j.  If L equals the image of the absorbed-block complex, then (ii) should hold
whenever u is in L; the script records the joint distribution of (i) and (ii).
"""
import os
import random
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'loop-braid-bfmwz-push-2026-09-17'))
import mutual_link as M  # noqa: E402
from stallings import Graph  # noqa: E402
import one_ring_push as O  # noqa: E402


def gens_with_model(n, v, w, c):
    """Generators of P_vw, each with its theta(pi(.)) image (None = trivial)."""
    out = []
    others = [i for i in range(1, n + 1) if i not in (v, w)]
    for i in others:
        for j in others:
            if i == j:
                continue
            g = M.A(i, j, n)
            if i == c:
                model = M.mul(M.mul(M.A(c, j, n), M.A(v, j, n), n), M.A(w, j, n), n)
            else:
                model = g
            out.append(('A%d%d' % (i, j), g, model))
    for k in others:
        out.append(('k%d-through-cable' % k, M.conj_ring_by(k, (v, w), n), None))
        out.append(('cable-through-%d' % k, M.cable_through((v, w), k, n), None))
    return out


def same_subgroup(g1, g2, u, n):
    A = O.image_subgroup(g1, u, n)
    B = O.image_subgroup(g2, u, n)
    return (all(B.contains(M.apply(g1[0], x)) for x in O.C_gens(u, n)) and
            all(A.contains(M.apply(g2[0], x)) for x in O.C_gens(u, n)))


def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 919)
    for n in (6, 7):
        v, w, c = 1, 2, 3
        gens = gens_with_model(n, v, w, c)
        # sanity: theta images of generators lie in P_vw and commute with A_vc
        h = M.A(v, c, n)
        e = O.ident_elt(n)
        sane = all(M.nec_Pu(m, v, w, n)[0] and M.same(M.mul(h, m, n), M.mul(m, h, n), n)
                   for _, _, m in gens if m is not None)
        print('n=%d: theta(gens) pass the P_vw test and commute with A_vc: %s' % (n, sane))
        types = [(4, 5), (5, 4), (4, 6)]
        std = O.I(e, types[0], e, (v, w), n)
        tally = Counter()
        examples = {}
        for length in (1, 2, 3, 4):
            for _ in range(150 if n == 6 else 60):
                g, m = e, e
                word = []
                for _ in range(length):
                    nm, x, mx = rng.choice(gens)
                    s = rng.random() < 0.5
                    word.append(nm + ('' if s else '^-1'))
                    g = M.mul(g, x if s else M.inverse(x), n)
                    if mx is not None:
                        m = M.mul(m, mx if s else M.inverse(mx), n)
                for u in types:
                    rank_ok = O.I(g, u, h, (v, w), n) == std
                    model_ok = same_subgroup(g, m, u, n)
                    key = ('rank-pass' if rank_ok else 'rank-FAIL',
                           'model-eq' if model_ok else 'model-NEQ')
                    tally[key] += 1
                    examples.setdefault(key, (word, u))
        print('n=%d tally (rank test, model equality): %s' % (n, dict(tally)))
        for k, ex in sorted(examples.items()):
            print('   example %s: g = %s, type %s' % (k, ' '.join(ex[0]), ex[1]))
        sys.stdout.flush()


if __name__ == '__main__':
    main()
