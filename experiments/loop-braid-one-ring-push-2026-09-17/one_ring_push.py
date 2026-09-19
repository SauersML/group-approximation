#!/usr/bin/env python3
"""One-ring pushes in the loop braid descending link: a free-factor adjacency invariant.

Setting (w8 artifact zp-loop-braid-forbidden-ring-push-reduction-2026-09-17.md, Section 7).
  A vertex of X_n of type u = (a,b) is a coset p P_u, P_u the cabling subgroup
  (generators as in mutual_link.py).  Put C_u := <x_a x_b, x_k (k != a,b)> <= F_n.

  (S) P_u stabilises C_u (checked on generators and inverses), so
        I(p P_u, q P_z) := rank( p(C_u) cap q(C_z) )
      is well defined on pairs of vertices and invariant under the left P-action.
      If p P_u and q P_z are adjacent, then (p P_u, q P_z) = r (P_u, P_z) for some r, so
        I = I_std(u, z) := rank(C_u cap C_z).
      So I != I_std certifies NON-adjacency.  (It never certifies adjacency.)

Checks:
  (0) (S) on generators, and I_std for disjoint types;
  (1) calibration on the model-artifact clasp: [1,(1,2)] and [A(1,3)^{+-1} or A(3,1)^{+-1}, (3,4)];
  (2) one-ring push b0 = [(v,w)], b0' = h[(v,w)], h in {A(v,c), A(w,c)}^{+-1}; for vertices
      u = g[(a,b)] with g in P_{(v,w)} (so u in lk(b0)) and {a,b} disjoint from {v,w,c},
      compute I(u, b0'); a nonstandard value shows u is NOT in lk(b0').
"""
import itertools
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'loop-braid-bfmwz-push-2026-09-17'))
import mutual_link as M  # noqa: E402
from stallings import Graph, intersect  # noqa: E402


def C_gens(u, n):
    a, b = u
    return [(a, b)] + [(k,) for k in range(1, n + 1) if k not in (a, b)]


def image_subgroup(g, u, n):
    """Stallings graph of g(C_u), g = (phi, phi^{-1})."""
    return Graph([M.apply(g[0], w) for w in C_gens(u, n)])


def I(p, u, q, z, n):
    return intersect(image_subgroup(p, u, n), image_subgroup(q, z, n)).rank()


def ident_elt(n):
    return (M.ident(n), M.ident(n))


def check_S(n, u):
    Cu = Graph(C_gens(u, n))
    ok = True
    for name, h in M.cabling_gens(u, n):
        for phi in h:
            ok &= all(Cu.contains(M.apply(phi, w)) for w in C_gens(u, n))
    return ok


def main():
    rng = random.Random(20260919)
    out = []
    allok = True
    # ---------------------------------------------------------------- (0)
    for n in (6, 7, 8):
        s = all(check_S(n, u) for u in itertools.permutations(range(1, n + 1), 2))
        e = ident_elt(n)
        std = sorted({I(e, u, e, z, n) for u in itertools.permutations(range(1, n + 1), 2)
                      for z in itertools.permutations(range(1, n + 1), 2)
                      if not set(u) & set(z)})
        out.append('(0) n=%d: P_u stabilises C_u for all u: %s; I_std(disjoint) values %s'
                   % (n, s, std))
        allok &= s
    # ---------------------------------------------------------------- (1)
    n = 6
    e = ident_elt(n)
    base = I(e, (1, 2), e, (3, 4), n)
    for nm, g in (('A13', M.A(1, 3, n)), ('A13^-1', M.inverse(M.A(1, 3, n))),
                  ('A31', M.A(3, 1, n)), ('A31^-1', M.inverse(M.A(3, 1, n))),
                  ('A14', M.A(1, 4, n)), ('A32', M.A(3, 2, n))):
        v = I(e, (1, 2), g, (3, 4), n)
        out.append('(1) n=6: I([1,(1,2)], [%s,(3,4)]) = %d  (std %d)  %s'
                   % (nm, v, base, 'NON-ADJACENT' if v != base else 'undecided'))
    # sanity: adjacent pairs r[(1,2)], r g[(3,4)] with r random, g in P_(1,2) P_(3,4)
    P12, P34 = M.cabling_gens((1, 2), n), M.cabling_gens((3, 4), n)
    allg = [h for _, h in M.cabling_gens((1, 2), n)] + [M.A(i, j, n) for i in range(1, n + 1)
                                                       for j in range(1, n + 1) if i != j]
    sane = True
    for _ in range(40):
        g = M.mul(M.random_product(P12, 3, n, rng), M.random_product(P34, 3, n, rng), n)
        r = M.random_product([(str(k), h) for k, h in enumerate(allg)], 3, n, rng)
        sane &= I(r, (1, 2), M.mul(r, g, n), (3, 4), n) == base
    out.append('(1) sanity: 40 random adjacent pairs give I_std: %s' % sane)
    allok &= sane
    print('\n'.join(out))
    sys.stdout.flush()
    out = []
    # ---------------------------------------------------------------- (2)
    for n in (6, 7, 8):
        v, w, c = 1, 2, 3
        Pvw = M.cabling_gens((v, w), n)
        e = ident_elt(n)
        pushes = [('A_vc', M.A(v, c, n)), ('A_vc^-1', M.inverse(M.A(v, c, n))),
                  ('A_wc', M.A(w, c, n)), ('A_wc^-1', M.inverse(M.A(w, c, n)))]
        types = [u for u in itertools.permutations(range(1, n + 1), 2)
                 if not set(u) & {v, w, c}]
        std = I(e, types[0], e, (v, w), n)
        for pname, h in pushes:
            # single generators of P_vw first
            bad = []
            for gname, g in Pvw:
                for u in types:
                    val = I(g, u, h, (v, w), n)
                    if val != std:
                        bad.append((gname, u, val))
            # Q'-vertices must pass
            q_ok = all(I(e, u, h, (v, w), n) == std for u in types)
            out.append('(2) n=%d push %s: Q-vertices of type avoiding v,w,c pass %s; '
                       'generator vertices g[(a,b)], g in gens(P_vw), NOT in lk(b0\'): %d'
                       % (n, pname, q_ok, len(bad)))
            for b in bad[:12]:
                out.append('      %s' % (b,))
        print('\n'.join(out))
        sys.stdout.flush()
        out = []
    # ---------------------------------------------------------------- (3)
    # consistency with the ESTABLISHED w9 pair-twist mutual link: for u0 = [(a,b)], push
    # tau_br, the triple-cable subgroup T (a,b,r) gives vertices t[(c,d)] ({c,d} avoiding a,b,r)
    # in lk(u0) cap lk(tau_br u0); the rank test must pass on them.
    for n in (6, 7):
        a, b, r = 1, 2, 3
        e = ident_elt(n)
        tau = M.twist((b, r), n)
        T = M.cabling_gens((a, b, r), n)
        types = [u for u in itertools.permutations(range(1, n + 1), 2)
                 if not set(u) & {a, b, r}]
        std = I(e, types[0], e, (a, b), n)
        ok3 = True
        for _ in range(25):
            t = M.random_product(T, 3, n, rng)
            for u in types[:4]:
                ok3 &= I(t, u, e, (a, b), n) == std and I(t, u, tau, (a, b), n) == std
        out.append('(3) n=%d: w9 pair-twist mutual-link vertices pass the rank test: %s' % (n, ok3))
        allok &= ok3
    # ---------------------------------------------------------------- (4)
    # hand-checkable certificate at n = 5: v,w,c,a,b = 1,2,3,4,5;  u = A_ca[(a,b)] lies in
    # lk(b0) (A_ca in P_vw) but not in lk(A_vc b0).
    n = 5
    g, h = M.A(3, 4, n), M.A(1, 3, n)
    G1, G2 = image_subgroup(g, (4, 5), n), image_subgroup(h, (1, 2), n)
    from stallings import intersect as _int
    J = _int(G1, G2)
    e = ident_elt(n)
    out.append('(4) n=5 certificate: A_ca(C_ab) = <%s>' % ', '.join(
        str(M.apply(g[0], x)) for x in C_gens((4, 5), n)))
    out.append('    A_vc(C_vw) = <%s>' % ', '.join(str(M.apply(h[0], x)) for x in C_gens((1, 2), n)))
    out.append('    rank of intersection = %d, basis %s;  standard rank(C_ab cap C_vw) = %d'
               % (J.rank(), J.basis(), I(e, (4, 5), e, (1, 2), n)))
    out.append('    A_ca in P_vw (generator of P_vw): %s' % any(
        same(g, x) for _, x in M.cabling_gens((1, 2), n)))
    print('\n'.join(out))
    print('ALL CHECKS PASSED' if allok else 'SOME CHECK FAILED')
    return allok


def same(g, h, n=5):
    return M.same(g, h, n)


if __name__ == '__main__':
    main()
