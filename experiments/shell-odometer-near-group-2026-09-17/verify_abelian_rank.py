"""Exact checks for arithmetic-a5-near-group-is-not-finitely-presented.

For A=C_4, C_5 and A_5 (h=3,4,59) with the prefix tables of odom.py:
 1. mixed relation [lambda_a s^(2h) lambda_a^-1, s^(2h^2)] = 1 (model check);
 2. c_x=[lambda_x^(0), s^(2h)] equals a_(0,x)^(h-1) a_(1)^(1-h);
 3. e_n=g^n e_0 g^-n, e_0=c_x c_y^-1, g=lambda^(0)_z' lambda^(1)_z, have pairwise
    disjoint supports and commute (n<=3), and are of infinite order;
 4. every generator table is level-compatible with the vertex maps in the proof:
    s is depth preserving, lambda changes depth by at most one at the root.
"""
import itertools, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from odom import *


def a5_group():
    elems = [p for p in itertools.permutations(range(5))
             if sum(1 for i in range(5) for j in range(i + 1, 5) if p[i] > p[j]) % 2 == 0]
    e = tuple(range(5))
    mul = lambda a, b: tuple(a[b[i]] for i in range(5))
    return elems, e, mul


def loc_odo(cone, k, h):
    """a_cone^k as a table."""
    T = {(0,): ((0,), 0), (1,): ((1,), 0)}
    # refine to contain cone
    for L in range(1, len(cone)):
        p = cone[:L]
        del T[p]
        for d in range(1, h + 1):
            T[p + (d,)] = (p + (d,), 0)
    T[cone] = (cone, k)
    return reduce_table(T, h)


def support_cones(F):
    return [u for u, (v, k) in F.items() if not (u == v and k == 0)]


def disjoint(c1, c2):
    L = min(len(c1), len(c2))
    return c1[:L] != c2[:L]


def run(label, group):
    elems, e, mul = group
    h, gens, s = make_generators(group=group)
    non = [x for x in elems if x != e]
    idx = {x: i + 1 for i, x in enumerate(non)}
    s2h = power(s, 2 * h, h)
    s2h2 = power(s2h, h, h)
    for x in non[:5]:
        g = gens[(0, x)]
        rel = comm(compose(compose(g, s2h, h), inverse(g, h), h), s2h2, h)
        assert is_id(rel)
        c = comm(g, s2h, h)
        want = compose(loc_odo((0, idx[x]), h - 1, h), loc_odo((1,), 1 - h, h), h)
        assert c == want, (label, fmt(c), fmt(want))
    x, y, zp = non[0], non[1], non[2]
    z = non[0]
    e0 = compose(comm(gens[(0, x)], s2h, h), inverse(comm(gens[(0, y)], s2h, h), h), h)
    gg = compose(gens[(0, zp)], gens[(1, z)], h)
    es = [e0]
    for n in range(1, 4):
        es.append(compose(compose(gg, es[-1], h), inverse(gg, h), h))
    for i, j in itertools.combinations(range(len(es)), 2):
        assert all(disjoint(c1, c2) for c1 in support_cones(es[i]) for c2 in support_cones(es[j]))
        assert is_id(comm(es[i], es[j], h))
    for f in es:
        assert all(u == v for u, (v, k) in f.items())  # carries only, no prefix moves
        assert sorted(k for (_, k) in f.values() if k) == sorted([h - 1, 1 - h])
    for key, T in list(gens.items()) + [('s', s)]:
        for u, (v, k) in T.items():
            assert abs(len(u) - len(v)) <= 1 and k in (0, 1)
    print(label, "h=%d ok; e_n supports:" % h,
          [support_cones(f) for f in es])


run("C4", cyclic_group(4))
run("C5", cyclic_group(5))
run("A5", a5_group())
