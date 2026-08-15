"""Finite-quotient screen against alternating groups of arbitrary small degree.

Generalises `atlas_relator_a9_screen.py` from degree nine to degree `m`.  With
`alpha : A8 -> A_m` the fixed embedding moving the first eight points, every
injective `beta : A8 -> A_m` whose image is an `A8` point-set stabiliser is
`conj_d . alpha . graph^eps` for `d in A_m` and `eps in {0,1}`.  Because the
minimal faithful permutation degree of `A8` is 8, for `m <= 11` every `A8`
subgroup of `A_m` is of that form (an `A8` orbit on `m <= 11` points is a union
of an 8-orbit and fixed points; a transitive or larger orbit would need a
subgroup of `A8` of index in `{9,10,11}`, and `A8` has none).

Running degree `m` screens every `F0 = <alpha(A8), beta(A8)>` inside `A_m` at
once, so degree 10 subsumes the `A9` case and adds `A10`.

The words tested are the complete spanning-tree kernel windows of
`atlas_kernel_collision_enumerator`.  A survivor would prove the tested window
does not normally generate `Nbar`; no survivor is one more passed screen.
"""

import argparse
import itertools
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_kernel_collision_enumerator import (  # noqa: E402
    enumerate_ball,
    factor_projections,
    spanning_tree_kernel_words,
)
from atlas_relator_a9_screen import (  # noqa: E402
    GENS,
    commutes_all,
    conjugate_all,
    coset_permutation_table,
    find_index_eight_subgroup,
    generated_subgroup,
    parity,
    perm_inv,
    perm_mul,
)
from atlas_two_chart_search import I4, gf2_inv  # noqa: E402


def all_even_permutations(m):
    """Every even permutation of {0..m-1} as rows of an int8 array."""
    perms = np.array(list(itertools.permutations(range(m))), dtype=np.int8)
    odd = np.zeros(len(perms), dtype=bool)
    for i in range(m):
        for j in range(i + 1, m):
            odd ^= perms[:, i] > perms[:, j]
    return perms[~odd]


def widen(table8, m):
    """Reinterpret a degree-nine table as degree m, fixing the extra points."""
    out = {}
    for key, value in table8.items():
        wide = np.arange(m, dtype=np.int8)
        wide[:8] = value[:8]
        out[key] = wide
    return out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--degree", type=int, default=10)
    parser.add_argument("--max-radius", type=int, default=5)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--smoke", type=int, default=0)
    args = parser.parse_args()

    m = args.degree
    if m > 11:
        raise SystemExit("degree > 11: the point-stabiliser classification "
                         "used here needs m <= 11")

    elements = generated_subgroup(GENS)
    subgroup = find_index_eight_subgroup(elements, args.seed)
    iota9 = coset_permutation_table(elements, subgroup)
    iota = widen(iota9, m)
    assert len({v.tobytes() for v in iota.values()}) == 20160
    rng = np.random.default_rng(1)
    keys = list(elements)
    from atlas_two_chart_search import gf2_mul
    for _ in range(300):
        g = elements[keys[rng.integers(len(keys))]]
        h = elements[keys[rng.integers(len(keys))]]
        assert np.array_equal(iota[gf2_mul(g, h).tobytes()],
                              perm_mul(iota[g.tobytes()], iota[h.tobytes()]))
    print("iota : GL_4(F2) -> A8 <= A%d verified (homomorphism, fixes 8..%d)"
          % (m, m - 1))

    iota_graph = {key: iota[gf2_inv(g).T.copy().tobytes()]
                  for key, g in elements.items()}

    windows = {}
    for radius in range(2, args.max_radius + 1):
        states, _ = enumerate_ball(radius)
        words, _s, _d = spanning_tree_kernel_words(states)
        windows[radius] = words
        print("radius %d window: %d words" % (radius, len(words)))

    identity = np.arange(m, dtype=np.int8)
    nontrivial = 0
    for radius in sorted(windows):
        for word in windows[radius]:
            value = identity
            for factor, matrix in word:
                if factor == 1:
                    value = perm_mul(value, iota[matrix.tobytes()])
            assert np.array_equal(value, iota[factor_projections(word)[0]
                                              .tobytes()])
            if not np.array_equal(value, identity):
                nontrivial += 1
    print("control: p_1 evaluation matches iota(p_1) (%d nontrivial)"
          % nontrivial)

    conditions = []
    for word in windows[2]:
        (f0, m0), (f1, m1), _c, _d = word
        x, y = ((m0, m1) if f0 == 1 else (m1, m0))
        conditions.append((x.tobytes(), y.tobytes()))
    print("radius-2 commuting conditions:", len(conditions))

    D = all_even_permutations(m)
    if args.smoke:
        D = D[:args.smoke]
    Dinv = np.argsort(D, axis=1).astype(np.int8)
    print("|A%d| candidates per twist: %d" % (m, len(D)))

    survivors = []
    for twist in (False, True):
        table = iota_graph if twist else iota
        alive = np.ones(len(D), dtype=bool)
        cache = {}
        for xkey, ykey in conditions:
            if not alive.any():
                break
            if ykey not in cache:
                cache[ykey] = conjugate_all(D, Dinv, table[ykey])
            alive &= commutes_all(cache[ykey], iota[xkey])
        idx = np.flatnonzero(alive)
        print("twist=%-5s stage 1 survivors: %d" % (twist, len(idx)))

        for k in idx:
            d, dinv = D[k], Dinv[k]
            ok = True
            for radius in sorted(windows):
                for word in windows[radius]:
                    value = identity
                    for factor, matrix in word:
                        key = matrix.tobytes()
                        letter = (iota[key] if factor == 1
                                  else perm_mul(perm_mul(d, table[key]), dinv))
                        value = perm_mul(value, letter)
                    if not np.array_equal(value, identity):
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                survivors.append((twist, D[k].tolist()))

    print("\nsurvivors after all windows:", len(survivors))
    if survivors:
        print("SCREEN FAILS -- example:", survivors[0])
    else:
        print("SCREEN PASSES -- no subgroup of A%d generated by two copies of"
              % m)
        print("   A8 kills the enumerated windows through radius",
              args.max_radius)


if __name__ == "__main__":
    main()
