"""Goursat-uncovered finite-quotient screen: the degree-nine case.

Setting (notes/ATLAS_RELATOR_EXTRACTION_2026-08-15.md).  A candidate relator
list `T` in `Rbar = ker(A8 * A8 ->> Q)` is usable in the canonical regular-A8
criterion only if `Nbar <= <<T>>`, and then `Pbar/<<T>>` is perfect and central
over the infinite simple `Q`, so it has no nontrivial finite quotient at all.
Any homomorphism `phi : Pbar -> F` onto a nontrivial finite group killing `T`
therefore refutes `T`.

Already screened elsewhere:
  * one factor restriction trivial -> the retraction onto `A8 x A8`
    (`atlas_relator_projection_screen.py`);
  * both injective, commuting images -> a quotient of `A8 x A8` by Goursat,
    same screen;
  * both injective, equal image -> the 40320 automorphism folds onto `A8`
    (`atlas_relator_finite_quotient_screen.py`).

What is left is `F0 = <alpha(A8), beta(A8)>` with both injective and the images
neither equal nor commuting.  Put `n = [F0 : alpha(A8)]`.

  If `beta(A8) <= alpha(A8)` then `F0 = alpha(A8)`: the fold case.  Otherwise
  `beta(A8) cap alpha(A8)` is proper in a copy of `A8`, so
  `n >= [beta(A8) : beta(A8) cap alpha(A8)] >= 8`, the minimal index of a
  proper subgroup of `A8`.  For n = 8 the kernel `N` of the degree-eight action
  meets `alpha(A8)` trivially (else `alpha(A8)` is normal and `beta(A8)`, being
  perfect, lands inside it), so `|N| <= 8` and `A8 -> Aut(N)` is trivial; then
  `alpha(A8) N = alpha(A8) x N` and `beta(A8)`, perfect, projects isomorphically
  into `alpha(A8)`, forcing `beta(A8) = alpha(A8)` again.  So the smallest
  genuinely new case is **n = 9**, where `F0` is transitive of degree nine with
  an `A8` point stabiliser, that is `F0 = A9`.

Since the minimal faithful permutation degree of `A8` is 8, every `A8` subgroup
of `A9` is a point stabiliser.  Fixing `alpha = iota` up to global conjugacy,
every injective `beta : A8 -> A9` is `conj_d . iota . graph^eps` with
`d in A9` and `eps in {0,1}`: exactly `2 * 181440 = 362880` pairs.

The isomorphism `iota : GL_4(F2) -> A8` is constructed here from scratch (there
is no computer-algebra system on the node): find a subgroup of order 2520, then
take the action on its eight cosets.
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
from atlas_two_chart_search import gf2_inv, gf2_mul, transvection  # noqa: E402

PAIRS = [(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2)]
GENS = [transvection(r, c) for r, c in PAIRS]
IDENTITY4 = np.eye(4, dtype=np.uint8)


def generated_subgroup(matrices):
    seen = {IDENTITY4.tobytes(): IDENTITY4}
    frontier = [IDENTITY4]
    while frontier:
        nxt = []
        for g in frontier:
            for s in matrices:
                h = gf2_mul(g, s)
                key = h.tobytes()
                if key not in seen:
                    seen[key] = h
                    nxt.append(h)
        frontier = nxt
    return seen


def find_index_eight_subgroup(elements, seed=0):
    """A subgroup of order 2520 (a copy of A7) inside GL_4(F2)."""
    rng = np.random.default_rng(seed)
    keys = list(elements)
    for _attempt in range(20000):
        a = elements[keys[rng.integers(len(keys))]]
        b = elements[keys[rng.integers(len(keys))]]
        sub = generated_subgroup([a, b, gf2_inv(a), gf2_inv(b)])
        if len(sub) == 2520:
            return sub
    raise RuntimeError("no order-2520 subgroup found")


def coset_permutation_table(elements, subgroup):
    """iota : GL_4(F2) -> Sym(8) as a dict from matrix key to a length-9 array."""
    coset_of = {}
    reps = []
    for key, g in elements.items():
        if key in coset_of:
            continue
        reps.append(g)
        index = len(reps) - 1
        for h in subgroup.values():
            coset_of[gf2_mul(h, g).tobytes()] = index
    assert len(reps) == 8, len(reps)

    table = {}
    for key, g in elements.items():
        image = np.arange(9, dtype=np.int8)
        for i in range(8):
            image[i] = coset_of[gf2_mul(reps[i], g).tobytes()]
        # The right-coset action satisfies image(gh) = image(h) . image(g), an
        # anti-homomorphism for the composition (p*q)(i) = p(q(i)) used here.
        # Inverting each value turns it into a genuine homomorphism.
        table[key] = perm_inv(image)
    return table


def parity(p):
    p = np.asarray(p, dtype=int)
    seen = np.zeros(len(p), dtype=bool)
    sign = 0
    for i in range(len(p)):
        if seen[i]:
            continue
        j, size = i, 0
        while not seen[j]:
            seen[j] = True
            j = p[j]
            size += 1
        sign += size - 1
    return sign % 2


def perm_mul(p, q):
    """(p*q)(i) = p(q(i))."""
    return p[q]


def perm_inv(p):
    out = np.empty_like(p)
    out[p] = np.arange(len(p), dtype=p.dtype)
    return out


def even_permutations(n=9):
    rows = [p for p in itertools.permutations(range(n))
            if parity(np.array(p)) == 0]
    return np.array(rows, dtype=np.int8)


def conjugate_all(D, Dinv, p):
    """Rows of `D p D^{-1}`, for one fixed permutation p and all rows of D."""
    return np.take_along_axis(D, p[Dinv], axis=1)


def commutes_all(Q, r):
    """Row-wise test [q, r] = 1, q a row of Q and r a fixed permutation."""
    return (Q[:, r] == np.take(r, Q)).all(axis=1)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-radius", type=int, default=5)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--smoke", type=int, default=0,
                        help="test only this many candidates per twist")
    args = parser.parse_args()

    elements = generated_subgroup(GENS)
    print("|GL_4(F2)| =", len(elements))
    subgroup = find_index_eight_subgroup(elements, args.seed)
    print("index-eight subgroup order:", len(subgroup))

    iota = coset_permutation_table(elements, subgroup)
    assert len({v.tobytes() for v in iota.values()}) == 20160
    assert all(parity(v) == 0 for v in iota.values())
    # homomorphism check on a sample of products
    rng = np.random.default_rng(1)
    keys = list(elements)
    for _ in range(400):
        g = elements[keys[rng.integers(len(keys))]]
        h = elements[keys[rng.integers(len(keys))]]
        assert np.array_equal(iota[gf2_mul(g, h).tobytes()],
                              perm_mul(iota[g.tobytes()], iota[h.tobytes()]))
    print("iota : GL_4(F2) -> A8 <= A9 verified "
          "(injective, even, fixes 8, homomorphism)")

    iota_graph = {key: iota[gf2_inv(g).T.copy().tobytes()]
                  for key, g in elements.items()}

    windows = {}
    for radius in range(2, args.max_radius + 1):
        states, _ = enumerate_ball(radius)
        words, _s, _d = spanning_tree_kernel_words(states)
        windows[radius] = words
        print("radius %d window: %d words" % (radius, len(words)))

    # Positive control for the word-evaluation path.  Setting beta trivial is
    # the retraction p_1, so evaluating a word that way must reproduce
    # iota(p_1(word)) computed independently in GL_4(F2).  Through radius 4
    # every p_1 is trivial; at radius 5 exactly 118 words have p_1 != 1, so
    # this control exercises both outcomes.
    identity9 = np.arange(9, dtype=np.int8)
    nontrivial_control = 0
    for radius in sorted(windows):
        for word in windows[radius]:
            value = identity9
            for factor, matrix in word:
                if factor == 1:
                    value = perm_mul(value, iota[matrix.tobytes()])
            expected = iota[factor_projections(word)[0].tobytes()]
            assert np.array_equal(value, expected), (radius, "p_1 control")
            if not np.array_equal(value, identity9):
                nontrivial_control += 1
    print("control: p_1 evaluation matches iota(p_1) on every window word "
          "(%d of them nontrivial)" % nontrivial_control)

    # ---- stage 1: the 20 radius-2 commuting conditions, vectorised over A9
    conditions = []
    for word in windows[2]:
        letters = list(word)
        assert len(letters) == 4
        (f0, m0), (f1, m1), (f2, m2), (f3, m3) = letters
        assert (f0, m0.tobytes()) == (f2, m2.tobytes())
        assert (f1, m1.tobytes()) == (f3, m3.tobytes())
        x, y = ((m0, m1) if f0 == 1 else (m1, m0))
        conditions.append((x.tobytes(), y.tobytes()))
    print("radius-2 commuting conditions:", len(conditions))

    D = even_permutations(9)
    if args.smoke:
        D = D[:args.smoke]
    Dinv = np.argsort(D, axis=1).astype(np.int8)
    print("|A9| candidates per twist:", len(D))

    survivors = []
    for twist in (False, True):
        table = iota_graph if twist else iota
        alive = np.ones(len(D), dtype=bool)
        conj_cache = {}
        for xkey, ykey in conditions:
            if not alive.any():
                break
            if ykey not in conj_cache:
                conj_cache[ykey] = conjugate_all(D, Dinv, table[ykey])
            alive &= commutes_all(conj_cache[ykey], iota[xkey])
        idx = np.flatnonzero(alive)
        print("twist=%-5s stage 1 survivors: %d" % (twist, len(idx)))

        # ---- stage 2: full word evaluation on the deeper windows
        for k in idx:
            d, dinv = D[k], Dinv[k]
            ok = True
            for radius in sorted(windows):
                for word in windows[radius]:
                    value = np.arange(9, dtype=np.int8)
                    for factor, matrix in word:
                        key = matrix.tobytes()
                        if factor == 1:
                            letter = iota[key]
                        else:
                            letter = perm_mul(perm_mul(d, table[key]), dinv)
                        value = perm_mul(value, letter)
                    if value[0] != 0 or not np.array_equal(
                            value, np.arange(9, dtype=np.int8)):
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                survivors.append((twist, D[k].tolist()))

    print("\nsurvivors after all windows:", len(survivors))
    if survivors:
        print("SCREEN FAILS -- example:", survivors[0])
        print("=> a degree-nine finite quotient kills the window,")
        print("   so the window does not normally generate Nbar")
    else:
        print("SCREEN PASSES -- no degree-nine (A9) finite quotient kills")
        print("   the enumerated windows through radius", args.max_radius)


if __name__ == "__main__":
    main()
