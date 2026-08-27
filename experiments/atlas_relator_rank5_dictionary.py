"""Step 2 of the rank-five Steinberg translation: the factorization dictionary.

Goal.  Express each of the 100 rank-five Steinberg generators

    x_kl(b) = 1 + E_k b E_l^*        (k != l in {1..5},  b in {1,e,f,e^*,f^*})

as an explicit word in the twelve atlas generators of `Pbar = K1 * K2`.

Choice of rank-five code.  Take the join of the two atlas charts,

    E = (000, 001, 010, 011, 1) = (gamma_1 e, gamma_1 f, gamma_2 e, gamma_2 f, gamma_3)

over the rank-three code `gamma = (00, 01, 1)` of `EXPLICIT_LEAVITT_ATLAS.md` §1.
This is a complete prefix code of size five, so `Theta_E` identifies `M_5(L)`
with `L` and `E_5(L)` with `Q`.  Note the chart-overlap theorem: `E` refines
`D_1` and `D_2` NON-uniformly, so `GL(E)` contains neither `K1` nor `K2`.  That
is irrelevant here -- what is needed is that each `x_kl(b)` be a *word* in
`K1 cup K2`, not that it lie in a chart.

Mechanism.  Write `p(k)` for the rank-three parent index of `E_k` and `s_k` for
its suffix (`s_5` empty).  Then

    E_k b E_l^* = gamma_{p(k)} (s_k b s_l^*) gamma_{p(l)}^*,

so whenever `p(k) != p(l)` the target lies in the abelian root subgroup

    U_ij(c) = 1 + gamma_i c gamma_j^*,   c in L,      U_ij(c) U_ij(c') = U_ij(c+c'),

and its coefficient `c = s_k b s_l^*` is a product of at most three letters of
`S cup {1} = {1,e,f,e^*,f^*}`.  Each such product is reached from the thirty
rank-three generators by iterating the Steinberg identity

    [ U_ik(a), U_kj(b) ] = U_ij(ab)      (i, j, k distinct),

and the thirty rank-three generators are already explicit words in `K1 cup K2`
(`atlas_two_chart_search.q`, which realises twenty of them as single chart
transvections and the remaining ten by the identities (7) of §3).

When `p(k) = p(l)` -- the four pairs (1,2), (2,1), (3,4), (4,3) -- route through
index five, whose parent is different from both:

    x_kl(b) = [ x_k5(b), x_5l(1) ].

Every construction is verified exactly against the target Leavitt element; no
step is taken on trust.
"""

import argparse
import itertools
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_kernel_collision_enumerator import evaluate_word  # noqa: E402
from atlas_two_chart_search import (  # noqa: E402
    GAMMA,
    commutator,
    inverse,
    leavitt_add,
    leavitt_is_one,
    product,
    q,
    reduce_word,
    transvection,
)

ONE = {((), ()): 1}
COEFF_LETTERS = ("1", "e", "f", "E", "F")     # E = e^*, F = f^*

# rank-five code E_k = gamma_{PARENT[k]} . SUFFIX[k]
PARENT = {1: 1, 2: 1, 3: 2, 4: 2, 5: 3}
SUFFIX = {1: "e", 2: "f", 3: "e", 4: "f", 5: None}
STAR_OF = {"e": "E", "f": "F"}
BIT_OF = {"e": "0", "f": "1"}


def leaf(k):
    base = GAMMA[PARENT[k]]
    return base if SUFFIX[k] is None else base + BIT_OF[SUFFIX[k]]


def path(text):
    return tuple(int(ch) for ch in text)


def target_element(k, l, b):
    """The exact Leavitt element 1 + E_k b E_l^*."""
    alpha, beta = leaf(k), leaf(l)
    if b in ("e", "f"):
        alpha = alpha + BIT_OF[b]
    elif b in ("E", "F"):
        beta = beta + ("0" if b == "E" else "1")
    return leavitt_add(ONE, {(path(alpha), path(beta)): 1})


def leavitt_equal(x, y):
    """Exact equality in L, via char-two addition and the identity test."""
    return leavitt_is_one(leavitt_add(leavitt_add(x, y), ONE))


def third_index(i, j):
    return 6 - i - j


def root_word(i, j, factors, memo):
    """A word for U_ij(a_1 ... a_t), factors a list of letters of S cup {1}."""
    factors = [a for a in factors if a != "1"] or ["1"]
    key = (i, j, tuple(factors))
    if key in memo:
        return memo[key]
    if len(factors) == 1:
        word = q(i, j, factors[0])
    else:
        k = third_index(i, j)
        left = root_word(i, k, factors[:1], memo)
        right = root_word(k, j, factors[1:], memo)
        word = commutator(left, right)
    word = reduce_word(word)
    memo[key] = word
    return word


def coefficient_factors(k, l, b):
    """The letters of c = s_k b s_l^*."""
    out = []
    if SUFFIX[k] is not None:
        out.append(SUFFIX[k])
    if b != "1":
        out.append(b)
    if SUFFIX[l] is not None:
        out.append(STAR_OF[SUFFIX[l]])
    return out or ["1"]


def rank5_word(k, l, b, memo):
    """An X-word for x_kl(b), together with a human-readable recipe."""
    i, j = PARENT[k], PARENT[l]
    if i != j:
        factors = coefficient_factors(k, l, b)
        return (root_word(i, j, factors, memo),
                "U_%d%d(%s)" % (i, j, "".join(factors)))
    # same rank-three parent: route through index five, whose parent differs
    left, _ = rank5_word(k, 5, b, memo)
    right, _ = rank5_word(5, l, "1", memo)
    return (reduce_word(commutator(left, right)),
            "[x_%d5(%s), x_5%d(1)]" % (k, b, l))


def transvection_lengths():
    """Word length in GL_4(F2) w.r.t. the six adjacent transvections."""
    from atlas_two_chart_search import gf2_mul
    import numpy as np
    gens = [transvection(r, c) for r, c in
            ((0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2))]
    identity = np.eye(4, dtype=np.uint8)
    lengths = {identity.tobytes(): 0}
    frontier = [identity]
    depth = 0
    while frontier:
        depth += 1
        nxt = []
        for g in frontier:
            for s in gens:
                h = gf2_mul(g, s)
                key = h.tobytes()
                if key not in lengths:
                    lengths[key] = depth
                    nxt.append(h)
        frontier = nxt
    return lengths


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--emit", default="")
    args = parser.parse_args()

    lengths = transvection_lengths()
    memo = {}
    entries = []
    failures = []

    for k, l in itertools.permutations(range(1, 6), 2):
        for b in COEFF_LETTERS:
            word, recipe = rank5_word(k, l, b, memo)

            value = evaluate_word(word)
            ok = leavitt_equal(value, target_element(k, l, b))
            if not ok:
                failures.append((k, l, b, recipe))
            entries.append({
                "k": k, "l": l, "b": b,
                "recipe": recipe,
                "syllables": len(word),
                "x_length": sum(lengths[m.tobytes()] for _f, m in word),
                "verified": ok,
            })

    print("rank-five generators built: %d" % len(entries))
    print("verified exactly:           %d" % sum(e["verified"] for e in entries))
    if failures:
        print("FAILURES:", failures[:10])
        return 1

    syl = [e["syllables"] for e in entries]
    xln = [e["x_length"] for e in entries]
    print("syllable length: min %d  max %d  total %d"
          % (min(syl), max(syl), sum(syl)))
    print("X-length:        min %d  max %d  total %d"
          % (min(xln), max(xln), sum(xln)))

    by_factors = {}
    for e in entries:
        by_factors.setdefault(e["recipe"].split("(")[0], 0)
        by_factors[e["recipe"].split("(")[0]] += 1
    print("recipes by shape:", dict(sorted(by_factors.items())))

    if args.emit:
        with open(args.emit, "w") as handle:
            json.dump({"code": [leaf(k) for k in range(1, 6)],
                       "entries": entries}, handle, indent=1)
        print("wrote", args.emit)
    return 0


if __name__ == "__main__":
    sys.exit(main())
