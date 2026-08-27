"""Exact objective of the TRUE criterion at the classical warm starts.

The canonical regular-A8 criterion (`notes/EXPLICIT_LEAVITT_ATLAS.md` §9) asks
for `U in U(20160k)` making

    pi(h) = lambda(h) tensor I_k        (h in K1)
    pi(h) = U (lambda(h) tensor I_k) U* (h in K2)

satisfy `max_{s in T_St} ||pi(s) - I||_2 -> 0`.  Since every `pi(s)` is
unitary,

    ||pi(s) - I||_2^2 = 2 - 2 Re tr_d(pi(s)),

so the objective needs only NORMALIZED TRACES.  At the classical warm starts
those traces are available in closed form, with no 20160-dimensional linear
algebra at all:

* **`U = I`, and more generally any `U` implementing an automorphism**
  (`pi(h) = lambda(theta(h))` for `theta in Aut(A8)`, i.e. the 40320
  inner/graph alignments).  Then `pi(s) = lambda(fold_theta(s))`, whose
  normalized trace is `1` if the fold is trivial and `0` otherwise.  So every
  relator contributes defect `0` or `sqrt(2)`.

* **`U = J`, the tensor flip** `J delta_g = delta_{g^{-1}}`.  Then
  `pi_J(w) = L_{p1(w)} R_{p2(w)}` (TF2), and

      tr(L_a R_b) = #{g : a g b^{-1} = g} = #{g : g^{-1} a g = b},

  which is `|C(b)|` when `a ~ b` and `0` otherwise; normalized,
  `1/|class(b)|` when `a ~ b`, else `0`.

This gives the first exact numbers for the true criterion on the real relator
list, at k = 1, in seconds.  It is a baseline, not an optimization.
"""

import argparse
import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_two_chart_search import gf2_inv, gf2_mul, transvection  # noqa: E402

I4 = np.eye(4, dtype=np.uint8)
GENS = [transvection(r, c) for r, c in
        ((0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2))]


def enumerate_group():
    seen = {I4.tobytes(): I4}
    frontier = [I4]
    while frontier:
        nxt = []
        for g in frontier:
            for s in GENS:
                h = gf2_mul(g, s)
                key = h.tobytes()
                if key not in seen:
                    seen[key] = h
                    nxt.append(h)
        frontier = nxt
    return seen


def conjugacy_classes(elements):
    """Map from element key to (class id, class size)."""
    cls = {}
    sizes = []
    for key, g in elements.items():
        if key in cls:
            continue
        cid = len(sizes)
        orbit = {key}
        frontier = [g]
        while frontier:
            nxt = []
            for x in frontier:
                for s in GENS:
                    y = gf2_mul(gf2_mul(s, x), gf2_inv(s))
                    k2 = y.tobytes()
                    if k2 not in orbit:
                        orbit.add(k2)
                        nxt.append(y)
            frontier = nxt
        for k2 in orbit:
            cls[k2] = cid
        sizes.append(len(orbit))
    return cls, sizes


def load(path):
    with open(path) as handle:
        payload = json.load(handle)
    out = []
    for entry in payload["relators"]:
        word = [(int(f), np.array([int(c) for c in bits],
                                 dtype=np.uint8).reshape(4, 4))
                for f, bits in entry["word"]]
        out.append((entry.get("name", "?"), word))
    return out


def summarise(label, defects):
    d = np.asarray(defects, dtype=np.float64)
    print("  %-28s max %.6f   RMS %.6f   mean %.6f   zero %d/%d"
          % (label, d.max(), np.sqrt((d ** 2).mean()), d.mean(),
             int((d == 0).sum()), len(d)))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("list_json")
    args = parser.parse_args()

    words = load(args.list_json)
    print("relators:", len(words))

    elements = enumerate_group()
    cls, sizes = conjugacy_classes(elements)
    print("|A8| = %d, conjugacy classes = %d" % (len(elements), len(sizes)))

    # ---- U = I (identity alignment); the fold is the product of ALL syllables
    fold_defects = []
    fold_trivial = 0
    for _name, word in words:
        value = I4.copy()
        for _factor, matrix in word:
            value = gf2_mul(value, matrix)
        if np.array_equal(value, I4):
            fold_trivial += 1
            fold_defects.append(0.0)
        else:
            fold_defects.append(np.sqrt(2.0))
    print()
    print("U = I  (identity alignment)")
    summarise("defect", fold_defects)

    # ---- U = J (tensor flip)
    flip_defects = []
    detail = []
    for name, word in words:
        p1 = I4.copy()
        p2 = I4.copy()
        for factor, matrix in word:
            if factor == 1:
                p1 = gf2_mul(p1, matrix)
            else:
                p2 = gf2_mul(p2, matrix)
        k1, k2 = p1.tobytes(), p2.tobytes()
        if cls[k1] == cls[k2]:
            tr = 1.0 / sizes[cls[k2]]
        else:
            tr = 0.0
        defect = np.sqrt(max(0.0, 2.0 - 2.0 * tr))
        flip_defects.append(defect)
        if defect > 0:
            detail.append((name, sizes[cls[k1]], sizes[cls[k2]],
                           cls[k1] == cls[k2], defect))
    print()
    print("U = J  (tensor flip)")
    summarise("defect", flip_defects)
    print("    nonzero-defect relators: %d" % len(detail))
    if detail:
        conj = sum(1 for r in detail if r[3])
        print("    of those, p1 ~ p2 (partial cancellation): %d" % conj)
        print("    distinct nonzero defect values: %s"
              % sorted({round(r[4], 6) for r in detail}))
        print("    examples:", [(r[0], r[1], r[2]) for r in detail[:5]])

    print()
    print("Every automorphism alignment (all 40320) gives defect 0 or sqrt(2)")
    print("per relator, so its max is sqrt(2) unless the alignment kills the")
    print("entire list -- which the fold screen already refuted.  The whole")
    print("classical sector therefore sits at max defect sqrt(2) = %.6f."
          % np.sqrt(2.0))
    return 0


if __name__ == "__main__":
    sys.exit(main())
