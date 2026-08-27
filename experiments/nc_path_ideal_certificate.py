#!/usr/bin/env python3
"""Exact bounded-degree two-sided ideal certificate search in a free algebra.

This is discovery infrastructure for
`fixed-coefficient-ideal-certificate-controls-hs-defect` and the rectangular
Wedderburn atlas route.  It searches, with exact rational arithmetic, for
certificates

    target = sum c * left * relation * right

inside a prescribed degree bound.  Generators are opaque noncommuting symbols;
block-typing, matrix-unit multiplication, unitarity, and any other identities
can simply be supplied as additional relations by a compiler front-end.

Input JSON example::

    {
      "generators": ["x", "y", "z"],
      "relations": {
        "r": [["1", ["x", "y"]], ["-1", []]]
      },
      "target": [["1", ["z", "x", "y"]], ["-1", ["z"]]],
      "max_degree": 3
    }

Coefficients are integers or rational strings accepted by `fractions.Fraction`.
The returned certificate is replayed exactly before it is printed.  Failure is
only failure within the requested finite degree/search grammar, never a
mathematical non-membership claim.
"""

from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction
from pathlib import Path

Word = tuple[str, ...]
Poly = dict[Word, Fraction]


def parse_poly(raw) -> Poly:
    out: Poly = {}
    for coeff, word in raw:
        w = tuple(word)
        c = Fraction(str(coeff))
        out[w] = out.get(w, Fraction()) + c
        if not out[w]:
            del out[w]
    return out


def poly_terms(poly: Poly):
    return [[str(c), list(w)] for w, c in sorted(poly.items())]


def sandwich(left: Word, poly: Poly, right: Word) -> Poly:
    return {left + w + right: c for w, c in poly.items()}


def max_degree(poly: Poly) -> int:
    return max((len(w) for w in poly), default=0)


def words(gens: list[str], max_len: int):
    yield ()
    for length in range(1, max_len + 1):
        yield from itertools.product(gens, repeat=length)


def lead(poly: Poly) -> Word:
    # Degree first makes output stable and puts the longest obstruction first.
    return max(poly, key=lambda w: (len(w), w))


def axpy(dst: Poly, scale: Fraction, src: Poly):
    for w, c in src.items():
        value = dst.get(w, Fraction()) + scale * c
        if value:
            dst[w] = value
        elif w in dst:
            del dst[w]


def comb_axpy(dst: dict[int, Fraction], scale: Fraction,
              src: dict[int, Fraction]):
    for idx, c in src.items():
        value = dst.get(idx, Fraction()) + scale * c
        if value:
            dst[idx] = value
        elif idx in dst:
            del dst[idx]


def build_candidates(gens, relations, degree):
    candidates = []
    for name in sorted(relations):
        relation = relations[name]
        budget = degree - max_degree(relation)
        if budget < 0:
            continue
        all_words = list(words(gens, budget))
        for left in all_words:
            for right in all_words:
                if len(left) + len(right) > budget:
                    continue
                candidates.append(
                    (name, left, right, sandwich(left, relation, right)))
    return candidates


def solve(candidates, target: Poly):
    """Exact echelon reduction carrying combinations of candidate columns."""
    basis: dict[Word, tuple[Poly, dict[int, Fraction]]] = {}
    for idx, (_, _, _, original) in enumerate(candidates):
        poly = dict(original)
        combination = {idx: Fraction(1)}
        while poly:
            pivot = lead(poly)
            if pivot not in basis:
                scale = poly[pivot]
                poly = {w: c / scale for w, c in poly.items()}
                combination = {
                    i: c / scale for i, c in combination.items()
                }
                basis[pivot] = (poly, combination)
                break
            basis_poly, basis_combination = basis[pivot]
            factor = -poly[pivot]  # stored basis vector is monic at pivot
            axpy(poly, factor, basis_poly)
            comb_axpy(combination, factor, basis_combination)

    remainder = dict(target)
    used: dict[int, Fraction] = {}
    while remainder:
        pivot = lead(remainder)
        if pivot not in basis:
            return None, {
                "missing_pivot": list(pivot),
                "remainder": poly_terms(remainder),
            }
        basis_poly, basis_combination = basis[pivot]
        factor = remainder[pivot]
        axpy(remainder, -factor, basis_poly)
        comb_axpy(used, factor, basis_combination)
    return used, None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    args = parser.parse_args()

    data = json.loads(args.input.read_text())
    generators = list(dict.fromkeys(data["generators"]))
    relations = {
        name: parse_poly(poly) for name, poly in data["relations"].items()
    }
    target = parse_poly(data["target"])
    degree = int(data["max_degree"])
    if max_degree(target) > degree:
        raise SystemExit("target exceeds max_degree")

    candidates = build_candidates(generators, relations, degree)
    coefficients, failure = solve(candidates, target)
    output = {
        "max_degree": degree,
        "candidate_count": len(candidates),
        "found": coefficients is not None,
    }

    if coefficients is not None:
        certificate = []
        replay: Poly = {}
        for idx, coefficient in sorted(coefficients.items()):
            name, left, right, poly = candidates[idx]
            certificate.append({
                "coefficient": str(coefficient),
                "left": list(left),
                "relation": name,
                "right": list(right),
            })
            axpy(replay, coefficient, poly)
        if replay != target:
            raise AssertionError("internal certificate replay failed")
        output["certificate"] = certificate
    else:
        output["failure"] = failure

    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
