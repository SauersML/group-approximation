#!/usr/bin/env python3
"""Exact, finite replay for the adjacent observable-growth proof.

No third-party dependencies. Run from any directory. The infinite unilateral
shift is evaluated on finite-support vectors; it is never truncated to a
finite-dimensional inverse pair. This script does not prove surjunctivity or
replace the all-depth mathematical proof in the Markdown artifact.
"""

import argparse
import itertools
import json
from collections import defaultdict


# Integer polynomials in normal forms S^a T^b, using only the relation TS=I.
ONE = {(0, 0): 1}
S = {(1, 0): 1}
T = {(0, 1): 1}


def clean(poly):
    return {term: coefficient for term, coefficient in poly.items() if coefficient}


def add(left, right, scale=1):
    result = defaultdict(int, left)
    for term, coefficient in right.items():
        result[term] += scale * coefficient
    return clean(result)


def mul(left, right):
    result = defaultdict(int)
    for (a, b), x in left.items():
        for (c, d), y in right.items():
            cancelled = min(b, c)
            result[(a + c - cancelled, b + d - cancelled)] += x * y
    return clean(result)


def product(*factors):
    result = ONE
    for factor in factors:
        result = mul(result, factor)
    return result


def power(letter, exponent):
    return {(exponent, 0): 1} if letter == "S" else {(0, exponent): 1}


E = add(ONE, mul(S, T), -1)


def require(condition, label):
    if not condition:
        raise AssertionError(label)


def stack_reduce(word):
    """Independent adjacent-letter rewriting, not the exponent formula."""
    stack = []
    for letter in word:
        if letter == "S" and stack and stack[-1] == "T":
            stack.pop()
        else:
            stack.append(letter)
    require("TS" not in "".join(stack), "normal form is reduced")
    return {(stack.count("S"), stack.count("T")): 1}


def evaluate(poly, vector):
    """Apply to finitely supported vectors on N: S e_i=e_(i+1), T e_0=0."""
    result = defaultdict(int)
    for (a, b), coefficient in poly.items():
        for index, value in vector.items():
            if index >= b:
                result[index - b + a] += coefficient * value
    return clean(result)


def check_bicyclic(depth):
    require(mul(T, S) == ONE, "TS=I")
    require(mul(S, T) != ONE, "reverse identity must not be silently assumed")
    require(mul(E, E) == E, "E is idempotent")
    require(mul(T, E) == {}, "TE=0")
    require(mul(E, S) == {}, "ES=0")
    require(evaluate(E, {0: 1}) == {0: 1}, "nonzero infinite shift defect")

    words_checked = 0
    for length in range(9):
        for letters in itertools.product("ST", repeat=length):
            word = "".join(letters)
            require(product(*(S if x == "S" else T for x in word)) ==
                    stack_reduce(word), "normal-form multiplication: " + word)
            words_checked += 1

    recovery_checked = 0
    representation_checked = 0
    for i in range(depth):
        for j in range(depth):
            recovered = product(E, power("T", i), power("S", j), E)
            require(recovered == (E if i == j else {}),
                    f"defect recovery ({i},{j})")
            recovery_checked += 1
            a = product(power("S", i), E, power("T", j))
            b = add(power("S", j), power("T", i), -1)
            for k in range(depth + 1):
                vector = {k: 1, k + depth + 1: -2}
                require(evaluate(mul(a, b), vector) ==
                        evaluate(a, evaluate(b, vector)),
                        f"independent infinite representation ({i},{j},{k})")
                representation_checked += 1

    # A bounded but full four-index check of e_ij e_kl = [j=k] e_il.
    width = min(depth, 8)
    units = {(i, j): product(power("S", i), E, power("T", j))
             for i in range(width) for j in range(width)}
    for i, j, k, ell in itertools.product(range(width), repeat=4):
        expected = units[(i, ell)] if j == k else {}
        require(mul(units[(i, j)], units[(k, ell)]) == expected,
                f"matrix-unit multiplication ({i},{j},{k},{ell})")

    return {
        "word_normal_forms_through_length": 8,
        "word_normal_forms_checked": words_checked,
        "recovery_indices_less_than": depth,
        "recovery_identities_checked": recovery_checked,
        "infinite_representation_compositions_checked": representation_checked,
        "matrix_unit_indices_less_than": width,
        "matrix_unit_products_checked": width ** 4,
    }


def pullback(monomial, direction):
    """Walsh substitution: multiplication uses symmetric difference."""
    result = set()
    for site, track in monomial:
        if track == "a":
            factors = {(site, "a"), (site if direction == "T" else site - 1, "b")}
        else:
            factors = {(site + (1 if direction == "T" else -1), "b")}
        result.symmetric_difference_update(factors)
    return frozenset(result)


def orbit(monomial):
    if not monomial:
        return frozenset()
    anchor = min(site for site, _ in monomial)
    return frozenset((site - anchor, track) for site, track in monomial)


def anchored_m(k):
    sites = range(k) if k >= 0 else range(k, 0)
    return orbit(frozenset({(0, "a")} | {(j, "b") for j in sites}))


def check_walsh(depth):
    sites = [(j, track) for j in range(-2, 3) for track in "ab"]
    for mask in range(1 << len(sites)):
        monomial = frozenset(s for i, s in enumerate(sites) if mask & (1 << i))
        require(pullback(pullback(monomial, "T"), "S") == monomial,
                "Walsh ST identity")
        require(pullback(pullback(monomial, "S"), "T") == monomial,
                "Walsh TS identity")

    beta = frozenset({(0, "b")})
    current = {beta, anchored_m(0), anchored_m(1)}
    rows = []
    for n in range(depth + 1):
        expected = {beta} | {anchored_m(k) for k in range(-n, n + 2)}
        require(current == expected, f"exact orbit list at depth {n}")
        require(len(current) == 2 * n + 3, f"exact dimension at depth {n}")
        rows.append({"depth": n, "distinct_orbits": len(current),
                     "von_neumann_dimension": len(current), "defect_rank": 0})
        current |= {orbit(pullback(m, direction))
                    for m in current for direction in "TS"}
    return {"inverse_monomials_checked": 1 << len(sites), "windows": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--depth", type=int, default=12,
                        help="finite replay depth (1 through 50; default 12)")
    args = parser.parse_args()
    if not 1 <= args.depth <= 50:
        parser.error("--depth must be between 1 and 50")
    result = {
        "status": "passed",
        "scope": "Finite exact algebra replay; all-depth proofs are in the Markdown artifact.",
        "lean_verified": False,
        "gottschalk_proved": False,
        "bicyclic": check_bicyclic(args.depth),
        "reversible_xor": check_walsh(args.depth),
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
