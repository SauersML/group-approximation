#!/usr/bin/env python3
"""Exact finite regressions for the noisy-direction counterexample.

The all-dimension proof is in the linked Markdown artifact. No simulation,
floating-point inference, or proof-assistant verification is used here.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "research/artifacts/unique-games-noisy-direction-replay-2026-09-07.json"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def j_map(x: int, k: int) -> int:
    """(a,b) -> (b,a+b) in each two-bit block of F_2^k."""
    require(k > 0 and k % 2 == 0, "even positive dimension required")
    out = 0
    for shift in range(0, k, 2):
        a, b = (x >> shift) & 1, (x >> (shift + 1)) & 1
        out |= b << shift
        out |= (a ^ b) << (shift + 1)
    return out


def pairs(n: int, b: int) -> list[tuple[int, int]]:
    return [(x, x ^ b) for x in range(n) if x < (x ^ b)]


def sign(mask: int, coordinate: int) -> int:
    return 1 - 2 * ((mask >> coordinate) & 1)


def selector_check(k: int) -> dict:
    n = 1 << k
    j = [j_map(x, k) for x in range(n)]
    require(len(set(j)) == n, "J is not bijective")
    require(all(j[j[x]] == (x ^ j[x]) for x in range(n)), "J^2+J+I != 0")
    edges = [frozenset((j[b], j[b] ^ b)) for b in range(1, n)]
    incidence = Counter(x for edge in edges for x in edge)
    require(incidence[0] == 0, "zero is an endpoint")
    require(all(incidence[x] == 2 for x in range(1, n)), "incidence is not two")
    for b in range(1, n):
        orbit = {b, j[b], j[j[b]]}
        require(len(orbit) == 3, "nonzero orbit has wrong size")
        require(set().union(*(edges[c - 1] for c in orbit)) == orbit, "wrong triangle")
        require(not set.intersection(*(set(edges[c - 1]) for c in orbit)), "triple star")
    if n <= 16:
        intersecting = sum(bool(a & b) for a in edges for b in edges)
        require(intersecting == 3 * (n - 1), "pair-intersection formula failed")
        for size in range(4):
            for subset in combinations(range(n), size):
                hits = sum(bool(set(subset) & edge) for edge in edges)
                require(hits <= 2 * size, "hitting bound failed")
    return {"N": n, "max_point_incidence": 2, "pair_star_density": str(Fraction(3, n - 1))}


def block_check() -> dict:
    """Exhaust the latent pair signs and all four coordinate noises."""
    rho = Fraction(1, 2)
    total = mean_true = mean_wrong = Fraction(0)
    for left, right in product((-1, 1), repeat=2):
        for noises in product((-1, 1), repeat=4):
            weight = Fraction(1, 4)
            for z in noises:
                weight *= (1 + rho * z) / 2
            y = [left * noises[0], left * noises[1], right * noises[2], right * noises[3]]
            true = Fraction(y[0] * y[1] + y[2] * y[3], 2)
            wrong = Fraction(y[0] * y[2] + y[1] * y[3], 2)
            require(-1 <= wrong <= 1, "wrong block range")
            total += weight
            mean_true += weight * true
            mean_wrong += weight * wrong
    require(total == 1 and mean_true == rho**2 and mean_wrong == 0, "block law failed")
    return {"latent_and_noise_states": 64, "true_mean": str(mean_true), "wrong_mean": str(mean_wrong)}


def noise_numerators(values: list[int], n: int) -> list[int]:
    """T_(1/2) on n ambient coordinates, denominator 4^n."""
    out = values.copy()
    for coordinate in range(n):
        stride = 1 << coordinate
        for base in range(0, len(out), 2 * stride):
            for lo in range(base, base + stride):
                hi = lo + stride
                a, b = out[lo], out[hi]
                out[lo], out[hi] = 3 * a + b, a + 3 * b
    return out


def exhaustive_check(k: int) -> dict:
    n = 1 << k
    all_pairs = [pairs(n, b) for b in range(1, n)]
    j = [j_map(x, k) for x in range(n)]
    functions, decoded, agreements = [], [], []
    for y in range(1 << n):
        scores = [sum(sign(y, x) == sign(y, z) for x, z in ps) for ps in all_pairs]
        b = 1 + max(range(n - 1), key=scores.__getitem__)
        agreements.append(scores)
        decoded.append(b)
        functions.append(sign(y, j[b]))
    full_mask = (1 << n) - 1
    require(all(decoded[y] == decoded[y ^ full_mask] for y in range(1 << n)), "decoder not even")
    require(all(functions[y] == -functions[y ^ full_mask] for y in range(1 << n)), "f not folded")

    noisy = noise_numerators(functions, n)
    # A separate direct transition-kernel evaluation calibrates noise order.
    if n == 4:
        for x in range(1 << n):
            direct = sum(functions[y] * 3 ** (n - (x ^ y).bit_count()) for y in range(1 << n))
            require(direct == noisy[x], "ambient noise kernel mismatch")
    denominator = 4**n
    coefficients, errors = [], []
    for b, ps in enumerate(all_pairs, start=1):
        numerator = 0
        for quotient in range(1 << (n // 2)):
            x = 0
            for index, (u, v) in enumerate(ps):
                if (quotient >> index) & 1:
                    x |= (1 << u) | (1 << v)
            numerator += noisy[x] * sign(x, j[b])
        coefficient = Fraction(numerator, denominator * (1 << (n // 2)))

        # Under the planted law, each ordered pair has weight 5/16 if
        # equal, 3/16 if different. Marginalize X before summing over Y.
        total_weight = error_weight = 0
        posterior_coefficient = Fraction(0)
        for y, scores in enumerate(agreements):
            equal = scores[b - 1]
            weight = 5**equal * 3 ** (n // 2 - equal)
            total_weight += weight
            if decoded[y] != b:
                error_weight += weight
            q = j[b]
            s, t = sign(y, q), sign(y, q ^ b)
            posterior = Fraction(2 * (s + t), 4 + s * t)
            posterior_coefficient += functions[y] * weight * posterior
        planted_denominator = 16 ** (n // 2)
        require(total_weight == planted_denominator, "planted law not normalized")
        require(coefficient == posterior_coefficient / planted_denominator, "independent coefficient mismatch")
        error = Fraction(error_weight, planted_denominator)
        require(abs(coefficient - Fraction(1, 2)) <= 2 * error, "coefficient/error inequality failed")
        coefficients.append(str(coefficient))
        errors.append(str(error))
    return {"N": n, "ambient_inputs_exhausted": 1 << n, "rho": "1/2",
            "selected_singleton_coefficients": coefficients, "decoder_error_probabilities": errors,
            "scope": "finite regression; asymptotic heaviness is proved in the Markdown artifact"}


def report() -> dict:
    # e_N <= (N-1)e^(-N/512) < N/2^32 at N=16384; e>2.
    threshold_bound = Fraction(1 << 14, 1 << 32)
    require(threshold_bound < Fraction(1, 8), "insufficient threshold")
    return {
        "schema": 1,
        "theorem_scope": "refutes the proposed affine glue and star-density lemmas; UGC remains open",
        "block_law": block_check(),
        "selector_checks": [selector_check(k) for k in (2, 4, 6, 8, 14)],
        "exact_exhaustions": [exhaustive_check(k) for k in (2, 4)],
        "sufficient_threshold": {"rho": "1/2", "N_at_least": 16384,
                                 "dimensions": "even", "error_strictly_below": str(threshold_bound),
                                 "singleton_coefficient_at_least": "1/4", "influence_at_least": "1/16"},
    }


def check_graph(path: Path) -> None:
    """Pin this contribution's effect; later proofs must update this contract."""
    nodes = json.loads(path.read_text(encoding="utf-8"))["nodes"]
    expected = {
        "noisy-affine-selector-defeats-bounded-hitting": "ESTABLISHED",
        "noisy-affine-selector-counterexample-proof": "COMPLETE",
        "affine-orientation-glue-lemma": "REFUTED",
        "affine-orientation-triangle-defect-is-small": "REFUTED",
        "glue-lemma-from-small-triangle-defect": "INVALIDATED",
        "rich-2to1-from-glue-lemma-modus-ponens": "INVALIDATED",
        "triangle-defect-globalizes-to-a-bounded-label-list": "ESTABLISHED",
        "glue-lemma-holds-for-quadratic-functions": "ESTABLISHED",
        "rich-2to1-conjecture-is-equivalent-to-ugc": "ESTABLISHED",
        "rich-2to1-games-conjecture": "OPEN",
        "unique-games-conjecture": "OPEN",
    }
    for name, status in expected.items():
        require(nodes[name]["status"] == status, f"unexpected Cairn state for {name}")
    for name in ("affine-orientation-glue-lemma", "affine-orientation-triangle-defect-is-small"):
        require("noisy-affine-selector-defeats-bounded-hitting" in nodes[name]["meta"]["refuted_by"],
                f"missing refutation link on {name}")
    require(nodes["unique-games-conjecture"]["meta"]["goal"] is True, "UGC goal flag missing")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--graph", type=Path, help="also validate a freshly compiled Cairn graph")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true", help="write deterministic exact replay report")
    mode.add_argument("--check", action="store_true", help="compare with committed replay report")
    args = parser.parse_args()
    result = report()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.write:
        REPORT.write_text(rendered, encoding="utf-8")
    elif args.check:
        require(REPORT.read_text(encoding="utf-8") == rendered, "replay report differs")
    else:
        print(rendered, end="")
    if args.graph:
        check_graph(args.graph)
        print("PASS: Cairn refutations, disabled routes, preserved theorems, and open UGC goal")
    if args.write or args.check:
        print("PASS: exact ambient-noise replay, planted-law cross-check, incidence, folding, and threshold")


if __name__ == "__main__":
    main()
