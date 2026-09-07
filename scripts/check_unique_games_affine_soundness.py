#!/usr/bin/env python3
"""Exact finite checks for the affine long-code soundness obstruction.

The universal proof is in the linked Markdown artifact. The small-game
exhaustions calibrate the construction; they do not prove the asymptotic
claim or the Unique Games Conjecture. Standard library only.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "research/artifacts/unique-games-affine-test-replay-2026-09-07.json"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def multiply(a: int, b: int, modulus: int) -> int:
    """Polynomial multiplication in F_2[t] modulo the supplied polynomial."""
    n = 1 << (modulus.bit_length() - 1)
    out = 0
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & n:
            a ^= modulus
    return out


def field_table(modulus: int) -> list[list[int]]:
    n = 1 << (modulus.bit_length() - 1)
    table = [[multiply(a, b, modulus) for b in range(n)] for a in range(n)]
    require(all(table[0][a] == 0 and table[1][a] == a for a in range(n)), "field identities")
    # A finite commutative polynomial quotient is a field if multiplication
    # by every nonzero element is a bijection. Check, rather than assume,
    # this property of each supplied modulus.
    require(all(set(table[a]) == set(range(n)) for a in range(1, n)), "modulus is not a field")
    require(len({table[a][a] for a in range(n)}) == n, "squaring is not bijective")
    return table


def projection(n: int, b: int, shift: int) -> tuple[int, ...]:
    representatives = [x for x in range(n) if x < (x ^ b)]
    index = {x: i for i, x in enumerate(representatives)}
    return tuple(index[min(a ^ shift, a ^ shift ^ b)] for a in range(n))


def field_checks(modulus: int) -> dict:
    table = field_table(modulus)
    n = len(table)
    square = [table[b][b] for b in range(n)]
    maximum = 0
    histogram: Counter[int] = Counter()
    for d in range(1, n):
        common: Counter[int] = Counter()
        for b in range(1, n):
            value = table[d][square[b]]
            # The two C values differ by nonzero b, so there is no
            # double-counting of the same common neighbor.
            common[value] += 1
            common[value ^ b] += 1
        for c in range(n):
            require(common[c] <= 3, "more than three common neighbors")
            maximum = max(maximum, common[c])
            histogram[common[c]] += 1
    checked_edges = 0
    if n <= 16:
        for u in range(n):
            directions = []
            for b in range(1, n):
                shift = table[u][square[b]]
                pi = projection(n, b, shift)
                fibers = [[a for a in range(n) if pi[a] == j] for j in range(n // 2)]
                require(all(len(fiber) == 2 for fiber in fibers), "projection not 2-to-1")
                require(all((fiber[0] ^ fiber[1]) == b for fiber in fibers), "wrong direction")
                require(pi[shift] == 0, "adaptive coordinate does not project to zero")
                directions.append(b)
                checked_edges += 1
            require(directions == list(range(1, n)), "nonuniform direction distribution")
    return {"N": n, "modulus_binary": bin(modulus), "field_verified": True,
            "D_C_pairs_exhausted": n * (n - 1), "max_common_neighbors": maximum,
            "common_neighbor_histogram": dict(sorted(histogram.items())),
            "edge_projections_exhausted": checked_edges}


def source_exhaustion() -> dict:
    table = field_table(0b111)
    n = len(table)
    maps = {(u, b): projection(n, b, table[u][table[b][b]])
            for u in range(n) for b in range(1, n)}
    best = 0
    witness: tuple[int, ...] | None = None
    cases = 0
    for labels in product(range(n), repeat=n):
        # Given left labels, every right label can be optimized independently.
        # This exhausts all labelings without repeating right assignments.
        score = sum(max(Counter(maps[u, b][labels[u]] for u in range(n)).values())
                    for b in range(1, n))
        if score > best:
            best, witness = score, labels
        cases += 1
    require(best == n * (n - 1), "N=4 normalization case should be satisfiable")
    return {"N": n, "left_assignments_exhausted": cases,
            "right_labels": "optimized independently for each complete left assignment",
            "exact_value": str(Fraction(best, n * (n - 1))), "left_witness": witness,
            "scope": "small normalization case; not the vanishing-value regime"}


def kernel(s: int, t: int, m: int, rho: Fraction) -> Fraction:
    return rho * (s == t) + (1 - rho) / m


def transition(a: tuple[int, ...], b: tuple[int, ...], m: int, rho: Fraction) -> Fraction:
    require(len(a) == len(b), "transition dimension mismatch")
    weight = Fraction(1)
    for s, t in zip(a, b):
        weight *= kernel(s, t, m, rho)
    return weight


def decode(word: tuple[int, ...]) -> int:
    n = len(word)
    scores = {b: sum(word[x] == word[x ^ b] for x in range(n)) for b in range(1, n)}
    # max preserves the first key on a tie; keys are increasing encodings.
    return max(scores, key=scores.__getitem__)


def block_checks(m: int, rho: Fraction) -> dict:
    total = true = wrong = Fraction(0)
    for a, b in product(range(m), repeat=2):
        planted = (a, a, b, b)
        for word in product(range(m), repeat=4):
            weight = transition(planted, word, m, rho) / (m * m)
            total += weight
            true += weight * Fraction((word[0] == word[1]) + (word[2] == word[3]), 2)
            wrong += weight * Fraction((word[0] == word[2]) + (word[1] == word[3]), 2)
    expected_true = Fraction(1, m) + (1 - Fraction(1, m)) * rho**2
    require(total == 1 and true == expected_true and wrong == Fraction(1, m), "block means")
    return {"m": m, "rho": str(rho), "states_exhausted": m**6,
            "true_equality_mean": str(true), "wrong_equality_mean": str(wrong)}


def ideal_checks(m: int, rho: Fraction) -> dict:
    # Independent direct enumeration of A_0, B_0, I, J.
    total = equal = Fraction(0)
    for a, b, i, j in product(range(m), repeat=4):
        weight = kernel(a, b, m, rho) * kernel(a, i, m, rho) * kernel(b, j, m, rho) / m
        total += weight
        equal += weight * (i == j)
    expected = Fraction(1, m) + (1 - Fraction(1, m)) * rho**3
    require(total == 1 and equal == expected, "three-noise equality law")
    return {"m": m, "rho": str(rho), "states_exhausted": m**4,
            "ideal_equality_probability": str(equal)}


def full_test(m: int, rho: Fraction) -> dict:
    """Exhaust the whole GF(4) test by exact conditional distributions.

    For each b,A average the output law over u and all ambient queries.
    The two choices of u and v, and their ambient noises, are conditionally
    independent, so a dot product gives the exact acceptance probability.
    """
    table = field_table(0b111)
    n = len(table)
    words = list(product(range(m), repeat=n))
    virtual = list(product(range(m), repeat=n // 2))
    decoded = {word: decode(word) for word in words}
    functions = [{word: word[table[u][table[decoded[word]][decoded[word]]]] for word in words}
                 for u in range(n)]
    for word in words:
        for t in range(m):
            shifted = tuple((a + t) % m for a in word)
            require(decoded[shifted] == decoded[word], "decoder not shift invariant")
            for u in range(n):
                require(functions[u][shifted] == (functions[u][word] + t) % m, "function not folded")
        representative = tuple((a - word[0]) % m for a in word)
        for u in range(n):
            require(functions[u][word] == (functions[u][representative] + word[0]) % m,
                    "folded variable extension mismatch")

    accepted = Fraction(0)
    error_by_direction = []
    expected_ideal = Fraction(1, m) + (1 - Fraction(1, m)) * rho**3
    for b in range(1, n):
        output_laws = {}
        ideal_laws = {}
        error = Fraction(0)
        for a in virtual:
            outputs = [Fraction(0) for _ in range(m)]
            ideals = [Fraction(0) for _ in range(m)]
            for u in range(n):
                q = table[u][table[b][b]]
                pi = projection(n, b, q)
                pullback = tuple(a[pi[x]] for x in range(n))
                for word in words:
                    weight = transition(pullback, word, m, rho) / n
                    outputs[functions[u][word]] += weight
                    ideals[word[q]] += weight
                    error += weight * (decoded[word] != b) / len(virtual)
                    if decoded[word] == b:
                        require(functions[u][word] == word[q], "successful decoder reads wrong coordinate")
            require(sum(outputs) == 1 and sum(ideals) == 1, "conditional law not normalized")
            output_laws[a], ideal_laws[a] = outputs, ideals
        acceptance_b = ideal_b = Fraction(0)
        for a, z in product(virtual, repeat=2):
            weight = transition(a, z, m, rho) / len(virtual)
            acceptance_b += weight * sum(x * y for x, y in zip(output_laws[a], output_laws[z]))
            ideal_b += weight * sum(x * y for x, y in zip(ideal_laws[a], ideal_laws[z]))
        require(ideal_b == expected_ideal, "pullback test does not match three-kernel oracle")
        require(acceptance_b >= ideal_b - 2 * error, "decoder-error coupling bound")
        accepted += acceptance_b / (n - 1)
        error_by_direction.append(str(error))
    return {"N": n, "m": m, "rho": str(rho),
            "ambient_words_per_function_exhausted": len(words),
            "virtual_words_exhausted": len(virtual), "left_functions": n,
            "exact_test_acceptance": str(accepted), "ideal_acceptance": str(expected_ideal),
            "decoder_errors_by_direction": error_by_direction,
            "folding": "exhaustive over all functions, inputs, and cyclic shifts",
            "scope": "complete finite test via conditional probabilities; no Monte Carlo"}


def finite_gap() -> dict:
    n = 16384
    rho = Fraction(99, 100)
    require(Fraction(n, 32) * rho**4 > 32, "exponent too small")
    # e_N < N exp(-32) < N/2^32, using e>2.
    error_upper = Fraction(n, 2**32)
    lower = rho**3 - 2 * error_upper
    require(lower > Fraction(97, 100), "finite output gap failed")
    require(128 * 128 == n and Fraction(2, 128) == Fraction(1, 64), "source bound")
    return {"N": n, "rho": str(rho), "m": "every integer >=2",
            "source_value_at_most": "1/64", "decoder_error_strictly_below": str(error_upper),
            "output_value_strictly_above": str(lower), "output_value_exceeds": "97/100",
            "scope": "rational check of universally proved bounds; large game not enumerated"}


def report() -> dict:
    return {"schema": 1,
            "theorem_scope": "explicit soundness obstruction for the affine-input folded noise test; UGC remains open",
            "field_and_root_checks": [field_checks(p) for p in (0b111, 0b10011, 0b1000011, 0x11B)],
            "source_exhaustion": source_exhaustion(),
            "pair_block_laws": [block_checks(m, Fraction(1, 2)) for m in (2, 3)],
            "ideal_noise_laws": [ideal_checks(m, rho) for m in (2, 3, 5)
                                 for rho in (Fraction(1, 2), Fraction(99, 100))],
            "full_test_exhaustions": [full_test(m, rho) for m in (2, 3)
                                      for rho in (Fraction(1, 2), Fraction(3, 4))],
            "concrete_finite_gap": finite_gap()}


def check_graph(path: Path) -> None:
    nodes = json.loads(path.read_text(encoding="utf-8"))["nodes"]
    expected = {
        "affine-shift-games-have-vanishing-value": "ESTABLISHED",
        "affine-shift-games-value-proof": "COMPLETE",
        "noisy-affine-direction-decoding-over-cyclic-alphabets": "ESTABLISHED",
        "cyclic-affine-direction-decoder-proof": "COMPLETE",
        "affine-long-code-test-has-no-uniform-soundness": "ESTABLISHED",
        "affine-long-code-soundness-counterexample-proof": "COMPLETE",
        "rich-2to1-conjecture-is-equivalent-to-ugc": "ESTABLISHED",
        "rich-2to1-games-conjecture": "OPEN",
        "unique-games-conjecture": "OPEN",
    }
    for name, status in expected.items():
        require(nodes[name]["status"] == status, f"unexpected Cairn state for {name}")
    requires = nodes["affine-long-code-soundness-counterexample-proof"]["meta"]["requires"]
    require(set(requires) == {"affine-shift-games-have-vanishing-value",
                             "noisy-affine-direction-decoding-over-cyclic-alphabets"},
            "counterexample dependency contract changed")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true", help="write the deterministic exact replay report")
    mode.add_argument("--check", action="store_true", help="compare with the committed report")
    parser.add_argument("--graph", type=Path, help="also validate a freshly compiled Cairn graph")
    args = parser.parse_args()
    rendered = json.dumps(report(), indent=2, sort_keys=True) + "\n"
    if args.write:
        REPORT.write_text(rendered, encoding="utf-8")
    elif args.check:
        require(REPORT.read_text(encoding="utf-8") == rendered, "replay report differs")
    else:
        print(rendered, end="")
    if args.graph:
        check_graph(args.graph)
        print("PASS: source bound, decoder, soundness obstruction, and open UGC state in Cairn")
    if args.write or args.check:
        print("PASS: field incidence, source exhaustion, folding, full noise test, and finite gap")


if __name__ == "__main__":
    main()
