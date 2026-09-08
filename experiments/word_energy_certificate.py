#!/usr/bin/env python3
"""Exact finite witnesses for failure of a fixed word-energy inequality.

Input: {"generator_count": 2, "subgroup_words": [[1]],
        "target_word": [-2, 1, 2]}.
Signed integer i denotes s_i, and -i denotes its inverse. Word products
act on column vectors from right to left. No floating-point arithmetic,
matrix library, or decision procedure for a presented group's word problem
is used. Only subgroup membership in the ambient FREE group is computed.

Usage:
  python3 experiments/word_energy_certificate.py build input.json
  python3 experiments/word_energy_certificate.py verify certificate.json

The verifier independently replays permutation tables; it does not trust
the folding algorithm or accept a membership report as a proof certificate.
See notes/PROPERTY_T_FREE_CONTEXT_ENERGY_2026-09-07.md.
"""

import argparse
import json
from pathlib import Path
import sys


SCHEMA = "word-energy-permutation-v1"


def inverse_word(word):
    return [-letter for letter in reversed(word)]


def reduce_word(word):
    reduced = []
    for letter in word:
        if reduced and reduced[-1] == -letter:
            reduced.pop()
        else:
            reduced.append(letter)
    return reduced


def validate_problem(problem):
    if not isinstance(problem, dict):
        raise ValueError("The input must be a JSON object")
    m = problem.get("generator_count")
    if type(m) is not int or m < 0:
        raise ValueError("generator_count must be a nonnegative integer")
    words = problem.get("subgroup_words")
    target = problem.get("target_word")
    if not isinstance(words, list) or not isinstance(target, list):
        raise ValueError("subgroup_words and target_word must be lists")
    for word in [*words, target]:
        if not isinstance(word, list) or any(
            type(x) is not int or not 1 <= abs(x) <= m for x in word
        ):
            raise ValueError("Each word must contain nonzero signed generator indices")
    return m, [list(w) for w in words], list(target)


def inverse_permutation(permutation):
    inverse = [0] * len(permutation)
    for source, target in enumerate(permutation):
        inverse[target] = source
    return inverse


def word_permutation(word, permutations):
    """Evaluate a matrix word on every basis index, rightmost letter first."""
    n = len(permutations[0]) if permutations else 1
    inverse = [inverse_permutation(p) for p in permutations]
    result = list(range(n))
    for letter in reversed(word):
        p = permutations[letter - 1] if letter > 0 else inverse[-letter - 1]
        result = [p[x] for x in result]
    return result


def build_certificate(problem):
    m, words, target = validate_problem(problem)
    parent = [0]
    edges = []

    def vertex():
        n = len(parent)
        parent.append(n)
        return n

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def edge(source, letter, destination):
        edges.extend([(source, letter, destination), (destination, -letter, source)])

    def path(word, close):
        current = 0
        for i, letter in enumerate(word):
            destination = 0 if close and i == len(word) - 1 else vertex()
            edge(current, letter, destination)
            current = destination
        return current

    # Right-labelled paths read inverse words. If P_i is a completed right
    # transition, U_i=P_i^{-1} has w(U) delta_o=delta_(o.w^{-1}).
    for word in words:
        path(inverse_word(reduce_word(word)), close=True)
    endpoint = path(inverse_word(reduce_word(target)), close=False)

    # Fold equally labelled edges with the same source. Including inverse
    # edges also enforces injectivity of every partial generator map.
    while True:
        transitions = {}
        for source, letter, destination in edges:
            key, destination = (find(source), letter), find(destination)
            if key in transitions and find(transitions[key]) != destination:
                first, second = sorted((find(transitions[key]), destination))
                parent[second] = first
                break
            transitions[key] = destination
        else:
            break

    common = {
        "generator_count": m,
        "subgroup_words": words,
        "target_word": target,
    }
    if find(endpoint) == find(0):
        return {
            "status": "member",
            **common,
            "method": "free-subgroup folding; not an independently replayable certificate",
        }

    roots = sorted({find(x) for x in range(len(parent))})
    index = {root: i for i, root in enumerate(roots)}
    n = len(roots)
    permutations = []
    for letter in range(1, m + 1):
        partial = {
            index[find(source)]: index[find(destination)]
            for source, label, destination in edges if label == letter
        }
        domain = sorted(set(range(n)) - partial.keys())
        codomain = sorted(set(range(n)) - set(partial.values()))
        if len(domain) != len(codomain):
            raise RuntimeError("Folded map was not injective")
        partial.update(zip(domain, codomain))
        permutations.append(inverse_permutation([partial[x] for x in range(n)]))

    certificate = {
        "schema": SCHEMA,
        "status": "nonmember",
        **common,
        "dimension": n,
        "basepoint": index[find(0)],
        "permutations": permutations,
    }
    verify_certificate(certificate)
    return certificate


def verify_certificate(certificate):
    """Validate only explicit, finite, exact permutation counterexamples."""
    m, words, target = validate_problem(certificate)
    if certificate.get("schema") != SCHEMA or certificate.get("status") != "nonmember":
        raise ValueError("An explicit nonmember permutation certificate is required")
    n, base = certificate.get("dimension"), certificate.get("basepoint")
    if type(n) is not int or n < 1 or type(base) is not int or not 0 <= base < n:
        raise ValueError("Invalid dimension or basepoint")
    bound = 1 + len(target) + sum(map(len, words))
    if n > bound:
        raise ValueError("The certificate exceeds the claimed dimension bound")
    permutations = certificate.get("permutations")
    if not isinstance(permutations, list) or len(permutations) != m:
        raise ValueError("Expected one permutation for every generator")
    for p in permutations:
        if (not isinstance(p, list) or any(type(x) is not int for x in p)
                or sorted(p) != list(range(n))):
            raise ValueError("Every generator table must be a permutation")
    if m == 0:
        raise ValueError("The rank-zero free group has no nonmember word")
    word_tables = [word_permutation(w, permutations) for w in words]
    endpoints = [p[base] for p in word_tables]
    if any(x != base for x in endpoints):
        raise ValueError("A subgroup word does not fix the basepoint")
    target_endpoint = word_permutation(target, permutations)[base]
    if target_endpoint == base:
        raise ValueError("The target word fixes the basepoint")
    return {
        "verified": True,
        "dimension": n,
        "dimension_bound": bound,
        "subgroup_displacements_squared": [0] * len(words),
        "target_displacement_squared": 2,
        # This diagnostic makes the global-norm distinction observable:
        # zero on the chosen vector does not mean the relator is identity.
        "subgroup_words_moving_some_basis_vector": [
            i for i, p in enumerate(word_tables) if p != list(range(n))
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["build", "verify"])
    parser.add_argument("input", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        data = json.loads(args.input.read_text(encoding="utf-8"))
        result = build_certificate(data) if args.command == "build" else verify_certificate(data)
    except (ValueError, OSError) as exc:
        print(json.dumps({"error": str(exc)}), file=sys.stderr)
        return 2
    output = json.dumps(result, indent=2) + "\n"
    if args.output is None:
        print(output, end="")
    else:
        args.output.write_text(output, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
