#!/usr/bin/env python3
"""Exact Bernstein certificate for the Higman word bound on U(2)^4.

The proof and its dimension boundary are in research/artifacts/higman-u2-bound.md.
The certificate records only a complete subdivision; the verifier reconstructs
every polynomial and every coefficient over the rationals. It proves no bound
on arbitrary larger matrix blocks and no nonhyperlinear existence theorem.
"""

import argparse
from fractions import Fraction as Q
from itertools import product
import json
from math import comb
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CERTIFICATE = ROOT / "research/artifacts/higman-u2-bernstein-certificate.json"
FORMAT = "higman-u2-bernstein-v1"
INDICES = tuple(product(range(4), repeat=4))
INDEX = {k: i for i, k in enumerate(INDICES)}
SIGNS = tuple((-1,) + s for s in product((-1, 1), repeat=3))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def prod(values):
    out = Q(1)
    for value in values:
        out *= value
    return out


def polynomial(signs):
    """Power coefficients of 2 sum h_i(x) - (2-2x_0) on one sign box."""
    require(tuple(signs) in SIGNS, "invalid sign box")
    p = {(0, 0, 0, 0): Q(14), (1, 0, 0, 0): Q(2)}

    def term(coefficient, powers):
        k = tuple(powers.get(i, 0) for i in range(4))
        p[k] = p.get(k, Q(0)) + coefficient

    for j in range(4):
        i = (j - 1) % 4
        term(-4, {j: 1})
        if signs[j] < 0:
            # 16 x_j (1-x_i^2)(1-x_j^2).
            for a, b, c in ((0, 1, 16), (2, 1, -16),
                            (0, 3, -16), (2, 3, 16)):
                term(c, {i: a, j: b})
    return p


def initial_coefficients(signs):
    """Tensor Bernstein coefficients, degree (3,3,3,3), on the whole box."""
    p = polynomial(signs)
    factors = {}
    for axis, sign in enumerate(signs):
        lo, hi = (-1, 0) if sign < 0 else (0, 1)
        for power in range(4):
            for k in range(4):
                factors[axis, power, k] = sum((
                    Q(comb(power, j) * lo ** (power-j) * (hi-lo) ** j * comb(k, j),
                      comb(3, j))
                    for j in range(min(power, k) + 1)), Q(0))
    return tuple(sum((c * prod(factors[a, m[a], k[a]] for a in range(4))
                      for m, c in p.items()), Q(0)) for k in INDICES)


def coefficient_lines(axis):
    for rest in product(range(4), repeat=3):
        yield tuple(INDEX[tuple(k if j == axis else rest[j - (j > axis)]
                               for j in range(4))] for k in range(4))


LINES = tuple(tuple(coefficient_lines(axis)) for axis in range(4))


def split(coefficients, axis):
    """Exact midpoint de Casteljau subdivision; both closed half-boxes survive."""
    require(type(axis) is int and 0 <= axis < 4, "split axis must be 0, 1, 2, or 3")
    left, right = list(coefficients), list(coefficients)
    for line in LINES[axis]:
        row = [coefficients[i] for i in line]
        lo, hi = [row[0]], [row[-1]]
        while len(row) > 1:
            row = [(a + b) / 2 for a, b in zip(row, row[1:])]
            lo.append(row[0])
            hi.append(row[-1])
        for i, a, b in zip(line, lo, reversed(hi)):
            left[i], right[i] = a, b
    return tuple(left), tuple(right)


def subdivision(coefficients, depth=0):
    """Find a partition. Hitting the depth limit is failure, never a proof."""
    if min(coefficients) >= 0:
        return None
    require(depth < 24, "subdivision depth exhausted: no certificate generated")
    choices = []
    for axis in range(4):
        left, right = split(coefficients, axis)
        choices.append((min(min(left), min(right)), axis, left, right))
    # Deterministic tie-breaking by the first axis. Search is outside the
    # verifier's trust boundary: verification accepts only complete trees.
    _, axis, left, right = max(choices, key=lambda c: c[0])
    return [axis, subdivision(left, depth+1), subdivision(right, depth+1)]


def generate():
    return {"format": FORMAT, "coefficient": "2", "matrix_dimension": 2,
            "orthants": [{"signs": list(s), "tree": subdivision(initial_coefficients(s))}
                         for s in SIGNS]}


def verify(certificate):
    require(isinstance(certificate, dict), "certificate must be an object")
    require(set(certificate) == {"format", "coefficient", "matrix_dimension", "orthants"},
            "unexpected certificate fields")
    require(certificate["format"] == FORMAT, "unsupported certificate format")
    require(certificate["coefficient"] == "2", "this verifier fixes coefficient 2")
    require(type(certificate["matrix_dimension"]) is int and
            certificate["matrix_dimension"] == 2, "this verifier covers U(2) only")
    orthants = certificate["orthants"]
    require(isinstance(orthants, list) and len(orthants) == 8,
            "exactly eight sign boxes are required")
    seen = set()
    stats = {"internal_nodes": 0, "leaves": 0, "max_depth": 0}
    leaf_minima = []

    def visit(coefficients, tree, depth):
        require(depth <= 64, "certificate tree is too deep")
        stats["max_depth"] = max(stats["max_depth"], depth)
        if tree is None:
            lower = min(coefficients)
            require(lower >= 0, "leaf has a negative Bernstein coefficient")
            leaf_minima.append(lower)
            stats["leaves"] += 1
            return
        require(isinstance(tree, list) and len(tree) == 3,
                "internal node must contain an axis and both children")
        axis, lo, hi = tree
        left, right = split(coefficients, axis)
        stats["internal_nodes"] += 1
        visit(left, lo, depth+1)
        visit(right, hi, depth+1)

    for entry in orthants:
        require(isinstance(entry, dict) and set(entry) == {"signs", "tree"},
                "invalid orthant record")
        signs = entry["signs"]
        require(isinstance(signs, list) and len(signs) == 4 and
                all(type(s) is int and s in (-1, 1) for s in signs),
                "invalid signs")
        signs = tuple(signs)
        require(signs in SIGNS and signs not in seen, "missing or duplicate sign box")
        seen.add(signs)
        visit(initial_coefficients(signs), entry["tree"], 0)
    require(seen == set(SIGNS), "incomplete sign coverage")
    return {"status": "verified", "scope": "U(2)^4 and common blocks of size at most 2",
            "coefficient": "2", "orthants": len(seen), **stats,
            "bernstein_coefficients_checked": len(INDICES) * stats["leaves"],
            "minimum_leaf_coefficient": str(min(leaf_minima)),
            "proves_unrestricted_matrix_bound": False,
            "proves_nonhyperlinear_existence": False}


def check_graph(path):
    nodes = json.loads(path.read_text(encoding="utf-8"))["nodes"]
    expected = {"higman-u2-word-energy-bound": "ESTABLISHED",
                "higman-u2-word-energy-bound-proof": "COMPLETE",
                "higman-hs-microstates-are-near-glued-exact-bs-cycles": "ESTABLISHED",
                "non-hyperlinear-group": "OPEN"}
    for name, status in expected.items():
        require(nodes[name]["status"] == status, f"unexpected Cairn state for {name}")
    require("higman-u2-word-energy-bound" in
            nodes["higman-bs-cycle-equivalence-proof"]["meta"]["requires"],
            "missing dependency on the U(2) theorem")
    # This is the boundary of this contribution, not a permanent prohibition
    # on proving the root: a future proof should update this expected state.


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    generation = commands.add_parser("generate", help="generate and verify a finite partition")
    generation.add_argument("--output", type=Path, required=True)
    verification = commands.add_parser("verify", help="verify the complete committed partition")
    verification.add_argument("path", type=Path, nargs="?", default=CERTIFICATE)
    verification.add_argument("--graph", type=Path)
    args = parser.parse_args()
    try:
        if args.command == "generate":
            certificate = generate()
            report = verify(certificate)
            args.output.write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8")
        else:
            report = verify(json.loads(args.path.read_text(encoding="utf-8")))
            if args.graph:
                check_graph(args.graph)
                report["cairn_dependency_check"] = "passed"
        print(json.dumps(report, indent=2))
    except (ValueError, TypeError, KeyError, OSError, RecursionError) as exc:
        parser.exit(64, f"invalid certificate: {exc}\n")


if __name__ == "__main__":
    main()
