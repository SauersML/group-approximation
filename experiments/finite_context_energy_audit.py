#!/usr/bin/env python3
"""Exact finite-context witnesses and free-group-ring certificate replay.

No numerical tolerances, external packages, or assertion-dependent checks.
The proof for arbitrary presentations is in
research/artifacts/finite-context-relator-energy.md; this program verifies
specified finite certificates and one explicit Heisenberg countermodel.
It is not a word-problem decision procedure or a Lean proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import deque
from pathlib import Path

Word = tuple[int, ...]
Poly = dict[Word, int]
Point = tuple[int, int, int]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def reduce_word(word: Word) -> Word:
    stack: list[int] = []
    for letter in word:
        require(type(letter) is int and letter != 0, "invalid free-group letter")
        if stack and stack[-1] == -letter:
            stack.pop()
        else:
            stack.append(letter)
    return tuple(stack)


def inverse(word: Word) -> Word:
    return tuple(-x for x in reversed(word))


def add(*polys: Poly) -> Poly:
    out: Poly = {}
    for poly in polys:
        for word, coeff in poly.items():
            require(type(coeff) is int, "only integral coefficients are supported")
            reduced = reduce_word(word)
            out[reduced] = out.get(reduced, 0) + coeff
    return {w: c for w, c in out.items() if c}


def scale(poly: Poly, coeff: int) -> Poly:
    return add({w: c * coeff for w, c in poly.items()})


def mul(left: Poly, right: Poly) -> Poly:
    out: Poly = {}
    for a, ac in left.items():
        for b, bc in right.items():
            w = reduce_word(a + b)
            out[w] = out.get(w, 0) + ac * bc
    return {w: c for w, c in out.items() if c}


def star(poly: Poly) -> Poly:
    return add({inverse(w): c for w, c in poly.items()})


def square(poly: Poly) -> Poly:
    return mul(star(poly), poly)


def monomial(word: Word) -> Poly:
    return {reduce_word(word): 1}


def difference(word: Word) -> Poly:
    return add(monomial(word), {(): -1})


def encode_poly(poly: Poly) -> list[dict]:
    return [{"word": list(w), "coefficient": c} for w, c in sorted(poly.items())]


def normal_closure_certificate(word: Word, factors: list[tuple[Word, Word, int]]) -> dict:
    """Factors are (relator, conjugator, sign); word equality is checked in F.

    Returns a literal integral sum-of-squares certificate, after replaying
    both sides independently with free reduction and coefficient arithmetic.
    """
    prefix: Word = ()
    zs: list[Poly] = []
    energies: list[Poly] = []
    for relator, conjugator, sign in factors:
        require(type(sign) is int and sign in (-1, 1), "invalid relator sign")
        r, g = reduce_word(relator), reduce_word(conjugator)
        signed_r = r if sign == 1 else inverse(r)
        a = reduce_word(g + signed_r + inverse(g))
        z = mul(monomial(prefix), difference(a))
        context = monomial(inverse(g))
        energy = mul(mul(star(context), square(difference(r))), context)
        require(square(z) == energy, "signed-relator square identity failed")
        zs.append(z)
        energies.append(energy)
        prefix = reduce_word(prefix + a)
    w = reduce_word(word)
    require(prefix == w, "supplied word is not the supplied product of conjugate relators")
    require(add(*zs) == difference(w), "telescoping identity failed")
    sos = [square(add(zs[i], scale(zs[j], -1)))
           for i in range(len(zs)) for j in range(i + 1, len(zs))]
    lhs = add(scale(add(*energies), len(factors)), scale(square(difference(w)), -1))
    require(lhs == add(*sos), "noncommutative sum-of-squares identity failed")
    return {
        "word": list(w),
        "factors": [{"relator": list(r), "conjugator": list(g), "sign": s}
                    for r, g, s in factors],
        "constant": len(factors),
        "square_count": len(sos),
        "telescoping_terms": [encode_poly(z) for z in zs],
        "square_roots": [encode_poly(add(zs[i], scale(zs[j], -1)))
                         for i in range(len(zs)) for j in range(i + 1, len(zs))],
        "identity_verified": True,
    }


def hmul(a: Point, b: Point) -> Point:
    x, y, z = a
    X, Y, Z = b
    return x + X, y + Y, z + Z + x * Y


def hinv(a: Point) -> Point:
    x, y, z = a
    return -x, -y, -z + x * y


GENERATORS: tuple[Point, ...] = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
RELATORS: tuple[Word, ...] = ((1, 2, -1, -2, -3), (1, 3, -1, -3), (2, 3, -2, -3))
CONTEXTS: tuple[Word, ...] = ((), (1,), (-1,), (2,), (-2,), (3,), (-3,),
                                  (1, 2), (-2, -1), (3, 1))
TARGET: Word = (3,)
POLYNOMIAL_CONTEXTS: tuple[Poly, ...] = (
    {(): 1, (1,): -2, (2, 3): 3},
    {(-1,): 2, (-2, -1): -1, (3, 1): 4},
    {},
)


def heval(word: Word) -> Point:
    point: Point = (0, 0, 0)
    for letter in word:
        g = GENERATORS[abs(letter) - 1]
        point = hmul(point, g if letter > 0 else hinv(g))
    return point


def ball(radius: int) -> list[Point]:
    require(type(radius) is int and radius >= 0, "invalid ball radius")
    distances: dict[Point, int] = {(0, 0, 0): 0}
    pending = deque([(0, 0, 0)])
    steps = GENERATORS + tuple(hinv(g) for g in GENERATORS)
    while pending:
        point = pending.popleft()
        if distances[point] == radius:
            continue
        for g in steps:
            target = hmul(g, point)
            if target not in distances:
                distances[target] = distances[point] + 1
                pending.append(target)
    return sorted(distances)


def build_witness(radius: int = 7) -> dict:
    points = ball(radius)
    index = {p: i for i, p in enumerate(points)}
    permutations: list[list[int]] = []
    for g in GENERATORS:
        partial = {i: index[hmul(g, p)] for i, p in enumerate(points) if hmul(g, p) in index}
        missing_domain = sorted(set(range(len(points))) - set(partial))
        missing_range = sorted(set(range(len(points))) - set(partial.values()))
        require(len(missing_domain) == len(missing_range), "partial permutation is not bijective")
        partial.update(zip(missing_domain, missing_range))
        permutations.append([partial[i] for i in range(len(points))])
    return {"schema": 1, "group": "integral Heisenberg group", "radius": radius,
            "points": [list(p) for p in points], "permutations": permutations,
            "origin_index": index[(0, 0, 0)]}


def inverse_permutation(perm: list[int]) -> list[int]:
    require(all(type(v) is int for v in perm), "nonintegral permutation entry")
    require(sorted(perm) == list(range(len(perm))), "not a permutation")
    inv = [0] * len(perm)
    for i, j in enumerate(perm):
        inv[j] = i
    return inv


def papply(word: Word, point: int, permutations: dict[int, list[int]]) -> int:
    for letter in reversed(word):
        point = permutations[letter][point]
    return point


def verify_witness(witness: dict) -> dict:
    require(witness["schema"] == 1, "unknown witness schema")
    radius = witness["radius"]
    points = [tuple(p) for p in witness["points"]]
    require(all(len(p) == 3 and all(type(x) is int for x in p) for p in points),
            "nonintegral Heisenberg point")
    require(points == ball(radius), "point list is not the complete specified ball")
    origin = witness["origin_index"]
    require(type(origin) is int and 0 <= origin < len(points) and points[origin] == (0, 0, 0),
            "wrong origin")
    require(len(witness["permutations"]) == 3, "expected three generators")
    permutations: dict[int, list[int]] = {}
    index = {p: i for i, p in enumerate(points)}
    internal_edges = 0
    for i, (g, perm) in enumerate(zip(GENERATORS, witness["permutations"]), 1):
        require(len(perm) == len(points), "wrong permutation dimension")
        permutations[i] = perm
        permutations[-i] = inverse_permutation(perm)
        for point, source in index.items():
            target = hmul(g, point)
            if target in index:
                require(perm[source] == index[target], "prescribed internal edge was changed")
                internal_edges += 1
    all_contexts = set(CONTEXTS).union(*(set(b) for b in POLYNOMIAL_CONTEXTS))
    needed = max([len(TARGET)] + [len(r) + len(q) for r in RELATORS for q in all_contexts])
    require(radius >= needed, "ball is too short for the specified relator contexts")
    require(all(heval(r) == (0, 0, 0) for r in RELATORS), "invalid Heisenberg relator")
    target_point = heval(TARGET)
    require(target_point != (0, 0, 0), "target is trivial")
    require(papply(TARGET, origin, permutations) == index[target_point], "wrong target orbit")
    tested_pairs = 0
    for r in RELATORS:
        for q in sorted(all_contexts):
            require(papply(r + q, origin, permutations) == papply(q, origin, permutations),
                    "context relator does not annihilate the base vector")
            tested_pairs += 1
    for b in POLYNOMIAL_CONTEXTS:
        vector: dict[int, int] = {}
        for q, c in b.items():
            i = papply(q, origin, permutations)
            vector[i] = vector.get(i, 0) + c
        for r in RELATORS:
            error: dict[int, int] = {}
            for i, c in vector.items():
                j = papply(r, i, permutations)
                error[j] = error.get(j, 0) + c
                error[i] = error.get(i, 0) - c
            require(all(c == 0 for c in error.values()), "polynomial-context defect is nonzero")
    moved = [sum(papply(r, i, permutations) != i for i in range(len(points))) for r in RELATORS]
    return {
        "dimension": len(points), "radius": radius, "internal_edges_checked": internal_edges,
        "relators": [list(r) for r in RELATORS], "word_context_pairs_checked": tested_pairs,
        "polynomial_contexts": [encode_poly(b) for b in POLYNOMIAL_CONTEXTS],
        "polynomial_context_pairs_checked": len(RELATORS) * len(POLYNOMIAL_CONTEXTS),
        "all_context_defect_vectors_zero": True, "target_word": list(TARGET),
        "target_group_element": list(target_point), "target_displacement_squared": 2,
        "global_relator_moved_points": moved,
        "global_relators_are_exact": all(x == 0 for x in moved),
    }


def sample_certificates() -> list[dict]:
    r: Word = (1, 2, -1, -2)
    # Literal products, including inverse relators and cancellation between factors.
    fixtures = [
        ((), []),
        (r, [(r, (), 1)]),
        (inverse(r), [(r, (), -1)]),
        (reduce_word((1,) + r + (-1,) + (2,) + inverse(r) + (-2,) + r),
         [(r, (1,), 1), (r, (2,), -1), (r, (), 1)]),
        ((), [(r, (1, 2), 1), (r, (1, 2), -1)]),
    ]
    return [normal_closure_certificate(word, factors) for word, factors in fixtures]


def replay(witness: dict) -> dict:
    payload = json.dumps(witness, sort_keys=True, separators=(",", ":")).encode()
    return {
        "schema": 1, "status": "verified", "arithmetic": "exact integers and free reduction",
        "scope": "specified certificates and finite model only; general theorems have written proofs",
        "witness_sha256": hashlib.sha256(payload).hexdigest(),
        "heisenberg_countermodel": verify_witness(witness),
        "normal_closure_certificates": sample_certificates(),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-witness", type=Path, help="check this explicit witness instead of constructing it")
    parser.add_argument("--witness-out", type=Path, help="save the complete finite permutation witness")
    parser.add_argument("--report-out", type=Path, help="save the exact replay report")
    args = parser.parse_args()
    try:
        witness = (json.loads(args.verify_witness.read_text()) if args.verify_witness else build_witness())
        report = replay(witness)
        if args.witness_out:
            args.witness_out.write_text(json.dumps(witness, separators=(",", ":")) + "\n")
        if args.report_out:
            args.report_out.write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps({"status": report["status"],
                          "countermodel": report["heisenberg_countermodel"],
                          "certificates_verified": len(report["normal_closure_certificates"])}))
    except (ValueError, KeyError, TypeError, IndexError, OSError) as exc:
        print(json.dumps({"status": "error", "error": str(exc)}))
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
