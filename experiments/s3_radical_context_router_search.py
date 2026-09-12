#!/usr/bin/env python3
"""Search three endpoint contexts on the S3 radical atlas.

The allowed radical characters are the even-parity triples R={000,011,101,110}.
An endpoint bit is a nonconstant affine function on R.  Each transport is a
coordinate permutation.  We seek 00/01/11 contexts whose three failure sets
partition R pointwise, the sharp deterministic form of the rank-one floor.
"""
from __future__ import annotations

from itertools import permutations, product

Radical = tuple[int, int, int]
Affine = tuple[int, Radical]

RADICALS: tuple[Radical, ...] = tuple(
    value for value in product((0, 1), repeat=3) if sum(value) % 2 == 0
)
PERMUTATIONS = tuple(permutations(range(3)))


def affine_value(form: Affine, value: Radical) -> int:
    constant, coefficients = form
    return constant ^ (sum(a & b for a, b in zip(coefficients, value)) & 1)


def permute(value: Radical, permutation: tuple[int, ...]) -> Radical:
    return tuple(value[index] for index in permutation)


def truth_vector(form: Affine) -> tuple[int, ...]:
    return tuple(affine_value(form, value) for value in RADICALS)


def audit() -> None:
    forms = []
    seen = set()
    for constant in (0, 1):
        for coefficients in product((0, 1), repeat=3):
            form = (constant, coefficients)
            truth = truth_vector(form)
            if truth in {(0, 0, 0, 0), (1, 1, 1, 1)} or truth in seen:
                continue
            seen.add(truth)
            forms.append(form)
    assert len(forms) == 6

    solutions = []
    for endpoints in product(forms, repeat=4):
        x0, x1, y0, y1 = endpoints
        for transports in product(PERMUTATIONS, repeat=3):
            p00, p01, p11 = transports
            failures = []
            for value in RADICALS:
                out00 = (affine_value(x0, value), affine_value(y0, permute(value, p00)))
                out01 = (affine_value(x0, value), affine_value(y1, permute(value, p01)))
                out11 = (affine_value(x1, value), affine_value(y1, permute(value, p11)))
                failures.append(
                    (
                        int(out00 != (1, 1)),
                        int(out01 == (1, 1)),
                        int(out11 != (1, 1)),
                    )
                )
            totals = tuple(sum(row) for row in failures)
            if all(any(row[index] for row in failures) for index in range(3)):
                complexity = (
                    sum(form[0] + sum(form[1]) for form in endpoints),
                    sum(sum(permutation[index] != index for index in range(3)) for permutation in transports),
                )
                score = (sum(totals), max(totals), max(totals) - min(totals), complexity)
                solutions.append((score, endpoints, transports, tuple(failures)))

    assert solutions
    solutions.sort()
    score, endpoints, transports, failures = solutions[0]
    assert len(solutions) == 233280
    assert score[:3] == (5, 2, 1)
    assert failures == ((1, 0, 1), (0, 1, 0), (0, 0, 1), (1, 0, 0))
    print(f"radical characters={RADICALS}")
    print(f"nonconstant affine endpoint bits={len(forms)}")
    print(f"candidate context atlases={len(solutions)}")
    print(f"minimum score (total,max,spread,complexity)={score}")
    print(f"endpoints (X0,X1,Y0,Y1)={endpoints}")
    print(f"transports (00,01,11)={transports}")
    print(f"failure triples by radical character={failures}")


if __name__ == "__main__":
    audit()
