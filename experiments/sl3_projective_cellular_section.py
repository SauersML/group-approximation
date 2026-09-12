"""Certify the norm of a rank-two integral harmonic lift section.

Each input is an exact ``Q^#`` vector together with an ambient integral lift
exported by ``sl3_projective_cellular_cvp.py``.  This program checks that the
two harmonic vectors have the stored Gauss-reduced Gram matrix and computes
the exact generalized characteristic polynomial of the resulting section.
Run with Sage on MSI.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from sage.all import QQ, RealField, ZZ, matrix


def read_lift(path: Path):
    qsharp = []
    lift = []
    digest = hashlib.sha256()
    with path.open(encoding="ascii") as stream:
        for expected_coordinate, line in enumerate(stream):
            digest.update(line.encode("ascii"))
            fields = line.split()
            if expected_coordinate == 0:
                if fields != ["coordinate", "qsharp", "lift"]:
                    raise ValueError("unexpected lift header")
                continue
            coordinate = expected_coordinate - 1
            if len(fields) != 3 or int(fields[0]) != coordinate:
                raise ValueError("malformed lift export")
            qsharp.append(QQ(fields[1]))
            lift.append(ZZ(fields[2]))
    return qsharp, lift, digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("first_lift", type=Path)
    parser.add_argument("second_lift", type=Path)
    parser.add_argument("summary", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    first_qsharp, first_lift, first_hash = read_lift(args.first_lift)
    second_qsharp, second_lift, second_hash = read_lift(args.second_lift)
    if len(first_lift) != len(second_lift):
        raise ValueError("lift dimensions differ")
    harmonic_basis = matrix(QQ, [first_qsharp, second_qsharp])
    integral_lifts = matrix(ZZ, [first_lift, second_lift])
    harmonic_gram = harmonic_basis * harmonic_basis.transpose()
    lift_gram = integral_lifts * integral_lifts.transpose()

    summary = json.loads(args.summary.read_text(encoding="utf-8"))
    stored_gram = matrix(QQ, [
        [QQ(entry) for entry in row]
        for row in summary["harmonic_lift_sequence"]["qsharp_gauss_reduced_gram"]
    ])
    if harmonic_gram != stored_gram:
        raise AssertionError("the supplied harmonic vectors are not the reduced basis")

    variable = QQ["lambda"].gen()
    polynomial = (lift_gram - variable * harmonic_gram).det()
    generalized = harmonic_gram.inverse() * lift_gram
    trace = generalized.trace()
    determinant = generalized.det()
    discriminant = trace * trace - 4 * determinant
    if discriminant < 0:
        raise AssertionError("generalized section spectrum is not real")
    real_field = RealField(256)
    root_discriminant = real_field(discriminant).sqrt()
    roots = sorted([
        float((real_field(trace) - root_discriminant) / 2),
        float((real_field(trace) + root_discriminant) / 2),
    ])
    if len(roots) != 2 or roots[0] <= 0:
        raise AssertionError("invalid generalized section spectrum")

    result = {
        "ambient_dimension": integral_lifts.ncols(),
        "harmonic_rank": 2,
        "harmonic_gram": [
            [str(entry) for entry in row] for row in harmonic_gram.rows()],
        "integral_lift_gram": [
            [int(entry) for entry in row] for row in lift_gram.rows()],
        "generalized_characteristic_polynomial": str(polynomial),
        "generalized_squared_singular_values": roots,
        "section_norm_upper_bound": roots[-1] ** 0.5,
        "first_lift_sha256": first_hash,
        "second_lift_sha256": second_hash,
        "exact_harmonic_gram_verified": True,
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
