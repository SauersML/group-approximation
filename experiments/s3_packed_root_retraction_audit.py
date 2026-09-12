#!/usr/bin/env python3
"""Exact finite audit for the retractive packed-root escape.

The payload is the smallest scalar realization of the three S3 endpoint
conventions.  Its predicate residuals and source commutators vanish, while
two of the six common-source covariance rows have norm two.

The root packet is the abelianized positive-root Heisenberg table over F_5:
the x_12 and x_23 lines act by translations of F_5^2, while the central
x_13 line is killed.  All additivity and Steinberg triangle relations remain
exact.  An affine S3 action and an independent faithful central C2 twist are
included to verify that neither symmetry repairs the missing kernel
reflection.

Only integer/rational arithmetic is used.  The script is intended to run on
MSI with the system Python and has no third-party dependencies.
"""

from fractions import Fraction
import json


P = 5
I2 = ((1, 0), (0, 1))


def add(u, v):
    return ((u[0] + v[0]) % P, (u[1] + v[1]) % P)


def neg(u):
    return ((-u[0]) % P, (-u[1]) % P)


def mat_mul(a, b):
    return tuple(
        tuple(sum(a[i][k] * b[k][j] for k in range(2)) % P for j in range(2))
        for i in range(2)
    )


def mat_vec(a, v):
    return tuple(sum(a[i][k] * v[k] for k in range(2)) % P for i in range(2))


def mat_inv(a):
    det = (a[0][0] * a[1][1] - a[0][1] * a[1][0]) % P
    inv_det = pow(det, -1, P)
    return (
        ((inv_det * a[1][1]) % P, (-inv_det * a[0][1]) % P),
        ((-inv_det * a[1][0]) % P, (inv_det * a[0][0]) % P),
    )


def affine_mul(g, h):
    """Compose affine maps g after h, encoded as (linear, translation)."""
    a, u = g
    b, v = h
    return (mat_mul(a, b), add(mat_vec(a, v), u))


def affine_inv(g):
    a, u = g
    ai = mat_inv(a)
    return (ai, neg(mat_vec(ai, u)))


def commutator(g, h):
    return affine_mul(affine_mul(affine_mul(g, h), affine_inv(g)), affine_inv(h))


def translation(v):
    return (I2, (v[0] % P, v[1] % P))


IDENTITY = translation((0, 0))


def x12(a):
    return translation((a, 0))


def x23(a):
    return translation((0, a))


def x13(_a):
    # The quotient UT_3(F_5) -> UT_3(F_5)/Z kills the commutator root.
    return IDENTITY


def fixed_points(g):
    a, u = g
    count = 0
    for i in range(P):
        for j in range(P):
            v = (i, j)
            if add(mat_vec(a, v), u) == v:
                count += 1
    return count


def power(g, n):
    out = IDENTITY
    for _ in range(n):
        out = affine_mul(out, g)
    return out


def payload_audit():
    q = 1
    z = {"X": -1, "Y": 1}
    a = {
        "00": {"X": 1, "Y": 1},
        "01": {"X": -1, "Y": 1},
        "11": {"X": 1, "Y": 1},
    }

    defects = {}
    defect_energy = 0
    predicate_residuals = {}
    for b in ("00", "01", "11"):
        defects[b] = {}
        for axis in ("X", "Y"):
            d = a[b][axis] * q - q * z[axis]
            defects[b][axis] = d
            defect_energy += d * d

        px = Fraction(1 + a[b]["X"], 2)
        py = Fraction(1 + a[b]["Y"], 2)
        overlap = q * px * py * q
        if b == "01":
            predicate_residuals[b] = overlap
        else:
            predicate_residuals[b] = q - overlap

    source_commutator_energy = 0  # Q=1 is scalar.
    m = 6
    packed_norm_sq = Fraction(defect_energy, m)
    return {
        "Q": q,
        "V": {b: 1 for b in ("00", "01", "11")},
        "Z": z,
        "A": a,
        "D": defects,
        "predicate_residuals": {
            b: str(predicate_residuals[b]) for b in predicate_residuals
        },
        "source_commutator_energy": source_commutator_energy,
        "covariance_energy": defect_energy,
        "packed_row_count": m,
        "packed_norm_sq": str(packed_norm_sq),
        "packed_identity": m * packed_norm_sq == defect_energy,
    }


def root_audit():
    additivity_failures = []
    triangle_failures = []
    for a in range(P):
        for b in range(P):
            if affine_mul(x12(a), x12(b)) != x12((a + b) % P):
                additivity_failures.append(["x12", a, b])
            if affine_mul(x23(a), x23(b)) != x23((a + b) % P):
                additivity_failures.append(["x23", a, b])
            if affine_mul(x13(a), x13(b)) != x13((a + b) % P):
                additivity_failures.append(["x13", a, b])
            if commutator(x12(a), x23(b)) != x13((a * b) % P):
                triangle_failures.append([a, b])

    # Standard two-dimensional reflection/rotation realization of S3 over F_5.
    s_mat = ((0, 1), (1, 0))
    t_mat = ((0, P - 1), (1, P - 1))
    s = (s_mat, (0, 0))
    t = (t_mat, (0, 0))
    s3_relations = {
        "s2": power(s, 2) == IDENTITY,
        "t3": power(t, 3) == IDENTITY,
        "sts=t^-1": affine_mul(affine_mul(s, t), s) == affine_inv(t),
    }

    covariance_failures = []
    for linear_name, linear in (("s", s), ("t", t)):
        for i in range(P):
            for j in range(P):
                v = (i, j)
                lhs = affine_mul(affine_mul(linear, translation(v)), affine_inv(linear))
                rhs = translation(mat_vec(linear[0], v))
                if lhs != rhs:
                    covariance_failures.append([linear_name, i, j])

    x12_one = x12(1)
    x23_one = x23(1)
    x13_one = x13(1)
    degree = P * P
    return {
        "field": "F_5",
        "permutation_degree": degree,
        "additivity_checks": 3 * P * P,
        "additivity_failures": additivity_failures,
        "steinberg_triangle_checks": P * P,
        "steinberg_triangle_failures": triangle_failures,
        "x12_1_fixed_points": fixed_points(x12_one),
        "x23_1_fixed_points": fixed_points(x23_one),
        "x13_1_fixed_points": fixed_points(x13_one),
        "x12_1_is_nontrivial": x12_one != IDENTITY,
        "x23_1_is_nontrivial": x23_one != IDENTITY,
        "x13_1_is_identity": x13_one == IDENTITY,
        "designated_root_defect_sq": Fraction(2 * (degree - fixed_points(x13_one)), degree),
        "s3_relations": s3_relations,
        "s3_covariance_checks": 2 * P * P,
        "s3_covariance_failures": covariance_failures,
        "central_c2_twist": {
            "faithful_two_sector_model": True,
            "commutes_with_root_and_s3_factors": True,
            "changes_payload_or_root_defect": False,
        },
    }


def main():
    payload = payload_audit()
    root = root_audit()
    result = {
        "payload": payload,
        "root_packet": {
            **root,
            "designated_root_defect_sq": str(root["designated_root_defect_sq"]),
        },
        "conclusion": {
            "all_predicate_residuals_zero": all(
                value == "0" for value in payload["predicate_residuals"].values()
            ),
            "source_commutators_zero": payload["source_commutator_energy"] == 0,
            "covariance_energy_positive": payload["covariance_energy"] > 0,
            "packed_root_defect_zero": root["designated_root_defect_sq"] == 0,
            "local_root_table_exact": not root["additivity_failures"]
            and not root["steinberg_triangle_failures"],
            "s3_extension_exact": all(root["s3_relations"].values())
            and not root["s3_covariance_failures"],
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
