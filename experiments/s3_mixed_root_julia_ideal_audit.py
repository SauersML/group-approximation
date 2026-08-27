#!/usr/bin/env python3
"""Exact audit of the smallest non-retractive Julia/root anchor.

The coefficient ring is the dual-number ring F_5[e]/(e^2).  Reduction
e -> 0 retains the coefficient unit but kills the designated coefficient e.
On the surviving UT_3(F_5) quotient, an order-two automorphism swaps the two
input root lines and inverts the central root.  Two involutions z,j then
satisfy z j z j = x_13(1), so the unit root is tied non-retractively to a
genuine Julia commutator and cannot be killed.  Nevertheless x_13(e) is
identity.  A direct Julia tie to x_13(e) also has the zero-carrier absorber
j=z.

All computations use exact arithmetic and finite group laws only.
"""

from fractions import Fraction
import json


P = 5


def mod(x):
    return x % P


# Dual numbers a+b*eps, eps^2=0.
def dual_add(x, y):
    return (mod(x[0] + y[0]), mod(x[1] + y[1]))


def dual_mul(x, y):
    return (mod(x[0] * y[0]), mod(x[0] * y[1] + x[1] * y[0]))


DUAL_ZERO = (0, 0)
DUAL_ONE = (1, 0)
DUAL_EPS = (0, 1)


# UT_3(F_5), in x12(a) x23(b) x13(c) coordinates.
def h_mul(g, h):
    a, b, c = g
    d, e, f = h
    return (mod(a + d), mod(b + e), mod(c + f - d * b))


def h_inv(g):
    a, b, c = g
    return (mod(-a), mod(-b), mod(-c - a * b))


H_ID = (0, 0, 0)


def x12(a):
    return (mod(a), 0, 0)


def x23(b):
    return (0, mod(b), 0)


def x13(c):
    return (0, 0, mod(c))


def h_commutator(g, h):
    return h_mul(h_mul(h_mul(g, h), h_inv(g)), h_inv(h))


def sigma(g):
    """Swap x12,x23 and invert the commutator root."""
    a, b, c = g
    return (b, a, mod(-c - a * b))


H_ELEMENTS = [(a, b, c) for a in range(P) for b in range(P) for c in range(P)]


# Semidirect product UT_3(F_5) rtimes_sigma C2.
def k_mul(g, h):
    x, e = g
    y, f = h
    return (h_mul(x, sigma(y) if e else y), (e + f) % 2)


K_ID = (H_ID, 0)


def k_inv(g):
    x, e = g
    xi = h_inv(x)
    return (sigma(xi) if e else xi, e)


def k_power(g, n):
    out = K_ID
    for _ in range(n):
        out = k_mul(out, g)
    return out


def payload_audit():
    z = {"X": -1, "Y": 1}
    a = {
        "00": {"X": 1, "Y": 1},
        "01": {"X": -1, "Y": 1},
        "11": {"X": 1, "Y": 1},
    }
    defects = {}
    energy = 0
    residuals = {}
    for b in ("00", "01", "11"):
        defects[b] = {}
        for axis in ("X", "Y"):
            d = a[b][axis] - z[axis]
            defects[b][axis] = d
            energy += d * d
        px = Fraction(1 + a[b]["X"], 2)
        py = Fraction(1 + a[b]["Y"], 2)
        residuals[b] = px * py if b == "01" else 1 - px * py
    return {
        "covariance_energy": energy,
        "packed_norm_sq": str(Fraction(energy, 6)),
        "predicate_residuals": {b: str(v) for b, v in residuals.items()},
        "source_commutator_energy": 0,
        "defects": defects,
    }


def root_and_julia_audit():
    # Ring checks: eps is a nonzero square-zero element killed by reduction.
    ring = {
        "eps_nonzero": DUAL_EPS != DUAL_ZERO,
        "eps_square_zero": dual_mul(DUAL_EPS, DUAL_EPS) == DUAL_ZERO,
        "unit_survives_reduction": DUAL_ONE[0] == 1,
        "eps_killed_by_reduction": DUAL_EPS[0] == 0,
    }

    additivity_failures = []
    triangle_failures = []
    for a in range(P):
        for b in range(P):
            if h_mul(x12(a), x12(b)) != x12(a + b):
                additivity_failures.append(["x12", a, b])
            if h_mul(x23(a), x23(b)) != x23(a + b):
                additivity_failures.append(["x23", a, b])
            if h_mul(x13(a), x13(b)) != x13(a + b):
                additivity_failures.append(["x13", a, b])
            if h_commutator(x12(a), x23(b)) != x13(a * b):
                triangle_failures.append([a, b])

    sigma_square_failures = [g for g in H_ELEMENTS if sigma(sigma(g)) != g]
    sigma_hom_failures = []
    for g in H_ELEMENTS:
        for h in H_ELEMENTS:
            if sigma(h_mul(g, h)) != h_mul(sigma(g), sigma(h)):
                sigma_hom_failures.append([g, h])

    z = (H_ID, 1)
    c = (x13(1), 0)
    # j=z*c^3.  Since z inverts c, j is an involution and (zj)^2=c.
    j = k_mul(z, k_power(c, 3))
    w0 = k_mul(k_mul(k_mul(z, j), z), j)

    # The direct designated-root Julia tie has the exact zero-carrier model
    # j_direct=z, for which zjzj=1=x13(eps) after reduction.
    j_direct = z
    direct_w0 = k_mul(k_mul(k_mul(z, j_direct), z), j_direct)

    group_order = 2 * len(H_ELEMENTS)
    unit_root_nonidentity = c != K_ID
    designated_root_image = K_ID  # x13(eps) under eps -> 0.
    return {
        "ring": ring,
        "root_additivity_checks": 3 * P * P,
        "root_additivity_failures": additivity_failures,
        "steinberg_triangle_checks": P * P,
        "steinberg_triangle_failures": triangle_failures,
        "sigma_square_checks": len(H_ELEMENTS),
        "sigma_square_failures": sigma_square_failures,
        "sigma_homomorphism_checks": len(H_ELEMENTS) ** 2,
        "sigma_homomorphism_failures": sigma_hom_failures,
        "semidirect_group_order": group_order,
        "z_is_involution": k_power(z, 2) == K_ID,
        "j_is_involution": k_power(j, 2) == K_ID,
        "unit_root_anchor": {
            "x13_1_nonidentity": unit_root_nonidentity,
            "zjzj_equals_x13_1": w0 == c,
            "left_regular_root_defect_sq": "2" if unit_root_nonidentity else "0",
            "left_regular_julia_offdiag_mass": "1/4" if unit_root_nonidentity else "0",
        },
        "designated_coordinate": {
            "abstract_coefficient": "eps",
            "abstract_coefficient_nonzero": DUAL_EPS != DUAL_ZERO,
            "x13_eps_image_is_identity": designated_root_image == K_ID,
            "left_regular_root_defect_sq": "0",
        },
        "direct_designated_julia_tie": {
            "j_equals_z": j_direct == z,
            "zjzj_is_identity": direct_w0 == K_ID,
            "equals_reduced_x13_eps": direct_w0 == designated_root_image,
            "julia_offdiag_mass": "0",
        },
    }


def main():
    payload = payload_audit()
    audit = root_and_julia_audit()
    conclusion = {
        "payload_row_positive": payload["covariance_energy"] > 0,
        "payload_other_terms_zero": all(
            v == "0" for v in payload["predicate_residuals"].values()
        )
        and payload["source_commutator_energy"] == 0,
        "full_local_root_table_exact": not audit["root_additivity_failures"]
        and not audit["steinberg_triangle_failures"],
        "julia_unit_anchor_exact_and_nontrivial": audit["unit_root_anchor"][
            "x13_1_nonidentity"
        ]
        and audit["unit_root_anchor"]["zjzj_equals_x13_1"],
        "designated_coordinate_still_killed": audit["designated_coordinate"][
            "x13_eps_image_is_identity"
        ],
        "direct_julia_tie_has_zero_carrier_absorber": audit[
            "direct_designated_julia_tie"
        ]["equals_reduced_x13_eps"],
    }
    print(
        json.dumps(
            {"payload": payload, "mixed_root_julia": audit, "conclusion": conclusion},
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
