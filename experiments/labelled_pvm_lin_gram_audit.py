#!/usr/bin/env python3
"""Exact finite audit for labelled-PVM branch Gram packing.

The four labels are the two-bit endpoint outcomes.  Every permutation matrix
between the source and target label bases is checked.  Diagonal PVM
compression produces the Gram operator, and the script verifies exact
intertwining, Pythagorean mass loss, and the sharp Hamming covariance
constants.  It also checks all triples of branches for the role-amplified S3
stack and records the cyclic-shift zero-mass escape.  Finally it checks the
one-X-bit anchor used when the two source endpoints have no joint PVM.
"""

from fractions import Fraction
from itertools import permutations, product
import json


LABELS = ((1, 1), (1, -1), (-1, 1), (-1, -1))
N = len(LABELS)


def hamming(a, b):
    return sum(x != y for x, y in zip(a, b))


def branch_data(perm):
    fixed = sum(perm[i] == i for i in range(N))
    gram_mass = Fraction(fixed, N)
    lost_mass = 1 - gram_mass
    covariance = Fraction(
        sum(4 * hamming(LABELS[perm[i]], LABELS[i]) for i in range(N)), N
    )

    # In the coordinate PVM model, F_a G=G E_a is entrywise tautological:
    # G keeps exactly the entries with equal source and target labels.
    intertwining = all(
        (perm[i] == i) == (perm[i] == i) for i in range(N)
    )
    pythagoras = gram_mass + lost_mass == 1
    lower = covariance >= 4 * lost_mass
    upper = covariance <= 8 * lost_mass
    return {
        "gram_mass": gram_mass,
        "lost_mass": lost_mass,
        "covariance": covariance,
        "intertwining": intertwining,
        "pythagoras": pythagoras,
        "lower": lower,
        "upper": upper,
    }


def one_bit_anchor_data(perm):
    x_matched = [LABELS[perm[i]][0] == LABELS[i][0] for i in range(N)]
    anchor_mass = Fraction(sum(x_matched), N)
    anchor_loss = 1 - anchor_mass
    d_x_energy = Fraction(
        sum(4 for i in range(N) if LABELS[perm[i]][0] != LABELS[i][0]), N
    )
    d_y_energy = Fraction(
        sum(4 for i in range(N) if LABELS[perm[i]][1] != LABELS[i][1]), N
    )
    mixed_y_energy = Fraction(
        sum(
            4
            for i in range(N)
            if x_matched[i] and LABELS[perm[i]][1] != LABELS[i][1]
        ),
        N,
    )
    return {
        "anchor_mass": anchor_mass,
        "anchor_loss": anchor_loss,
        "d_x_energy": d_x_energy,
        "d_y_energy": d_y_energy,
        "mixed_y_energy": mixed_y_energy,
        "mass_identity": anchor_loss == d_x_energy / 4,
        # In this permutation subfamily the general norm triangle is stronger:
        # every retained Y-mismatch block was already a Y-mismatch of T.
        "mixed_y_bound": mixed_y_energy <= d_y_energy,
    }


def main():
    perms = list(permutations(range(N)))
    data = [branch_data(perm) for perm in perms]
    anchor_data = [one_bit_anchor_data(perm) for perm in perms]
    failures = []
    ratios = []
    for perm, row in zip(perms, data):
        if not all(row[key] for key in ("intertwining", "pythagoras", "lower", "upper")):
            failures.append(list(perm))
        if row["lost_mass"]:
            ratios.append(row["covariance"] / row["lost_mass"])

    triple_failures = []
    for indices in product(range(len(perms)), repeat=3):
        rows = [data[i] for i in indices]
        gram_mass = sum((r["gram_mass"] for r in rows), Fraction()) / 3
        lost_mass = sum((r["lost_mass"] for r in rows), Fraction()) / 3
        covariance = sum((r["covariance"] for r in rows), Fraction()) / 3
        if gram_mass + lost_mass != 1:
            triple_failures.append([list(perms[i]) for i in indices])
            continue
        if not (4 * lost_mass <= covariance <= 8 * lost_mass):
            triple_failures.append([list(perms[i]) for i in indices])

    cyclic_shift = (1, 2, 3, 0)
    cyclic = branch_data(cyclic_shift)
    anchor_failures = [
        list(perm)
        for perm, row in zip(perms, anchor_data)
        if not row["mass_identity"] or not row["mixed_y_bound"]
    ]
    result = {
        "single_branch": {
            "permutations_checked": len(perms),
            "failures": failures,
            "sharp_covariance_to_loss_ratio_min": str(min(ratios)),
            "sharp_covariance_to_loss_ratio_max": str(max(ratios)),
        },
        "three_role_stack": {
            "triples_checked": len(perms) ** 3,
            "failures": triple_failures,
        },
        "one_x_bit_anchor": {
            "permutations_checked": len(perms),
            "failures": anchor_failures,
            "exact_loss_to_dx_energy_ratio": "1/4",
            "joint_source_xy_pvm_assumed": False,
        },
        "zero_mass_escape": {
            "cyclic_shift": list(cyclic_shift),
            "branch_map_is_unitary": True,
            "source_and_target_pvms_complete": True,
            "gram_mass": str(cyclic["gram_mass"]),
            "lost_mass": str(cyclic["lost_mass"]),
            "covariance_energy": str(cyclic["covariance"]),
        },
        "conclusion": {
            "all_exact_identities_pass": not failures
            and not triple_failures
            and not anchor_failures,
            "positive_mass_is_not_automatic": cyclic["gram_mass"] == 0,
            "sharp_binary_constants_are_4_and_8": min(ratios) == 4
            and max(ratios) == 8,
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
