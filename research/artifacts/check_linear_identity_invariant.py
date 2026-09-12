#!/usr/bin/env python3
"""Exact finite certificate used by the global two-packet trace proof.

The finite computation classifies every involution in the two double-coset
sets that can contribute the identity to a linear packet term.  The companion
Markdown artifact proves that none of the six nonidentity values in either
set is conjugate to a constant transposition.
"""

from pathlib import Path
import runpy
import sys


sys.argv = ["verify-kl-gate-c3-corner.py", "--final-only", "--family=none"]
data = runpy.run_path(
    str(Path(__file__).with_name("verify-kl-gate-c3-corner.py"))
)

add = data["add"]
corner_a = data["corner_a"]
corner_b = data["corner_b"]
g = data["g"]
g2 = data["g2"]
mat = data["mat"]
mul = data["mul"]
ONE = data["ONE"]
S0 = data["S0"]
S1 = data["S1"]
T0 = data["T0"]
T1 = data["T1"]
theta2 = data["theta2"]
U1 = data["U1"]
U2 = data["U2"]
U3 = data["U3"]
V1 = data["V1"]
V2 = data["V2"]
V3 = data["V3"]
ZERO = data["ZERO"]

U2_inverse = theta2(mat(ZERO, ONE, ONE, add(T0, ONE)))
V2_inverse = theta2(mat(ZERO, ONE, ONE, add(S0, ONE)))
assert mul(U2, U2_inverse) == mul(U2_inverse, U2) == ONE
assert mul(V2, V2_inverse) == mul(V2_inverse, V2) == ONE

e_support = (g, g2)


def corner_support_with_inverses(lifts, inverses):
    """Return support element -> inverse after the F_2 corner expansion."""
    parity = {}
    for left in e_support:
        left_inverse = g2 if left == g else g
        for unit, unit_inverse in zip(lifts, inverses):
            for right in e_support:
                right_inverse = g2 if right == g else g
                value = mul(mul(left, unit), right)
                value_inverse = mul(mul(right_inverse, unit_inverse), left_inverse)
                if value in parity:
                    del parity[value]
                else:
                    parity[value] = value_inverse
    return parity


support_a = corner_support_with_inverses(
    (U1, U2, U3), (U1, U2_inverse, g2)
)
support_b = corner_support_with_inverses(
    (V1, V2, V3), (V1, V2_inverse, g2)
)
assert set(support_a) == set(corner_a)
assert set(support_b) == set(corner_b)


def involutions_in_double_cosets(support_with_inverses):
    values = set()
    for unit_inverse in support_with_inverses.values():
        for left in e_support:
            for right in e_support:
                value = mul(mul(left, unit_inverse), right)
                if mul(value, value) == ONE:
                    values.add(value)
    return values


def six_nilpotent_perturbations(coefficients):
    values = set()
    for coefficient in coefficients:
        values.add(theta2(mat(ONE, coefficient, ZERO, ONE)))
        values.add(theta2(mat(ONE, ZERO, coefficient, ONE)))
        values.add(
            theta2(
                mat(
                    add(ONE, coefficient),
                    coefficient,
                    coefficient,
                    add(ONE, coefficient),
                )
            )
        )
    return values


a_involutions = involutions_in_double_cosets(support_a)
b_involutions = involutions_in_double_cosets(support_b)
assert a_involutions == {ONE} | six_nilpotent_perturbations((T0, T1))
assert b_involutions == {ONE} | six_nilpotent_perturbations((S0, S1))

print("A inverse double-cosets: identity plus six t-nilpotent involutions")
print("B inverse double-cosets: identity plus six s-nilpotent involutions")
