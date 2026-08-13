"""Audit the star/inverse seam in the short hard-pair projection formula.

The characteristic-two certificate for ``p_001`` uses the Leavitt
anti-involution.  A unitary group representation instead sends group inverse
to operator adjoint.  This script verifies exactly that these operations do
not agree on the first hard prefix and that replacing every Leavitt star by
group inverse makes the four-term certificate vanish.
"""

import json
import sys

sys.path.insert(0, "experiments")

from atlas_kernel_collision_enumerator import ONE  # noqa: E402
from atlas_survivor_infinite_projection import hard_pairs  # noqa: E402
from atlas_survivor_prefix_obstruction import (  # noqa: E402
    cylinder_projection,
    leavitt_is_zero,
    leavitt_star,
)
from atlas_two_chart_search import leavitt_add, leavitt_mul  # noqa: E402


def product(*values):
    result = ONE
    for value in values:
        result = leavitt_mul(result, value)
    return result


def xor_sum(*values):
    result = {}
    for value in values:
        result = leavitt_add(result, value)
    return result


def equal(left, right):
    return leavitt_is_zero(xor_sum(left, right))


def power(value, exponent):
    if exponent < 0:
        inverse = None
        running = ONE
        for candidate_exponent in range(1, 257):
            running = product(running, value)
            if equal(running, ONE):
                inverse = power(value, candidate_exponent - 1)
                break
        if inverse is None:
            raise AssertionError("failed to find finite order")
        return power(inverse, -exponent)
    result = ONE
    for _ in range(exponent):
        result = product(result, value)
    return result


def order(value, limit=256):
    running = ONE
    for exponent in range(1, limit + 1):
        running = product(running, value)
        if equal(running, ONE):
            return exponent
    return None


def main():
    _, _, _, _, q, ell = hard_pairs()[0]
    q_star = leavitt_star(q)
    ell_star = leavitt_star(ell)
    q_inverse = power(q, -1)
    ell_inverse = power(ell, -1)

    correct_certificate = xor_sum(
        product(ell_star, ell),
        product(q_star, q_star, ell_star, ell),
        product(ell_star, ell, q, q),
        product(q_star, q_star, ell_star, ell, q, q),
    )
    inverse_substitution = xor_sum(
        product(ell_inverse, ell),
        product(q_inverse, q_inverse, ell_inverse, ell),
        product(ell_inverse, ell, q, q),
        product(q_inverse, q_inverse, ell_inverse, ell, q, q),
    )
    target = cylinder_projection("001")

    result = {
        "hard_pair": "class 11, forward rotation 0",
        "q_order": order(q),
        "ell_order": order(ell),
        "q_leavitt_star_equals_group_inverse": equal(q_star, q_inverse),
        "ell_leavitt_star_equals_group_inverse": equal(ell_star, ell_inverse),
        "correct_certificate_equals_p_001": equal(correct_certificate, target),
        "p_001_nonzero": not leavitt_is_zero(target),
        "inverse_substitution_is_zero": leavitt_is_zero(inverse_substitution),
        "inverse_substitution_explanation":
            "1 + q^-2 + q^2 + q^-2 q^2 = q^-2 + q^2 = 0 because q^4 = 1",
    }
    if result != {
        "hard_pair": "class 11, forward rotation 0",
        "q_order": 4,
        "ell_order": 2,
        "q_leavitt_star_equals_group_inverse": False,
        "ell_leavitt_star_equals_group_inverse": False,
        "correct_certificate_equals_p_001": True,
        "p_001_nonzero": True,
        "inverse_substitution_is_zero": True,
        "inverse_substitution_explanation":
            "1 + q^-2 + q^2 + q^-2 q^2 = q^-2 + q^2 = 0 because q^4 = 1",
    }:
        raise AssertionError(result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
