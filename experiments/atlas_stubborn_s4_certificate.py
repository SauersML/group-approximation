"""Certify a finite quotient of the stubborn local atlas package.

The phase-preserving multi-relator optimizer consistently leaves certified
zero classes 70, 86, 90, and 91 near distance ``sqrt(2)`` while retaining
the phase class 11.  All five words happen to lie in a free product of two
order-24 matrix subgroups.  This script identifies those subgroups with S4,
then verifies a concrete quotient onto PSL(2,7): the four certified-zero
words become the identity while class 11 remains a nontrivial involution.

Everything below is finite exact arithmetic: matrices are over F2 and
permutations are tuples.  The companion GAP script independently discovered
the quotient from the resulting S4*S4 presentation.
"""

import collections
import json

import numpy as np

from atlas_kernel_collision_enumerator import (
    enumerate_ball,
    factor_projections,
    spanning_tree_kernel_words,
)
from atlas_two_chart_search import I4, gf2_mul, matrix_key


ZERO_INDICES = (70, 86, 90, 91)
PHASE_INDEX = 11

# Triangle generators s^2=t^3=(st)^4=1 for the two local S4 subgroups.
S_KEYS = {
    1: "01000000000100000001010000000001",
    2: "01000000000101000000010000000001",
}
T_KEYS = {
    1: "01010100000101000001000000000001",
    2: "01000000010101000001000000000001",
}

# Images found by GAP.  Tuple entries are zero-based images; multiplication
# below follows GAP's right-action convention, (x^(ab))=(x^a)^b.
CERTIFICATE = {
    "s1": (7, 6, 4, 5, 2, 3, 1, 0),
    "t1": (0, 3, 7, 4, 1, 2, 6, 5),
    "s2": (1, 0, 3, 2, 7, 6, 5, 4),
    "t2": (0, 1, 4, 5, 6, 7, 2, 3),
}

CENTRAL_CERTIFICATE = {
    "s1": (10, 5, 8, 14, 9, 1, 13, 12, 2, 4, 0, 15, 7, 6, 3, 11),
    "t1": (4, 8, 14, 1, 13, 5, 10, 2, 3, 9, 11, 6, 12, 0, 7, 15),
    "s2": (2, 10, 0, 6, 14, 7, 3, 5, 12, 11, 1, 9, 8, 15, 4, 13),
    "t2": (0, 1, 7, 3, 4, 12, 11, 8, 2, 15, 5, 13, 10, 6, 9, 14),
}
CENTRAL_PHASE = (
    3, 4, 6, 0, 1, 9, 2, 11, 13, 5, 14, 7, 15, 8, 10, 12,
)


def matrix_from_key(key):
    return np.frombuffer(bytes.fromhex(key), dtype=np.uint8).reshape(4, 4)


def permutation_product(left, right):
    """GAP product: apply ``left`` and then ``right``."""
    return tuple(right[left[index]] for index in range(len(left)))


def permutation_inverse(value):
    answer = [0] * len(value)
    for source, target in enumerate(value):
        answer[target] = source
    return tuple(answer)


def permutation_power(value, exponent):
    identity = tuple(range(len(value)))
    if exponent < 0:
        return permutation_power(permutation_inverse(value), -exponent)
    answer = identity
    base = value
    while exponent:
        if exponent & 1:
            answer = permutation_product(answer, base)
        base = permutation_product(base, base)
        exponent >>= 1
    return answer


def generated_permutation_group(generators):
    identity = tuple(range(len(generators[0])))
    seen = {identity}
    queue = collections.deque([identity])
    while queue:
        value = queue.popleft()
        for generator in generators:
            following = permutation_product(value, generator)
            if following not in seen:
                seen.add(following)
                queue.append(following)
    return seen


def local_factorizations(factor):
    """Return exact words in s,t for every element of the local subgroup."""
    s = matrix_from_key(S_KEYS[factor])
    t = matrix_from_key(T_KEYS[factor])
    t_inverse = gf2_mul(t, t)
    steps = ((f"s{factor}", s), (f"t{factor}", t),
             (f"t{factor}^-1", t_inverse))
    identity_key = matrix_key(I4)
    words = {identity_key: ()}
    values = {identity_key: I4.copy()}
    queue = collections.deque([identity_key])
    while queue:
        key = queue.popleft()
        value = values[key]
        for name, generator in steps:
            following = gf2_mul(value, generator)
            following_key = matrix_key(following)
            if following_key not in words:
                words[following_key] = words[key] + (name,)
                values[following_key] = following
                queue.append(following_key)
    if len(words) != 24:
        raise AssertionError(f"factor {factor} local subgroup is not S4")
    st = gf2_mul(s, t)
    if (matrix_key(gf2_mul(s, s)) != identity_key
            or matrix_key(gf2_mul(gf2_mul(t, t), t)) != identity_key
            or matrix_key(gf2_mul(gf2_mul(gf2_mul(st, st), st), st))
            != identity_key):
        raise AssertionError("triangle presentation relations failed")
    return words


def boundary_words():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    identity_key = matrix_key(I4)
    boundary = [word for word in words if any(
        matrix_key(projection) != identity_key
        for projection in factor_projections(word))]
    if len(boundary) != 234:
        raise AssertionError("complete boundary changed")
    return boundary


def translate(word, factorizations):
    answer = []
    for factor, matrix in word:
        key = matrix_key(matrix)
        if key not in factorizations[factor]:
            raise AssertionError("word left its asserted local S4 subgroup")
        answer.extend(factorizations[factor][key])
    return tuple(answer)


def evaluate_symbols(word, certificate=CERTIFICATE):
    identity = tuple(range(len(next(iter(certificate.values())))))
    value = identity
    for symbol in word:
        inverse = symbol.endswith("^-1")
        generator = certificate[symbol.removesuffix("^-1")]
        if inverse:
            generator = permutation_inverse(generator)
        value = permutation_product(value, generator)
    return value


def cycles(value):
    seen = set()
    answer = []
    for start in range(len(value)):
        if start in seen or value[start] == start:
            continue
        cycle = []
        point = start
        while point not in seen:
            seen.add(point)
            cycle.append(point + 1)
            point = value[point]
        answer.append(cycle)
    return answer


def main():
    identity = tuple(range(8))
    for factor in (1, 2):
        s = CERTIFICATE[f"s{factor}"]
        t = CERTIFICATE[f"t{factor}"]
        if (permutation_power(s, 2) != identity
                or permutation_power(t, 3) != identity
                or permutation_power(permutation_product(s, t), 4)
                != identity):
            raise AssertionError("certificate does not respect S4 relations")

    factorizations = {
        factor: local_factorizations(factor) for factor in (1, 2)
    }
    boundary = boundary_words()
    records = []
    for index in (*ZERO_INDICES, PHASE_INDEX):
        translated = translate(boundary[index], factorizations)
        image = evaluate_symbols(translated)
        expected_identity = index in ZERO_INDICES
        if (image == identity) != expected_identity:
            raise AssertionError(f"unexpected certificate image at {index}")
        records.append({
            "boundary_index": index,
            "target": "identity" if expected_identity else "nonidentity",
            "s4_word": list(translated),
            "image_cycles": cycles(image),
            "image_order": next(
                exponent for exponent in range(1, 9)
                if permutation_power(image, exponent) == identity),
        })

    image_group = generated_permutation_group(list(CERTIFICATE.values()))
    if len(image_group) != 168:
        raise AssertionError("certificate image does not have order 168")

    central_identity = tuple(range(16))
    for factor in (1, 2):
        s = CENTRAL_CERTIFICATE[f"s{factor}"]
        t = CENTRAL_CERTIFICATE[f"t{factor}"]
        if (permutation_power(s, 2) != central_identity
                or permutation_power(t, 3) != central_identity
                or permutation_power(permutation_product(s, t), 4)
                != central_identity):
            raise AssertionError("central certificate lost S4 relations")
    for index in ZERO_INDICES:
        translated = translate(boundary[index], factorizations)
        if evaluate_symbols(translated, CENTRAL_CERTIFICATE) != central_identity:
            raise AssertionError("central certificate lost a zero relation")
    central_phase_image = evaluate_symbols(
        translate(boundary[PHASE_INDEX], factorizations), CENTRAL_CERTIFICATE)
    if central_phase_image != CENTRAL_PHASE:
        raise AssertionError("central phase image changed")
    central_group = generated_permutation_group(
        list(CENTRAL_CERTIFICATE.values()))
    if len(central_group) != 2688:
        raise AssertionError("central certificate image order changed")
    center = [
        value for value in central_group
        if all(permutation_product(value, generator)
               == permutation_product(generator, value)
               for generator in CENTRAL_CERTIFICATE.values())
    ]
    if set(center) != {central_identity, CENTRAL_PHASE}:
        raise AssertionError("central certificate center is not C2")
    factor_orders = [
        len(generated_permutation_group([
            CENTRAL_CERTIFICATE[f"s{factor}"],
            CENTRAL_CERTIFICATE[f"t{factor}"],
        ]))
        for factor in (1, 2)
    ]
    if factor_orders != [24, 24]:
        raise AssertionError("central certificate collapsed a local factor")
    print(json.dumps({
        "local_factor_orders": [
            len(factorizations[1]), len(factorizations[2])],
        "quotient_image_order": len(image_group),
        "quotient_image_isomorphic_to": "PSL(2,7)",
        "records": records,
        "central_certificate": {
            "image_order": len(central_group),
            "image_structure": "(C2^4) : PSL(3,2)",
            "center_order": len(center),
            "factor_image_orders": factor_orders,
            "phase_cycles": cycles(central_phase_image),
            "phase_order": 2,
        },
    }, indent=2))


if __name__ == "__main__":
    main()
