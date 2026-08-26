"""Sparse exact balanced-area collector for the complete rank-five Atlas packet.

This implements (BAT1) without dense regular-A8 matrices and without the
formal 3^(2l) sector expansion.  Expand

    U = E tensor 1 + ((I+W)/2-E) tensor S + ((I-W)/2) tensor D

one projector slot at a time.  Terms with no E stay affine permutations
``L_g W^epsilon``.  For terms containing E, choose the first E in the
original slot order and rotate the tracial product to it.  Between successive
E's only one affine permutation must be retained, and a segment contributes
iff its translation part is the identity.  Coefficient words are reduced in
parallel to ``t^A S^a D^b`` using ``S D = t D S``.

The conservative state cap aborts before a large allocation and prints an
exact remote/MSI command.  No 20,160 by 20,160 matrix is allocated.
"""

import argparse
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import atlas_relator_rank5_complete_packet as complete_packet  # noqa: E402
from atlas_two_chart_search import I4, gf2_inv, gf2_mul  # noqa: E402


GROUP_ORDER = 20_160
IDENTITY = I4.tobytes()
MONOMIAL_IDENTITY = (0, 0, 0)  # area, S exponent, D exponent


def matrix_from_key(key):
    return np.frombuffer(key, dtype=np.uint8).reshape(4, 4)


@lru_cache(maxsize=8_192)
def group_mul(left, right):
    return gf2_mul(matrix_from_key(left), matrix_from_key(right)).tobytes()


@lru_cache(maxsize=None)
def outer(value):
    return gf2_inv(matrix_from_key(value)).T.copy().tobytes()


def affine_mul(left, right):
    """Multiply L_g W^epsilon by L_h W^eta."""
    g, epsilon = left
    h, eta = right
    return (group_mul(g, outer(h) if epsilon else h), epsilon ^ eta)


AFFINE_IDENTITY = (IDENTITY, 0)
AFFINE_OUTER = (IDENTITY, 1)


def monomial_mul(left, right):
    """Multiply t^A S^a D^b using S D = t D S."""
    area, a, b = left
    other_area, c, d = right
    return (area + other_area - b * c, a + c, b + d)


MONOMIALS = {0: MONOMIAL_IDENTITY, 1: (0, 1, 0), 2: (0, 0, 1)}
MONOMIAL_INVERSES = {0: MONOMIAL_IDENTITY, 1: (0, -1, 0), 2: (0, 0, -1)}


# An alternative is (is_E_reset, affine_label, coefficient_monomial, scalar).
def controlled_alternatives(inverse=False):
    monomials = MONOMIAL_INVERSES if inverse else MONOMIALS
    return (
        (True, AFFINE_IDENTITY, monomials[0], Fraction(1)),
        (False, AFFINE_IDENTITY, monomials[1], Fraction(1, 2)),
        (False, AFFINE_OUTER, monomials[1], Fraction(1, 2)),
        (True, AFFINE_IDENTITY, monomials[1], Fraction(-1)),
        (False, AFFINE_IDENTITY, monomials[2], Fraction(1, 2)),
        (False, AFFINE_OUTER, monomials[2], Fraction(-1, 2)),
    )


LEFT_CONTROLLED = controlled_alternatives(False)
RIGHT_CONTROLLED = controlled_alternatives(True)


def fixed_alternatives(matrix):
    return ((False, (matrix, 0), MONOMIAL_IDENTITY, Fraction(1)),)


def word_slots(word):
    slots = []
    projector_positions = []
    for factor, matrix in word:
        if factor == 1:
            slots.append(("fixed", fixed_alternatives(matrix.tobytes())))
        else:
            projector_positions.append(len(slots))
            slots.append(("left", LEFT_CONTROLLED))
            slots.append(("fixed", fixed_alternatives(matrix.tobytes())))
            projector_positions.append(len(slots))
            slots.append(("right", RIGHT_CONTROLLED))
    return slots, projector_positions


def add_state(target, key, value):
    if not value:
        return
    updated = target.get(key, Fraction(0)) + value
    if updated:
        target[key] = updated
    elif key in target:
        del target[key]


class StateCapExceeded(RuntimeError):
    pass


def advance(states, alternatives, state_cap, allow_reset,
            reset_requires_identity, remaining_left, remaining_right):
    next_states = {}
    for (affine, monomial), scalar in states.items():
        for is_reset, right_affine, right_monomial, right_scalar in alternatives:
            if is_reset:
                if not allow_reset:
                    continue
                if reset_requires_identity and affine[0] != IDENTITY:
                    continue
                product_affine = AFFINE_IDENTITY
            else:
                product_affine = affine_mul(affine, right_affine)
            product_monomial = monomial_mul(monomial, right_monomial)
            _area, a, b = product_monomial
            if not (-remaining_left <= a <= remaining_right):
                continue
            if not (-remaining_left <= b <= remaining_right):
                continue
            add_state(next_states, (product_affine, product_monomial),
                      scalar * right_scalar)
    if len(next_states) > state_cap:
        raise StateCapExceeded("%d states" % len(next_states))
    return next_states


@lru_cache(maxsize=1)
def twisted_fixed_counts():
    """Return g -> #{x in GL(4,2): g outer(x)=x}, using 4x4 matrices."""
    # g = x outer(x)^(-1) = x x^T.
    counts = defaultdict(int)
    for bits in range(1 << 16):
        matrix = np.array([(bits >> i) & 1 for i in range(16)],
                          dtype=np.uint8).reshape(4, 4)
        try:
            gf2_inv(matrix)
        except ValueError:
            continue
        counts[gf2_mul(matrix, matrix.T).tobytes()] += 1
    if sum(counts.values()) != GROUP_ORDER:
        raise AssertionError("GL(4,2) enumeration changed")
    return dict(counts)


def affine_trace(affine):
    matrix, parity = affine
    if not parity:
        return Fraction(int(matrix == IDENTITY))
    return Fraction(twisted_fixed_counts().get(matrix, 0), GROUP_ORDER)


def balanced_add(polynomial, states, trace_function):
    for (affine, (area, a, b)), scalar in states.items():
        if a == 0 and b == 0:
            polynomial[area] += scalar * trace_function(affine)


def collect_word(word, state_cap):
    slots, projector_positions = word_slots(word)
    polynomial = defaultdict(Fraction)
    peak = 1

    states = {(AFFINE_IDENTITY, MONOMIAL_IDENTITY): Fraction(1)}
    left_remaining = sum(kind == "left" for kind, _alternatives in slots)
    right_remaining = sum(kind == "right" for kind, _alternatives in slots)
    for kind, alternatives in slots:
        left_remaining -= kind == "left"
        right_remaining -= kind == "right"
        states = advance(states, alternatives, state_cap, False, False,
                         left_remaining, right_remaining)
        peak = max(peak, len(states))
    balanced_add(polynomial, states, affine_trace)

    slot_count = len(slots)
    for distinguished in projector_positions:
        _kind, distinguished_alternatives = slots[distinguished]
        reset_choices = tuple(alt for alt in distinguished_alternatives if alt[0])
        states = {}
        for _is_reset, _affine, monomial, scalar in reset_choices:
            add_state(states, (AFFINE_IDENTITY, monomial), scalar)
        sequence = [(distinguished + offset) % slot_count
                    for offset in range(1, slot_count)]
        left_remaining = sum(slots[index][0] == "left" for index in sequence)
        right_remaining = sum(slots[index][0] == "right" for index in sequence)
        for original_index in sequence:
            kind, alternatives = slots[original_index]
            left_remaining -= kind == "left"
            right_remaining -= kind == "right"
            # Original slots preceding the distinguished E are constrained
            # to be non-E so every expansion term is counted exactly once.
            allow_reset = original_index > distinguished
            states = advance(states, alternatives, state_cap,
                             allow_reset, True,
                             left_remaining, right_remaining)
            peak = max(peak, len(states))
        balanced_add(
            polynomial,
            states,
            lambda affine: Fraction(int(affine[0] == IDENTITY), GROUP_ORDER),
        )
    return {area: value for area, value in polynomial.items() if value}, peak


def encode_fraction(value):
    return [value.numerator, value.denominator]


def output_digest(rows):
    payload = json.dumps(rows, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode("ascii")).hexdigest()


def deserialize_word(entry):
    return [(factor, np.array([int(c) for c in bits], dtype=np.uint8)
                     .reshape(4, 4))
            for factor, bits in entry["word"]]


def poly_strip(value):
    value = list(value)
    while value and not value[-1]:
        value.pop()
    return tuple(value)


def poly_add(left, right):
    out = [Fraction(0)] * max(len(left), len(right))
    for index, coefficient in enumerate(left):
        out[index] += coefficient
    for index, coefficient in enumerate(right):
        out[index] += coefficient
    return poly_strip(out)


def poly_mul(left, right):
    if not left or not right:
        return ()
    out = [Fraction(0)] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] += a * b
    return poly_strip(out)


def poly_scale(value, scalar):
    return poly_strip([scalar * coefficient for coefficient in value])


def poly_divmod(dividend, divisor):
    if not divisor:
        raise ZeroDivisionError("zero polynomial")
    quotient = [Fraction(0)] * max(1, len(dividend) - len(divisor) + 1)
    remainder = list(dividend)
    while len(poly_strip(remainder)) >= len(divisor):
        remainder = list(poly_strip(remainder))
        degree = len(remainder) - len(divisor)
        coefficient = remainder[-1] / divisor[-1]
        quotient[degree] += coefficient
        for index, value in enumerate(divisor):
            remainder[index + degree] -= coefficient * value
    return poly_strip(quotient), poly_strip(remainder)


def poly_xgcd(left, right):
    old_r, r = poly_strip(left), poly_strip(right)
    old_s, s = (Fraction(1),), ()
    old_t, t = (), (Fraction(1),)
    while r:
        quotient, remainder = poly_divmod(old_r, r)
        old_r, r = r, remainder
        old_s, s = s, poly_add(old_s, poly_scale(poly_mul(quotient, s), -1))
        old_t, t = t, poly_add(old_t, poly_scale(poly_mul(quotient, t), -1))
    if not old_r:
        return (), (), ()
    scale = Fraction(1, 1) / old_r[-1]
    return (poly_scale(old_r, scale), poly_scale(old_s, scale),
            poly_scale(old_t, scale))


def laurent_relation(polynomial):
    """Return the shift and ordinary polynomial for f(t)-1 on C*."""
    coefficients = dict(polynomial)
    coefficients[0] = coefficients.get(0, Fraction(0)) - 1
    coefficients = {area: value for area, value in coefficients.items() if value}
    if not coefficients:
        return 0, ()
    minimum = min(coefficients)
    maximum = max(coefficients)
    return minimum, tuple(coefficients.get(area, Fraction(0))
                          for area in range(minimum, maximum + 1))


def encode_polynomial(value):
    return [encode_fraction(coefficient) for coefficient in value]


def collect(entries, state_cap, max_relators, stop_gcd_one):
    rows = []
    global_peak = 0
    running_gcd = ()
    bezout = {}
    relation_polynomials = {}
    gcd_steps = []
    selected = entries if max_relators <= 0 else entries[:max_relators]
    for index, entry in enumerate(selected):
        word = deserialize_word(entry)
        try:
            polynomial, peak = collect_word(word, state_cap)
        except StateCapExceeded as error:
            raise StateCapExceeded("%s (%s): %s" %
                                   (entry["name"], entry["source"], error))
        shift, relation = laurent_relation(polynomial)
        rows.append({
            "index": index,
            "source": entry["source"],
            "name": entry["name"],
            "syllables": entry["syllables"],
            "factor2_syllables": sum(1 for factor, _matrix in word
                                      if factor == 2),
            "peak_sparse_states": peak,
            "coefficients": [[area, *encode_fraction(polynomial[area])]
                             for area in sorted(polynomial)],
            "relation_shift": shift,
        })
        global_peak = max(global_peak, peak)
        if relation:
            relation_polynomials[index] = relation
            if not running_gcd:
                scale = Fraction(1, 1) / relation[-1]
                running_gcd = poly_scale(relation, scale)
                bezout = {index: (scale,)}
            else:
                running_gcd, old_multiplier, new_multiplier = poly_xgcd(
                    running_gcd, relation
                )
                bezout = {old_index: poly_mul(old_multiplier, certificate)
                           for old_index, certificate in bezout.items()}
                bezout[index] = new_multiplier
            gcd_steps.append({"index": index, "name": entry["name"],
                              "degree": len(running_gcd) - 1})
            if stop_gcd_one and running_gcd == (Fraction(1),):
                break
    certified = ()
    for relation_index, multiplier in bezout.items():
        certified = poly_add(
            certified,
            poly_mul(multiplier, relation_polynomials[relation_index]),
        )
    if certified != running_gcd:
        raise AssertionError("incremental Bezout certificate failed")
    decision = {
        "running_gcd": encode_polynomial(running_gcd),
        "gcd_steps": gcd_steps,
        "bezout_certificate": [
            {"index": index, "multiplier": encode_polynomial(multiplier)}
            for index, multiplier in sorted(bezout.items()) if multiplier
        ],
        "common_nonzero_root_excluded": running_gcd == (Fraction(1),),
        "certificate_identity":
            "sum multiplier[index] * t^(-relation_shift[index]) "
            "* (f_index(t)-1) = running_gcd(t)",
    }
    return rows, global_peak, decision


def run_controls(state_cap):
    from atlas_two_chart_search import gf2_inv, transvection

    generator = transvection(0, 1)
    controls = (
        ("empty", [], {0: Fraction(1)}),
        ("first_chart_nonidentity", [(1, generator)], {}),
        ("second_chart_nonidentity", [(2, generator)], {}),
        ("second_chart_identity", [(2, I4)], {0: Fraction(1)}),
        ("second_chart_cancel",
         [(2, generator), (2, gf2_inv(generator))], {0: Fraction(1)}),
    )
    for name, word, expected in controls:
        polynomial, _peak = collect_word(word, state_cap)
        if polynomial != expected:
            raise AssertionError("control %s failed: %s != %s" %
                                 (name, polynomial, expected))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--emit", default="",
                        help="write exact sparse BAT1 JSON to this path")
    parser.add_argument("--max-relators", type=int, default=0,
                        help="process only this initial prefix (0 means all)")
    parser.add_argument("--state-cap", type=int, default=50_000,
                        help="abort before a sparse state exceeds this cap")
    parser.add_argument("--stop-gcd-one", action="store_true",
                        help="stop once the exact incremental gcd is one")
    args = parser.parse_args()

    metadata, entries = complete_packet.assemble(False)
    run_controls(args.state_cap)
    try:
        rows, peak, decision = collect(entries, args.state_cap,
                                       args.max_relators, args.stop_gcd_one)
    except StateCapExceeded as error:
        print("LIGHTWEIGHT STOP:", error)
        print("remote/MSI command:")
        print("python3 experiments/atlas_three_mode_balanced_area.py "
              "--state-cap 2000000 --stop-gcd-one --emit "
              "experiments/atlas-rank5-balanced-area.json")
        return 3

    result_metadata = {
        "schema": "atlas-rank5-balanced-area-v1",
        "packet_word_list_sha256": metadata["word_list_sha256"],
        "packet_entries": len(entries),
        "processed_entries": len(rows),
        "state_cap": args.state_cap,
        "peak_sparse_states": peak,
        "balanced_table_sha256": output_digest(rows),
        "normal_form": "t^A S^a D^b with S D = t D S",
        "label_normal_forms": ["L_g W^epsilon", "first-E cyclic reset"],
        "gcd_decision": decision,
    }
    print(json.dumps(result_metadata, sort_keys=True))
    if args.emit:
        with open(args.emit, "w") as handle:
            json.dump({"metadata": result_metadata, "relators": rows},
                      handle, sort_keys=True, separators=(",", ":"))
            handle.write("\n")
        print("wrote", args.emit)
    return 0


if __name__ == "__main__":
    sys.exit(main())
