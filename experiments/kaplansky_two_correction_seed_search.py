"""Test four exact affine lifts for a literal Kaplansky inverse pair on MSI.

The two corrections are supported on four group elements and evaluate to
zero in the binary Leavitt algebra. Only the four prescribed cases are used;
the partner universe is the existing radius-three/four atlas ball.
"""

import argparse
import json
import time

from depth_one_paired_leavitt_return_search import ONE, equal, multiply
from kaplansky_asymmetric_atlas_search import (
    S0, atlas_generators, cayley_ball, evaluate_sum, from_key, key,
    multiply_keys, solve_left_inverse,
)
from kaplansky_unipotent_product_search import A_WORDS, literal_product


CORRECTION_WORDS = (
    ((5, 3), (5, 3, 1), (5, 3, 4), (5, 3, 1, 4)),
    ((5, 3, 1), (5, 3, 4), (5, 3, 1, 3), (5, 4)),
)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=float, default=52)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    started = time.monotonic()
    identity = key(ONE)
    generators = tuple(key(g) for _, g in atlas_generators())

    def evaluate_word(word):
        result = identity
        for index in word:
            result = multiply_keys(result, generators[index])
        return result

    base = {evaluate_word(word) for word in A_WORDS}
    assert len(base) == 11
    mandatory = {evaluate_word(word) for word in A_WORDS[:4]}
    corrections = [
        {evaluate_word(word) for word in words} for words in CORRECTION_WORDS
    ]
    for correction in corrections:
        assert len(correction) == 4
        assert equal(evaluate_sum([from_key(g) for g in correction]), frozenset())

    cases = []
    for case in range(4):
        support = base.copy()
        for bit, correction in enumerate(corrections):
            if (case >> bit) & 1:
                support.symmetric_difference_update(correction)
        assert mandatory <= support
        assert len(support) % 2 == 1
        assert equal(evaluate_sum([from_key(g) for g in support]), S0)
        cases.append(tuple(sorted(support)))

    result = {
        "status": "running", "base_words": A_WORDS,
        "correction_words": CORRECTION_WORDS,
        "case_support_sizes": [len(case) for case in cases], "checks": [],
    }

    def record():
        result["elapsed_seconds"] = time.monotonic() - started
        with open(args.output, "w") as stream:
            json.dump(result, stream, indent=2)

    record()
    for radius in (3, 4):
        if radius == 4 and time.monotonic() - started > 15:
            result["status"] = "radius_four_not_started_after_slow_radius_three"
            break
        _, ball, words = cayley_ball(radius)
        for case, a_keys in enumerate(cases):
            if time.monotonic() - started > args.seconds:
                result["status"] = "budget_expired_between_cases"
                record()
                print(json.dumps(result), flush=True)
                return
            case_started = time.monotonic()
            a_support = [from_key(g) for g in a_keys]
            inverse = solve_left_inverse(ball, a_support)
            result["checks"].append({
                "radius": radius, "partner_count": len(ball), "case": case,
                "a_support_size": len(a_keys), "solvable": inverse is not None,
                "seconds": time.monotonic() - case_started,
            })
            print(json.dumps(result["checks"][-1]), flush=True)
            record()
            if inverse is None:
                continue

            b_keys = tuple(key(ball[i]) for i in inverse)
            forward = literal_product(b_keys, a_keys)
            reverse = literal_product(a_keys, b_keys)
            assert forward == {identity}
            assert reverse != {identity}
            b_evaluation = evaluate_sum([from_key(g) for g in b_keys])
            assert equal(multiply(b_evaluation, S0), ONE)
            assert not equal(multiply(S0, b_evaluation), ONE)
            result.update(
                status="COUNTEREXAMPLE_FOUND", hit_case=case, hit_radius=radius,
                a_keys=a_keys, b_words=[words[i] for i in inverse],
                reverse_keys=sorted(reverse),
            )
            record()
            print(json.dumps(result), flush=True)
            return
    else:
        result["status"] = "no_hit_in_all_eight_prescribed_checks"

    record()
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
