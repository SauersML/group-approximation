"""Audit the aligned and one-chart-trivial strata of the Atlas six relators.

This is deliberately not another ambient-degree scan.  It evaluates the six
literal frozen words in three canonical degree-eleven representations:

* the two marked natural A8 charts are aligned;
* the first chart is trivial and the second is natural;
* the first chart is natural and the second is trivial.

Together with the exhaustive A11 census, the aligned evaluation identifies
the unique five-boundary survivor.  The two retraction evaluations are the
componentwise input needed when permutation representations split into
natural A8 orbit blocks.
"""

import json

from atlas_six_relator_a11_scan import RELATOR_ORDER, decode_words, evaluate
from atlas_a9_two_chart_scan import exceptional_a8_map, inverse, multiply


DEGREE = 11


def order(value):
    identity = tuple(range(len(value)))
    power = identity
    for exponent in range(1, 1000):
        power = multiply(power, value)
        if power == identity:
            return exponent
    raise AssertionError("permutation order exceeded audit bound")


def support(value):
    return [index + 1 for index, image in enumerate(value) if index != image]


def evaluate_stratum(words, images, first_natural, second_natural):
    identity = tuple(range(DEGREE))
    result = {}
    for name in RELATOR_ORDER:
        value = identity
        for factor, key in words[name]:
            natural = first_natural if factor == 1 else second_natural
            letter = images[key] if natural else identity
            value = multiply(value, letter)
        result[name] = {
            "identity": value == identity,
            "order": order(value),
            "support": support(value),
        }
    return result


def main():
    words, matrices = decode_words()
    images = exceptional_a8_map(matrices, DEGREE)
    identity = tuple(range(DEGREE))
    aligned = {}
    for name in RELATOR_ORDER:
        value = evaluate(words[name], images, identity, inverse(identity), identity)
        aligned[name] = {
            "identity": value == identity,
            "order": order(value),
            "support": support(value),
        }

    record = {
        "ambient": "natural A8 action on eight points plus three fixed points",
        "relators": list(RELATOR_ORDER),
        "aligned_charts": aligned,
        "first_chart_trivial": evaluate_stratum(words, images, False, True),
        "second_chart_trivial": evaluate_stratum(words, images, True, False),
    }
    print(json.dumps(record, indent=2))


if __name__ == "__main__":
    main()
