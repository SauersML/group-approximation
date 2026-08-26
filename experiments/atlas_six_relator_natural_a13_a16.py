"""Exact six-relator screen for natural A8 pairs with union degree 13--16.

Fix the first natural A8 on points 0,...,7. If the two eight-point supports
have union of size n, their intersection has size 16-n. Natural A8 is
6-transitive, so for n=13,...,16 there is one support position up to the
first chart. Every labeling of the second chart is a bijection from the
standard eight-point A8 set to that support; the 8! bijections include both
inner and outer markings.

The audit is pure exact permutation arithmetic. It uses the frozen six
free-product words and the already certified exceptional-isomorphism table
``atlas-a8-natural.json``. It does not enumerate any ambient alternating
group.
"""

from collections import Counter
import itertools
import json
import os


RELATOR_ORDER = ("s_0", "s_11", "s_30", "s_44", "s_55", "c_19243")


def multiply(left, right):
    """GAP right-action product: apply left, then right."""
    return tuple(right[left[index]] for index in range(len(left)))


def load_data():
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-a8-natural.json"), encoding="utf-8") as stream:
        natural = json.load(stream)["matrices"]
    with open(
        os.path.join(here, "atlas-six-relator-relative-pieces.json"),
        encoding="utf-8",
    ) as stream:
        relators = json.load(stream)["relators"]
    images = {
        key: tuple(int(value) - 1 for value in permutation)
        for key, permutation in natural.items()
    }
    words = {
        name: tuple((int(factor), key) for factor, key in relators[name]["word"])
        for name in RELATOR_ORDER
    }
    missing = sorted({key for word in words.values() for _, key in word} - images.keys())
    if missing:
        raise AssertionError(f"natural A8 table misses {len(missing)} word matrices")
    return images, words


def first_image(permutation, degree):
    return permutation + tuple(range(8, degree))


def second_image(permutation, labeling, degree):
    value = list(range(degree))
    for source, target in enumerate(permutation):
        value[labeling[source]] = labeling[target]
    return tuple(value)


def evaluate(word, first, second, identity):
    value = identity
    for factor, key in word:
        value = multiply(value, first[key] if factor == 1 else second[key])
    return value


def screen_degree(degree, images, words):
    overlap = 16 - degree
    support = tuple(range(overlap)) + tuple(range(8, degree))
    if len(support) != 8:
        raise AssertionError("second support does not have size eight")
    identity = tuple(range(degree))
    first = {key: first_image(value, degree) for key, value in images.items()}
    failure = Counter()
    survivors = []
    tested = 0
    for labeling in itertools.permutations(support):
        tested += 1
        second = {
            key: second_image(value, labeling, degree)
            for key, value in images.items()
        }
        for name in RELATOR_ORDER:
            if evaluate(words[name], first, second, identity) != identity:
                failure[name] += 1
                break
        else:
            survivors.append(tuple(value + 1 for value in labeling))
    if tested != 40320 or sum(failure.values()) + len(survivors) != tested:
        raise AssertionError("marking census did not close")
    return {
        "union_degree": degree,
        "support_intersection_size": overlap,
        "second_support": [value + 1 for value in support],
        "markings_tested": tested,
        "first_failure_histogram": {
            name: failure[name] for name in RELATOR_ORDER
        },
        "survivor_count": len(survivors),
        "first_survivor": None if not survivors else list(survivors[0]),
    }


def main():
    images, words = load_data()
    records = [screen_degree(degree, images, words) for degree in range(13, 17)]
    print(json.dumps({
        "ambient": "two marked natural A8 supports",
        "relators": list(RELATOR_ORDER),
        "degrees": records,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

